// Copyright 2013, Alex Horn. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

#ifndef __SMT_Z3_H_
#define __SMT_Z3_H_

#include <z3++.h>
#include <vector>

#include "smt.h"

namespace smt
{

class Z3Solver : public Solver
{
private:
  z3::context m_z3_context;
  z3::solver m_z3_solver;
  z3::expr m_z3_expr;

  template<typename T>
  Error nocast_encode_literal(
     const Expr* const expr,
     T literal)
  {
    const Sort& sort = expr->sort();

    if (sort.is_bool()) {
      m_z3_expr = m_z3_context.bool_val(literal);
    } else if (sort.is_int()) {
      m_z3_expr = m_z3_context.int_val(literal);
    } else if (sort.is_real()) {
      m_z3_expr = m_z3_context.real_val(literal);
    } else if (sort.is_bv()) {
      m_z3_expr = m_z3_context.bv_val(literal, sort.bv_size());
    } else {
      return UNSUPPORT_ERROR;
    }

    return OK;
  }

  template<typename T>
  Error cast_encode_literal(
     const Expr* const expr,
     T literal)
  {
    if (std::is_signed<T>::value) {
      return nocast_encode_literal<long long>(expr, literal);
    } else {
      return nocast_encode_literal<unsigned long long>(expr, literal);
    }
  }

#define SMT_Z3_NOCAST_ENCODE_BUILTIN_LITERAL(type)      \
  virtual Error __encode_literal(                       \
     const Expr* const expr,                            \
     type literal) override                             \
  {                                                     \
    return nocast_encode_literal(expr, literal);        \
  }                                                     \

#define SMT_Z3_CAST_ENCODE_BUILTIN_LITERAL(type)        \
  virtual Error __encode_literal(                       \
    const Expr* const expr,                             \
     type literal) override                             \
  {                                                     \
    return cast_encode_literal(expr, literal);          \
  }                                                     \

SMT_Z3_NOCAST_ENCODE_BUILTIN_LITERAL(bool)
SMT_Z3_NOCAST_ENCODE_BUILTIN_LITERAL(int)
SMT_Z3_NOCAST_ENCODE_BUILTIN_LITERAL(unsigned int)
SMT_Z3_NOCAST_ENCODE_BUILTIN_LITERAL(long long)
SMT_Z3_NOCAST_ENCODE_BUILTIN_LITERAL(unsigned long long)

SMT_Z3_CAST_ENCODE_BUILTIN_LITERAL(char)
SMT_Z3_CAST_ENCODE_BUILTIN_LITERAL(signed char)
SMT_Z3_CAST_ENCODE_BUILTIN_LITERAL(unsigned char)
SMT_Z3_CAST_ENCODE_BUILTIN_LITERAL(wchar_t)
SMT_Z3_CAST_ENCODE_BUILTIN_LITERAL(char16_t)
SMT_Z3_CAST_ENCODE_BUILTIN_LITERAL(char32_t)
SMT_Z3_CAST_ENCODE_BUILTIN_LITERAL(short)
SMT_Z3_CAST_ENCODE_BUILTIN_LITERAL(unsigned short)
SMT_Z3_CAST_ENCODE_BUILTIN_LITERAL(long)
SMT_Z3_CAST_ENCODE_BUILTIN_LITERAL(unsigned long)

  Error build_sort(const Sort& sort, z3::sort& z3_sort)
  {
    assert(!sort.is_func());

    if (sort.is_bool()) {
      z3_sort = m_z3_context.bool_sort();
    } else if (sort.is_int()) {
      z3_sort = m_z3_context.int_sort();
    } else if (sort.is_real()) {
      z3_sort = m_z3_context.int_sort();
    } else if (sort.is_bv()) {
      z3_sort = m_z3_context.bv_sort(sort.bv_size());
    } else if (sort.is_array()) {
      z3::sort z3_domain_sort(m_z3_context);
      z3::sort z3_range_sort(m_z3_context);

      Error err;
      err = build_sort(sort.sorts(0), z3_domain_sort);
      if (err) {
        return err;
      }
      err = build_sort(sort.sorts(1), z3_range_sort);
      if (err) {
        return err;
      }

      z3_sort = m_z3_context.array_sort(z3_domain_sort, z3_range_sort);
    } else {
      return UNSUPPORT_ERROR;
    }
    return OK;
  }

  Error decl_func(
    const std::string& symbol,
    const Sort& sort,
    z3::func_decl& z3_func_decl)
  {
    assert(sort.is_func());

    Error err;
    const z3::sort z3_arch_sort(m_z3_context);
    const size_t arity = sort.sorts_size() - 1;
    std::vector<z3::sort> z3_domain_sorts(arity, z3_arch_sort);
    for (int i = 0; i < arity; i++) {
      err = build_sort(sort.sorts(i), z3_domain_sorts[i]);
      if (err) {
        return err;
      }
    }

    z3::sort z3_range_sort(m_z3_context);
    err = build_sort(sort.sorts(arity), z3_range_sort);
    if (err) {
      return err;
    }

    z3_func_decl = m_z3_context.function(symbol.c_str(), arity,
      z3_domain_sorts.data(), z3_range_sort);
    return OK;
  }

  virtual Error __encode_constant(
    const Expr* const expr,
    const UnsafeDecl& decl) override
  {
    z3::sort z3_sort(m_z3_context);
    const Error err = build_sort(decl.sort(), z3_sort);
    if (err) {
      return err;
    }
    m_z3_expr = m_z3_context.constant(decl.symbol().c_str(), z3_sort);
    return OK;
  }

  virtual Error __encode_func_app(
    const Expr* const expr,
    const UnsafeDecl& func_decl,
    const size_t arity,
    const SharedExpr* const args) override
  {
    Error err;
    z3::func_decl z3_func_decl(m_z3_context);
    err = decl_func(func_decl.symbol(), func_decl.sort(), z3_func_decl);
    if (err) {
      return err;
    }

    const z3::expr z3_arch_expr(m_z3_context);
    std::vector<z3::expr> z3_args(arity, z3_arch_expr);
    for (int i = 0; i < arity; i++) {
      err = args[i].encode(*this);
      if (err) {
        return err;
      }
      z3_args[i] = m_z3_expr;
    }
    m_z3_expr = z3_func_decl(z3_args.size(), z3_args.data());

    return OK;
  }

  virtual Error __encode_const_array(
    const Expr* const expr,
    const SharedExpr& init) override
  {
    const Sort& sort = expr->sort();
    assert(sort.is_array());

    Error err;
    z3::sort z3_domain_sort(m_z3_context);
    err = build_sort(sort.sorts(0), z3_domain_sort);
    if (err) {
      return err;
    }

    err = init.encode(*this);
    if (err) {
      return err;
    }
    m_z3_expr = z3::const_array(z3_domain_sort, m_z3_expr);
    return OK;
  }

  virtual Error __encode_array_select(
    const Expr* const expr,
    const SharedExpr& array,
    const SharedExpr& index) override
  {
    Error err;

    err = array.encode(*this);
    if (err) {
      return err;
    }
    const z3::expr z3_array_expr(m_z3_expr);

    err = index.encode(*this);
    if (err) {
      return err;
    }
    const z3::expr z3_index_expr(m_z3_expr);

    m_z3_expr = z3::select(z3_array_expr, z3_index_expr);
    return OK;
  }

  virtual Error __encode_array_store(
    const Expr* const expr,
    const SharedExpr& array,
    const SharedExpr& index,
    const SharedExpr& value) override
  {
    Error err;

    err = array.encode(*this);
    if (err) {
      return err;
    }
    const z3::expr z3_array_expr(m_z3_expr);

    err = index.encode(*this);
    if (err) {
      return err;
    }
    const z3::expr z3_index_expr(m_z3_expr);

    err = value.encode(*this);
    if (err) {
      return err;
    }
    const z3::expr z3_value_expr(m_z3_expr);

    m_z3_expr = z3::store(z3_array_expr, z3_index_expr, z3_value_expr);
    return OK;
  }

  virtual Error __encode_unary_lnot(
    const Expr* const expr,
    const SharedExpr& arg) override
  {
    const Error err = arg.encode(*this);
    if (err)
      return err;

    m_z3_expr = !m_z3_expr;
    return OK;
  }

  virtual Error __encode_unary_not(
    const Expr* const expr,
    const SharedExpr& arg) override
  {
    const Error err = arg.encode(*this);
    if (err)
      return err;

    m_z3_expr = ~m_z3_expr;
    return OK;
  }

  virtual Error __encode_unary_sub(
    const Expr* const expr,
    const SharedExpr& arg) override
  {
    const Error err = arg.encode(*this);
    if (err)
      return err;

    m_z3_expr = -m_z3_expr;
    return OK;
  }

  virtual Error __encode_binary_sub(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg) override
  {
    Error err;
    err = larg.encode(*this);
    if (err)
      return err;

    const z3::expr lexpr(m_z3_expr);

    err = rarg.encode(*this);
    if (err)
      return err;

    const z3::expr rexpr(m_z3_expr);

    m_z3_expr = lexpr - rexpr;
    return OK;
  }

  virtual Error __encode_binary_and(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg) override
  {
    Error err;
    err = larg.encode(*this);
    if (err)
      return err;

    const z3::expr lexpr(m_z3_expr);

    err = rarg.encode(*this);
    if (err)
      return err;

    const z3::expr rexpr(m_z3_expr);

    m_z3_expr = lexpr & rexpr;
    return OK;
  }

  virtual Error __encode_binary_or(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg) override
  {
    Error err;
    err = larg.encode(*this);
    if (err)
      return err;

    const z3::expr lexpr(m_z3_expr);

    err = rarg.encode(*this);
    if (err)
      return err;

    const z3::expr rexpr(m_z3_expr);

    m_z3_expr = lexpr | rexpr;
    return OK;
  }

  virtual Error __encode_binary_xor(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg) override
  {
    Error err;
    err = larg.encode(*this);
    if (err)
      return err;

    const z3::expr lexpr(m_z3_expr);

    err = rarg.encode(*this);
    if (err)
      return err;

    const z3::expr rexpr(m_z3_expr);

    m_z3_expr = lexpr ^ rexpr;
    return OK;
  }

  virtual Error __encode_binary_lshl(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg) override
  {
    Error err;
    err = larg.encode(*this);
    if (err)
      return err;

    const z3::expr lexpr(m_z3_expr);

    err = rarg.encode(*this);
    if (err)
      return err;

    const z3::expr rexpr(m_z3_expr);


    m_z3_expr = z3::expr(m_z3_context,
      Z3_mk_bvshl(m_z3_context, lexpr, rexpr));

    return OK;
  }

  virtual Error __encode_binary_lshr(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg) override
  {
    Error err;
    err = larg.encode(*this);
    if (err)
      return err;

    const z3::expr lexpr(m_z3_expr);

    err = rarg.encode(*this);
    if (err)
      return err;

    const z3::expr rexpr(m_z3_expr);


    m_z3_expr = z3::expr(m_z3_context,
      Z3_mk_bvlshr(m_z3_context, lexpr, rexpr));

    return OK;
  }

  virtual Error __encode_binary_land(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg) override
  {
    Error err;
    err = larg.encode(*this);
    if (err)
      return err;

    const z3::expr lexpr(m_z3_expr);

    err = rarg.encode(*this);
    if (err)
      return err;

    const z3::expr rexpr(m_z3_expr);

    m_z3_expr = lexpr && rexpr;
    return OK;
  }

  virtual Error __encode_binary_lor(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg) override
  {
    Error err;
    err = larg.encode(*this);
    if (err)
      return err;

    const z3::expr lexpr(m_z3_expr);

    err = rarg.encode(*this);
    if (err)
      return err;

    const z3::expr rexpr(m_z3_expr);

    m_z3_expr = lexpr || rexpr;
    return OK;
  }

  virtual Error __encode_binary_imp(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg) override
  {
    Error err;
    err = larg.encode(*this);
    if (err)
      return err;

    const z3::expr lexpr(m_z3_expr);

    err = rarg.encode(*this);
    if (err)
      return err;

    const z3::expr rexpr(m_z3_expr);

    m_z3_expr = implies(lexpr, rexpr);
    return OK;
  }

  virtual Error __encode_binary_eql(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg) override
  {
    Error err;
    err = larg.encode(*this);
    if (err)
      return err;

    const z3::expr lexpr(m_z3_expr);

    err = rarg.encode(*this);
    if (err)
      return err;

    const z3::expr rexpr(m_z3_expr);

    m_z3_expr = lexpr == rexpr;
    return OK;
  }

  virtual Error __encode_binary_add(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg) override
  {
    Error err;
    err = larg.encode(*this);
    if (err)
      return err;

    const z3::expr lexpr(m_z3_expr);

    err = rarg.encode(*this);
    if (err)
      return err;

    const z3::expr rexpr(m_z3_expr);

    m_z3_expr = lexpr + rexpr;
    return OK;
  }

  virtual Error __encode_binary_mul(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg) override
  {
    Error err;
    err = larg.encode(*this);
    if (err)
      return err;

    const z3::expr lexpr(m_z3_expr);

    err = rarg.encode(*this);
    if (err)
      return err;

    const z3::expr rexpr(m_z3_expr);

    m_z3_expr = lexpr * rexpr;
    return OK;
  }

  virtual Error __encode_binary_quo(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg) override
  {
    Error err;
    err = larg.encode(*this);
    if (err)
      return err;

    const z3::expr lexpr(m_z3_expr);

    err = rarg.encode(*this);
    if (err)
      return err;

    const z3::expr rexpr(m_z3_expr);

    const Sort& sort = expr->sort();
    if (sort.is_bv() && !sort.is_signed())
      m_z3_expr = udiv(lexpr, rexpr);
    else
      m_z3_expr = lexpr / rexpr;

    return OK;
  }

  virtual Error __encode_binary_rem(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg) override
  {
    return UNSUPPORT_ERROR;
  }

  virtual Error __encode_binary_lss(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg) override
  {
    Error err;
    err = larg.encode(*this);
    if (err)
      return err;

    const z3::expr lexpr(m_z3_expr);

    err = rarg.encode(*this);
    if (err)
      return err;

    const z3::expr rexpr(m_z3_expr);

    const Sort& larg_sort = larg.sort();
    if (larg_sort.is_bv() && !larg_sort.is_signed())
      m_z3_expr = ult(lexpr, rexpr);
    else
      m_z3_expr = lexpr < rexpr;

    return OK;
  }

  virtual Error __encode_binary_gtr(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg) override
  {
    Error err;
    err = larg.encode(*this);
    if (err)
      return err;

    const z3::expr lexpr(m_z3_expr);

    err = rarg.encode(*this);
    if (err)
      return err;

    const z3::expr rexpr(m_z3_expr);

    const Sort& larg_sort = larg.sort();
    if (larg_sort.is_bv() && !larg_sort.is_signed())
      m_z3_expr = ugt(lexpr, rexpr);
    else
      m_z3_expr = lexpr > rexpr;

    return OK;
  }

  virtual Error __encode_binary_neq(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg) override
  {
    Error err;
    err = larg.encode(*this);
    if (err)
      return err;

    const z3::expr lexpr(m_z3_expr);

    err = rarg.encode(*this);
    if (err)
      return err;

    const z3::expr rexpr(m_z3_expr);

    m_z3_expr = lexpr != rexpr;
    return OK;
  }

  virtual Error __encode_binary_leq(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg) override
  {
    Error err;
    err = larg.encode(*this);
    if (err)
      return err;

    const z3::expr lexpr(m_z3_expr);

    err = rarg.encode(*this);
    if (err)
      return err;

    const z3::expr rexpr(m_z3_expr);

    const Sort& larg_sort = larg.sort();
    if (larg_sort.is_bv() && !larg_sort.is_signed())
      m_z3_expr = ule(lexpr, rexpr);
    else
      m_z3_expr = lexpr <= rexpr;

    return OK;
  }

  virtual Error __encode_binary_geq(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg) override
  {
    Error err;
    err = larg.encode(*this);
    if (err)
      return err;

    const z3::expr lexpr(m_z3_expr);

    err = rarg.encode(*this);
    if (err)
      return err;

    const z3::expr rexpr(m_z3_expr);

    const Sort& larg_sort = larg.sort();
    if (larg_sort.is_bv() && !larg_sort.is_signed())
      m_z3_expr = uge(lexpr, rexpr);
    else
      m_z3_expr = lexpr >= rexpr;

    return OK;
  }

  virtual Error __encode_nary(
    const Expr* const expr,
    Opcode opcode,
    const SharedExprs& args) override
  {
    switch (opcode)
    {
    case NEQ:
    case LAND:
    case LOR:
      break;

    default:
      return UNSUPPORT_ERROR;
    }

    Error err;

    size_t i = 0, args_size = args.size();
    Z3_ast asts[args_size];
    for (const SharedExpr& arg : args)
    {
      err = arg.encode(*this);
      if (err)
        return err;

      asts[i] = m_z3_expr;
      Z3_inc_ref(m_z3_context, asts[i]);

      assert(i < args_size);
      i++;
    }

    if (opcode == NEQ)
      m_z3_expr = z3::expr(m_z3_context,
        Z3_mk_distinct(m_z3_context, args_size, asts));
    else if (opcode == LAND)
      m_z3_expr = z3::expr(m_z3_context,
        Z3_mk_and(m_z3_context, args_size, asts));
    else if (opcode == LOR)
      m_z3_expr = z3::expr(m_z3_context,
        Z3_mk_or(m_z3_context, args_size, asts));

    for (i = 0; i < args_size; i++)
      Z3_dec_ref(m_z3_context, asts[i]);

    return OK;
  }

  virtual Error __encode_bv_zero_extend(
    const Expr* const expr,
    const SharedExpr& bv,
    const unsigned ext) override
  {
    const Error err = bv.encode(*this);
    if (err) {
      return err;
    }

    m_z3_expr = z3::expr(m_z3_context,
      Z3_mk_zero_ext(m_z3_context, ext, m_z3_expr));
    return OK;
  }

  virtual Error __encode_bv_sign_extend(
    const Expr* const expr,
    const SharedExpr& bv,
    const unsigned ext) override
  {
    const Error err = bv.encode(*this);
    if (err) {
      return err;
    }

    m_z3_expr = z3::expr(m_z3_context,
      Z3_mk_sign_ext(m_z3_context, ext, m_z3_expr));
    return OK;
  }

  virtual Error __encode_bv_extract(
    const Expr* const expr,
    const SharedExpr& bv,
    const unsigned high,
    const unsigned low) override
  {
    const Error err = bv.encode(*this);
    if (err) {
      return err;
    }

    m_z3_expr = z3::expr(m_z3_context,
      Z3_mk_extract(m_z3_context, high, low, m_z3_expr));
    return OK;
  }

  virtual void __notify_delete(const Expr* const expr) override
  {
    // do nothing
  }

  virtual void __reset() override
  {
    m_z3_solver.reset();
  }

  virtual void __push() override
  {
    m_z3_solver.push();
  }

  virtual void __pop() override
  {
    m_z3_solver.pop();
  }

  virtual Error __unsafe_add(const SharedExpr& condition) override
  {
    const Error err = condition.encode(*this);
    if (err)
      return err;

    m_z3_solver.add(m_z3_expr);
    return OK;
  }

  virtual Error __add(const Bool& condition) override
  {
    return __unsafe_add(condition);
  }

  virtual CheckResult __check() override
  {
    switch (m_z3_solver.check()) {
    case z3::unsat:
      return unsat;
    case z3::sat:
      return sat;
    case z3::unknown:
      return unknown;
    }
  }

  class TemporaryAssertions
  {
  private:
    z3::solver& m_solver_ref;

  public:
    TemporaryAssertions(z3::solver& solver_ref)
    : m_solver_ref(solver_ref)
    {
      m_solver_ref.push();
    }

    ~TemporaryAssertions()
    {
      m_solver_ref.pop();
    }
  };

  virtual std::pair<CheckResult, SharedExprs::size_type>
  __check_assumptions(
    const SharedExprs& assumptions,
    SharedExprs& unsat_core) override
  {
    static constexpr char s_z3_prop_prefix[] = "z3_prop!";

    TemporaryAssertions temporary_assertions(m_z3_solver);
    Error err;

    z3::expr z3_prop(m_z3_context);
    z3::expr_vector z3_props(m_z3_context);
    z3_props.resize(assumptions.size());

    size_t z3_props_index = 0;
    for (const SharedExpr& assumption : assumptions)
    {
      err = assumption.encode(*this);
      assert(err == OK);

      if (m_z3_expr.is_const())
      {
        Z3_ast_vector_set(m_z3_context, z3_props, z3_props_index++, m_z3_expr);
      }
      else
      {
        const std::string name = s_z3_prop_prefix + std::to_string(z3_props_index);
        z3_prop = m_z3_context.constant(name.c_str(), m_z3_context.bool_sort());
        m_z3_solver.add(implies(z3_prop, m_z3_expr));
        Z3_ast_vector_set(m_z3_context, z3_props, z3_props_index++, z3_prop);
      }
    }

    z3::check_result check_result = m_z3_solver.check(z3_props);
    switch (check_result)
    {
    case z3::sat:
      return {sat, 0};
    case z3::unknown:
      return {unknown, 0};
    default:
      assert(check_result == z3::unsat);
    }

    if (unsat_core.empty())
      return {unsat, 0};

    z3::expr_vector z3_unsat_core = m_z3_solver.unsat_core();
    if (z3_unsat_core.empty())
      return {unsat, 0};

    const size_t z3_unsat_core_size = z3_unsat_core.size();
    const size_t z3_props_size = z3_props.size();

    assert(z3_unsat_core_size != 0);
    assert(z3_unsat_core_size <= z3_props_size);

    size_t i, j;
    z3::expr x(m_z3_context);
    SharedExprs::size_type k = unsat_core.size();
    for (i = z3_props_size; i != 0 && k != 0; --i)
    {
      x = z3_props[i - 1];
      for (j = i - 1; j != 0; --j)
      {
        if (eq(x, z3_props[j - 1]))
          goto SKIP_DUPLICATE;
      }

      // ordering of assumptions in z3_unsat_core is undefined
      for (j = 0; j < z3_unsat_core_size; ++j)
      {
        if (eq(x, z3_unsat_core[j]))
          unsat_core[--k] = assumptions[i - 1];
      }

      SKIP_DUPLICATE: continue;
    }

    // z3_unsat_core may contain duplicates
    assert(unsat_core.size() - k <= z3_unsat_core_size);
    return {unsat, unsat_core.size() - k};
  }

public:
  /// Auto configure Z3
  Z3Solver()
  : Solver(),
    m_z3_context(),
    m_z3_solver(m_z3_context),
    m_z3_expr(m_z3_context) {}

  Z3Solver(Logic logic)
  : Solver(logic),
    m_z3_context(),
    m_z3_solver(m_z3_context, Logics::acronyms[logic]),
    m_z3_expr(m_z3_context) {}

  z3::context& context()
  {
    return m_z3_context;
  }

  z3::solver& solver()
  {
    return m_z3_solver;
  }

  const z3::expr& expr() const
  {
    return m_z3_expr;
  }
};

}

#endif
