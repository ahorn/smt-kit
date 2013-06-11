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
     const Sort& sort,
     T literal)
  {
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
     const Sort& sort,
     T literal)
  {
    if (std::is_signed<T>::value) {
      return nocast_encode_literal<long long>(sort, literal);
    } else {
      return nocast_encode_literal<unsigned long long>(sort, literal);
    }
  }

#define SMT_Z3_NOCAST_ENCODE_BUILTIN_LITERAL(type)\
  virtual Error __encode_literal(                 \
     const Sort& sort,                            \
     type literal) override                       \
  {                                               \
    return nocast_encode_literal(sort, literal);  \
  }                                               \

#define SMT_Z3_CAST_ENCODE_BUILTIN_LITERAL(type)  \
  virtual Error __encode_literal(                 \
     const Sort& sort,                            \
     type literal) override                       \
  {                                               \
    return cast_encode_literal(sort, literal);    \
  }                                               \

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
    const UnsafeDecl& func_decl,
    const size_t arity,
    const UnsafeExprPtr* const arg_ptrs) override
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
      err = arg_ptrs[i]->encode(*this);
      if (err) {
        return err;
      }
      z3_args[i] = m_z3_expr;
    }
    m_z3_expr = z3_func_decl(z3_args.size(), z3_args.data());

    return OK;
  }

  virtual Error __encode_const_array(
    const Sort& sort,
    UnsafeExprPtr init_ptr) override
  {
    assert(sort.is_array());

    Error err;
    z3::sort z3_domain_sort(m_z3_context);
    err = build_sort(sort.sorts(0), z3_domain_sort);
    if (err) {
      return err;
    }

    err = init_ptr->encode(*this);
    if (err) {
      return err;
    }
    m_z3_expr = z3::const_array(z3_domain_sort, m_z3_expr);
    return OK;
  }

  virtual Error __encode_array_select(
    UnsafeExprPtr array_ptr,
    UnsafeExprPtr index_ptr) override
  {
    Error err;

    err = array_ptr->encode(*this);
    if (err) {
      return err;
    }
    const z3::expr z3_array_expr(m_z3_expr);

    err = index_ptr->encode(*this);
    if (err) {
      return err;
    }
    const z3::expr z3_index_expr(m_z3_expr);

    m_z3_expr = z3::select(z3_array_expr, z3_index_expr);
    return OK;
  }

  virtual Error __encode_array_store(
    UnsafeExprPtr array_ptr,
    UnsafeExprPtr index_ptr,
    UnsafeExprPtr value_ptr) override
  {
    Error err;

    err = array_ptr->encode(*this);
    if (err) {
      return err;
    }
    const z3::expr z3_array_expr(m_z3_expr);

    err = index_ptr->encode(*this);
    if (err) {
      return err;
    }
    const z3::expr z3_index_expr(m_z3_expr);

    err = value_ptr->encode(*this);
    if (err) {
      return err;
    }
    const z3::expr z3_value_expr(m_z3_expr);

    m_z3_expr = z3::store(z3_array_expr, z3_index_expr, z3_value_expr);
    return OK;
  }

  virtual Error __encode_unary(
    Opcode opcode,
    const Sort& sort,
    UnsafeExprPtr ptr) override
  {
    const Error err = ptr->encode(*this);
    if (err) {
      return err;
    }
    switch (opcode) {
    case LNOT:
      m_z3_expr = !m_z3_expr;
      break;
    case NOT:
      m_z3_expr = ~m_z3_expr;
      break;
    case SUB:
      m_z3_expr = -m_z3_expr;
      break;
    default:
      return OPCODE_ERROR;
    }

    return OK;
  }

  virtual Error __encode_binary(
    Opcode opcode,
    const Sort& sort,
    UnsafeExprPtr lptr,
    UnsafeExprPtr rptr) override
  {
    Error err;
    err = lptr->encode(*this);
    if (err) {
      return err;
    }
    const z3::expr lexpr(m_z3_expr);

    err = rptr->encode(*this);
    if (err) {
      return err;
    }
    const z3::expr rexpr(m_z3_expr);

    switch (opcode) {
    case SUB:
      m_z3_expr = lexpr - rexpr;
      break;
    case AND:
      m_z3_expr = lexpr & rexpr;
      break;
    case OR:
      m_z3_expr = lexpr | rexpr;
      break;
    case XOR:
      m_z3_expr = lexpr ^ rexpr;
      break;
    case LAND:
      m_z3_expr = lexpr && rexpr;
      break;
    case LOR:
      m_z3_expr = lexpr || rexpr;
      break;
    case IMP:
      m_z3_expr = implies(lexpr, rexpr);
      break;
    case EQL:
      m_z3_expr = lexpr == rexpr;
      break;
    case ADD:
      m_z3_expr = lexpr + rexpr;
      break;
    case MUL:
      m_z3_expr = lexpr * rexpr;
      break;
    case QUO:
      if (sort.is_bv() && !sort.is_signed()) {
        m_z3_expr = udiv(lexpr, rexpr);
      } else {
        m_z3_expr = lexpr / rexpr;
      }
      break;
    case REM:
      return UNSUPPORT_ERROR;
    case LSS:
      {
        const Sort& lptr_sort = lptr->sort();
        if (lptr_sort.is_bv() && !lptr_sort.is_signed()) {
          m_z3_expr = ult(lexpr, rexpr);
        } else {
          m_z3_expr = lexpr < rexpr;
        }
      }
      break;
    case GTR:
      {
        const Sort& lptr_sort = lptr->sort();
        if (lptr_sort.is_bv() && !lptr_sort.is_signed()) {
          m_z3_expr = ugt(lexpr, rexpr);
        } else {
          m_z3_expr = lexpr > rexpr;
        }
      }
      break;
    case NEQ:
      m_z3_expr = lexpr != rexpr;
      break;
    case LEQ:
      {
        const Sort& lptr_sort = lptr->sort();
        if (lptr_sort.is_bv() && !lptr_sort.is_signed()) {
          m_z3_expr = ule(lexpr, rexpr);
        } else {
          m_z3_expr = lexpr <= rexpr;
        }
      }
      break;
    case GEQ:
      {
        const Sort& lptr_sort = lptr->sort();
        if (lptr_sort.is_bv() && !lptr_sort.is_signed()) {
          m_z3_expr = uge(lexpr, rexpr);
        } else {
          m_z3_expr = lexpr >= rexpr;
        }
      }
      break;
    default:
      return OPCODE_ERROR;
    }

    return OK;
  }

  virtual Error __encode_nary(
    Opcode opcode,
    const Sort& sort,
    const UnsafeExprPtrs& ptrs) override
  {
    if (opcode == NEQ) {
      // SMT-LIB 2.0 distinct variadic function, formula size O(N)
      size_t i = 0, ptrs_size = ptrs.size();
      Z3_ast asts[ptrs_size];
      for (const UnsafeExprPtr ptr : ptrs) {
        ptr->encode(*this);
        asts[i] = m_z3_expr;
        Z3_inc_ref(m_z3_context, asts[i]);

        assert(i < ptrs_size);
        i++;
      }

      m_z3_expr = z3::expr(m_z3_context,
        Z3_mk_distinct(m_z3_context, ptrs_size, asts));

      for (i = 0; i < ptrs_size; i++) {
        Z3_dec_ref(m_z3_context, asts[i]);
      }
    } else {
      return UNSUPPORT_ERROR;
    }

    return OK;
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

  virtual Error __unsafe_add(UnsafeExprPtr condition) override
  {
    const Error err = condition->encode(*this);
    if (err) {
      return err;
    }
    m_z3_solver.add(expr());
    return OK;
  }

  virtual Error __add(ExprPtr<sort::Bool> condition) override
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

public:
  Z3Solver()
  : m_z3_context(),
    m_z3_solver(m_z3_context),
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
