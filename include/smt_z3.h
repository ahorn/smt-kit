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
  z3::ast m_z3_ast;

  template<typename T>
  Error nocast_encode_builtin(
     const Sort& sort,
     T literal)
  {
    if (sort.is_bool()) {
      m_z3_ast = m_z3_context.bool_val(literal);
    } else if (sort.is_int()) {
      m_z3_ast = m_z3_context.int_val(literal);
    } else if (sort.is_real()) {
      m_z3_ast = m_z3_context.real_val(literal);
    } else if (sort.is_bv()) {
      m_z3_ast = m_z3_context.bv_val(literal, sort.bv_size());
    } else {
      return UNSUPPORT_ERROR;
    }

    return OK;
  }

  template<typename T>
  Error cast_encode_builtin(
     const Sort& sort,
     T literal)
  {
    if (std::is_signed<T>::value) {
      return nocast_encode_builtin<long long>(sort, literal);
    } else {
      return nocast_encode_builtin<unsigned long long>(sort, literal);
    }
  }

#define SMT_Z3_NOCAST_ENCODE_BUILTIN_LITERAL(type)\
  virtual Error __encode_builtin(                 \
     const Sort& sort,                            \
     type literal) override                       \
  {                                               \
    return nocast_encode_builtin(sort, literal);  \
  }                                               \

#define SMT_Z3_CAST_ENCODE_BUILTIN_LITERAL(type)  \
  virtual Error __encode_builtin(                 \
     const Sort& sort,                            \
     type literal) override                       \
  {                                               \
    return cast_encode_builtin(sort, literal);    \
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

  Error __build_sort(const Sort& sort, z3::sort& z3_sort)
  {
    if (sort.is_bool()) {
      z3_sort = m_z3_context.bool_sort();
    } else if (sort.is_int()) {
      z3_sort = m_z3_context.int_sort();
    } else if (sort.is_real()) {
      z3_sort = m_z3_context.int_sort();
    } else if (sort.is_bv()) {
      z3_sort = m_z3_context.bv_sort(sort.bv_size());
    } else if (sort.is_func()) {
      return DECL_ERROR;
    } else if (sort.is_array()) {
      z3::sort z3_domain_sort(m_z3_context);
      z3::sort z3_range_sort(m_z3_context);

      Error err;
      err = __build_sort(sort.sorts(0), z3_domain_sort);
      if (err) {
        return err;
      }
      err = __build_sort(sort.sorts(1), z3_range_sort);
      if (err) {
        return err;
      }

      z3_sort = m_z3_context.array_sort(z3_domain_sort, z3_range_sort);
    } else {
      return UNSUPPORT_ERROR;
    }
    return OK;
  }

  virtual Error __encode_decl(
    const std::string& symbol,
    const Sort& sort) override
  {
    Error err;
    if (sort.is_func()) {
      const z3::sort z3_arch_sort(m_z3_context);
      const size_t arity = sort.sorts_size() - 1;
      std::vector<z3::sort> z3_domain_sorts(arity, z3_arch_sort);
      for (int i = 0; i < arity; i++) {
        err = __build_sort(sort.sorts(i), z3_domain_sorts[i]);
        if (err) {
          return err;
        }
      }

      z3::sort z3_range_sort(m_z3_context);
      err = __build_sort(sort.sorts(arity), z3_range_sort);
      if (err) {
        return err;
      }

      m_z3_ast = m_z3_context.function(symbol.c_str(), arity,
        z3_domain_sorts.data(), z3_range_sort);
    } else {
      z3::sort z3_sort(m_z3_context);
      err = __build_sort(sort, z3_sort);
      if (err) {
        return err;
      }

      m_z3_ast = m_z3_context.constant(symbol.c_str(), z3_sort);
    }
    return OK;
  }

  virtual Error __encode_func_app(
    const UnsafeExprPtr func_ptr,
    const size_t arity,
    const UnsafeExprPtr* const arg_ptrs) override
  {
    assert(func_ptr->sort().is_func());
    assert(0 < arity);

    Error err;
    err = func_ptr->encode(*this);
    if (err) {
      return err;
    }
    const z3::func_decl z3_func_decl(m_z3_context,
      (Z3_func_decl)(static_cast<Z3_ast>(m_z3_ast)));

    const z3::expr z3_arch_expr(m_z3_context);
    std::vector<z3::expr> z3_args(arity, z3_arch_expr);
    for (int i = 0; i < arity; i++) {
      err = arg_ptrs[i]->encode(*this);
      if (err) {
        return err;
      }
      z3_args[i] = z3::expr(m_z3_context, m_z3_ast);
    }
    m_z3_ast = z3_func_decl(z3_args.size(), z3_args.data());

    return OK;
  }

  virtual Error __encode_const_array(
    const Sort& sort,
    UnsafeExprPtr init_ptr) override
  {
    assert(sort.is_array());

    Error err;
    z3::sort z3_domain_sort(m_z3_context);
    err = __build_sort(sort.sorts(0), z3_domain_sort);
    if (err) {
      return err;
    }

    err = init_ptr->encode(*this);
    if (err) {
      return err;
    }
    const z3::expr z3_init_expr(m_z3_context, m_z3_ast);
    m_z3_ast = z3::const_array(z3_domain_sort, z3_init_expr);
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
    const z3::expr z3_array_expr(m_z3_context, m_z3_ast);

    err = index_ptr->encode(*this);
    if (err) {
      return err;
    }
    const z3::expr z3_index_expr(m_z3_context, m_z3_ast);

    m_z3_ast = z3::select(z3_array_expr, z3_index_expr);
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
    const z3::expr z3_array_expr(m_z3_context, m_z3_ast);

    err = index_ptr->encode(*this);
    if (err) {
      return err;
    }
    const z3::expr z3_index_expr(m_z3_context, m_z3_ast);

    err = value_ptr->encode(*this);
    if (err) {
      return err;
    }
    const z3::expr z3_value_expr(m_z3_context, m_z3_ast);

    m_z3_ast = z3::store(z3_array_expr, z3_index_expr, z3_value_expr);
    return OK;
  }

  virtual Error __encode_builtin(
    Opcode opcode,
    const Sort& sort,
    UnsafeExprPtr ptr) override
  {
    const Error err = ptr->encode(*this);
    if (err) {
      return err;
    }
    const z3::expr expr(m_z3_context, m_z3_ast);
    switch (opcode) {
    case LNOT:
      m_z3_ast = !expr;
      break;
    case NOT:
      m_z3_ast = ~expr;
      break;
    case SUB:
      m_z3_ast = -expr;
      break;
    default:
      return OP_ERROR;
    }

    return OK;
  }

  virtual Error __encode_builtin(
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
    const z3::expr lexpr(m_z3_context, m_z3_ast);

    err = rptr->encode(*this);
    if (err) {
      return err;
    }
    const z3::expr rexpr(m_z3_context, m_z3_ast);

    switch (opcode) {
    case SUB:
      m_z3_ast = lexpr - rexpr;
      break;
    case AND:
      m_z3_ast = lexpr & rexpr;
      break;
    case OR:
      m_z3_ast = lexpr | rexpr;
      break;
    case XOR:
      m_z3_ast = lexpr ^ rexpr;
      break;
    case LAND:
      m_z3_ast = lexpr && rexpr;
      break;
    case LOR:
      m_z3_ast = lexpr || rexpr;
      break;
    case IMP:
      m_z3_ast = implies(lexpr, rexpr);
      break;
    case EQL:
      m_z3_ast = lexpr == rexpr;
      break;
    case ADD:
      m_z3_ast = lexpr + rexpr;
      break;
    case MUL:
      m_z3_ast = lexpr * rexpr;
      break;
    case QUO:
      if (sort.is_bv() && !sort.is_signed()) {
        m_z3_ast = udiv(lexpr, rexpr);
      } else {
        m_z3_ast = lexpr / rexpr;
      }
      break;
    case REM:
      return UNSUPPORT_ERROR;
    case LSS:
      if (sort.is_bv() && !sort.is_signed()) {
        m_z3_ast = ult(lexpr, rexpr);
      } else {
        m_z3_ast = lexpr < rexpr;
      }
      break;
    case GTR:
      if (sort.is_bv() && !sort.is_signed()) {
        m_z3_ast = ugt(lexpr, rexpr);
      } else {
        m_z3_ast = lexpr > rexpr;
      }
      break;
    case NEQ:
      m_z3_ast = lexpr != rexpr;
      break;
    case LEQ:
      if (sort.is_bv() && !sort.is_signed()) {
        m_z3_ast = ule(lexpr, rexpr);
      } else {
        m_z3_ast = lexpr <= rexpr;
      }
      break;
    case GEQ:
      if (sort.is_bv() && !sort.is_signed()) {
        m_z3_ast = uge(lexpr, rexpr);
      } else {
        m_z3_ast = lexpr >= rexpr;
      }
      break;
    default:
      return OP_ERROR;
    }

    return OK;
  }

  virtual void __push() override
  {
    m_z3_solver.push();
  }

  virtual void __pop() override
  {
    m_z3_solver.pop();
  }

  virtual Error __add(ExprPtr<sort::Bool> condition) override
  {
    const Error err = condition->encode(*this);
    if (err) {
      return err;
    }
    m_z3_solver.add(expr());
    return OK;
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
    m_z3_ast(m_z3_context) {}

  z3::context& context()
  {
    return m_z3_context;
  }

  z3::solver& solver()
  {
    return m_z3_solver;
  }

  const z3::ast& ast() const
  {
    return m_z3_ast;
  }

  z3::expr expr()
  {
    return z3::expr(m_z3_context, m_z3_ast);
  }
};

}

#endif