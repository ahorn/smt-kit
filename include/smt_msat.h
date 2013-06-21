// Copyright 2013, Alex Horn. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

#ifndef __SMT_MSAT_H_
#define __SMT_MSAT_H_

#include <limits>
#include <cinttypes>
#include <mathsat.h>

#include "smt.h"

namespace smt
{

class MsatSolver : public Solver
{
private:
  msat_config m_config;
  msat_env m_env;
  msat_term m_term;

  void set_term(msat_term term)
  {
    m_term = term;
    assert(!MSAT_ERROR_TERM(m_term));
  }

  Error encode_number(
     const Sort& sort,
     const std::string& literal_rep)
  {
    assert(!sort.is_bool());

    const char * const literal_str = literal_rep.c_str(); 
    if (sort.is_int()) {
      set_term(msat_make_number(m_env, literal_str));
    } else if (sort.is_bv()) {
      constexpr size_t base = 10;
      set_term(msat_make_bv_number(m_env, literal_str,
        sort.bv_size(), base));
    } else {
      return UNSUPPORT_ERROR;
    }

    return OK;
  }

  template<typename T>
  Error encode_literal(
     const Sort& sort,
     typename std::enable_if<std::is_unsigned<T>::value, T>::type literal)
  {
    static_assert(std::is_unsigned<bool>::value, "Bool must be unsigned");

    if (sort.is_bool()) {
      if (literal) {
        set_term(msat_make_true(m_env));
      } else {
        set_term(msat_make_false(m_env));
      }
      return OK;
    }

    return encode_number(sort, std::to_string(literal));
  }

  template<typename T>
  Error encode_literal(
     const Sort& sort,
     typename std::enable_if<std::is_signed<T>::value, T>::type literal)
  {
    if (sort.is_bv() and literal < 0) {
      assert(std::numeric_limits<intmax_t>::min() < literal);
      std::string abs_literal_rep = std::to_string(std::abs(literal));
      const Error err = encode_number(sort, std::move(abs_literal_rep));
      if (err) {
        return err;
      }

      set_term(msat_make_bv_neg(m_env, m_term));
      return OK;
    }

    return encode_number(sort, std::to_string(literal));
  }

#define SMT_MSAT_CAST_ENCODE_BUILTIN_LITERAL(type) \
  virtual Error __encode_literal(                  \
     const Sort& sort,                             \
     type literal) override                        \
  {                                                \
    return encode_literal<type>(sort, literal);    \
  }                                                \

SMT_MSAT_CAST_ENCODE_BUILTIN_LITERAL(bool)
SMT_MSAT_CAST_ENCODE_BUILTIN_LITERAL(char)
SMT_MSAT_CAST_ENCODE_BUILTIN_LITERAL(signed char)
SMT_MSAT_CAST_ENCODE_BUILTIN_LITERAL(unsigned char)
SMT_MSAT_CAST_ENCODE_BUILTIN_LITERAL(wchar_t)
SMT_MSAT_CAST_ENCODE_BUILTIN_LITERAL(char16_t)
SMT_MSAT_CAST_ENCODE_BUILTIN_LITERAL(char32_t)
SMT_MSAT_CAST_ENCODE_BUILTIN_LITERAL(short)
SMT_MSAT_CAST_ENCODE_BUILTIN_LITERAL(unsigned short)
SMT_MSAT_CAST_ENCODE_BUILTIN_LITERAL(int)
SMT_MSAT_CAST_ENCODE_BUILTIN_LITERAL(unsigned int)
SMT_MSAT_CAST_ENCODE_BUILTIN_LITERAL(long)
SMT_MSAT_CAST_ENCODE_BUILTIN_LITERAL(unsigned long)
SMT_MSAT_CAST_ENCODE_BUILTIN_LITERAL(long long)
SMT_MSAT_CAST_ENCODE_BUILTIN_LITERAL(unsigned long long)

  Error build_type(const Sort& sort, msat_type& type)
  {
    if (sort.is_bool()) {
      type = msat_get_bool_type(m_env);
    } else if (sort.is_int()) {
      type = msat_get_integer_type(m_env);
    } else if (sort.is_bv()) {
      type = msat_get_bv_type(m_env, sort.bv_size());
    } else if (sort.is_func()) {
      Error err;
      const size_t arity = sort.sorts_size() - 1;
      msat_type arg_types[arity];
      for (int i = 0; i < arity; i++) {
        err = build_type(sort.sorts(i), arg_types[i]);
        if (err) {
          return err;
        }
      }

      msat_type range_type;
      err = build_type(sort.sorts(arity), range_type);
      if (err) {
        return err;
      }

      type = msat_get_function_type(m_env, arg_types, arity, range_type);
    } else if (sort.is_array()) {
      msat_type domain_type;
      msat_type range_type;

      Error err;
      err = build_type(sort.sorts(0), domain_type);
      if (err) {
        return err;
      }
      err = build_type(sort.sorts(1), range_type);
      if (err) {
        return err;
      }

      // Based on our testing, MathSAT5 does not reliably support Bool as range
      assert(!msat_is_bool_type(m_env, range_type));

      type = msat_get_array_type(m_env, domain_type, range_type);
    } else {
      return UNSUPPORT_ERROR;
    }

    assert(!MSAT_ERROR_TYPE(type));
    return OK;
  }

  virtual Error __encode_constant(
    const UnsafeDecl& decl) override
  {
    Error err;

    msat_type type;
    err = build_type(decl.sort(), type);
    if (err) {
      return err;
    }
    const char* const name = decl.symbol().c_str();
    const msat_decl constant_decl = msat_declare_function(m_env, name, type);
    assert(!MSAT_ERROR_DECL(constant_decl));
    set_term(msat_make_constant(m_env, constant_decl));
    return OK;
  }

  virtual Error __encode_func_app(
    const UnsafeDecl& decl,
    const size_t arity,
    const UnsafeTerm* const args) override
  {
    Error err;
    msat_type func_type;
    err = build_type(decl.sort(), func_type);
    if (err) {
      return err;
    }

    msat_term arg_terms[arity];
    for (int i = 0; i < arity; i++) {
      err = args[i].encode(*this);
      if (err) {
        return err;
      }
      arg_terms[i] = m_term;
    }

    const char* const name = decl.symbol().c_str();
    const msat_decl func_decl = msat_declare_function(m_env, name, func_type);
    assert(!MSAT_ERROR_DECL(func_decl));
    set_term(msat_make_uf(m_env, func_decl, arg_terms));
    return OK;
  }

  virtual Error __encode_const_array(
    const Sort& sort,
    const UnsafeTerm& init) override
  {
    return UNSUPPORT_ERROR;
  }

  virtual Error __encode_array_select(
    const UnsafeTerm& array,
    const UnsafeTerm& index) override
  {
    Error err;
    err = array.encode(*this);
    if (err) {
      return err;
    }
    const msat_term array_term = m_term;

    err = index.encode(*this);
    if (err) {
      return err;
    }
    const msat_term index_term = m_term;

    set_term(msat_make_array_read(m_env, array_term, index_term));
    return OK;
  }

  virtual Error __encode_array_store(
    const UnsafeTerm& array,
    const UnsafeTerm& index,
    const UnsafeTerm& value) override
  {
    Error err;
    err = array.encode(*this);
    if (err) {
      return err;
    }
    const msat_term array_term = m_term;

    err = index.encode(*this);
    if (err) {
      return err;
    }
    const msat_term index_term = m_term;

    err = value.encode(*this);
    if (err) {
      return err;
    }
    const msat_term value_term = m_term;

    set_term(msat_make_array_write(m_env, array_term, index_term, value_term));
    return OK;
  }

  virtual Error __encode_unary(
    Opcode opcode,
    const Sort& sort,
    const UnsafeTerm& arg) override
  {
    const Error err = arg.encode(*this);
    if (err) {
      return err;
    }

    switch (opcode) {
    case LNOT:
      set_term(msat_make_not(m_env, m_term));
      break;
    case NOT:
      set_term(msat_make_bv_not(m_env, m_term));
      break;
    case SUB:
      if (sort.is_bv()) {
        set_term(msat_make_bv_neg(m_env, m_term));
      } else {
        return UNSUPPORT_ERROR;
      }
      break;
    default:
      return OPCODE_ERROR;
    }

    return OK;
  }

  virtual Error __encode_binary(
    Opcode opcode,
    const Sort& sort,
    const UnsafeTerm& larg,
    const UnsafeTerm& rarg) override
  {
    Error err;
    err = larg.encode(*this);
    if (err) {
      return err;
    }
    const msat_term lterm = m_term;

    err = rarg.encode(*this);
    if (err) {
      return err;
    }
    const msat_term rterm = m_term;

    switch (opcode) {
    case SUB:
      set_term(msat_make_bv_minus(m_env, lterm, rterm));
      break;
    case AND:
      set_term(msat_make_bv_and(m_env, lterm, rterm));
      break;
    case OR:
      set_term(msat_make_bv_or(m_env, lterm, rterm));
      break;
    case XOR:
      set_term(msat_make_bv_xor(m_env, lterm, rterm));
      break;
    case LAND:
      set_term(msat_make_and(m_env, lterm, rterm));
      break;
    case LOR:
      set_term(msat_make_or(m_env, lterm, rterm));
      break;
    case IMP:
      {
        const msat_term not_lterm = msat_make_not(m_env, lterm);
        assert(!MSAT_ERROR_TERM(not_lterm));
        set_term(msat_make_or(m_env, not_lterm, rterm));
      }
      break;
    case EQL:
      if (larg.sort().is_bool()) {
        set_term(msat_make_iff(m_env, lterm, rterm));
      } else {
        set_term(msat_make_equal(m_env, lterm, rterm));
      }
      break;
    case ADD:
      if (sort.is_bv()) {
        set_term(msat_make_bv_plus(m_env, lterm, rterm));
      } else if (sort.is_int()) {
        set_term(msat_make_plus(m_env, lterm, rterm));
      } else {
        return UNSUPPORT_ERROR;
      }
      break;
    case MUL:
      if (sort.is_bv()) {
        set_term(msat_make_bv_times(m_env, lterm, rterm));
      } else if (sort.is_int()) {
        set_term(msat_make_times(m_env, lterm, rterm));
      } else {
        return UNSUPPORT_ERROR;
      }
      break;
    case QUO:
      if (sort.is_bv()) {
        if (sort.is_signed()) {
          set_term(msat_make_bv_sdiv(m_env, lterm, rterm));
        } else {
          set_term(msat_make_bv_udiv(m_env, lterm, rterm));
        }
      } else {
        return UNSUPPORT_ERROR;
      }
      break;
    case REM:
      if (sort.is_bv()) {
        if (sort.is_signed()) {
          set_term(msat_make_bv_srem(m_env, lterm, rterm));
        } else {
          set_term(msat_make_bv_urem(m_env, lterm, rterm));
        }
      } else {
        return UNSUPPORT_ERROR;
      }
      break;
    case LSS:
      if (larg.sort().is_bv()) {
        if (larg.sort().is_signed()) {
          set_term(msat_make_bv_slt(m_env, lterm, rterm));
        } else {
          set_term(msat_make_bv_ult(m_env, lterm, rterm));
        }
      } else if (larg.sort().is_int()) {
        const msat_term leq_term = msat_make_leq(m_env, lterm, rterm);
        assert(!MSAT_ERROR_TERM(leq_term));
        const msat_term eq_term = msat_make_equal(m_env, lterm, rterm);
        assert(!MSAT_ERROR_TERM(eq_term));
        const msat_term neq_term = msat_make_not(m_env, eq_term);
        assert(!MSAT_ERROR_TERM(neq_term));
        set_term(msat_make_and(m_env, leq_term, neq_term));
      } else {
        return UNSUPPORT_ERROR;
      }
      break;
    case GTR:
      if (larg.sort().is_bv()) {
        if (larg.sort().is_signed()) {
          set_term(msat_make_bv_slt(m_env, rterm, lterm));
        } else {
          set_term(msat_make_bv_ult(m_env, rterm, lterm));
        }
      } else if (larg.sort().is_int()) {
        const msat_term geq_term = msat_make_leq(m_env, rterm, lterm);
        assert(!MSAT_ERROR_TERM(geq_term));
        const msat_term eq_term = msat_make_equal(m_env, lterm, rterm);
        assert(!MSAT_ERROR_TERM(eq_term));
        const msat_term neq_term = msat_make_not(m_env, eq_term);
        assert(!MSAT_ERROR_TERM(neq_term));
        set_term(msat_make_and(m_env, geq_term, neq_term));
      }
      break;
    case NEQ:
      msat_term eq_term;
      if (larg.sort().is_bool()) {
        eq_term = msat_make_iff(m_env, lterm, rterm);
      } else {
        eq_term = msat_make_equal(m_env, lterm, rterm);
      }
      assert(!MSAT_ERROR_TERM(eq_term));
      set_term(msat_make_not(m_env, eq_term));
      break;
    case LEQ:
      if (larg.sort().is_bv()) {
        if (larg.sort().is_signed()) {
          set_term(msat_make_bv_sleq(m_env, lterm, rterm));
        } else {
          set_term(msat_make_bv_uleq(m_env, lterm, rterm));
        }
      } else if (larg.sort().is_int()) {
        set_term(msat_make_leq(m_env, lterm, rterm));
      }
      break;
    case GEQ:
      if (larg.sort().is_bv()) {
        if (larg.sort().is_signed()) {
          set_term(msat_make_bv_sleq(m_env, rterm, lterm));
        } else {
          set_term(msat_make_bv_uleq(m_env, rterm, lterm));
        }
      } else if (larg.sort().is_int()) {
        set_term(msat_make_leq(m_env, rterm, lterm));
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
    const UnsafeTerms& args) override
  {
    if (opcode == NEQ) {
      // pair-wise disequality, formula size O(N^2)
      const Sort& bool_sort = internal::sort<sort::Bool>();
      msat_term distinct_term = msat_make_true(m_env);
      assert(!MSAT_ERROR_TERM(distinct_term));
      for (UnsafeTerms::const_iterator outer = args.cbegin();
           outer != args.cend(); outer++) {

        for (UnsafeTerms::const_iterator inner = outer + 1;
             inner != args.cend(); inner++) {

          encode_binary(NEQ, bool_sort, *outer, *inner);
          distinct_term = msat_make_and(m_env, distinct_term, m_term);
          assert(!MSAT_ERROR_TERM(distinct_term));
        }

      }
      m_term = distinct_term;
      return OK;
    } else {
      return UNSUPPORT_ERROR;
    }
  }

  virtual void __reset() override
  {
    msat_reset_env(m_env);
  }

  virtual void __push() override
  {
    msat_push_backtrack_point(m_env);
  }

  virtual void __pop() override
  {
    msat_pop_backtrack_point(m_env);
  }

  virtual Error __unsafe_add(const UnsafeTerm& condition) override
  {
    const Error err = condition.encode(*this);
    if (err) {
      return err;
    }
    const int status = msat_assert_formula(m_env, m_term);
    assert(status == 0);
    return OK;
  }

  virtual Error __add(const Term<sort::Bool>& condition) override
  {
    return __unsafe_add(condition);
  }

  virtual CheckResult __check() override
  {
    switch (msat_solve(m_env)) {
    case MSAT_UNSAT:
      return unsat;
    case MSAT_SAT:
      return sat;
    case MSAT_UNKNOWN:
      return unknown;
    }
  }

public:
  /// Auto configure MathSAT5
  MsatSolver()
  : m_config(msat_create_config()),
    m_env(msat_create_env(m_config)),
    m_term()
  {
    assert(!MSAT_ERROR_CONFIG(m_config));
    assert(!MSAT_ERROR_ENV(m_env));

    MSAT_MAKE_ERROR_TERM(m_term);
  }

  MsatSolver(Logic logic)
  : m_config(msat_create_default_config(Logics::acronyms[logic])),
    m_env(msat_create_env(m_config)),
    m_term()
  {
    assert(!MSAT_ERROR_CONFIG(m_config));
    assert(!MSAT_ERROR_ENV(m_env));

    MSAT_MAKE_ERROR_TERM(m_term);
  }

  ~MsatSolver()
  {
    msat_destroy_config(m_config);
    msat_destroy_env(m_env);
  }

  // `MSAT_ERROR_ENV(MsatSolver::env())` is false
  const msat_env env() const
  {
    return m_env;
  }

  // `MSAT_ERROR_TERM(MsatSolver::term())` is false
  const msat_term term() const
  {
    return m_term;
  }
};

}

#endif
