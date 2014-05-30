// Copyright 2013, Alex Horn. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

#ifndef __SMT_MSAT_H_
#define __SMT_MSAT_H_

#include <limits>
#include <cinttypes>
#include <mathsat.h>
#include <unordered_map>

#include "smt.h"

namespace smt
{

class MsatSolver : public Solver
{
private:
  msat_config m_config;
  msat_env m_env;
  msat_term m_term;

  typedef std::unordered_map<uintptr_t, const msat_term> TermMap;
  TermMap m_term_map;

  // \return has m_term been set to cached expression?
  bool find_term(const Expr* const expr)
  {
    const TermMap::const_iterator citer = m_term_map.find(
      reinterpret_cast<uintptr_t>(expr));

    if (citer == m_term_map.cend())
      return false;

    m_term = citer->second;
    return true;
  }

  // \pre: not find_term(expr)
  void cache_term(const Expr* const expr, const msat_term term)
  {
    m_term = term;
    assert(!MSAT_ERROR_TERM(m_term));

    bool ok = std::get<1>(m_term_map.emplace(
      reinterpret_cast<uintptr_t>(expr), term));
    assert(ok);
  }

  Error encode_number(
     const Expr* const expr,
     const std::string& literal_rep)
  {
    const Sort& sort = expr->sort();
    assert(!sort.is_bool());

    const char * const literal_str = literal_rep.c_str(); 
    if (sort.is_int()) {
      cache_term(expr, msat_make_number(m_env, literal_str));
    } else if (sort.is_bv()) {
      constexpr size_t base = 10;
      cache_term(expr, msat_make_bv_number(m_env, literal_str,
        sort.bv_size(), base));
    } else {
      return UNSUPPORT_ERROR;
    }

    return OK;
  }

  template<typename T>
  Error encode_literal(
     const Expr* const expr,
     typename std::enable_if<std::is_unsigned<T>::value, T>::type literal)
  {
    static_assert(std::is_unsigned<bool>::value, "Bool must be unsigned");

    const Sort& sort = expr->sort();
    if (sort.is_bool()) {
      if (literal) {
        cache_term(expr, msat_make_true(m_env));
      } else {
        cache_term(expr, msat_make_false(m_env));
      }
      return OK;
    }

    return encode_number(expr, std::to_string(literal));
  }

  template<typename T>
  Error encode_literal(
     const Expr* const expr,
     typename std::enable_if<std::is_signed<T>::value, T>::type literal)
  {
    const Sort& sort = expr->sort();

    if (sort.is_bv() and literal < 0) {
      assert(std::numeric_limits<intmax_t>::min() < literal);
      std::string abs_literal_rep = std::to_string(std::abs(literal));

      constexpr size_t base = 10;
      const msat_term number_term = msat_make_bv_number(m_env,
        abs_literal_rep.c_str(), sort.bv_size(), base);

      assert(!MSAT_ERROR_TERM(number_term));
      cache_term(expr, msat_make_bv_neg(m_env, number_term));
      return OK;
    }

    return encode_number(expr, std::to_string(literal));
  }

#define SMT_MSAT_CAST_ENCODE_BUILTIN_LITERAL(type)    \
  virtual Error __encode_literal(                     \
     const Expr* const expr,                          \
     type literal) override                           \
  {                                                   \
    if (find_term(expr))                              \
      return OK;                                      \
                                                      \
    return encode_literal<type>(expr, literal);       \
  }                                                   \

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
    const Expr* const expr,
    const UnsafeDecl& decl) override
  {
    if (find_term(expr))
      return OK;

    Error err;

    msat_type type;
    err = build_type(decl.sort(), type);
    if (err) {
      return err;
    }
    const char* const name = decl.symbol().c_str();
    const msat_decl constant_decl = msat_declare_function(m_env, name, type);
    assert(!MSAT_ERROR_DECL(constant_decl));
    cache_term(expr, msat_make_constant(m_env, constant_decl));
    return OK;
  }

  virtual Error __encode_func_app(
    const Expr* const expr,
    const UnsafeDecl& decl,
    const size_t arity,
    const SharedExpr* const args) override
  {
    if (find_term(expr))
      return OK;

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
    cache_term(expr, msat_make_uf(m_env, func_decl, arg_terms));
    return OK;
  }

  virtual Error __encode_const_array(
    const Expr* const expr,
    const SharedExpr& init) override
  {
    return UNSUPPORT_ERROR;
  }

  virtual Error __encode_array_select(
    const Expr* const expr,
    const SharedExpr& array,
    const SharedExpr& index) override
  {
    if (find_term(expr))
      return OK;

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

    cache_term(expr, msat_make_array_read(m_env, array_term, index_term));
    return OK;
  }

  virtual Error __encode_array_store(
    const Expr* const expr,
    const SharedExpr& array,
    const SharedExpr& index,
    const SharedExpr& value) override
  {
    if (find_term(expr))
      return OK;

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

    cache_term(expr, msat_make_array_write(m_env, array_term, index_term, value_term));
    return OK;
  }

  virtual Error __encode_unary_lnot(
    const Expr* const expr,
    const SharedExpr& arg) override
  {
    if (find_term(expr))
      return OK;

    const Error err = arg.encode(*this);
    if (err)
      return err;

    cache_term(expr, msat_make_not(m_env, m_term));
    return OK;
  }

  virtual Error __encode_unary_not(
    const Expr* const expr,
    const SharedExpr& arg) override
  {
    if (find_term(expr))
      return OK;

    const Error err = arg.encode(*this);
    if (err)
      return err;

    cache_term(expr, msat_make_bv_not(m_env, m_term));
    return OK;
  }

  virtual Error __encode_unary_sub(
    const Expr* const expr,
    const SharedExpr& arg) override
  {
    if (!expr->sort().is_bv())
      return UNSUPPORT_ERROR;

    if (find_term(expr))
      return OK;

    const Error err = arg.encode(*this);
    if (err)
      return err;

    cache_term(expr, msat_make_bv_neg(m_env, m_term));
    return OK;
  }

  virtual Error __encode_binary_sub(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg) override
  {
    if (find_term(expr))
      return OK;

    Error err;
    err = larg.encode(*this);
    if (err)
      return err;

    const msat_term lterm = m_term;

    err = rarg.encode(*this);
    if (err)
      return err;

    const msat_term rterm = m_term;

    cache_term(expr, msat_make_bv_minus(m_env, lterm, rterm));
    return OK;
  }

  virtual Error __encode_binary_and(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg) override
  {
    if (find_term(expr))
      return OK;

    Error err;
    err = larg.encode(*this);
    if (err)
      return err;

    const msat_term lterm = m_term;

    err = rarg.encode(*this);
    if (err)
      return err;

    const msat_term rterm = m_term;

    cache_term(expr, msat_make_bv_and(m_env, lterm, rterm));
    return OK;
  }

  virtual Error __encode_binary_or(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg) override
  {
    if (find_term(expr))
      return OK;

    Error err;
    err = larg.encode(*this);
    if (err)
      return err;

    const msat_term lterm = m_term;

    err = rarg.encode(*this);
    if (err)
      return err;

    const msat_term rterm = m_term;

    cache_term(expr, msat_make_bv_or(m_env, lterm, rterm));
    return OK;
  }

  virtual Error __encode_binary_xor(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg) override
  {
    if (find_term(expr))
      return OK;

    Error err;
    err = larg.encode(*this);
    if (err)
      return err;

    const msat_term lterm = m_term;

    err = rarg.encode(*this);
    if (err)
      return err;

    const msat_term rterm = m_term;

    cache_term(expr, msat_make_bv_xor(m_env, lterm, rterm));
    return OK;
  }

  virtual Error __encode_binary_land(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg) override
  {
    if (find_term(expr))
      return OK;

    Error err;
    err = larg.encode(*this);
    if (err)
      return err;

    const msat_term lterm = m_term;

    err = rarg.encode(*this);
    if (err)
      return err;

    const msat_term rterm = m_term;

    cache_term(expr, msat_make_and(m_env, lterm, rterm));
    return OK;
  }

  virtual Error __encode_binary_lor(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg) override
  {
    if (find_term(expr))
      return OK;

    Error err;
    err = larg.encode(*this);
    if (err)
      return err;

    const msat_term lterm = m_term;

    err = rarg.encode(*this);
    if (err)
      return err;

    const msat_term rterm = m_term;

    cache_term(expr, msat_make_or(m_env, lterm, rterm));
    return OK;
  }

  virtual Error __encode_binary_imp(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg) override
  {
    if (find_term(expr))
      return OK;

    Error err;
    err = larg.encode(*this);
    if (err)
      return err;

    const msat_term lterm = m_term;

    err = rarg.encode(*this);
    if (err)
      return err;

    const msat_term rterm = m_term;

    const msat_term not_lterm = msat_make_not(m_env, lterm);
    assert(!MSAT_ERROR_TERM(not_lterm));
    cache_term(expr, msat_make_or(m_env, not_lterm, rterm));

    return OK;
  }

  virtual Error __encode_binary_eql(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg) override
  {
    if (find_term(expr))
      return OK;

    Error err;
    err = larg.encode(*this);
    if (err)
      return err;

    const msat_term lterm = m_term;

    err = rarg.encode(*this);
    if (err)
      return err;

    const msat_term rterm = m_term;

    if (larg.sort().is_bool())
      cache_term(expr, msat_make_iff(m_env, lterm, rterm));
    else
      cache_term(expr, msat_make_equal(m_env, lterm, rterm));

    return OK;
  }

  virtual Error __encode_binary_add(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg) override
  {
    if (find_term(expr))
      return OK;

    Error err;
    err = larg.encode(*this);
    if (err)
      return err;

    const msat_term lterm = m_term;

    err = rarg.encode(*this);
    if (err)
      return err;

    const msat_term rterm = m_term;
    const Sort& sort = expr->sort();

    if (sort.is_bv())
      cache_term(expr, msat_make_bv_plus(m_env, lterm, rterm));
    else if (sort.is_int())
      cache_term(expr, msat_make_plus(m_env, lterm, rterm));
    else
      return UNSUPPORT_ERROR;

    return OK;
  }

  virtual Error __encode_binary_mul(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg) override
  {
    if (find_term(expr))
      return OK;

    Error err;
    err = larg.encode(*this);
    if (err)
      return err;

    const msat_term lterm = m_term;

    err = rarg.encode(*this);
    if (err)
      return err;

    const msat_term rterm = m_term;
    const Sort& sort = expr->sort();

    if (sort.is_bv())
      cache_term(expr, msat_make_bv_times(m_env, lterm, rterm));
    else if (sort.is_int())
      cache_term(expr, msat_make_times(m_env, lterm, rterm));
    else
      return UNSUPPORT_ERROR;

    return OK;
  }

  virtual Error __encode_binary_quo(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg) override
  {
    if (find_term(expr))
      return OK;

    Error err;
    err = larg.encode(*this);
    if (err)
      return err;

    const msat_term lterm = m_term;

    err = rarg.encode(*this);
    if (err)
      return err;

    const msat_term rterm = m_term;
    const Sort& sort = expr->sort();

    if (!sort.is_bv())
      return UNSUPPORT_ERROR;

    if (sort.is_signed())
      cache_term(expr, msat_make_bv_sdiv(m_env, lterm, rterm));
    else
      cache_term(expr, msat_make_bv_udiv(m_env, lterm, rterm));

    return OK;
  }

  virtual Error __encode_binary_rem(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg) override
  {
    if (find_term(expr))
      return OK;

    Error err;
    err = larg.encode(*this);
    if (err)
      return err;

    const msat_term lterm = m_term;

    err = rarg.encode(*this);
    if (err)
      return err;

    const msat_term rterm = m_term;
    const Sort& sort = expr->sort();

    if (!sort.is_bv())
      return UNSUPPORT_ERROR;

    if (sort.is_signed())
      cache_term(expr, msat_make_bv_srem(m_env, lterm, rterm));
    else
      cache_term(expr, msat_make_bv_urem(m_env, lterm, rterm));

    return OK;
  }

  virtual Error __encode_binary_lss(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg) override
  {
    if (find_term(expr))
      return OK;

    Error err;
    err = larg.encode(*this);
    if (err)
      return err;

    const msat_term lterm = m_term;

    err = rarg.encode(*this);
    if (err)
      return err;

    const msat_term rterm = m_term;

    if (larg.sort().is_bv())
    {
      if (larg.sort().is_signed())
        cache_term(expr, msat_make_bv_slt(m_env, lterm, rterm));
      else
        cache_term(expr, msat_make_bv_ult(m_env, lterm, rterm));
    }
    else if (larg.sort().is_int())
    {
      const msat_term leq_term = msat_make_leq(m_env, lterm, rterm);
      assert(!MSAT_ERROR_TERM(leq_term));
      const msat_term eq_term = msat_make_equal(m_env, lterm, rterm);
      assert(!MSAT_ERROR_TERM(eq_term));
      const msat_term neq_term = msat_make_not(m_env, eq_term);
      assert(!MSAT_ERROR_TERM(neq_term));
      cache_term(expr, msat_make_and(m_env, leq_term, neq_term));
    }
    else
    {
      return UNSUPPORT_ERROR;
    }

    return OK;
  }

  virtual Error __encode_binary_gtr(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg) override
  {
    if (find_term(expr))
      return OK;

    Error err;
    err = larg.encode(*this);
    if (err)
      return err;

    const msat_term lterm = m_term;

    err = rarg.encode(*this);
    if (err)
      return err;

    const msat_term rterm = m_term;

    if (larg.sort().is_bv())
    {
      if (larg.sort().is_signed())
        cache_term(expr, msat_make_bv_slt(m_env, rterm, lterm));
      else
        cache_term(expr, msat_make_bv_ult(m_env, rterm, lterm));
    }
    else if (larg.sort().is_int())
    {
      const msat_term geq_term = msat_make_leq(m_env, rterm, lterm);
      assert(!MSAT_ERROR_TERM(geq_term));
      const msat_term eq_term = msat_make_equal(m_env, lterm, rterm);
      assert(!MSAT_ERROR_TERM(eq_term));
      const msat_term neq_term = msat_make_not(m_env, eq_term);
      assert(!MSAT_ERROR_TERM(neq_term));
      cache_term(expr, msat_make_and(m_env, geq_term, neq_term));
    }

    return OK;
  }

  virtual Error __encode_binary_neq(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg) override
  {
    if (find_term(expr))
      return OK;

    Error err;
    err = larg.encode(*this);
    if (err)
      return err;

    const msat_term lterm = m_term;

    err = rarg.encode(*this);
    if (err)
      return err;

    const msat_term rterm = m_term;

    msat_term eq_term;
    if (larg.sort().is_bool())
      eq_term = msat_make_iff(m_env, lterm, rterm);
    else
      eq_term = msat_make_equal(m_env, lterm, rterm);

    assert(!MSAT_ERROR_TERM(eq_term));
    cache_term(expr, msat_make_not(m_env, eq_term));

    return OK;
  }

  virtual Error __encode_binary_leq(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg) override
  {
    if (find_term(expr))
      return OK;

    Error err;
    err = larg.encode(*this);
    if (err)
      return err;

    const msat_term lterm = m_term;

    err = rarg.encode(*this);
    if (err)
      return err;

    const msat_term rterm = m_term;

    if (larg.sort().is_bv())
    {
      if (larg.sort().is_signed())
        cache_term(expr, msat_make_bv_sleq(m_env, lterm, rterm));
      else
        cache_term(expr, msat_make_bv_uleq(m_env, lterm, rterm));
    }
    else if (larg.sort().is_int())
    {
      cache_term(expr, msat_make_leq(m_env, lterm, rterm));
    }

    return OK;
  }

  virtual Error __encode_binary_geq(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg) override
  {
    if (find_term(expr))
      return OK;

    Error err;
    err = larg.encode(*this);
    if (err)
      return err;

    const msat_term lterm = m_term;

    err = rarg.encode(*this);
    if (err)
      return err;

    const msat_term rterm = m_term;

    if (larg.sort().is_bv())
    {
      if (larg.sort().is_signed())
        cache_term(expr, msat_make_bv_sleq(m_env, rterm, lterm));
      else
        cache_term(expr, msat_make_bv_uleq(m_env, rterm, lterm));
    }
    else if (larg.sort().is_int())
    {
      cache_term(expr, msat_make_leq(m_env, rterm, lterm));
    }

    return OK;
  }

  virtual Error __encode_nary(
    const Expr* const expr,
    Opcode opcode,
    const SharedExprs& args) override
  {
    if (find_term(expr))
      return OK;

    Error err;

    if (opcode == NEQ)
    {
      // pair-wise disequality, formula size O(N^2)
      const Sort& bool_sort = internal::sort<Bool>();
      msat_term distinct_term = msat_make_true(m_env);
      for (SharedExprs::const_iterator outer = args.cbegin();
           outer != args.cend(); ++outer)
      {
        outer->encode(*this);
        const msat_term outer_term = m_term;

        for (SharedExprs::const_iterator inner = outer + 1;
             inner != args.cend(); ++inner)
        {
          assert(outer->sort() == inner->sort());

          inner->encode(*this);
          const msat_term inner_term = m_term;

          msat_term eq_term;
          if (outer->sort().is_bool())
            eq_term = msat_make_iff(m_env, outer_term, inner_term);
          else
            eq_term = msat_make_equal(m_env, outer_term, inner_term);

          distinct_term = msat_make_and(m_env, distinct_term,
            msat_make_not(m_env, eq_term));
        }

      }

      cache_term(expr, distinct_term);
      return OK;
    }

    if (opcode == LAND)
    {
      msat_term and_term = msat_make_true(m_env);
      for (const SharedExpr& arg : args)
      {
        err = arg.encode(*this);
        if (err)
          return err;

        and_term = msat_make_and(m_env, and_term, m_term);
      }

      cache_term(expr, and_term);
      return OK;
    }

    if (opcode == LOR)
    {
      msat_term or_term = msat_make_false(m_env);
      for (const SharedExpr& arg : args)
      {
        err = arg.encode(*this);
        if (err)
          return err;

        or_term = msat_make_or(m_env, or_term, m_term);
      }

      cache_term(expr, or_term);
      return OK;
    }

    return UNSUPPORT_ERROR;
  }

  virtual Error __encode_bv_zero_extend(
    const Expr* const expr,
    const SharedExpr& bv,
    const unsigned ext) override
  {
    if (find_term(expr))
      return OK;

    const Error err = bv.encode(*this);
    if (err) {
      return err;
    }

    cache_term(expr, msat_make_bv_zext(m_env, ext, m_term));
    return OK;
  }

  virtual Error __encode_bv_sign_extend(
    const Expr* const expr,
    const SharedExpr& bv,
    const unsigned ext) override
  {
    if (find_term(expr))
      return OK;

    const Error err = bv.encode(*this);
    if (err) {
      return err;
    }

    cache_term(expr, msat_make_bv_sext(m_env, ext, m_term));
    return OK;
  }

  virtual Error __encode_bv_extract(
    const Expr* const expr,
    const SharedExpr& bv,
    const unsigned high,
    const unsigned low) override
  {
    if (find_term(expr))
      return OK;

    const Error err = bv.encode(*this);
    if (err) {
      return err;
    }

    cache_term(expr, msat_make_bv_extract(m_env, high, low, m_term));
    return OK;
  }

  virtual void __notify_delete(const Expr* const expr) override
  {
    m_term_map.erase(reinterpret_cast<uintptr_t>(expr));
  }

  virtual void __reset() override
  {
    // keeps terms around!
    int status = msat_reset_env(m_env);
    assert(status == 0);
    m_term_map.clear();
  }

  virtual void __push() override
  {
    msat_push_backtrack_point(m_env);
  }

  virtual void __pop() override
  {
    msat_pop_backtrack_point(m_env);
  }

  virtual Error __unsafe_add(const SharedExpr& condition) override
  {
    const Error err = condition.encode(*this);
    if (err) {
      return err;
    }
    const int status = msat_assert_formula(m_env, m_term);
    assert(status == 0);
    return OK;
  }

  virtual Error __add(const Bool& condition) override
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

  virtual std::pair<CheckResult, SharedExprs::size_type>
  __check_assumptions(
    const SharedExprs& assumptions,
    SharedExprs& unsat_core) override
  {
    static constexpr char s_msat_prop_prefix[] = "msat_prop!";

    Error err;

    const size_t msat_props_size = assumptions.size();
    msat_term msat_props[msat_props_size];

    msat_term* msat_assertions = nullptr;
    size_t msat_props_index = 0, msat_assertions_size = 0;
    for (const SharedExpr& assumption : assumptions)
    {
      err = assumption.encode(*this);
      assert(err == OK);

      if (msat_term_is_constant(m_env, m_term))
      {
        msat_props[msat_props_index] = m_term;
      }
      else
      {
        // restore assertions later
        if (msat_assertions == nullptr)
          msat_assertions = msat_get_asserted_formulas(m_env, &msat_assertions_size);

        const msat_type bool_type = msat_get_bool_type(m_env);
        assert(!MSAT_ERROR_TYPE(bool_type));

        const std::string name = s_msat_prop_prefix + std::to_string(msat_props_index);
        const msat_decl constant_decl = msat_declare_function(m_env, name.c_str(), bool_type);
        assert(!MSAT_ERROR_DECL(constant_decl));

        const msat_term constant_term = msat_make_constant(m_env, constant_decl);
        assert(!MSAT_ERROR_TERM(constant_term));

        const msat_term iff_term = msat_make_iff(m_env, constant_term, m_term);
        assert(!MSAT_ERROR_TERM(iff_term));

        const int status = msat_assert_formula(m_env, iff_term);
        assert(status == 0);

        msat_props[msat_props_index] = constant_term;
      }

      assert(msat_props_index < msat_props_size);
      msat_props_index++;
    }

    msat_result result = msat_solve_with_assumptions(
      m_env, msat_props, msat_props_size);
    switch (result)
    {
    case MSAT_SAT:
      return {sat, 0};
    case MSAT_UNKNOWN:
      return {unknown, 0};
    default:
      assert(result == MSAT_UNSAT);
    }

    size_t msat_unsat_core_size;
    msat_term* msat_unsat_core = msat_get_unsat_assumptions(m_env, &msat_unsat_core_size);

    size_t term_id, i, j;
    SharedExprs::size_type k = unsat_core.size();
    for (i = msat_props_size; i != 0 && k != 0; --i)
    {
      term_id = msat_term_id(msat_props[i - 1]);
      for (j = i - 1; j != 0; --j)
      {
        if (term_id == msat_term_id(msat_props[j - 1]))
          goto SKIP_DUPLICATE;
      }

      // assume arbitrary ordering of assumptions in msat_unsat_core
      for (j = 0; j < msat_unsat_core_size; ++j)
      {
        if (term_id == msat_term_id(msat_unsat_core[j]))
          unsat_core[--k] = assumptions[i - 1];
      }

      SKIP_DUPLICATE: continue;
    }

    msat_free(msat_unsat_core);

    // restore original assertions
    if (msat_assertions != nullptr)
    {
      int status = msat_reset_env(m_env);
      assert(status == 0);

      while (msat_assertions_size != 0)
        msat_assert_formula(m_env, msat_assertions[--msat_assertions_size]);

      msat_free(msat_assertions);
    }

    // assume that msat_unsat_core may contain duplicates
    assert(unsat_core.size() - k <= msat_unsat_core_size);
    assert(msat_assertions_size == 0);
    return {unsat, unsat_core.size() - k};
  }

public:
  /// Auto configure MathSAT5
  MsatSolver()
  : Solver(),
    m_config(msat_create_config()),
    m_env(msat_create_env(m_config)),
    m_term(),
    m_term_map()
  {
    assert(!MSAT_ERROR_CONFIG(m_config));
    assert(!MSAT_ERROR_ENV(m_env));

    MSAT_MAKE_ERROR_TERM(m_term);
  }

  MsatSolver(Logic logic)
  : Solver(logic),
    m_config(msat_create_default_config(Logics::acronyms[logic])),
    m_env(msat_create_env(m_config)),
    m_term(),
    m_term_map()
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
