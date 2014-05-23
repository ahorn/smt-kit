// Copyright 2014, Alex Horn. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

#ifndef _SMT_STP_H_
#define _SMT_STP_H_

#include "smt.h"

#include <unordered_map>
#include <cstdint>
#include <tuple>

// avoid name clash
#define Expr VCExpr
#include <stp/c_interface.h>
#undef Expr

namespace smt
{

/// Experimental, Solver with bit vector support only!

/// May leak memory -- it is not always clear when the
/// STP interface frees memory automatically.
///
/// \see_also klee/lib/solver/Solver.cpp
/// \see_also StpSolver::__notify_delete(const Expr * const)
class StpSolver : public Solver
{
private:
  VC m_vc;
  VCExpr m_expr;

  typedef std::unordered_map<uintptr_t, const VCExpr> ExprMap;
  ExprMap m_expr_map;

  // \return has m_expr been set to cached expression?
  bool find_expr(const Expr* const expr)
  {
    const ExprMap::const_iterator citer = m_expr_map.find(
      reinterpret_cast<uintptr_t>(expr));

    if (citer == m_expr_map.cend())
      return false;

    m_expr = citer->second;
    return true;
  }

  // \pre: not find_expr(expr)
  void cache_expr(const Expr* const expr, const VCExpr vc_expr)
  {
    m_expr = vc_expr;

    bool ok = std::get<1>(m_expr_map.emplace(
      reinterpret_cast<uintptr_t>(expr), vc_expr));
    assert(ok);
  }
  
  template<typename T>
  void encode_bv_literal(
    const Expr* const expr,
    const unsigned bv_size,
    const T number)
  {
    if (find_expr(expr))
      return;

    cache_expr(expr, vc_bvConstExprFromInt(m_vc, bv_size, number));
  }

#define SMT_STP_ENCODE_BV_LITERAL(type)                     \
  virtual Error __encode_literal(                           \
     const Expr* const expr,                                \
     type literal) override                                 \
  {                                                         \
    const Sort& sort = expr->sort();                        \
    if (!sort.is_bv())                                      \
      return UNSUPPORT_ERROR;                               \
                                                            \
    encode_bv_literal<type>(expr, sort.bv_size(), literal); \
    return OK;                                              \
  }                                                         \

SMT_STP_ENCODE_BV_LITERAL(char)
SMT_STP_ENCODE_BV_LITERAL(signed char)
SMT_STP_ENCODE_BV_LITERAL(unsigned char)
SMT_STP_ENCODE_BV_LITERAL(wchar_t)
SMT_STP_ENCODE_BV_LITERAL(char16_t)
SMT_STP_ENCODE_BV_LITERAL(char32_t)
SMT_STP_ENCODE_BV_LITERAL(short)
SMT_STP_ENCODE_BV_LITERAL(unsigned short)
SMT_STP_ENCODE_BV_LITERAL(int)
SMT_STP_ENCODE_BV_LITERAL(unsigned int)
SMT_STP_ENCODE_BV_LITERAL(long)
SMT_STP_ENCODE_BV_LITERAL(unsigned long)
SMT_STP_ENCODE_BV_LITERAL(long long)
SMT_STP_ENCODE_BV_LITERAL(unsigned long long)

  virtual Error __encode_literal(
    const Expr* const expr,
    bool literal) override
  {
    const Sort& sort = expr->sort();
    if (sort.is_bool())
    {
      if (literal)
        m_expr = vc_trueExpr(m_vc);
      else
        m_expr = vc_falseExpr(m_vc);

      return OK;
    }

    if (!sort.is_bv())
      return UNSUPPORT_ERROR;

    encode_bv_literal<unsigned>(expr, sort.bv_size(), literal);
    return OK;
  }

  Error build_type(const Sort& sort, Type& type)
  {
    if (sort.is_bool())
    {
      type = vc_boolType(m_vc);
    }
    else if (sort.is_bv())
    {
      type = vc_bvType(m_vc, sort.bv_size());
    }
    else if (sort.is_array())
    {
      Type domain_type;
      Type range_type;

      Error err;
      err = build_type(sort.sorts(0), domain_type);
      if (err)
        return err;

      err = build_type(sort.sorts(1), range_type);
      if (err)
        return err;

      type = vc_arrayType(m_vc, domain_type, range_type);
    }
    else
    {
      return UNSUPPORT_ERROR;
    }

    return OK;
  }

  virtual Error __encode_constant(
    const Expr* const expr,
    const UnsafeDecl& decl) override
  {
    if (find_expr(expr))
      return OK;

    Type type;
    Error err = build_type(decl.sort(), type);
    if (err)
      return err;

    cache_expr(expr, vc_varExpr(m_vc, decl.symbol().c_str(), type));
    return OK;
  }

  virtual Error __encode_func_app(
    const Expr* const expr,
    const UnsafeDecl& decl,
    const size_t arity,
    const SharedExpr* const args) override
  {
    return UNSUPPORT_ERROR;
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
    if (find_expr(expr))
      return OK;

    Error err;
    err = array.encode(*this);
    if (err)
      return err;

    const VCExpr array_expr = m_expr;

    err = index.encode(*this);
    if (err)
      return err;

    const VCExpr index_expr = m_expr;

    cache_expr(expr, vc_readExpr(m_vc, array_expr, index_expr));
    return OK;
  }

  virtual Error __encode_array_store(
    const Expr* const expr,
    const SharedExpr& array,
    const SharedExpr& index,
    const SharedExpr& value) override
  {
    if (find_expr(expr))
      return OK;

    Error err;
    err = array.encode(*this);
    if (err)
      return err;

    const VCExpr array_expr = m_expr;

    err = index.encode(*this);
    if (err)
      return err;

    const VCExpr index_expr = m_expr;

    err = value.encode(*this);
    if (err)
      return err;

    const VCExpr value_expr = m_expr;

    cache_expr(expr, vc_writeExpr(m_vc, array_expr, index_expr, value_expr));
    return OK;
  }

  virtual Error __encode_unary_lnot(
    const Expr* const expr,
    const SharedExpr& arg) override
  {
    if (find_expr(expr))
      return OK;

    const Error err = arg.encode(*this);
    if (err)
      return err;

    cache_expr(expr, vc_notExpr(m_vc, m_expr));
    return OK;
  }

  virtual Error __encode_unary_not(
    const Expr* const expr,
    const SharedExpr& arg) override
  {
    if (find_expr(expr))
      return OK;

    const Error err = arg.encode(*this);
    if (err)
      return err;

    cache_expr(expr, vc_bvNotExpr(m_vc, m_expr));
    return OK;
  }

  virtual Error __encode_unary_sub(
    const Expr* const expr,
    const SharedExpr& arg) override
  {
    if (!expr->sort().is_bv())
      return UNSUPPORT_ERROR;

    if (find_expr(expr))
      return OK;

    const Error err = arg.encode(*this);
    if (err)
      return err;

    cache_expr(expr, vc_bvUMinusExpr(m_vc, m_expr));
    return OK;
  }

  virtual Error __encode_binary_sub(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg) override
  {
    const Sort& sort = expr->sort();
    if (!sort.is_bv())
      return UNSUPPORT_ERROR;

    if (find_expr(expr))
      return OK;

    Error err;
    err = larg.encode(*this);
    if (err)
      return err;

    const VCExpr lexpr = m_expr;

    err = rarg.encode(*this);
    if (err)
      return err;

    const VCExpr rexpr = m_expr;

    cache_expr(expr, vc_bvMinusExpr(m_vc, sort.bv_size(), lexpr, rexpr));
    return OK;
  }

  virtual Error __encode_binary_and(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg) override
  {
    if (!larg.sort().is_bv() || !rarg.sort().is_bv())
      return UNSUPPORT_ERROR;

    if (find_expr(expr))
      return OK;

    Error err;
    err = larg.encode(*this);
    if (err)
      return err;

    const VCExpr lexpr = m_expr;

    err = rarg.encode(*this);
    if (err)
      return err;

    const VCExpr rexpr = m_expr;

    cache_expr(expr, vc_bvAndExpr(m_vc, lexpr, rexpr));
    return OK;
  }

  virtual Error __encode_binary_or(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg) override
  {
    if (!larg.sort().is_bv() || !rarg.sort().is_bv())
      return UNSUPPORT_ERROR;

    if (find_expr(expr))
      return OK;

    Error err;
    err = larg.encode(*this);
    if (err)
      return err;

    const VCExpr lexpr = m_expr;

    err = rarg.encode(*this);
    if (err)
      return err;

    const VCExpr rexpr = m_expr;

    cache_expr(expr, vc_bvOrExpr(m_vc, lexpr, rexpr));
    return OK;
  }

  virtual Error __encode_binary_xor(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg) override
  {
    if (!larg.sort().is_bv() || !rarg.sort().is_bv())
      return UNSUPPORT_ERROR;

    if (find_expr(expr))
      return OK;

    Error err;
    err = larg.encode(*this);
    if (err)
      return err;

    const VCExpr lexpr = m_expr;

    err = rarg.encode(*this);
    if (err)
      return err;

    const VCExpr rexpr = m_expr;

    cache_expr(expr, vc_bvXorExpr(m_vc, lexpr, rexpr));
    return OK;
  }

  virtual Error __encode_binary_land(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg) override
  {
    if (!larg.sort().is_bool() || !rarg.sort().is_bool())
      return UNSUPPORT_ERROR;

    if (find_expr(expr))
      return OK;

    Error err;
    err = larg.encode(*this);
    if (err)
      return err;

    const VCExpr lexpr = m_expr;

    err = rarg.encode(*this);
    if (err)
      return err;

    const VCExpr rexpr = m_expr;

    cache_expr(expr, vc_andExpr(m_vc, lexpr, rexpr));
    return OK;
  }

  virtual Error __encode_binary_lor(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg) override
  {
    if (!larg.sort().is_bool() || !rarg.sort().is_bool())
      return UNSUPPORT_ERROR;

    if (find_expr(expr))
      return OK;

    Error err;
    err = larg.encode(*this);
    if (err)
      return err;

    const VCExpr lexpr = m_expr;

    err = rarg.encode(*this);
    if (err)
      return err;

    const VCExpr rexpr = m_expr;

    cache_expr(expr, vc_orExpr(m_vc, lexpr, rexpr));
    return OK;
  }

  virtual Error __encode_binary_imp(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg) override
  {
    if (!larg.sort().is_bool() || !rarg.sort().is_bool())
      return UNSUPPORT_ERROR;

    if (find_expr(expr))
      return OK;

    Error err;
    err = larg.encode(*this);
    if (err)
      return err;

    const VCExpr lexpr = m_expr;

    err = rarg.encode(*this);
    if (err)
      return err;

    const VCExpr rexpr = m_expr;

    cache_expr(expr, vc_impliesExpr(m_vc, lexpr, rexpr));
    return OK;
  }

  virtual Error __encode_binary_eql(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg) override
  {
    if (find_expr(expr))
      return OK;

    Error err;
    err = larg.encode(*this);
    if (err)
      return err;

    const VCExpr lexpr = m_expr;

    err = rarg.encode(*this);
    if (err)
      return err;

    const VCExpr rexpr = m_expr;

    if (larg.sort().is_bool())
      cache_expr(expr, vc_iffExpr(m_vc, lexpr, rexpr));
    else
      cache_expr(expr, vc_eqExpr(m_vc, lexpr, rexpr));

    return OK;
  }

  virtual Error __encode_binary_add(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg) override
  {
    const Sort& sort = expr->sort();

    if (!sort.is_bv())
      return UNSUPPORT_ERROR;

    if (find_expr(expr))
      return OK;

    Error err;
    err = larg.encode(*this);
    if (err)
      return err;

    const VCExpr lexpr = m_expr;

    err = rarg.encode(*this);
    if (err)
      return err;

    const VCExpr rexpr = m_expr;

    cache_expr(expr, vc_bvPlusExpr(m_vc, sort.bv_size(), lexpr, rexpr));
    return OK;
  }

  virtual Error __encode_binary_mul(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg) override
  {
    const Sort& sort = expr->sort();

    if (!sort.is_bv())
      return UNSUPPORT_ERROR;

    if (find_expr(expr))
      return OK;

    Error err;
    err = larg.encode(*this);
    if (err)
      return err;

    const VCExpr lexpr = m_expr;

    err = rarg.encode(*this);
    if (err)
      return err;

    const VCExpr rexpr = m_expr;

    cache_expr(expr, vc_bvMultExpr(m_vc, sort.bv_size(), lexpr, rexpr));
    return OK;
  }

  virtual Error __encode_binary_quo(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg) override
  {
    const Sort& sort = expr->sort();
    if (!sort.is_bv())
      return UNSUPPORT_ERROR;

    if (find_expr(expr))
      return OK;

    Error err;
    err = larg.encode(*this);
    if (err)
      return err;

    const VCExpr lexpr = m_expr;

    err = rarg.encode(*this);
    if (err)
      return err;

    const VCExpr rexpr = m_expr;

    if (sort.is_signed())
      cache_expr(expr, vc_sbvDivExpr(m_vc, sort.bv_size(), lexpr, rexpr));
    else
      cache_expr(expr, vc_bvDivExpr(m_vc, sort.bv_size(), lexpr, rexpr));

    return OK;
  }

  virtual Error __encode_binary_rem(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg) override
  {
    const Sort& sort = expr->sort();

    if (!sort.is_bv())
      return UNSUPPORT_ERROR;

    if (find_expr(expr))
      return OK;

    Error err;
    err = larg.encode(*this);
    if (err)
      return err;

    const VCExpr lexpr = m_expr;

    err = rarg.encode(*this);
    if (err)
      return err;

    const VCExpr rexpr = m_expr;

    if (sort.is_signed())
      cache_expr(expr, vc_sbvModExpr(m_vc, sort.bv_size(), lexpr, rexpr));
    else
      cache_expr(expr, vc_bvModExpr(m_vc, sort.bv_size(), lexpr, rexpr));

    return OK;
  }

  virtual Error __encode_binary_lss(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg) override
  {
    if (!larg.sort().is_bv() || !rarg.sort().is_bv())
      return UNSUPPORT_ERROR;

    if (find_expr(expr))
      return OK;

    Error err;
    err = larg.encode(*this);
    if (err)
      return err;

    const VCExpr lexpr = m_expr;

    err = rarg.encode(*this);
    if (err)
      return err;

    const VCExpr rexpr = m_expr;

    if (larg.sort().is_signed())
      cache_expr(expr, vc_sbvLtExpr(m_vc, lexpr, rexpr));
    else
      cache_expr(expr, vc_bvLtExpr(m_vc, lexpr, rexpr));

    return OK;
  }

  virtual Error __encode_binary_gtr(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg) override
  {
    if (!larg.sort().is_bv() || !rarg.sort().is_bv())
      return UNSUPPORT_ERROR;

    if (find_expr(expr))
      return OK;

    Error err;
    err = larg.encode(*this);
    if (err)
      return err;

    const VCExpr lexpr = m_expr;

    err = rarg.encode(*this);
    if (err)
      return err;

    const VCExpr rexpr = m_expr;

    if (larg.sort().is_signed())
      cache_expr(expr, vc_sbvGtExpr(m_vc, lexpr, rexpr));
    else
      cache_expr(expr, vc_bvGtExpr(m_vc, lexpr, rexpr));

    return OK;
  }

  virtual Error __encode_binary_neq(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg) override
  {
    if (find_expr(expr))
      return OK;

    Error err;
    err = larg.encode(*this);
    if (err)
      return err;

    const VCExpr lexpr = m_expr;

    err = rarg.encode(*this);
    if (err)
      return err;

    const VCExpr rexpr = m_expr;

    VCExpr eq_expr;
    if (larg.sort().is_bool())
      eq_expr = vc_iffExpr(m_vc, lexpr, rexpr);
    else
      eq_expr = vc_eqExpr(m_vc, lexpr, rexpr);

    cache_expr(expr, vc_notExpr(m_vc, eq_expr));
    return OK;
  }

  virtual Error __encode_binary_leq(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg) override
  {
    if (!larg.sort().is_bv() || !rarg.sort().is_bv())
      return UNSUPPORT_ERROR;

    if (find_expr(expr))
      return OK;

    Error err;
    err = larg.encode(*this);
    if (err)
      return err;

    const VCExpr lexpr = m_expr;

    err = rarg.encode(*this);
    if (err)
      return err;

    const VCExpr rexpr = m_expr;

    if (larg.sort().is_signed())
      cache_expr(expr, vc_sbvLeExpr(m_vc, lexpr, rexpr));
    else
      cache_expr(expr, vc_bvLeExpr(m_vc, lexpr, rexpr));

    return OK;
  }

  virtual Error __encode_binary_geq(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg) override
  {
    if (!larg.sort().is_bv() || !rarg.sort().is_bv())
      return UNSUPPORT_ERROR;

    if (find_expr(expr))
      return OK;

    Error err;
    err = larg.encode(*this);
    if (err)
      return err;

    const VCExpr lexpr = m_expr;

    err = rarg.encode(*this);
    if (err)
      return err;

    const VCExpr rexpr = m_expr;

    if (larg.sort().is_signed())
      cache_expr(expr, vc_sbvGeExpr(m_vc, lexpr, rexpr));
    else
      cache_expr(expr, vc_bvGeExpr(m_vc, lexpr, rexpr));

    return OK;
  }

  virtual Error __encode_nary(
    const Expr* const expr,
    Opcode opcode,
    const SharedExprs& args) override
  {
    if (find_expr(expr))
      return OK;

    Error err;

    if (opcode == NEQ)
    {
      // pair-wise disequality, formula size O(N^2)
      const Sort& bool_sort = internal::sort<Bool>();
      VCExpr pairwise_expr = vc_trueExpr(m_vc);
      for (SharedExprs::const_iterator outer = args.cbegin();
           outer != args.cend(); ++outer)
      {
        err = outer->encode(*this);
        if (err)
          return err;

        const VCExpr outer_expr = m_expr;

        for (SharedExprs::const_iterator inner = outer + 1;
             inner != args.cend(); ++inner)
        {
          assert(outer->sort() == inner->sort());

          err = inner->encode(*this);
          if (err)
            return err;

          const VCExpr inner_expr = m_expr;

          VCExpr eq_expr;
          if (outer->sort().is_bool())
            eq_expr = vc_iffExpr(m_vc, outer_expr, inner_expr);
          else
            eq_expr = vc_eqExpr(m_vc, outer_expr, inner_expr);

          pairwise_expr = vc_andExpr(m_vc, pairwise_expr,
            vc_notExpr(m_vc, eq_expr));
        }
      }

      cache_expr(expr, pairwise_expr);
      return OK;
    }

    if (opcode == LAND)
    {
      VCExpr and_expr = vc_trueExpr(m_vc);
      for (const SharedExpr& arg : args)
      {
        err = arg.encode(*this);
        if (err)
          return err;

        and_expr = vc_andExpr(m_vc, and_expr, m_expr);
      }

      cache_expr(expr, and_expr);
      return OK;
    }

    return UNSUPPORT_ERROR;
  }

  virtual Error __encode_bv_zero_extend(
    const Expr* const expr,
    const SharedExpr& bv,
    const unsigned ext) override
  {
    if (find_expr(expr))
      return OK;

    const Error err = bv.encode(*this);
    if (err)
      return err;

    const VCExpr zero_expr = vc_bvConstExprFromInt(m_vc, ext, 0);
    cache_expr(expr, vc_bvConcatExpr(m_vc, zero_expr, m_expr));
    return OK;
  }

  virtual Error __encode_bv_sign_extend(
    const Expr* const expr,
    const SharedExpr& bv,
    const unsigned ext) override
  {
    if (find_expr(expr))
      return OK;

    const Error err = bv.encode(*this);
    if (err)
      return err;

    const Sort& sort = expr->sort();
    assert(sort.bv_size() == ext + bv.sort().bv_size());
    cache_expr(expr, vc_bvSignExtend(m_vc, m_expr, sort.bv_size()));
    return OK;
  }

  virtual Error __encode_bv_extract(
    const Expr* const expr,
    const SharedExpr& bv,
    const unsigned high,
    const unsigned low) override
  {
    if (find_expr(expr))
      return OK;

    const Error err = bv.encode(*this);
    if (err)
      return err;

    cache_expr(expr, vc_bvExtract(m_vc, m_expr, high, low));
    return OK;
  }

  virtual void __notify_delete(const Expr* const expr) override
  {
    // Newer versions of STP delete expressions automatically.
    // If we want to free VCExpr pointers ourselves, we would
    // have to set EXPRDELETE to zero to avoid double-free errors.
    // But experiments indicate that this is significantly slower
    // (sometimes 30X) than letting STP manage its own memory.
    //
    // We still erase the entry from m_expr_map so a new
    // expression at the same address is cached correctly.
    m_expr_map.erase(reinterpret_cast<uintptr_t>(expr));
  }

  virtual void __reset() override
  {
    vc_Destroy(m_vc);
    m_vc = vc_createValidityChecker();
    m_expr_map.clear();
  }

  virtual void __push() override
  {
    vc_push(m_vc);
  }

  virtual void __pop() override
  {
    vc_pop(m_vc);
  }

  virtual Error __unsafe_add(const SharedExpr& condition) override
  {
    const Error err = condition.encode(*this);
    if (err)
      return err;

    vc_assertFormula(m_vc, m_expr);
    return OK;
  }

  virtual Error __add(const Bool& condition) override
  {
    return __unsafe_add(condition);
  }

  virtual CheckResult __check() override
  {
    // "\phi implies false" is equivalent to "not(\phi)"
    // where \phi is the conjunction of assertFormula()
    const int result = vc_query(m_vc, vc_falseExpr(m_vc));

    switch(result)
    {
    case 0:
      return sat;
    case 1:
      return unsat;

    default:
      return unknown;
    }
  }

public:
  /// Auto configure STP
  StpSolver()
  : Solver(),
    m_vc(vc_createValidityChecker()),
    m_expr(),
    m_expr_map()
  {
    assert(m_vc && "unable to create validity checker");
  }

  /// Only AF_ABV and QF_BV is supported
  StpSolver(Logic logic)
  : Solver(logic),
    m_vc(vc_createValidityChecker()),
    m_expr(),
    m_expr_map()
  {
    assert(logic == QF_ABV_LOGIC || logic == QF_BV_LOGIC);
    assert(m_vc && "unable to create validity checker");
  }

  ~StpSolver()
  {
    vc_Destroy(m_vc);
  }

  const VC vc() const
  {
    return m_vc;
  }

  const VCExpr expr() const
  {
    return m_expr;
  }

};

}

#endif
