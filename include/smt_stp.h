// Copyright 2014, Alex Horn. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

#ifndef _SMT_STP_H_
#define _SMT_STP_H_

#include <stp/c_interface.h>

// avoid name clash
typedef Expr VCExpr;

#include "smt.h"

namespace smt
{

/// Solver with bit vector support only!
class StpSolver : public Solver
{
private:
  VC m_vc;
  VCExpr m_expr;
  
  template<typename T>
  void encode_bv_literal(const unsigned bv_size, const T number)
  {
    m_expr = vc_bvConstExprFromInt(m_vc, bv_size, number);
  }

#define SMT_STP_ENCODE_BV_LITERAL(type)               \
  virtual Error __encode_literal(                     \
     const Sort& sort,                                \
     type literal) override                           \
  {                                                   \
    if (!sort.is_bv())                                \
      return UNSUPPORT_ERROR;                         \
                                                      \
    encode_bv_literal<type>(sort.bv_size(), literal); \
    return OK;                                        \
  }                                                   \

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

  virtual Error __encode_literal(const Sort& sort, bool literal) override
  {
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

    encode_bv_literal<unsigned>(sort.bv_size(), literal);
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
    const UnsafeDecl& decl) override
  {
    Type type;
    Error err = build_type(decl.sort(), type);
    if (err)
      return err;

    m_expr = vc_varExpr(m_vc, decl.symbol().c_str(), type);
    return OK;
  }

  virtual Error __encode_func_app(
    const UnsafeDecl& decl,
    const size_t arity,
    const UnsafeTerm* const args) override
  {
    return UNSUPPORT_ERROR;
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
    if (err)
      return err;

    const VCExpr array_expr = m_expr;

    err = index.encode(*this);
    if (err)
      return err;

    const VCExpr index_expr = m_expr;

    m_expr = vc_readExpr(m_vc, array_expr, index_expr);
    return OK;
  }

  virtual Error __encode_array_store(
    const UnsafeTerm& array,
    const UnsafeTerm& index,
    const UnsafeTerm& value) override
  {
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

    m_expr = vc_writeExpr(m_vc, array_expr, index_expr, value_expr);
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
      m_expr = vc_notExpr(m_vc, m_expr);
      break;
    case NOT:
      m_expr = vc_bvNotExpr(m_vc, m_expr);
      break;
    case SUB:
      if (!sort.is_bv())
        return UNSUPPORT_ERROR;

      m_expr = vc_bvUMinusExpr(m_vc, m_expr);
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
    if (err)
      return err;

    const VCExpr lexpr = m_expr;

    err = rarg.encode(*this);
    if (err)
      return err;

    const VCExpr rexpr = m_expr;

    switch (opcode) {
    case SUB:
      if (!sort.is_bv())
        return UNSUPPORT_ERROR;

      m_expr = vc_bvMinusExpr(m_vc, sort.bv_size(), lexpr, rexpr);
      break;
    case AND:
      if (!larg.sort().is_bv() || !rarg.sort().is_bv())
        return OPCODE_ERROR;

      m_expr = vc_bvAndExpr(m_vc, lexpr, rexpr);
      break;
    case OR:
      if (!larg.sort().is_bv() || !rarg.sort().is_bv())
        return OPCODE_ERROR;

      m_expr = vc_bvOrExpr(m_vc, lexpr, rexpr);
      break;
    case XOR:
      if (!larg.sort().is_bv() || !rarg.sort().is_bv())
        return OPCODE_ERROR;

      m_expr = vc_bvXorExpr(m_vc, lexpr, rexpr);
      break;
    case LAND:
      if (!larg.sort().is_bool() || !rarg.sort().is_bool())
        return OPCODE_ERROR;

      m_expr = vc_andExpr(m_vc, lexpr, rexpr);
      break;
    case LOR:
      if (!larg.sort().is_bool() || !rarg.sort().is_bool())
        return OPCODE_ERROR;

      m_expr = vc_orExpr(m_vc, lexpr, rexpr);
      break;
    case IMP:
      if (!larg.sort().is_bool() || !rarg.sort().is_bool())
        return OPCODE_ERROR;

      m_expr = vc_impliesExpr(m_vc, lexpr, rexpr);
      break;
    case EQL:
      if (larg.sort().is_bool())
        m_expr = vc_iffExpr(m_vc, lexpr, rexpr);
      else
        m_expr = vc_eqExpr(m_vc, lexpr, rexpr);

      break;
    case ADD:
      if (!sort.is_bv())
        return UNSUPPORT_ERROR;

      m_expr = vc_bvPlusExpr(m_vc, sort.bv_size(), lexpr, rexpr);
      break;
    case MUL:
      if (!sort.is_bv())
        return UNSUPPORT_ERROR;

      m_expr = vc_bvMultExpr(m_vc, sort.bv_size(), lexpr, rexpr);
      break;
    case QUO:
      if (!sort.is_bv())
        return UNSUPPORT_ERROR;

      if (sort.is_signed())
        m_expr = vc_sbvDivExpr(m_vc, sort.bv_size(), lexpr, rexpr);
      else
        m_expr = vc_bvDivExpr(m_vc, sort.bv_size(), lexpr, rexpr);

      break;
    case REM:
      if (!sort.is_bv())
        return UNSUPPORT_ERROR;

      if (sort.is_signed())
        m_expr = vc_sbvModExpr(m_vc, sort.bv_size(), lexpr, rexpr);
      else
        m_expr = vc_bvModExpr(m_vc, sort.bv_size(), lexpr, rexpr);

      break;
    case LSS:
      if (!larg.sort().is_bv() || !rarg.sort().is_bv())
        return UNSUPPORT_ERROR;

      if (larg.sort().is_signed())
        m_expr = vc_sbvLtExpr(m_vc, lexpr, rexpr);
      else
        m_expr = vc_bvLtExpr(m_vc, lexpr, rexpr);
      
      break;
    case GTR:
      if (!larg.sort().is_bv() || !rarg.sort().is_bv())
        return UNSUPPORT_ERROR;

      if (larg.sort().is_signed())
        m_expr = vc_sbvGtExpr(m_vc, lexpr, rexpr);
      else
        m_expr = vc_bvGtExpr(m_vc, lexpr, rexpr);
      
      break;
    case NEQ:
      VCExpr eq_expr;
      if (larg.sort().is_bool())
        eq_expr = vc_iffExpr(m_vc, lexpr, rexpr);
      else
        eq_expr = vc_eqExpr(m_vc, lexpr, rexpr);

      m_expr = vc_notExpr(m_vc, eq_expr);

      break;
    case LEQ:
      if (!larg.sort().is_bv() || !rarg.sort().is_bv())
        return UNSUPPORT_ERROR;

      if (larg.sort().is_signed())
        m_expr = vc_sbvLeExpr(m_vc, lexpr, rexpr);
      else
        m_expr = vc_bvLeExpr(m_vc, lexpr, rexpr);
      
      break;
    case GEQ:
      if (!larg.sort().is_bv() || !rarg.sort().is_bv())
        return UNSUPPORT_ERROR;

      if (larg.sort().is_signed())
        m_expr = vc_sbvGeExpr(m_vc, lexpr, rexpr);
      else
        m_expr = vc_bvGeExpr(m_vc, lexpr, rexpr);
      
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
    return UNSUPPORT_ERROR;
  }

  virtual Error __encode_bv_zero_extend(
    const Sort& sort,
    const UnsafeTerm& bv,
    const unsigned ext) override
  {
    const Error err = bv.encode(*this);
    if (err)
      return err;

    const VCExpr zero_expr = vc_bvConstExprFromInt(m_vc, ext, 0);
    m_expr = vc_bvConcatExpr(m_vc, zero_expr, m_expr);
    return OK;
  }

  virtual Error __encode_bv_sign_extend(
    const Sort& sort,
    const UnsafeTerm& bv,
    const unsigned ext) override
  {
    const Error err = bv.encode(*this);
    if (err)
      return err;

    assert(sort.bv_size() == ext + bv.sort().bv_size());
    m_expr = vc_bvSignExtend(m_vc, m_expr, sort.bv_size());
    return OK;
  }

  virtual Error __encode_bv_extract(
    const Sort& sort,
    const UnsafeTerm& bv,
    const unsigned high,
    const unsigned low) override
  {
    const Error err = bv.encode(*this);
    if (err)
      return err;

    m_expr = vc_bvExtract(m_vc, m_expr, high, low);
    return OK;
  }

  virtual void __reset() override
  {
    vc_Destroy(m_vc);
    m_vc = vc_createValidityChecker();
  }

  virtual void __push() override
  {
    vc_push(m_vc);
  }

  virtual void __pop() override
  {
    vc_pop(m_vc);
  }

  virtual Error __unsafe_add(const UnsafeTerm& condition) override
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
  : m_vc(vc_createValidityChecker()),
    m_expr() {}

  /// Only AF_ABV and QF_BV is supported
  StpSolver(Logic logic)
  : m_vc(vc_createValidityChecker()),
    m_expr()
  {
    assert(logic == QF_ABV_LOGIC || logic == QF_BV_LOGIC);
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
