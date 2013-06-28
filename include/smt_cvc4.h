// Copyright 2013, Alex Horn. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

#ifndef __SMT_CVC4_H_
#define __SMT_CVC4_H_

#include <cvc4/expr/expr.h>
#include <cvc4/expr/expr_manager.h>
#include <cvc4/smt/smt_engine.h>

// Conflicts with gtest headers, include gtest/gtest.h _after_ smt_cvc4.h!
#undef EXPECT_TRUE
#undef EXPECT_FALSE
#undef Message

#include "smt.h"

#include <unordered_map>

namespace smt
{

class CVC4Solver : public Solver
{
private:
  CVC4::ExprManager m_expr_manager;
  CVC4::SmtEngine m_smt_engine;
  CVC4::Expr m_expr;

  // Cache CVC4 expressions

  // We should not use symbol names as key because these need not be unique
  // across different SMT-LIB 2.0 namespaces such as sorts, bindings etc.
  typedef std::unordered_map<std::string, const CVC4::Expr> ExprMap;
  ExprMap m_expr_map;

  void set_expr(const CVC4::Expr& expr)
  {
    m_expr = expr;
  }

  template<typename T>
  Error nostring_encode_number(const Sort& sort, T literal)
  {
    assert(!sort.is_bool());

    if (sort.is_bv()) {
      set_expr(m_expr_manager.mkConst(CVC4::BitVector(sort.bv_size(),
        CVC4::Integer(literal))));
    } else if (sort.is_int() || sort.is_real()) {
      set_expr(m_expr_manager.mkConst(CVC4::Rational(literal)));
    } else {
      return UNSUPPORT_ERROR;
    }

    return OK;
  }

  Error string_encode_number(const Sort& sort, std::string&& literal)
  {
    assert(!sort.is_bool());

    // Should use move semantics on the integer once CVC4 supports it
    const CVC4::Integer integer(std::move(literal));
    if (sort.is_bv()) {
      set_expr(m_expr_manager.mkConst(CVC4::BitVector(sort.bv_size(), integer)));
    } else if (sort.is_int() || sort.is_real()) {
      set_expr(m_expr_manager.mkConst(CVC4::Rational(integer)));
    } else {
      return UNSUPPORT_ERROR;
    }

    return OK;
  }

  virtual Error __encode_literal(const Sort& sort, bool literal) override
  {
    assert(sort.is_bool());

    set_expr(m_expr_manager.mkConst(literal));
    return OK;
  }

#define SMT_CVC4_NOSTRING_ENCODE_LITERAL(type)                            \
  virtual Error __encode_literal(const Sort& sort, type literal) override \
  {                                                                       \
    return nostring_encode_number<type>(sort, literal);                   \
  }                                                                       \

#define SMT_CVC4_STRING_ENCODE_LITERAL(type)                              \
  virtual Error __encode_literal(const Sort& sort, type literal) override \
  {                                                                       \
    return string_encode_number(sort, std::to_string(literal));           \
  }                                                                       \

SMT_CVC4_NOSTRING_ENCODE_LITERAL(char)
SMT_CVC4_NOSTRING_ENCODE_LITERAL(signed char)
SMT_CVC4_NOSTRING_ENCODE_LITERAL(unsigned char)

SMT_CVC4_STRING_ENCODE_LITERAL(wchar_t)
SMT_CVC4_STRING_ENCODE_LITERAL(char16_t)
SMT_CVC4_STRING_ENCODE_LITERAL(char32_t)

SMT_CVC4_NOSTRING_ENCODE_LITERAL(short)
SMT_CVC4_NOSTRING_ENCODE_LITERAL(unsigned short)
SMT_CVC4_NOSTRING_ENCODE_LITERAL(int)
SMT_CVC4_NOSTRING_ENCODE_LITERAL(unsigned int)
SMT_CVC4_NOSTRING_ENCODE_LITERAL(long)
SMT_CVC4_NOSTRING_ENCODE_LITERAL(unsigned long)

SMT_CVC4_STRING_ENCODE_LITERAL(long long)
SMT_CVC4_STRING_ENCODE_LITERAL(unsigned long long)

  Error build_type(const Sort& sort, CVC4::Type& type)
  {
    if (sort.is_bool()) {
      type = m_expr_manager.booleanType();
    } else if (sort.is_int()) {
      type = m_expr_manager.integerType();
    } else if (sort.is_bv()) {
      type = m_expr_manager.mkBitVectorType(sort.bv_size());
    } else if (sort.is_func()) {
      Error err;
      const size_t sorts_size = sort.sorts_size();
      std::vector<CVC4::Type> types;
      types.reserve(sorts_size);
      for (int i = 0; i < sorts_size; i++) {
        CVC4::Type type;
        err = build_type(sort.sorts(i), type);
        if (err) {
          return err;
        }
        types.push_back(type);
      }

      type = m_expr_manager.mkFunctionType(types);
    } else if (sort.is_array()) {
      CVC4::Type domain_type;
      CVC4::Type range_type;

      Error err;
      err = build_type(sort.sorts(0), domain_type);
      if (err) {
        return err;
      }
      err = build_type(sort.sorts(1), range_type);
      if (err) {
        return err;
      }

      type = m_expr_manager.mkArrayType(domain_type, range_type);
    } else {
      return UNSUPPORT_ERROR;
    }

    return OK;
  }

  virtual Error __encode_constant(
    const UnsafeDecl& decl) override
  {
    Error err;

    const std::string& const_symbol = decl.symbol();
    ExprMap::const_iterator it = m_expr_map.find(const_symbol);
    if (it == m_expr_map.cend()) {
      CVC4::Type type;
      err = build_type(decl.sort(), type);
      if (err) {
        return err;
      }

      set_expr(m_expr_manager.mkVar(const_symbol, type));
      m_expr_map.insert(ExprMap::value_type(const_symbol, m_expr));
    } else {
      set_expr(it->second);
    }

    return OK;
  }

  virtual Error __encode_func_app(
    const UnsafeDecl& decl,
    const size_t arity,
    const UnsafeTerm* const args) override
  {
    Error err;
    CVC4::Expr func_expr;
    const std::string& func_symbol = decl.symbol();
    ExprMap::const_iterator it = m_expr_map.find(func_symbol);
    if (it == m_expr_map.cend()) {
      CVC4::Type func_type;
      err = build_type(decl.sort(), func_type);
      if (err) {
        return err;
      }
      func_expr = m_expr_manager.mkVar(func_symbol, func_type);
      m_expr_map.insert(ExprMap::value_type(func_symbol, func_expr));
    } else {
      func_expr = it->second;
    }

    std::vector<CVC4::Expr> exprs;
    exprs.reserve(arity);
    for (int i = 0; i < arity; i++) {
      err = args[i].encode(*this);
      if (err) {
        return err;
      }
      exprs.push_back(m_expr);
    }

    set_expr(m_expr_manager.mkExpr(CVC4::kind::APPLY_UF, func_expr, exprs));
    return OK;
  }

  virtual Error __encode_const_array(
    const Sort& sort,
    const UnsafeTerm& init) override
  {
    Error err;

    CVC4::Type type;
    err = build_type(sort, type);
    if (err) {
      return err;
    }

    err = init.encode(*this);
    if (err) {
      return err;
    }

    const CVC4::ArrayType array_type(type);
    set_expr(m_expr_manager.mkConst(CVC4::ArrayStoreAll(array_type, m_expr)));
    return OK;
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
    const CVC4::Expr array_expr = m_expr;

    err = index.encode(*this);
    if (err) {
      return err;
    }
    const CVC4::Expr index_expr = m_expr;

    set_expr(m_expr_manager.mkExpr(CVC4::kind::SELECT,
      array_expr, index_expr));
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
    const CVC4::Expr array_expr = m_expr;

    err = index.encode(*this);
    if (err) {
      return err;
    }
    const CVC4::Expr index_expr = m_expr;

    err = value.encode(*this);
    if (err) {
      return err;
    }
    const CVC4::Expr value_expr = m_expr;

    set_expr(m_expr_manager.mkExpr(CVC4::kind::STORE,
      array_expr, index_expr, value_expr));
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

    CVC4::kind::Kind_t kind;
    switch (opcode) {
    case LNOT:
      kind = CVC4::kind::NOT;
      break;
    case NOT:
      kind = CVC4::kind::BITVECTOR_NOT;
      break;
    case SUB:
      if (sort.is_bv()) {
        kind = CVC4::kind::BITVECTOR_NEG;
      } else {
        kind = CVC4::kind::UMINUS;
      }
      break;
    default:
      return OPCODE_ERROR;
    }

    set_expr(m_expr_manager.mkExpr(kind, m_expr));
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
    const CVC4::Expr lexpr(m_expr);

    err = rarg.encode(*this);
    if (err) {
      return err;
    }
    const CVC4::Expr rexpr(m_expr);

    CVC4::kind::Kind_t kind;
    switch (opcode) {
    case SUB:
      if (sort.is_bv()) {
        kind = CVC4::kind::BITVECTOR_SUB;
      } else {
        kind = CVC4::kind::MINUS;
      }
      break;
    case AND:
      kind = CVC4::kind::BITVECTOR_AND;
      break;
    case OR:
      kind = CVC4::kind::BITVECTOR_OR;
      break;
    case XOR:
      kind = CVC4::kind::BITVECTOR_XOR;
      break;
    case LAND:
      kind = CVC4::kind::AND;
      break;
    case LOR:
      kind = CVC4::kind::OR;
      break;
    case IMP:
      kind = CVC4::kind::IMPLIES;
      break;
    case EQL:
      if (larg.sort().is_bool()) {
        kind = CVC4::kind::IFF;
      } else {
        kind = CVC4::kind::EQUAL;
      }
      break;
    case ADD:
      if (sort.is_bv()) {
        kind = CVC4::kind::BITVECTOR_PLUS;
      } else {
        kind = CVC4::kind::PLUS;
      }
      break;
    case MUL:
      if (sort.is_bv()) {
        kind = CVC4::kind::BITVECTOR_MULT;
      } else {
        kind = CVC4::kind::MULT;
      }
      break;
    case QUO:
      if (sort.is_bv()) {
        if (sort.is_signed()) {
          kind = CVC4::kind::BITVECTOR_SDIV;
        } else {
          kind = CVC4::kind::BITVECTOR_UDIV;
        }
      } else if (sort.is_int()) {
        kind = CVC4::kind::INTS_DIVISION;
      } else if (sort.is_real()) {
        kind = CVC4::kind::DIVISION;
      } else {
        return UNSUPPORT_ERROR;
      }
      break;
    case REM:
      if (sort.is_bv()) {
        if (sort.is_signed()) {
          kind = CVC4::kind::BITVECTOR_SREM;
        } else {
          kind = CVC4::kind::BITVECTOR_UREM;
        }
      } else if (sort.is_int()) {
        kind = CVC4::kind::INTS_MODULUS;
      } else {
        return UNSUPPORT_ERROR;
      }
      break;
    case LSS:
      if (larg.sort().is_bv()) {
        if (larg.sort().is_signed()) {
          kind = CVC4::kind::BITVECTOR_SLT;
        } else {
          kind = CVC4::kind::BITVECTOR_ULT;
        }
      } else {
        kind = CVC4::kind::LT;
      }
      break;
    case GTR:
      if (larg.sort().is_bv()) {
        if (larg.sort().is_signed()) {
          kind = CVC4::kind::BITVECTOR_SGT;
        } else {
          kind = CVC4::kind::BITVECTOR_UGT;
        }
      } else {
        kind = CVC4::kind::GT;
      }
      break;
    case NEQ:
      kind = CVC4::kind::DISTINCT;

      break;
    case LEQ:
      if (larg.sort().is_bv()) {
        if (larg.sort().is_signed()) {
          kind = CVC4::kind::BITVECTOR_SLE;
        } else {
          kind = CVC4::kind::BITVECTOR_ULE;
        }
      } else {
        kind = CVC4::kind::LEQ;
      }
      break;
    case GEQ:
      if (larg.sort().is_bv()) {
        if (larg.sort().is_signed()) {
          kind = CVC4::kind::BITVECTOR_SGE;
        } else {
          kind = CVC4::kind::BITVECTOR_UGE;
        }
      } else {
        kind = CVC4::kind::GEQ;
      }
      break;
    default:
      return OPCODE_ERROR;
    }

    set_expr(m_expr_manager.mkExpr(kind, lexpr, rexpr));
    return OK;
  }

  virtual Error __encode_nary(
    Opcode opcode,
    const Sort& sort,
    const UnsafeTerms& args) override
  {
    Error err;

    if (opcode == NEQ) {
      std::vector<CVC4::Expr> exprs;
      exprs.reserve(args.size());
      for (UnsafeTerms::const_reference arg : args) {
        err = arg.encode(*this);
        if (err) {
          return err;
        }
        exprs.push_back(m_expr);
      }

      set_expr(m_expr_manager.mkExpr(CVC4::kind::DISTINCT, exprs));
      return OK;
    } else {
      return UNSUPPORT_ERROR;
    }
  }

  virtual void __reset() override
  {
    // currently unsupported
    assert(false);
  }

  virtual void __push() override
  {
    m_smt_engine.push();
  }

  virtual void __pop() override
  {
    m_smt_engine.pop();
  }

  virtual Error __unsafe_add(const UnsafeTerm& condition) override
  {
    const Error err = condition.encode(*this);
    if (err) {
      return err;
    }
    // unclear how to use assertFormula()'s return value
    m_smt_engine.assertFormula(m_expr);
    return OK;
  }

  virtual Error __add(const Bool& condition) override
  {
    return __unsafe_add(condition);
  }

  virtual CheckResult __check() override
  {
    switch (m_smt_engine.checkSat().isSat()) {
    case CVC4::Result::Sat::UNSAT:
      return unsat;
    case CVC4::Result::Sat::SAT:
      return sat;
    case CVC4::Result::Sat::SAT_UNKNOWN:
      return unknown;
    }
  }

public:
  /// Auto configure CVC4
  CVC4Solver()
  : m_expr_manager(),
    m_smt_engine(&m_expr_manager),
    m_expr(),
    m_expr_map()
  {
    m_smt_engine.setOption("incremental", true);
    m_smt_engine.setOption("output-language", "smt2");
  }

  CVC4Solver(const CVC4::Options& options)
  : m_expr_manager(options),
    m_smt_engine(&m_expr_manager),
    m_expr(),
    m_expr_map()
  {
    m_smt_engine.setOption("incremental", true);
  }

  CVC4Solver(Logic logic)
  : m_expr_manager(),
    m_smt_engine(&m_expr_manager),
    m_expr(),
    m_expr_map()
  {
    m_smt_engine.setOption("incremental", true);
    m_smt_engine.setOption("output-language", "smt2");
    m_smt_engine.setLogic(Logics::acronyms[logic]);
  }

  CVC4::ExprManager& expr_manager()
  {
    return m_expr_manager;
  }

  CVC4::SmtEngine& smt_engine()
  {
    return m_smt_engine;
  }

  CVC4::Expr expr() const
  {
    // copy
    return m_expr;
  }
};

}

#endif
