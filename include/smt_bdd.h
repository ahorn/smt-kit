// Copyright 2014, Alex Horn. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

#ifndef _SMT_BDD_H_
#define _SMT_BDD_H_

#include <unordered_map>
#include <string>
#include <vector>
#include <stack>

#include "bdd.h"
#include "smt.h"

namespace smt
{

using namespace bdd;

/// Use binary decision diagrams (BDDs) to solve the Boolean skeleton of formulas

/// This solver merely aims to illustrate how symbolic execution can
/// use Boolean abstraction techniques for path condition checks.
class BDDSolver : public Solver
{
private:
  BDDManager m_bdd_manager;

  // always call set_bdd() instead of directly assigning field
  BDD m_bdd;

  typedef std::unordered_map<uintptr_t, const BDD> BDDMap;
  BDDMap m_bdd_map;

  typedef std::vector<const BDD> BDDs;
  BDDs m_assertions;

  typedef std::stack<unsigned> AssertionStack;
  AssertionStack m_assertion_stack;

  unsigned m_binary_relation_counter;

  /// \pre: expr->sort().is_bool()
  Error abstract_binary_relation(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg)
  {
    static constexpr char s_prefix[] = "binary_relation_bdd!";

    assert(expr->sort().is_bool());
    if (find_bdd(expr))
      return OK;

    BDD binary_relation_bdd = m_bdd_manager.make_var(
      s_prefix + std::to_string(m_binary_relation_counter++));

    assert(m_binary_relation_counter != 0);
    set_bdd(expr, binary_relation_bdd);
    return OK;
  }

  bool is_abstract() const
  {
    return m_binary_relation_counter != 0;
  }

  bool find_bdd(const Expr* const expr)
  {
    const BDDMap::const_iterator citer = m_bdd_map.find(
      reinterpret_cast<uintptr_t>(expr));

    if (citer == m_bdd_map.cend())
      return false;

    m_bdd = citer->second;
    return true;
  }

  // \pre: not find_bdd(expr)
  void set_bdd(const Expr* const expr, const BDD& bdd)
  {
    m_bdd = bdd;

    bool ok = std::get<1>(m_bdd_map.emplace(
      reinterpret_cast<uintptr_t>(expr), bdd));
    assert(ok);
  }

  virtual Error __encode_literal(
    const Expr* const expr,
    const Sort& sort,
    bool literal)
  {
    if (find_bdd(expr))
      return OK;

    if (!expr->sort().is_bool())
      return UNSUPPORT_ERROR;

    if (literal)
      set_bdd(expr, m_bdd_manager.True());
    else
      set_bdd(expr, m_bdd_manager.False());

    return OK;
  }

#define SMT_BDD_CAST_ENCODE_BUILTIN_LITERAL(type)     \
  virtual Error __encode_literal(                     \
     const Expr* const expr,                          \
     const Sort& sort,                                \
     type literal) override                           \
  {                                                   \
    return UNSUPPORT_ERROR;                           \
  }                                                   \

SMT_BDD_CAST_ENCODE_BUILTIN_LITERAL(char)
SMT_BDD_CAST_ENCODE_BUILTIN_LITERAL(signed char)
SMT_BDD_CAST_ENCODE_BUILTIN_LITERAL(unsigned char)
SMT_BDD_CAST_ENCODE_BUILTIN_LITERAL(wchar_t)
SMT_BDD_CAST_ENCODE_BUILTIN_LITERAL(char16_t)
SMT_BDD_CAST_ENCODE_BUILTIN_LITERAL(char32_t)
SMT_BDD_CAST_ENCODE_BUILTIN_LITERAL(short)
SMT_BDD_CAST_ENCODE_BUILTIN_LITERAL(unsigned short)
SMT_BDD_CAST_ENCODE_BUILTIN_LITERAL(int)
SMT_BDD_CAST_ENCODE_BUILTIN_LITERAL(unsigned int)
SMT_BDD_CAST_ENCODE_BUILTIN_LITERAL(long)
SMT_BDD_CAST_ENCODE_BUILTIN_LITERAL(unsigned long)
SMT_BDD_CAST_ENCODE_BUILTIN_LITERAL(long long)
SMT_BDD_CAST_ENCODE_BUILTIN_LITERAL(unsigned long long)

  virtual Error __encode_constant(
    const Expr* const expr,
    const UnsafeDecl& decl) override
  {
    if (find_bdd(expr))
      return OK;

    if (decl.sort().is_bool())
      set_bdd(expr, m_bdd_manager.make_var(decl.symbol()));

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
    const Sort& sort,
    const SharedExpr& init) override
  {
    return UNSUPPORT_ERROR;
  }

  virtual Error __encode_array_select(
    const Expr* const expr,
    const SharedExpr& array,
    const SharedExpr& index) override
  {
    return UNSUPPORT_ERROR;
  }

  virtual Error __encode_array_store(
    const Expr* const expr,
    const SharedExpr& array,
    const SharedExpr& index,
    const SharedExpr& value) override
  {
    return UNSUPPORT_ERROR;
  }

  virtual Error __encode_unary_lnot(
    const Expr* const expr,
    const Sort& sort,
    const SharedExpr& arg) override
  {
    if (find_bdd(expr))
      return OK;

    const Error err = arg.encode(*this);
    if (err)
      return err;

    set_bdd(expr, !m_bdd);
    return OK;
  }

  virtual Error __encode_unary_not(
    const Expr* const expr,
    const Sort& sort,
    const SharedExpr& arg) override
  {
    return UNSUPPORT_ERROR;
  }

  virtual Error __encode_unary_sub(
    const Expr* const expr,
    const Sort& sort,
    const SharedExpr& arg) override
  {
    return UNSUPPORT_ERROR;
  }

  virtual Error __encode_binary_sub(
    const Expr* const expr,
    const Sort& sort,
    const SharedExpr& larg,
    const SharedExpr& rarg) override
  {
    return UNSUPPORT_ERROR;
  }

  virtual Error __encode_binary_and(
    const Expr* const expr,
    const Sort& sort,
    const SharedExpr& larg,
    const SharedExpr& rarg) override
  {
    return UNSUPPORT_ERROR;
  }

  virtual Error __encode_binary_or(
    const Expr* const expr,
    const Sort& sort,
    const SharedExpr& larg,
    const SharedExpr& rarg) override
  {
    return UNSUPPORT_ERROR;
  }

  virtual Error __encode_binary_xor(
    const Expr* const expr,
    const Sort& sort,
    const SharedExpr& larg,
    const SharedExpr& rarg) override
  {
    return UNSUPPORT_ERROR;
  }

  virtual Error __encode_binary_land(
    const Expr* const expr,
    const Sort& sort,
    const SharedExpr& larg,
    const SharedExpr& rarg) override
  {
    if (find_bdd(expr))
      return OK;

    Error err;
    err = larg.encode(*this);
    if (err)
      return err;

    const BDD lbdd = m_bdd;

    err = rarg.encode(*this);
    if (err)
      return err;

    const BDD rbdd = m_bdd;

    set_bdd(expr, lbdd & rbdd);
    return OK;
  }

  virtual Error __encode_binary_lor(
    const Expr* const expr,
    const Sort& sort,
    const SharedExpr& larg,
    const SharedExpr& rarg) override
  {
    if (find_bdd(expr))
      return OK;

    Error err;
    err = larg.encode(*this);
    if (err)
      return err;

    const BDD lbdd = m_bdd;

    err = rarg.encode(*this);
    if (err)
      return err;

    const BDD rbdd = m_bdd;

    set_bdd(expr, lbdd | rbdd);
    return OK;
  }

  virtual Error __encode_binary_imp(
    const Expr* const expr,
    const Sort& sort,
    const SharedExpr& larg,
    const SharedExpr& rarg) override
  {
    if (find_bdd(expr))
      return OK;

    Error err;
    err = larg.encode(*this);
    if (err)
      return err;

    const BDD lbdd = m_bdd;

    err = rarg.encode(*this);
    if (err)
      return err;

    const BDD rbdd = m_bdd;

    set_bdd(expr, !lbdd | rbdd);
    return OK;
  }

  virtual Error __encode_binary_eql(
    const Expr* const expr,
    const Sort& sort,
    const SharedExpr& larg,
    const SharedExpr& rarg) override
  {
    return abstract_binary_relation(expr, larg, rarg);
  }

  virtual Error __encode_binary_add(
    const Expr* const expr,
    const Sort& sort,
    const SharedExpr& larg,
    const SharedExpr& rarg) override
  {
    return UNSUPPORT_ERROR;
  }

  virtual Error __encode_binary_mul(
    const Expr* const expr,
    const Sort& sort,
    const SharedExpr& larg,
    const SharedExpr& rarg) override
  {
    return UNSUPPORT_ERROR;
  }

  virtual Error __encode_binary_quo(
    const Expr* const expr,
    const Sort& sort,
    const SharedExpr& larg,
    const SharedExpr& rarg) override
  {
    return UNSUPPORT_ERROR;
  }

  virtual Error __encode_binary_rem(
    const Expr* const expr,
    const Sort& sort,
    const SharedExpr& larg,
    const SharedExpr& rarg) override
  {
    return UNSUPPORT_ERROR;
  }

  virtual Error __encode_binary_lss(
    const Expr* const expr,
    const Sort& sort,
    const SharedExpr& larg,
    const SharedExpr& rarg) override
  {
    return abstract_binary_relation(expr, larg, rarg);
  }

  virtual Error __encode_binary_gtr(
    const Expr* const expr,
    const Sort& sort,
    const SharedExpr& larg,
    const SharedExpr& rarg) override
  {
    return abstract_binary_relation(expr, larg, rarg);
  }

  virtual Error __encode_binary_neq(
    const Expr* const expr,
    const Sort& sort,
    const SharedExpr& larg,
    const SharedExpr& rarg) override
  {
    return abstract_binary_relation(expr, larg, rarg);
  }

  virtual Error __encode_binary_leq(
    const Expr* const expr,
    const Sort& sort,
    const SharedExpr& larg,
    const SharedExpr& rarg) override
  {
    return abstract_binary_relation(expr, larg, rarg);
  }

  virtual Error __encode_binary_geq(
    const Expr* const expr,
    const Sort& sort,
    const SharedExpr& larg,
    const SharedExpr& rarg) override
  {
    return abstract_binary_relation(expr, larg, rarg);
  }

  virtual Error __encode_nary(
    const Expr* const expr,
    Opcode opcode,
    const Sort& sort,
    const SharedExprs& args) override
  {
    return UNSUPPORT_ERROR;
  }

  virtual Error __encode_bv_zero_extend(
    const Expr* const expr,
    const Sort& sort,
    const SharedExpr& bv,
    const unsigned ext) override
  {
    return UNSUPPORT_ERROR;
  }

  virtual Error __encode_bv_sign_extend(
    const Expr* const expr,
    const Sort& sort,
    const SharedExpr& bv,
    const unsigned ext) override
  {
    return UNSUPPORT_ERROR;
  }

  virtual Error __encode_bv_extract(
    const Expr* const expr,
    const Sort& sort,
    const SharedExpr& bv,
    const unsigned high,
    const unsigned low) override
  {
    return UNSUPPORT_ERROR;
  }

  virtual void __notify_delete(const Expr* const expr) override
  {
    m_bdd_map.erase(reinterpret_cast<uintptr_t>(expr));
  }

  virtual void __reset() override
  {
    m_bdd_map.clear();
    m_assertions.clear();
    m_bdd = m_bdd_manager.True();

    while (!m_assertion_stack.empty())
      m_assertion_stack.pop();

    m_binary_relation_counter = 0;
  }

  virtual void __push() override
  {
    m_assertion_stack.push(0);
  }

  virtual void __pop() override
  {
    assert(!m_assertion_stack.empty());

    unsigned n = m_assertion_stack.top();
    assert(n <= m_assertions.size());

    for (; 0 != n; --n)
      m_assertions.pop_back();

    m_assertion_stack.pop();
  }

  virtual Error __unsafe_add(const SharedExpr& condition) override
  {
    const Error err = condition.encode(*this);
    if (err)
      return err;

    m_assertions.push_back(m_bdd);

    if (!m_assertion_stack.empty())
      ++m_assertion_stack.top();

    return OK;
  }

  virtual Error __add(const Bool& condition) override
  {
    return __unsafe_add(condition);
  }

  virtual CheckResult __check() override
  {
    BDD formula = m_bdd_manager.True();
    for (const BDD& bdd : m_assertions)
      formula = formula & bdd;

    if (formula.is_false())
      return unsat;

    if (is_abstract())
      return unknown;

    return sat;
  }

public:
  BDDSolver()
  : Solver(),
    m_bdd_manager(),
    m_bdd(m_bdd_manager.True()),
    m_bdd_map(),
    m_assertions(),
    m_assertion_stack(),
    m_binary_relation_counter(0) {}

  BDDSolver(Logic logic)
  : Solver(logic),
    m_bdd_manager(),
    m_bdd(m_bdd_manager.True()),
    m_bdd_map(),
    m_assertions(),
    m_assertion_stack(),
    m_binary_relation_counter(0) {}
};

}

#endif
