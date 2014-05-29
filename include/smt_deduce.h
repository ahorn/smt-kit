// Copyright 2014, Alex Horn. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

#ifndef _SMT_LATTICE_H_
#define _SMT_LATTICE_H_

#include <unordered_map>
#include <vector>
#include <stack>

#include "smt.h"

namespace smt
{

/// Deduce facts in the Boolean skeleton of formulas using unit propagation

/// This solver shows how symbolic execution can use abstraction techniques
/// to check whether the Boolean skeleton of path conditions is unsatisfiable.
///
/// This solver design is inspired by recent papers on abstract satisfaction,
/// see D'Silva, Haller and Kroening who published in POPL'13 and POPL'14.
class DeduceSolver : public Solver
{
private:
  static constexpr Error conflict_error()
  {
    return static_cast<Error>(404U);
  }

  /// Partial assignment for predicates in the Boolean skeleton of the
  /// formula to be checked for unsatisfiability

  /// Unit propagation is implemented as an abstract transformer that
  /// assigns satisfying truth values to the Boolean variables according
  /// to the in-order traversal of the formula's syntactic structure.
  ///
  /// Conflicts are detected by unit_propagate(), the only function
  /// that is allowed to directly update the partial assignments!
  typedef std::unordered_map<uintptr_t, bool> PartialAssignment;

  /// Partial assignment of predicates in the Boolean skeleton
  PartialAssignment m_partial_assignment;

  /// Used to interpret the formula in negation normal form
  bool m_is_negation;

  bool is_top(uintptr_t addr)
  {
    PartialAssignment::const_iterator citer = m_partial_assignment.find(addr);
    return citer == m_partial_assignment.cend();
  }

  bool is_false(uintptr_t addr)
  {
    PartialAssignment::const_iterator citer = m_partial_assignment.find(addr);
    if (citer == m_partial_assignment.cend())
      return false;

    return !citer->second;
  }

  Error unit_propagate(const Expr* const expr, bool fact)
  {
    PartialAssignment::iterator iter;
    bool ok;

    std::tie(iter, ok) = m_partial_assignment.emplace(
      reinterpret_cast<uintptr_t>(expr), fact);
    const bool is_consistent = iter->second == fact;

    /// a newly inserted fact cannot yield a conflict
    assert(!ok || is_consistent);

    if (!is_consistent)
      return conflict_error();

    return OK;
  }

  /// \pre: expr->sort().is_bool()
  Error abstract_binary_relation(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg)
  {
    return unit_propagate(expr, !m_is_negation);
  }

  virtual Error __encode_literal(
    const Expr* const expr,
    bool literal)
  {
    if (!expr->sort().is_bool())
      return UNSUPPORT_ERROR;

    if (literal == m_is_negation)
      return conflict_error();

    return OK;
  }

#define SMT_LATTICE_CAST_ENCODE_BUILTIN_LITERAL(type) \
  virtual Error __encode_literal(                     \
     const Expr* const expr,                          \
     type literal) override                           \
  {                                                   \
    return UNSUPPORT_ERROR;                           \
  }                                                   \

SMT_LATTICE_CAST_ENCODE_BUILTIN_LITERAL(char)
SMT_LATTICE_CAST_ENCODE_BUILTIN_LITERAL(signed char)
SMT_LATTICE_CAST_ENCODE_BUILTIN_LITERAL(unsigned char)
SMT_LATTICE_CAST_ENCODE_BUILTIN_LITERAL(wchar_t)
SMT_LATTICE_CAST_ENCODE_BUILTIN_LITERAL(char16_t)
SMT_LATTICE_CAST_ENCODE_BUILTIN_LITERAL(char32_t)
SMT_LATTICE_CAST_ENCODE_BUILTIN_LITERAL(short)
SMT_LATTICE_CAST_ENCODE_BUILTIN_LITERAL(unsigned short)
SMT_LATTICE_CAST_ENCODE_BUILTIN_LITERAL(int)
SMT_LATTICE_CAST_ENCODE_BUILTIN_LITERAL(unsigned int)
SMT_LATTICE_CAST_ENCODE_BUILTIN_LITERAL(long)
SMT_LATTICE_CAST_ENCODE_BUILTIN_LITERAL(unsigned long)
SMT_LATTICE_CAST_ENCODE_BUILTIN_LITERAL(long long)
SMT_LATTICE_CAST_ENCODE_BUILTIN_LITERAL(unsigned long long)

  virtual Error __encode_constant(
    const Expr* const expr,
    const UnsafeDecl& decl) override
  {
    if (!decl.sort().is_bool())
      return UNSUPPORT_ERROR;

    return unit_propagate(expr, !m_is_negation);
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
    const SharedExpr& arg) override
  {
    m_is_negation = !m_is_negation;
    const Error err = arg.encode(*this);
    m_is_negation = !m_is_negation;

    if (err)
      return err;

    return OK;
  }

  virtual Error __encode_unary_not(
    const Expr* const expr,
    const SharedExpr& arg) override
  {
    return UNSUPPORT_ERROR;
  }

  virtual Error __encode_unary_sub(
    const Expr* const expr,
    const SharedExpr& arg) override
  {
    return UNSUPPORT_ERROR;
  }

  virtual Error __encode_binary_sub(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg) override
  {
    return UNSUPPORT_ERROR;
  }

  virtual Error __encode_binary_and(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg) override
  {
    return UNSUPPORT_ERROR;
  }

  virtual Error __encode_binary_or(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg) override
  {
    return UNSUPPORT_ERROR;
  }

  virtual Error __encode_binary_xor(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg) override
  {
    return UNSUPPORT_ERROR;
  }

  virtual Error __encode_binary_land(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg) override
  {
    Error err;
    if (!m_is_negation || is_false(larg.addr()))
    {
      err = rarg.encode(*this);
      if (err)
        return err;
    }

    if (!m_is_negation || is_false(rarg.addr()))
    {
      err = larg.encode(*this);
      if (err)
        return err;
    }

    return OK;
  }

  virtual Error __encode_binary_lor(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg) override
  {
    Error err;
    if (m_is_negation || is_false(larg.addr()))
    {
      err = rarg.encode(*this);
      if (err)
        return err;
    }

    if (m_is_negation || is_false(rarg.addr()))
    {
      err = larg.encode(*this);
      if (err)
        return err;
    }

    return OK;
  }

  virtual Error __encode_binary_imp(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg) override
  {
    return UNSUPPORT_ERROR;
  }

  virtual Error __encode_binary_eql(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg) override
  {
    return abstract_binary_relation(expr, larg, rarg);
  }

  virtual Error __encode_binary_add(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg) override
  {
    return UNSUPPORT_ERROR;
  }

  virtual Error __encode_binary_mul(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg) override
  {
    return UNSUPPORT_ERROR;
  }

  virtual Error __encode_binary_quo(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg) override
  {
    return UNSUPPORT_ERROR;
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
    return abstract_binary_relation(expr, larg, rarg);
  }

  virtual Error __encode_binary_gtr(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg) override
  {
    return abstract_binary_relation(expr, larg, rarg);
  }

  virtual Error __encode_binary_neq(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg) override
  {
    return abstract_binary_relation(expr, larg, rarg);
  }

  virtual Error __encode_binary_leq(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg) override
  {
    return abstract_binary_relation(expr, larg, rarg);
  }

  virtual Error __encode_binary_geq(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg) override
  {
    return abstract_binary_relation(expr, larg, rarg);
  }

  virtual Error __encode_nary(
    const Expr* const expr,
    Opcode opcode,
    const SharedExprs& args) override
  {
    switch (opcode)
    {
    case LAND:
    case LOR:
      break;

    default:
      return UNSUPPORT_ERROR;
    }

    Error err;
    for (const SharedExpr& arg : args)
    {
      err = arg.encode(*this);
      if (err)
        return err;
    }

    return OK;
  }

  virtual Error __encode_bv_zero_extend(
    const Expr* const expr,
    const SharedExpr& bv,
    const unsigned ext) override
  {
    return UNSUPPORT_ERROR;
  }

  virtual Error __encode_bv_sign_extend(
    const Expr* const expr,
    const SharedExpr& bv,
    const unsigned ext) override
  {
    return UNSUPPORT_ERROR;
  }

  virtual Error __encode_bv_extract(
    const Expr* const expr,
    const SharedExpr& bv,
    const unsigned high,
    const unsigned low) override
  {
    return UNSUPPORT_ERROR;
  }

  virtual void __notify_delete(const Expr* const expr) override
  {
    m_partial_assignment.erase(reinterpret_cast<uintptr_t>(expr));
  }

  virtual void __reset() override
  {
    m_partial_assignment.clear();
    m_is_negation = false;
  }

  virtual void __push() override
  {
  }

  virtual void __pop() override
  {
  }

  virtual Error __unsafe_add(const SharedExpr& condition) override
  {
    return OK;
  }

  virtual Error __add(const Bool& condition) override
  {
    return __unsafe_add(condition);
  }

  /// Is the conjunction of assertions unsatisfiable?

  /// Since this implementation considers only the Boolean skeleton of the
  /// formula, __check() is necessarily incomplete.
  virtual CheckResult __check() override
  {
    Error err;
    PartialAssignment::size_type size;

    m_partial_assignment.clear();
    for (;;)
    {
      size = m_partial_assignment.size();
      err = __encode_nary(nullptr, LAND, Solver::assertions().terms);

      if (err == conflict_error())
        return unsat;

      // reached fixed point
      if (size == m_partial_assignment.size())
        return unknown;
    }

    return sat;
  }

  virtual std::pair<CheckResult, SharedExprs::size_type>
  __check_assumptions(
    const SharedExprs& assumptions,
    SharedExprs& unsat_core) override
  {
    return {unknown, 0};
  }

public:
  DeduceSolver()
  : Solver(),
    m_partial_assignment(),
    m_is_negation(false) {}

  DeduceSolver(Logic logic)
  : Solver(logic),
    m_partial_assignment(),
    m_is_negation(false) {}
};

}

#endif
