// Copyright 2013, Alex Horn. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

#include "smt.h"

namespace smt
{

Expr::SolverPtrs Expr::s_solver_ptrs;

constexpr const char* const Logics::acronyms[24];

static constexpr size_t MAX_BV_SIZE = 1024;
static const Sort* bv_sorts[2][MAX_BV_SIZE] = { nullptr };

const Sort& bv_sort(bool is_signed, size_t size)
{
  assert(size < MAX_BV_SIZE);

  if (bv_sorts[is_signed][size] == nullptr) {
    bv_sorts[is_signed][size] = new Sort(
      false, false, false,
      true, is_signed, size);
  }

  return *bv_sorts[is_signed][size];
}

SharedExpr constant(const UnsafeDecl& decl)
{
  return make_shared_expr<ConstantExpr>(decl);
}

SharedExpr apply(
  const UnsafeDecl& func_decl,
  const SharedExpr& arg)
{
  constexpr size_t arity = 1;
  std::array<SharedExpr, arity> args = { arg };
  return make_shared_expr<FuncAppExpr<arity>>(
    func_decl, std::move(args));
}

SharedExpr apply(
  const UnsafeDecl& func_decl,
  const SharedExpr& larg,
  const SharedExpr& rarg)
{
  constexpr size_t arity = 2;
  std::array<SharedExpr, arity> args = { larg, rarg };
  return make_shared_expr<FuncAppExpr<arity>>(
    func_decl, std::move(args));
}

SharedExpr distinct(SharedExprs&& terms)
{
  return make_shared_expr<NaryExpr<NEQ>>(
    internal::sort<Bool>(), std::move(terms));
}

SharedExpr select(
  const SharedExpr& array,
  const SharedExpr& index)
{
  return make_shared_expr<ArraySelectExpr>(
    array, index);
}

SharedExpr implies(
  const SharedExpr& larg,
  const SharedExpr& rarg)
{
  return make_shared_expr<BinaryExpr<IMP>>(
    internal::sort<Bool>(), larg, rarg);
}

SharedExpr implies(
  const Bool& larg,
  const SharedExpr& rarg)
{
  return make_shared_expr<BinaryExpr<IMP>>(
    internal::sort<Bool>(), larg, rarg);
}

SharedExpr implies(
  const SharedExpr& larg,
  const Bool& rarg)
{
  return make_shared_expr<BinaryExpr<IMP>>(
    internal::sort<Bool>(), larg, rarg);
}

Bool implies(
  const Bool& larg,
  const Bool& rarg)
{
  return Bool(make_shared_expr<BinaryExpr<IMP>>(
    internal::sort<Bool>(), larg, rarg));
}

SharedExpr store(
  const SharedExpr& array,
  const SharedExpr& index,
  const SharedExpr& value)
{
  return make_shared_expr<ArrayStoreExpr>(
    array, index, value);
}

Solver::Solver()
: m_stats{0},
  m_is_timer_on(false)
{
  m_stats.encode_elapsed_time = ElapsedTime::zero();
  m_stats.check_elapsed_time = ElapsedTime::zero();

  Expr::register_solver(this);
}

Solver::Solver(Logic logic)
: m_stats{0},
  m_is_timer_on(false)
{
  m_stats.encode_elapsed_time = ElapsedTime::zero();
  m_stats.check_elapsed_time = ElapsedTime::zero();

  Expr::register_solver(this);
}

Solver::~Solver()
{
  Expr::unregister_solver(this);
}

Error Solver::encode_constant(
  const Expr* const expr,
  const UnsafeDecl& decl)
{
  ElapsedTimer timer(m_stats.encode_elapsed_time, m_is_timer_on);

  m_stats.constants++;
  return __encode_constant(expr, decl);
}

Error Solver::encode_func_app(
  const Expr* const expr,
  const UnsafeDecl& func_decl,
  const size_t arity,
  const SharedExpr* const args)
{
  ElapsedTimer timer(m_stats.encode_elapsed_time, m_is_timer_on);

  assert(0 < arity);
  assert(args != nullptr);

  m_stats.func_apps++;
  return __encode_func_app(expr, func_decl, arity, args);
}

Error Solver::encode_const_array(
  const Expr* const expr,
  const Sort& sort,
  const SharedExpr& init)
{
  ElapsedTimer timer(m_stats.encode_elapsed_time, m_is_timer_on);

  assert(!init.is_null());

  return __encode_const_array(expr, sort, init);
}

Error Solver::encode_array_select(
  const Expr* const expr,
  const SharedExpr& array,
  const SharedExpr& index)
{
  ElapsedTimer timer(m_stats.encode_elapsed_time, m_is_timer_on);

  assert(!array.is_null());
  assert(!index.is_null());

  m_stats.array_selects++;
  return __encode_array_select(expr, array, index);
}

Error Solver::encode_array_store(
  const Expr* const expr,
  const SharedExpr& array,
  const SharedExpr& index,
  const SharedExpr& value)
{
  ElapsedTimer timer(m_stats.encode_elapsed_time, m_is_timer_on);

  assert(!array.is_null());
  assert(!index.is_null());
  assert(!value.is_null());

  m_stats.array_stores++;
  return __encode_array_store(expr, array, index, value);
}

Error Solver::encode_nary(
  const Expr* const expr,
  Opcode opcode,
  const Sort& sort,
  const SharedExprs& args)
{
  ElapsedTimer timer(m_stats.encode_elapsed_time, m_is_timer_on);

  assert(!args.empty());

  switch (opcode) {
  case EQL:
    m_stats.equalities += args.size();
    break;
  case NEQ:
    m_stats.disequalities += args.size();
    break;
  case LAND:
    m_stats.conjunctions += args.size();
    break;
  case LOR:
    m_stats.disjunctions += args.size();
    break;
   default:
    ;
  }

  m_stats.nary_ops++;
  return __encode_nary(expr, opcode, sort, args);
}

Error Solver::encode_bv_zero_extend(
  const Expr* const expr,
  const Sort& sort,
  const SharedExpr& bv,
  const unsigned ext)
{
  ElapsedTimer timer(m_stats.encode_elapsed_time, m_is_timer_on);

  assert(bv.sort().is_bv());
  return __encode_bv_zero_extend(expr, sort, bv, ext);
}

Error Solver::encode_bv_sign_extend(
  const Expr* const expr,
  const Sort& sort,
  const SharedExpr& bv,
  const unsigned ext)
{
  ElapsedTimer timer(m_stats.encode_elapsed_time, m_is_timer_on);

  assert(bv.sort().is_bv());
  return __encode_bv_sign_extend(expr, sort, bv, ext);
}

Error Solver::encode_bv_extract(
  const Expr* const expr,
  const Sort& sort,
  const SharedExpr& bv,
  const unsigned high,
  const unsigned low)
{
  ElapsedTimer timer(m_stats.encode_elapsed_time, m_is_timer_on);

  assert(bv.sort().is_bv());
  return __encode_bv_extract(expr, sort, bv, high, low);
}

void Solver::reset()
{
  return __reset();
}

void Solver::push()
{
  return __push();
}

void Solver::pop()
{
  return __pop();
}

void Solver::unsafe_add(const SharedExpr& condition)
{
  NonReentrantTimer<ElapsedTime> timer(m_stats.encode_elapsed_time);

  assert(condition.sort().is_bool());
  const Error err = __unsafe_add(condition);
  assert(err == OK);
}

void Solver::add(const Bool& condition)
{
  const Error err = __unsafe_add(condition);
  assert(err == OK);
}

CheckResult Solver::check()
{
  NonReentrantTimer<ElapsedTime> timer(m_stats.check_elapsed_time);

  return __check();
}

Bool Identity<LAND, Bool>::term(literal<Bool>(true));

}
