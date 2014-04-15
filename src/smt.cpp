// Copyright 2013, Alex Horn. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

#include "smt.h"

namespace smt
{

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

UnsafeTerm constant(const UnsafeDecl& decl)
{
  return UnsafeTerm(std::make_shared<ConstantExpr>(decl));
}

UnsafeTerm apply(
  const UnsafeDecl& func_decl,
  const UnsafeTerm& arg)
{
  constexpr size_t arity = 1;
  std::array<UnsafeTerm, arity> args = { arg };
  return UnsafeTerm(std::make_shared<FuncAppExpr<arity>>(
    func_decl, std::move(args)));
}

UnsafeTerm apply(
  const UnsafeDecl& func_decl,
  const UnsafeTerm& larg,
  const UnsafeTerm& rarg)
{
  constexpr size_t arity = 2;
  std::array<UnsafeTerm, arity> args = { larg, rarg };
  return UnsafeTerm(std::make_shared<FuncAppExpr<arity>>(
    func_decl, std::move(args)));
}

UnsafeTerm distinct(UnsafeTerms&& terms)
{
  return UnsafeTerm(std::make_shared<NaryExpr<NEQ>>(
    internal::sort<Bool>(), std::move(terms)));
}

UnsafeTerm select(
  const UnsafeTerm& array,
  const UnsafeTerm& index)
{
  return UnsafeTerm(std::make_shared<ArraySelectExpr>(
    array, index));
}

UnsafeTerm implies(
  const UnsafeTerm& larg,
  const UnsafeTerm& rarg)
{
  return UnsafeTerm(std::make_shared<BinaryExpr<IMP>>(
    internal::sort<Bool>(), larg, rarg));
}

Bool implies(
  const Bool& larg,
  const Bool& rarg)
{
  return Bool(std::make_shared<BinaryExpr<IMP>>(
    internal::sort<Bool>(), larg, rarg));
}

UnsafeTerm store(
  const UnsafeTerm& array,
  const UnsafeTerm& index,
  const UnsafeTerm& value)
{
  return UnsafeTerm(std::make_shared<ArrayStoreExpr>(
    array, index, value));
}

Error Solver::encode_constant(
  const UnsafeDecl& decl)
{
  m_stats.constants++;
  return __encode_constant(decl);
}

Error Solver::encode_func_app(
  const UnsafeDecl& func_decl,
  const size_t arity,
  const UnsafeTerm* const args)
{
  assert(0 < arity);
  assert(args != nullptr);

  m_stats.func_apps++;
  return __encode_func_app(func_decl, arity, args);
}

Error Solver::encode_const_array(
  const Sort& sort,
  const UnsafeTerm& init)
{
  assert(!init.is_null());

  return __encode_const_array(sort, init);
}

Error Solver::encode_array_select(
  const UnsafeTerm& array,
  const UnsafeTerm& index)
{
  assert(!array.is_null());
  assert(!index.is_null());

  m_stats.array_selects++;
  return __encode_array_select(array, index);
}

Error Solver::encode_array_store(
  const UnsafeTerm& array,
  const UnsafeTerm& index,
  const UnsafeTerm& value)
{
  assert(!array.is_null());
  assert(!index.is_null());
  assert(!value.is_null());

  m_stats.array_stores++;
  return __encode_array_store(array, index, value);
}

Error Solver::encode_unary(
  Opcode opcode,
  const Sort& sort,
  const UnsafeTerm& arg)
{
  assert(!arg.is_null());

  m_stats.unary_ops++;
  return __encode_unary(opcode, sort, arg);
}

Error Solver::encode_binary(
  Opcode opcode,
  const Sort& sort,
  const UnsafeTerm& larg,
  const UnsafeTerm& rarg)
{
  assert(!larg.is_null());
  assert(!rarg.is_null());
  assert(larg.sort() == rarg.sort());

  switch (opcode) {
  case EQL:
    m_stats.equalities++;
    break;
  case NEQ:
    m_stats.disequalities++;
    break;
  case LSS:
  case GTR:
  case LEQ:
  case GEQ:
    m_stats.inequalities++;
    break;
  case IMP:
    m_stats.implications++;
    break;
  case LAND:
    m_stats.conjunctions++;
    break;
  case LOR:
    m_stats.disjunctions++;
    break;
   default:
    ;
  }

  m_stats.binary_ops++;
  return __encode_binary(opcode, sort, larg, rarg);
}

Error Solver::encode_nary(
  Opcode opcode,
  const Sort& sort,
  const UnsafeTerms& args)
{
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
  return __encode_nary(opcode, sort, args);
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

void Solver::unsafe_add(const UnsafeTerm& condition)
{
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
  return __check();
}

Bool Identity<LAND, Bool>::term(literal<Bool>(true));

}
