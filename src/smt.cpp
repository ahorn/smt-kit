// Copyright 2013, Alex Horn. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

#include "smt.h"

namespace smt
{

Error Solver::encode_constant(
  const UnsafeDecl& decl)
{
  return __encode_constant(decl);
}

Error Solver::encode_func_app(
  const UnsafeDecl& func_decl,
  const size_t arity,
  const UnsafeExprPtr* const arg_ptrs)
{
  assert(0 < arity);
  assert(arg_ptrs != nullptr);

  return __encode_func_app(func_decl, arity, arg_ptrs);
}

Error Solver::encode_const_array(
  const Sort& sort,
  UnsafeExprPtr init_ptr)
{
  assert(init_ptr != nullptr);

  return __encode_const_array(sort, init_ptr);
}

Error Solver::encode_array_select(
  UnsafeExprPtr array_ptr,
  UnsafeExprPtr index_ptr)
{
  assert(array_ptr != nullptr);
  assert(index_ptr != nullptr);

  return __encode_array_select(array_ptr, index_ptr);
}

Error Solver::encode_array_store(
  UnsafeExprPtr array_ptr,
  UnsafeExprPtr index_ptr,
  UnsafeExprPtr value_ptr)
{
  assert(array_ptr != nullptr);
  assert(index_ptr != nullptr);
  assert(value_ptr != nullptr);

  return __encode_array_store(array_ptr, index_ptr, value_ptr);
}

Error Solver::encode_builtin(
  Opcode opcode,
  const Sort& sort,
  UnsafeExprPtr expr_ptr)
{
  assert(expr_ptr != nullptr);

  return __encode_builtin(opcode, sort, expr_ptr);
}

Error Solver::encode_builtin(
  Opcode opcode,
  const Sort& sort,
  UnsafeExprPtr lptr,
  UnsafeExprPtr rptr)
{
  assert(lptr != nullptr);
  assert(rptr != nullptr);
  assert(&lptr->sort() == &rptr->sort());

  return __encode_builtin(opcode, sort, lptr, rptr);
}

void Solver::push()
{
  return __push();
}

void Solver::pop()
{
  return __pop();
}

Error Solver::add(ExprPtr<sort::Bool> condition)
{
  return __add(condition);
}

CheckResult Solver::check()
{
  return __check();
}

ExprPtr<sort::Bool> implies(ExprPtr<sort::Bool> lptr, ExprPtr<sort::Bool> rptr)
{
  return ExprPtr<sort::Bool>(new BuiltinBinaryExpr<IMP, sort::Bool>(lptr, rptr));
}

ExprPtr<sort::Bool> Identity<LAND, sort::Bool>::expr_ptr(literal<sort::Bool>(true));

}
