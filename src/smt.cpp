// Copyright 2013, Alex Horn. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

#include "smt.h"

namespace smt
{

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

UnsafeExprPtr constant(const UnsafeDecl& decl)
{
  return UnsafeExprPtr(new UnsafeConstantExpr(decl));
}

UnsafeExprPtr apply(UnsafeDecl func_decl, UnsafeExprPtr arg_ptr)
{
  return UnsafeExprPtr(new UnsafeFuncAppExpr<1>(func_decl, { arg_ptr }));
}

UnsafeExprPtr apply(
  UnsafeDecl func_decl,
  UnsafeExprPtr larg_ptr,
  UnsafeExprPtr rarg_ptr)
{
  return UnsafeExprPtr(new UnsafeFuncAppExpr<2>(func_decl,
    { larg_ptr, rarg_ptr }));
}

UnsafeExprPtr distinct(UnsafeExprPtrs&& ptrs)
{
  return UnsafeExprPtr(new UnsafeNaryExpr(
    internal::sort<sort::Bool>(), NEQ, std::move(ptrs)));
}

UnsafeExprPtr select(UnsafeExprPtr array_ptr, UnsafeExprPtr index_ptr)
{
  return UnsafeExprPtr(new UnsafeArraySelectExpr(array_ptr, index_ptr));
}

UnsafeExprPtr implies(UnsafeExprPtr lptr, UnsafeExprPtr rptr)
{
  return UnsafeExprPtr(new UnsafeBinaryExpr(
    internal::sort<sort::Bool>(), IMP, lptr, rptr));
}

ExprPtr<sort::Bool> implies(ExprPtr<sort::Bool> lptr, ExprPtr<sort::Bool> rptr)
{
  return ExprPtr<sort::Bool>(new BinaryExpr<IMP, sort::Bool>(lptr, rptr));
}

UnsafeExprPtr store(
  UnsafeExprPtr array_ptr,
  UnsafeExprPtr index_ptr,
  UnsafeExprPtr value_ptr)
{
  return UnsafeExprPtr(new UnsafeArrayStoreExpr(
    array_ptr, index_ptr, value_ptr));
}

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

Error Solver::encode_unary(
  Opcode opcode,
  const Sort& sort,
  UnsafeExprPtr expr_ptr)
{
  assert(expr_ptr != nullptr);

  return __encode_unary(opcode, sort, expr_ptr);
}

Error Solver::encode_binary(
  Opcode opcode,
  const Sort& sort,
  UnsafeExprPtr lptr,
  UnsafeExprPtr rptr)
{
  assert(lptr != nullptr);
  assert(rptr != nullptr);
  assert(lptr->sort() == rptr->sort());

  return __encode_binary(opcode, sort, lptr, rptr);
}

Error Solver::encode_nary(
  Opcode opcode,
  const Sort& sort,
  const UnsafeExprPtrs& ptrs)
{
  assert(!ptrs.empty());

  return __encode_nary(opcode, sort, ptrs);
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

Error Solver::unsafe_add(UnsafeExprPtr condition)
{
  return __unsafe_add(condition);
}

Error Solver::add(ExprPtr<sort::Bool> condition)
{
  return __add(condition);
}

CheckResult Solver::check()
{
  return __check();
}

ExprPtr<sort::Bool> Identity<LAND, sort::Bool>::expr_ptr(literal<sort::Bool>(true));

}
