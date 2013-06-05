// Copyright 2013, Alex Horn. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

#include "smt.h"

namespace smt
{

ExprPtr<sort::Bool> implies(ExprPtr<sort::Bool> lptr, ExprPtr<sort::Bool> rptr)
{
  return ExprPtr<sort::Bool>(new BuiltinBinaryExpr<IMP, sort::Bool>(lptr, rptr));
}

ExprPtr<sort::Bool> Identity<LAND, sort::Bool>::expr_ptr(literal<sort::Bool>(true));

}
