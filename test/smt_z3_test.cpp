#include "gtest/gtest.h"

#include "smt.h"
#include "smt_z3.h"

using namespace smt;

TEST(SmtZ3Test, BvNoCastBuiltinLiteralExpr)
{
  Z3Solver s;

  const BuiltinLiteralExpr<int> e0(42);
  EXPECT_EQ(OK, e0.encode(s));

  const z3::expr expr(s.expr());
  EXPECT_TRUE(expr.is_bv());
  EXPECT_TRUE(expr.is_const());
  EXPECT_EQ(sizeof(int) * 8, expr.get_sort().bv_size());

  z3::solver& solver = s.solver();

  solver.add(42 == expr);
  EXPECT_EQ(z3::sat, solver.check());

  solver.add(42 != expr);
  EXPECT_EQ(z3::unsat, solver.check());
}

TEST(SmtZ3Test, BvCastBuiltinLiteralExpr)
{
  Z3Solver s;

  const BuiltinLiteralExpr<char> e0('A');
  EXPECT_EQ(OK, e0.encode(s));

  const z3::expr expr(s.expr());
  EXPECT_TRUE(expr.is_bv());
  EXPECT_TRUE(expr.is_const());
  EXPECT_EQ(sizeof(char) * 8, expr.get_sort().bv_size());

  z3::solver& solver = s.solver();

  solver.push();
  {
    solver.add('A' == expr);
    EXPECT_EQ(z3::sat, solver.check());
  }
  solver.pop();

  solver.push();
  {
    solver.add('A' != expr);
    EXPECT_EQ(z3::unsat, solver.check());
  }
  solver.pop();
}

TEST(SmtZ3Test, Bv64CastBuiltinLiteralExpr)
{
  Z3Solver s;

  const BuiltinLiteralExpr<long> e0(42L);
  EXPECT_EQ(OK, e0.encode(s));

  const z3::expr expr(s.expr());
  EXPECT_TRUE(expr.is_bv());
  EXPECT_TRUE(expr.is_const());

  // due to Z3_mk_int64
  EXPECT_EQ(sizeof(int64_t) * 8, expr.get_sort().bv_size());

  z3::solver& solver = s.solver();

  solver.add(42 == expr);
  EXPECT_EQ(z3::sat, solver.check());

  solver.add(42 != expr);
  EXPECT_EQ(z3::unsat, solver.check());
}

TEST(SmtZ3Test, BoolBuiltinLiteralExpr)
{
  Z3Solver s;

  const BuiltinLiteralExpr<sort::Bool, bool> e0(true);
  EXPECT_EQ(OK, e0.encode(s));

  const z3::expr expr(s.expr());
  EXPECT_TRUE(expr.is_bool());
  EXPECT_TRUE(expr.is_const());

  z3::solver& solver = s.solver();

  solver.push();
  {
    solver.add(expr);
    EXPECT_EQ(z3::sat, solver.check());
  }
  solver.pop();

  solver.push();
  {
    solver.add(!expr);
    EXPECT_EQ(z3::unsat, solver.check());
  }
  solver.pop();
}

TEST(SmtZ3Test, IntBuiltinLiteralExpr)
{
  Z3Solver s;

  const BuiltinLiteralExpr<sort::Int, char> e0('A');
  EXPECT_EQ(OK, e0.encode(s));

  const z3::expr expr(s.expr());
  EXPECT_TRUE(expr.is_int());
  EXPECT_TRUE(expr.is_const());

  z3::solver& solver = s.solver();

  solver.push();
  {
    solver.add('A' == expr);
    EXPECT_EQ(z3::sat, solver.check());
  }
  solver.pop();

  solver.push();
  {
    solver.add('A' != expr);
    EXPECT_EQ(z3::unsat, solver.check());
  }
  solver.pop();
}

TEST(SmtZ3Test, RealBuiltinLiteralExpr)
{
  Z3Solver s;

  // note that float and double are unsupported
  const BuiltinLiteralExpr<sort::Real, int> e0(7);
  EXPECT_EQ(OK, e0.encode(s));

  const z3::expr expr(s.expr());
  EXPECT_TRUE(expr.is_real());
  EXPECT_TRUE(expr.is_const());

  z3::solver& solver = s.solver();

  solver.push();
  {
    solver.add(7 == expr);
    EXPECT_EQ(z3::sat, solver.check());
  }
  solver.pop();

  solver.push();
  {
    solver.add(7 != expr);
    EXPECT_EQ(z3::unsat, solver.check());
  }
  solver.pop();
}

TEST(SmtZ3Test, DeclExpr)
{
  Z3Solver s;
  constexpr size_t bv_size = sizeof(long) * 8;

  const DeclExpr<long> e0("x");
  EXPECT_EQ(OK, e0.encode(s));

  const z3::expr expr(s.expr());
  EXPECT_TRUE(expr.is_bv());
  EXPECT_TRUE(expr.is_const());
  EXPECT_EQ(bv_size, expr.get_sort().bv_size());

  z3::solver& solver = s.solver();

  solver.push();
  {
    solver.add(42 == expr);
    EXPECT_EQ(z3::sat, solver.check());
  }
  solver.pop();

  solver.push();
  {
    solver.add(42 != expr);
    EXPECT_EQ(z3::sat, solver.check());
  }
  solver.pop();

  solver.push();
  {
    const z3::sort z3_sort(s.context().bv_sort(bv_size));
    const z3::expr z3_expr(s.context().constant("x", z3_sort));
    solver.add(z3_expr != expr);
    EXPECT_EQ(z3::unsat, solver.check());
  }
  solver.pop();
}

TEST(SmtZ3Test, BuiltinUnaryExpr)
{
  Z3Solver s;

  const ExprPtr<int> e0_ptr(new BuiltinLiteralExpr<int>(42));
  const BuiltinUnaryExpr<SUB, int> e1(e0_ptr);

  EXPECT_EQ(OK, e1.encode(s));

  const z3::expr expr(s.expr());
  EXPECT_TRUE(expr.is_bv());
  EXPECT_TRUE(expr.is_app());
  EXPECT_EQ(sizeof(int) * 8, expr.get_sort().bv_size());

  z3::solver& solver = s.solver();

  solver.push();
  {
    solver.add(-42 == expr);
    EXPECT_EQ(z3::sat, solver.check());
  }
  solver.pop();

  solver.push();
  {
    solver.add(-42 != expr);
    EXPECT_EQ(z3::unsat, solver.check());
  }
  solver.pop();
}

TEST(SmtZ3Test, BuiltinBinaryExpr)
{
  Z3Solver s;
  z3::expr expr(s.context());

  const ExprPtr<long> e0_ptr(new BuiltinLiteralExpr<long>(42L));
  const ExprPtr<long> e1_ptr(new BuiltinLiteralExpr<long>(7L));
  const BuiltinBinaryExpr<ADD, long> e2(e0_ptr, e1_ptr);

  EXPECT_EQ(OK, e2.encode(s));

  expr = s.expr();
  EXPECT_TRUE(expr.is_bv());
  EXPECT_TRUE(expr.is_app());
  EXPECT_EQ(sizeof(long) * 8, expr.get_sort().bv_size());

  z3::solver& solver = s.solver();

  solver.push();
  {
    solver.add(49 == expr);
    EXPECT_EQ(z3::sat, solver.check());
  }
  solver.pop();

  solver.push();
  {
    solver.add(49 != expr);
    EXPECT_EQ(z3::unsat, solver.check());
  }
  solver.pop();

  const BuiltinBinaryExpr<LSS, long, sort::Bool> e3(e0_ptr, e1_ptr);

  EXPECT_EQ(OK, e3.encode(s));

  expr = s.expr();
  EXPECT_TRUE(expr.is_bool());
  EXPECT_TRUE(expr.is_app());

  solver.push();
  {
    solver.add(expr);
    EXPECT_EQ(z3::unsat, solver.check());
  }
  solver.pop();

  const BuiltinBinaryExpr<GTR, long, sort::Bool> e4(e0_ptr, e1_ptr);

  EXPECT_EQ(OK, e4.encode(s));

  expr = s.expr();
  EXPECT_TRUE(expr.is_bool());
  EXPECT_TRUE(expr.is_app());

  solver.push();
  {
    solver.add(expr);
    EXPECT_EQ(z3::sat, solver.check());
  }
  solver.pop();
}

TEST(SmtZ3Test, LogicalImplication)
{
  Z3Solver s;
  z3::expr expr(s.context());

  const ExprPtr<sort::Bool> e0_ptr(new DeclExpr<sort::Bool>("x"));
  const ExprPtr<sort::Bool> e1_ptr(new DeclExpr<sort::Bool>("y"));
  const BuiltinBinaryExpr<IMP, sort::Bool> e2(e0_ptr, e1_ptr);

  EXPECT_EQ(OK, e2.encode(s));

  expr = s.expr();
  EXPECT_TRUE(expr.is_bool());
  EXPECT_TRUE(expr.is_app());

  z3::solver& solver = s.solver();

  const z3::expr x_expr(s.context().bool_const("x"));
  const z3::expr y_expr(s.context().bool_const("y"));
  solver.push();
  {
    solver.add(implies(x_expr, y_expr) == expr);
    EXPECT_EQ(z3::sat, solver.check());
  }
  solver.pop();

  solver.push();
  {
    solver.add(implies(x_expr, y_expr) != expr);
    EXPECT_EQ(z3::unsat, solver.check());
  }
  solver.pop();
}

TEST(SmtZ3Test, FuncDeclExpr)
{
  Z3Solver s;

  const DeclExpr<sort::Func<sort::Int, long>> e0("f");
  EXPECT_EQ(OK, e0.encode(s));

  const z3::func_decl f_decl(s.context(),
    (Z3_func_decl)(static_cast<Z3_ast>(s.ast())));
  EXPECT_EQ("f", f_decl.name().str());
  EXPECT_EQ(1, f_decl.arity());
  EXPECT_TRUE(f_decl.domain(0).is_int());
  EXPECT_TRUE(f_decl.range().is_bv());
  EXPECT_EQ(sizeof(long) * 8, f_decl.range().bv_size());
}

TEST(SmtZ3Test, UnaryFuncAppExpr)
{
  Z3Solver s;

  const ExprPtr<sort::Func<sort::Int, long>> e0_ptr(new DeclExpr<sort::Func<sort::Int, long>>("f"));
  const ExprPtr<sort::Int> e1_ptr(new BuiltinLiteralExpr<sort::Int, int>(7));
  const FuncAppExpr<sort::Int, long> e2(e0_ptr, std::make_tuple(e1_ptr));

  EXPECT_EQ(OK, e2.encode(s));
  const z3::expr app_expr(s.expr());

  z3::context& context = s.context();
  z3::solver& solver = s.solver();

  const z3::sort long_bv_sort(context.bv_sort(sizeof(long) * 8));
  const z3::func_decl f_decl(context.function("f", context.int_sort(), long_bv_sort));

  solver.push();
  {
    solver.add(f_decl(3) == app_expr);
    EXPECT_EQ(z3::sat, solver.check());
  }
  solver.pop();

  solver.push();
  {
    solver.add(f_decl(3) != app_expr);
    EXPECT_EQ(z3::sat, solver.check());
  }
  solver.pop();

  solver.push();
  {
    solver.add(f_decl(7) == app_expr);
    EXPECT_EQ(z3::sat, solver.check());
  }
  solver.pop();

  solver.push();
  {
    solver.add(f_decl(7) != app_expr);
    EXPECT_EQ(z3::unsat, solver.check());
  }
  solver.pop();
}

TEST(SmtZ3Test, BinaryFuncAppExpr)
{
  Z3Solver s;

  const ExprPtr<sort::Func<sort::Int, bool, long>> e0_ptr(new DeclExpr<sort::Func<sort::Int, bool, long>>("f"));
  const ExprPtr<sort::Int> e1_ptr(new BuiltinLiteralExpr<sort::Int, int>(7));
  const ExprPtr<bool> e2_ptr(new DeclExpr<bool>("x"));
  const FuncAppExpr<sort::Int, bool, long> e3(e0_ptr, std::make_tuple(e1_ptr, e2_ptr));

  EXPECT_EQ(OK, e3.encode(s));
  const z3::expr app_expr(s.expr());

  z3::context& context = s.context();
  z3::solver& solver = s.solver();

  const z3::sort bool_bv_sort(context.bv_sort(sizeof(bool) * 8));
  const z3::sort long_bv_sort(context.bv_sort(sizeof(long) * 8));
  const z3::func_decl f_decl(context.function("f", context.int_sort(),
    bool_bv_sort, long_bv_sort));

  const z3::expr x_expr(s.context().constant("x", bool_bv_sort));
  solver.push();
  {
    solver.add(f_decl(3, x_expr) == app_expr);
    EXPECT_EQ(z3::sat, solver.check());
  }
  solver.pop();

  solver.push();
  {
    solver.add(f_decl(3, x_expr) != app_expr);
    EXPECT_EQ(z3::sat, solver.check());
  }
  solver.pop();

  solver.push();
  {
    solver.add(f_decl(7, x_expr) == app_expr);
    EXPECT_EQ(z3::sat, solver.check());
  }
  solver.pop();

  solver.push();
  {
    solver.add(f_decl(7, x_expr) != app_expr);
    EXPECT_EQ(z3::unsat, solver.check());
  }
  solver.pop();
}

TEST(SmtZ3Test, ConstArrayExpr)
{
  Z3Solver s;

  const ExprPtr<sort::Int> init_ptr(new BuiltinLiteralExpr<sort::Int, int>(7));
  const ConstArrayExpr<sort::Int, sort::Int> e0(init_ptr);

  EXPECT_EQ(OK, e0.encode(s));

  const z3::expr const_array_expr(s.expr());
  EXPECT_TRUE(const_array_expr.is_app());
  EXPECT_TRUE(const_array_expr.is_array());

  z3::context& context = s.context();
  z3::solver& solver = s.solver();

  const z3::expr i_expr(context.int_const("i"));
  const z3::expr j_expr(context.int_const("j"));

  solver.push();
  {
    solver.add(z3::select(const_array_expr, i_expr) == 7);
    EXPECT_EQ(z3::sat, solver.check());
  }
  solver.pop();

  solver.push();
  {
    solver.add(z3::select(const_array_expr, i_expr) != 7);
    EXPECT_EQ(z3::unsat, solver.check());
  }
  solver.pop();

  solver.push();
  {
    solver.add(z3::select(const_array_expr, i_expr) != z3::select(const_array_expr, j_expr));
    EXPECT_EQ(z3::unsat, solver.check());
  }
  solver.pop();
}

TEST(SmtZ3Test, ArraySelectExpr)
{
  Z3Solver s;

  const ExprPtr<sort::Array<sort::Int, sort::Bool>> array_ptr(
    new DeclExpr<sort::Array<sort::Int, sort::Bool>>("x"));

  const ExprPtr<sort::Int> index_ptr(new DeclExpr<sort::Int>("i"));
  const ArraySelectExpr<sort::Int, sort::Bool> e0(array_ptr, index_ptr);

  EXPECT_EQ(OK, e0.encode(s));

  const z3::expr select_expr(s.expr());
  EXPECT_TRUE(select_expr.is_app());
  EXPECT_TRUE(select_expr.is_bool());

  z3::context& context = s.context();
  z3::solver& solver = s.solver();

  solver.add(context.bool_val(true) == select_expr);
  EXPECT_EQ(z3::sat, solver.check());

  const z3::sort array_sort = context.array_sort(context.int_sort(), context.bool_sort());
  const z3::expr array_expr = context.constant("x", array_sort);
  const z3::expr i_expr(context.int_const("i"));
  const z3::expr j_expr(context.int_const("j"));
  const z3::expr store_expr = z3::store(array_expr, j_expr, context.bool_val(false));
  solver.add(array_expr == store_expr);
  EXPECT_EQ(z3::sat, solver.check());

  solver.add(i_expr == j_expr);
  EXPECT_EQ(z3::unsat, solver.check());
}

TEST(SmtZ3Test, ArrayStoreExpr)
{
  Z3Solver s;

  const ExprPtr<sort::Array<sort::Int, sort::Int>> array_ptr(
    new DeclExpr<sort::Array<sort::Int, sort::Int>>("x"));

  const ExprPtr<sort::Int> index_ptr(new DeclExpr<sort::Int>("i"));
  const ExprPtr<sort::Int> value_ptr(new BuiltinLiteralExpr<sort::Int, int>(7));
  const ArrayStoreExpr<sort::Int, sort::Int> e0(array_ptr, index_ptr, value_ptr);

  EXPECT_EQ(OK, e0.encode(s));

  const z3::expr store_expr(s.expr());
  EXPECT_TRUE(store_expr.is_app());
  EXPECT_TRUE(store_expr.is_array());

  z3::context& context = s.context();
  z3::solver& solver = s.solver();

  const z3::expr i_expr(context.int_const("i"));
  const z3::expr j_expr(context.int_const("j"));

  solver.push();
  {
    solver.add(z3::select(store_expr, i_expr) == 7);
    EXPECT_EQ(z3::sat, solver.check());
  }
  solver.pop();

  solver.push();
  {
    solver.add(z3::select(store_expr, i_expr) != 7);
    EXPECT_EQ(z3::unsat, solver.check());
  }
  solver.pop();

  solver.push();
  {
    solver.add(z3::select(store_expr, j_expr) == 7);
    EXPECT_EQ(z3::sat, solver.check());
  }
  solver.pop();

  solver.push();
  {
    solver.add(z3::select(store_expr, j_expr) != 7);
    EXPECT_EQ(z3::sat, solver.check());
  }
  solver.pop();
}

TEST(SmtZ3Test, Add)
{
  Z3Solver s;

  const ExprPtr<long> e0_ptr = any<long>("x");
  EXPECT_EQ(OK, s.add(0 < e0_ptr));

  const ExprPtr<sort::Int> e1_ptr = any<sort::Int>("y");
  EXPECT_EQ(OK, s.add(0 < e1_ptr));

  z3::context& context = s.context();
  z3::solver& solver = s.solver();

  EXPECT_EQ(z3::sat, solver.check());

  const z3::expr x_expr(context.bv_const("x", sizeof(long) * 8));
  const z3::expr y_expr(context.int_const("y"));

  solver.push();
  {
    solver.add(3 == x_expr);
    EXPECT_EQ(z3::sat, solver.check());
  }
  solver.pop();

  solver.push();

  {
    solver.add(0 > x_expr);
    EXPECT_EQ(z3::unsat, solver.check());
  }
  solver.pop();

  solver.push();
  {
    solver.add(3 == y_expr);
    EXPECT_EQ(z3::sat, solver.check());
  }
  solver.pop();

  solver.push();
  {
    solver.add(0 > y_expr);
    EXPECT_EQ(z3::unsat, solver.check());
  }
  solver.pop();
}

TEST(SmtZ3Test, Functional)
{
  Z3Solver solver;

  auto x = any<long>("x");
  EXPECT_EQ(OK, solver.add(0 < x));

  auto y = any<sort::Int>("y");
  EXPECT_EQ(OK, solver.add(0 < y));

  EXPECT_EQ(smt::sat, solver.check());

  solver.push();
  {
    solver.add(3 == x);
    EXPECT_EQ(smt::sat, solver.check());
  }
  solver.pop();

  EXPECT_EQ(smt::sat, solver.check());

  solver.push();

  {
    solver.add(0 > x);
    EXPECT_EQ(smt::unsat, solver.check());
  }
  solver.pop();

  EXPECT_EQ(smt::sat, solver.check());

  solver.push();
  {
    solver.add(3 == y);
    EXPECT_EQ(smt::sat, solver.check());
  }
  solver.pop();

  EXPECT_EQ(smt::sat, solver.check());

  solver.push();
  {
    solver.add(0 > y);
    EXPECT_EQ(smt::unsat, solver.check());
  }
  solver.pop();

  EXPECT_EQ(smt::sat, solver.check());
}