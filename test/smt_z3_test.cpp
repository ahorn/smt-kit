#include "gtest/gtest.h"

#include "smt.h"
#include "smt_z3.h"

#include <sstream>
#include <cstdint>

using namespace smt;

TEST(SmtZ3Test, BvNoCastLiteralExpr)
{
  Z3Solver s;

  const LiteralExpr<int> e0(42);
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

TEST(SmtZ3Test, BvCastLiteralExpr)
{
  Z3Solver s;

  const LiteralExpr<char> e0('A');
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

TEST(SmtZ3Test, Bv64CastLiteralExpr)
{
  Z3Solver s;

  const LiteralExpr<long> e0(42L);
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

TEST(SmtZ3Test, BoolLiteralExpr)
{
  Z3Solver s;

  const LiteralExpr<sort::Bool, bool> e0(true);
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

TEST(SmtZ3Test, IntLiteralExpr)
{
  Z3Solver s;

  const LiteralExpr<sort::Int, char> e0('A');
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

TEST(SmtZ3Test, RealLiteralExpr)
{
  Z3Solver s;

  // note that float and double are unsupported
  const LiteralExpr<sort::Real, int> e0(7);
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

TEST(SmtZ3Test, Decl)
{
  Z3Solver s;
  constexpr size_t bv_size = sizeof(long) * 8;

  const Decl<long> d0("x");
  ExprPtr<long> e0_ptr = constant(d0);
  EXPECT_EQ(OK, e0_ptr->encode(s));

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

TEST(SmtZ3Test, UnaryExpr)
{
  Z3Solver s;

  const ExprPtr<int> e0_ptr(new LiteralExpr<int>(42));
  const UnaryExpr<SUB, int> e1(e0_ptr);

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

TEST(SmtZ3Test, BinaryExpr)
{
  Z3Solver s;
  z3::expr expr(s.context());

  const ExprPtr<long> e0_ptr(new LiteralExpr<long>(42L));
  const ExprPtr<long> e1_ptr(new LiteralExpr<long>(7L));
  const BinaryExpr<ADD, long> e2(e0_ptr, e1_ptr);

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

  const BinaryExpr<LSS, long, sort::Bool> e3(e0_ptr, e1_ptr);

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

  const BinaryExpr<GTR, long, sort::Bool> e4(e0_ptr, e1_ptr);

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

TEST(SmtZ3Test, Distinct)
{
  Z3Solver s;

  const ExprPtr<long> x = any<long>("x");
  const ExprPtr<long> y = any<long>("y");
  const ExprPtr<long> z = any<long>("z");
  const ExprPtr<long> w = any<long>("w");

  ExprPtrs<long> operand_ptrs(3);
  operand_ptrs.push_back(x);
  operand_ptrs.push_back(y);
  operand_ptrs.push_back(z);

  ExprPtr<sort::Bool> d(distinct(std::move(operand_ptrs)));

  EXPECT_EQ(OK, d->encode(s));
  std::stringstream out;
  out << s.expr();
  EXPECT_EQ("(distinct x y z)", out.str());

  s.add(d);

  EXPECT_EQ(sat, s.check());

  s.push();
  {
    s.add(x == y);
    EXPECT_EQ(unsat, s.check());
  }
  s.pop();

  s.push();
  {
    s.add(x == z);
    EXPECT_EQ(unsat, s.check());
  }
  s.pop();

  s.push();
  {
    s.add(y == z);
    EXPECT_EQ(unsat, s.check());
  }
  s.pop();

  s.push();
  {
    s.add(x == w);
    EXPECT_EQ(sat, s.check());
  }
  s.pop();

  s.push();
  {
    s.add(y == w);
    EXPECT_EQ(sat, s.check());
  }
  s.pop();

  s.push();
  {
    s.add(z == w);
    EXPECT_EQ(sat, s.check());
  }
  s.pop();
}

TEST(SmtZ3Test, LogicalImplication)
{
  Z3Solver s;
  z3::expr expr(s.context());

  const Decl<sort::Bool> d0("x");
  const Decl<sort::Bool> d1("y");
  const ExprPtr<sort::Bool> e0_ptr = constant(d0);
  const ExprPtr<sort::Bool> e1_ptr = constant(d1);
  const BinaryExpr<IMP, sort::Bool> e2(e0_ptr, e1_ptr);

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

TEST(SmtZ3Test, UnaryFuncAppExpr)
{
  Z3Solver s;

  Decl<sort::Func<sort::Int, long>> d0("f");
  const ExprPtr<sort::Int> e1_ptr(new LiteralExpr<sort::Int, int>(7));
  const FuncAppExpr<sort::Int, long> e2(d0, std::make_tuple(e1_ptr));

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

  const Decl<sort::Func<sort::Int, bool, long>> d0("f");
  const Decl<bool> d2("x");
  const ExprPtr<sort::Int> e1_ptr(new LiteralExpr<sort::Int, int>(7));
  const ExprPtr<bool> e2_ptr = constant(d2);
  const FuncAppExpr<sort::Int, bool, long> e3(d0, std::make_tuple(e1_ptr, e2_ptr));

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

  const ExprPtr<sort::Int> init_ptr(new LiteralExpr<sort::Int, int>(7));
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

  constexpr char const array_name[] = "array";
  const Decl<sort::Array<sort::Int, sort::Bool>> array_decl(array_name);
  const Decl<sort::Int> index_decl("i");
  const ExprPtr<sort::Array<sort::Int, sort::Bool>> array_ptr = constant(array_decl);
  const ExprPtr<sort::Int> index_ptr = constant(index_decl);
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
  const z3::expr array_expr = context.constant(array_name, array_sort);
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

  const Decl<sort::Array<sort::Int, sort::Int>> array_decl("array");
  const Decl<sort::Int> index_decl("i");
  const ExprPtr<sort::Array<sort::Int, sort::Int>> array_ptr = constant(array_decl);
  const ExprPtr<sort::Int> index_ptr = constant(index_decl);
  const ExprPtr<sort::Int> value_ptr(new LiteralExpr<sort::Int, int>(7));
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

TEST(SmtZ3Test, BinaryBvSignedOperatorLSS)
{
  Z3Solver solver;

  ExprPtr<int8_t> x = any<int8_t>("x");
  EXPECT_EQ(OK, solver.add('\0' < x));

  std::stringstream out;
  out << solver.expr();
  EXPECT_EQ("(bvslt #x00 x)", out.str());
}

TEST(SmtZ3Test, BinaryBvUnsignedOperatorLSS)
{
  Z3Solver solver;

  ExprPtr<uint8_t> x = any<uint8_t>("x");
  EXPECT_EQ(OK, solver.add('\0' < x));

  std::stringstream out;
  out << solver.expr();
  EXPECT_EQ("(bvult #x00 x)", out.str());
}

TEST(SmtZ3Test, BinaryBvSignedOperatorGTR)
{
  Z3Solver solver;

  ExprPtr<int8_t> x = any<int8_t>("x");
  EXPECT_EQ(OK, solver.add('\0' > x));

  std::stringstream out;
  out << solver.expr();
  EXPECT_EQ("(bvsgt #x00 x)", out.str());
}

TEST(SmtZ3Test, BinaryBvUnsignedOperatorGTR)
{
  Z3Solver solver;

  ExprPtr<uint8_t> x = any<uint8_t>("x");
  EXPECT_EQ(OK, solver.add('\0' > x));

  std::stringstream out;
  out << solver.expr();
  EXPECT_EQ("(bvugt #x00 x)", out.str());
}

TEST(SmtZ3Test, BinaryBvSignedOperatorNEQ)
{
  Z3Solver solver;

  ExprPtr<int8_t> x = any<int8_t>("x");
  EXPECT_EQ(OK, solver.add('\0' != x));

  std::stringstream out;
  out << solver.expr();
  EXPECT_EQ("(distinct #x00 x)", out.str());
}

TEST(SmtZ3Test, BinaryBvUnsignedOperatorNEQ)
{
  Z3Solver solver;

  ExprPtr<uint8_t> x = any<uint8_t>("x");
  EXPECT_EQ(OK, solver.add('\0' != x));

  std::stringstream out;
  out << solver.expr();
  EXPECT_EQ("(distinct #x00 x)", out.str());
}

TEST(SmtZ3Test, BinaryBvSignedOperatorLEQ)
{
  Z3Solver solver;

  ExprPtr<int8_t> x = any<int8_t>("x");
  EXPECT_EQ(OK, solver.add('\0' <= x));

  std::stringstream out;
  out << solver.expr();
  EXPECT_EQ("(bvsle #x00 x)", out.str());
}

TEST(SmtZ3Test, BinaryBvUnsignedOperatorLEQ)
{
  Z3Solver solver;

  ExprPtr<uint8_t> x = any<uint8_t>("x");
  EXPECT_EQ(OK, solver.add('\0' <= x));

  std::stringstream out;
  out << solver.expr();
  EXPECT_EQ("(bvule #x00 x)", out.str());
}

TEST(SmtZ3Test, BinaryBvSignedOperatorGEQ)
{
  Z3Solver solver;

  ExprPtr<int8_t> x = any<int8_t>("x");
  EXPECT_EQ(OK, solver.add('\0' >= x));

  std::stringstream out;
  out << solver.expr();
  EXPECT_EQ("(bvsge #x00 x)", out.str());
}

TEST(SmtZ3Test, BinaryBvUnsignedOperatorGEQ)
{
  Z3Solver solver;

  ExprPtr<uint8_t> x = any<uint8_t>("x");
  EXPECT_EQ(OK, solver.add('\0' >= x));

  std::stringstream out;
  out << solver.expr();
  EXPECT_EQ("(bvuge #x00 x)", out.str());
}

TEST(SmtZ3Test, BinaryIntOperatorLSS)
{
  Z3Solver solver;

  ExprPtr<sort::Int> x = any<sort::Int>("x");
  EXPECT_EQ(OK, solver.add(0 < x));

  std::stringstream out;
  out << solver.expr();
  EXPECT_EQ("(< 0 x)", out.str());
}

TEST(SmtZ3Test, BinaryIntOperatorGTR)
{
  Z3Solver solver;

  ExprPtr<sort::Int> x = any<sort::Int>("x");
  EXPECT_EQ(OK, solver.add(0 > x));

  std::stringstream out;
  out << solver.expr();
  EXPECT_EQ("(> 0 x)", out.str());
}

TEST(SmtZ3Test, BinaryIntOperatorNEQ)
{
  Z3Solver solver;

  ExprPtr<sort::Int> x = any<sort::Int>("x");
  EXPECT_EQ(OK, solver.add(0 != x));

  std::stringstream out;
  out << solver.expr();
  EXPECT_EQ("(distinct 0 x)", out.str());
}

TEST(SmtZ3Test, BinaryIntOperatorLEQ)
{
  Z3Solver solver;

  ExprPtr<sort::Int> x = any<sort::Int>("x");
  EXPECT_EQ(OK, solver.add(0 <= x));

  std::stringstream out;
  out << solver.expr();
  EXPECT_EQ("(<= 0 x)", out.str());
}

TEST(SmtZ3Test, BinaryIntOperatorGEQ)
{
  Z3Solver solver;

  ExprPtr<sort::Int> x = any<sort::Int>("x");
  EXPECT_EQ(OK, solver.add(0 >= x));

  std::stringstream out;
  out << solver.expr();
  EXPECT_EQ("(>= 0 x)", out.str());
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

TEST(SmtZ3Test, Reset)
{
  Z3Solver s;

  EXPECT_EQ(sat, s.check());
  s.add(literal<sort::Bool>(false));
  EXPECT_EQ(unsat, s.check());
  s.reset();
  EXPECT_EQ(sat, s.check());
}

TEST(SmtZ3Test, UnsafeAdd)
{
  Z3Solver s;

  const Sort& bv_sort = internal::sort<int64_t>();
  const Sort& func_sort = internal::sort<sort::Func<int64_t, int64_t>>();
  const UnsafeDecl const_decl("x", bv_sort);
  const UnsafeDecl func_decl("f", func_sort);
  const UnsafeExprPtr seven_ptr(literal(bv_sort, 7));
  const UnsafeExprPtr x_ptr(constant(const_decl));
  const UnsafeExprPtr app_ptr(apply(func_decl, seven_ptr));

  UnsafeExprPtrs ptrs;
  ptrs.push_back(seven_ptr);
  ptrs.push_back(x_ptr);
  ptrs.push_back(app_ptr);

  const UnsafeExprPtr distinct_ptr(distinct(std::move(ptrs)));

  const Sort& array_sort = internal::sort<sort::Array<uint32_t, int64_t>>();
  const Sort& index_sort = internal::sort<uint32_t>();
  const UnsafeDecl array_decl("array", array_sort);
  const UnsafeDecl index_decl("index", index_sort);
  const UnsafeExprPtr array_ptr(constant(array_decl));
  const UnsafeExprPtr index_ptr(constant(index_decl));
  const UnsafeExprPtr store_ptr(store(array_ptr, index_ptr, app_ptr));
  const UnsafeExprPtr select_ptr(select(store_ptr, index_ptr));

  const UnsafeExprPtr eq_ptr(select_ptr == x_ptr);
  const UnsafeExprPtr and_ptr(eq_ptr && distinct_ptr);

  s.unsafe_add(and_ptr);
  EXPECT_EQ(unsat, s.check());

  std::stringstream out;
  out << s.expr();
  EXPECT_EQ("(let ((a!1 "
               "(= (select (store array index (f #x0000000000000007)) index) x)))\n  "
           "(and a!1 (distinct #x0000000000000007 x (f #x0000000000000007))))", out.str());
}
