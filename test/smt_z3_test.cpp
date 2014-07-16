#include "gtest/gtest.h"

#include "smt.h"
#include "smt_z3.h"

#include <sstream>
#include <cstdint>

using namespace smt;

TEST(SmtZ3Test, BvNoCastLiteralExpr)
{
  Z3Solver s;

  const LiteralExpr<int> e0(internal::sort<Bv<int>>(), 42);
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

  const LiteralExpr<char> e0(internal::sort<Bv<char>>(), 'A');
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

  const LiteralExpr<long> e0(internal::sort<Bv<long>>(), 42L);
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

  const LiteralExpr<bool> e0(internal::sort<Bool>(), true);
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

  const LiteralExpr<char> e0(internal::sort<Int>(), 'A');
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
  const LiteralExpr<int> e0(internal::sort<Real>(), 7);
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

  const Decl<Bv<long>> d0("x");
  Bv<long> e0_term = constant(d0);
  EXPECT_EQ(OK, static_cast<SharedExpr>(e0_term).encode(s));

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

  const Bv<int> e0_term(make_shared_expr<LiteralExpr<int>>(
    internal::sort<Bv<int>>(), 42));
  const UnaryExpr<SUB> e1(internal::sort<Bv<int>>(), e0_term);

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

  const Bv<long> e0_term(make_shared_expr<LiteralExpr<long>>(internal::sort<Bv<long>>(), 42L));
  const Bv<long> e1_term(make_shared_expr<LiteralExpr<long>>(internal::sort<Bv<long>>(), 7L));
  const BinaryExpr<ADD> e2(internal::sort<Bv<long>>(), e0_term, e1_term);

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

  const BinaryExpr<LSS> e3(internal::sort<Bool>(), e0_term, e1_term);

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

  const BinaryExpr<GTR> e4(internal::sort<Bool>(), e0_term, e1_term);

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

  const Bv<long> x = any<Bv<long>>("x");
  const Bv<long> y = any<Bv<long>>("y");
  const Bv<long> z = any<Bv<long>>("z");
  const Bv<long> w = any<Bv<long>>("w");

  Terms<Bv<long>> operand_terms(3);
  operand_terms.push_back(x);
  operand_terms.push_back(y);
  operand_terms.push_back(z);

  Bool d(distinct(std::move(operand_terms)));

  EXPECT_EQ(OK, static_cast<SharedExpr>(d).encode(s));
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

TEST(SmtZ3Test, Conjunction)
{
  Z3Solver s;

  const Bool x = any<Bool>("x");
  const Bool y = any<Bool>("y");
  const Bool z = any<Bool>("z");
  const Bool w = any<Bool>("w");

  Terms<Bool> operand_terms(3);
  operand_terms.push_back(x);
  operand_terms.push_back(y);
  operand_terms.push_back(z);

  Bool d(conjunction(std::move(operand_terms)));

  EXPECT_EQ(OK, static_cast<SharedExpr>(d).encode(s));
  std::stringstream out;
  out << s.expr();
  EXPECT_EQ("(and x y z)", out.str());

  s.add(d);

  EXPECT_EQ(sat, s.check());

  s.push();
  {
    s.add(not x);
    EXPECT_EQ(unsat, s.check());
  }
  s.pop();

  s.push();
  {
    s.add(not y);
    EXPECT_EQ(unsat, s.check());
  }
  s.pop();

  s.push();
  {
    s.add(not z);
    EXPECT_EQ(unsat, s.check());
  }
  s.pop();

  s.push();
  {
    s.add(not w);
    EXPECT_EQ(sat, s.check());
  }
  s.pop();
}

TEST(SmtZ3Test, Disjunction)
{
  Z3Solver s;

  const Bool x = any<Bool>("x");
  const Bool y = any<Bool>("y");
  const Bool z = any<Bool>("z");
  const Bool w = any<Bool>("w");

  Terms<Bool> operand_terms(3);
  operand_terms.push_back(x);
  operand_terms.push_back(y);
  operand_terms.push_back(z);

  Bool d(disjunction(std::move(operand_terms)));

  EXPECT_EQ(OK, static_cast<SharedExpr>(d).encode(s));
  std::stringstream out;
  out << s.expr();
  EXPECT_EQ("(or x y z)", out.str());

  s.add(d);

  EXPECT_EQ(sat, s.check());

  s.push();
  {
    s.add(not x and not y and not z);
    EXPECT_EQ(unsat, s.check());
  }
  s.pop();

  s.push();
  {
    s.add(not x);
    s.add(not y);
    s.add(not z);
    EXPECT_EQ(unsat, s.check());
  }
  s.pop();

  s.push();
  {
    s.add(not x);
    EXPECT_EQ(sat, s.check());
  }
  s.pop();

  s.push();
  {
    s.add(not y);
    EXPECT_EQ(sat, s.check());
  }
  s.pop();

  s.push();
  {
    s.add(not z);
    EXPECT_EQ(sat, s.check());
  }
  s.pop();

  s.push();
  {
    s.add(not w);
    EXPECT_EQ(sat, s.check());
  }
  s.pop();
}

TEST(SmtZ3Test, LogicalImplication)
{
  Z3Solver s;
  z3::expr expr(s.context());

  const Decl<Bool> d0("x");
  const Decl<Bool> d1("y");
  const Bool e0_term = constant(d0);
  const Bool e1_term = constant(d1);
  const BinaryExpr<IMP> e2(internal::sort<Bool>(), e0_term, e1_term);

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

  Decl<Func<Int, Bv<long>>> d0("f");
  const Int e1_term(make_shared_expr<LiteralExpr<int>>(
    internal::sort<Int>(), 7));
  const FuncAppExpr<1> e2(d0, { e1_term });

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

  const Decl<Func<Int, Bv<bool>, Bv<long>>> d0("f");
  const Decl<Bv<bool>> d2("x");
  const Int e1_term(make_shared_expr<LiteralExpr<int>>(internal::sort<Int>(), 7));
  const Bv<bool> e2_term = constant(d2);
  const FuncAppExpr<2> e3(d0, { e1_term, e2_term });

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

  const Int init_term(make_shared_expr<LiteralExpr<int>>(
    internal::sort<Int>(), 7));
  const ConstArrayExpr e0(internal::sort<Array<Int, Int>>(), init_term);

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
  const Decl<Array<Int, Bool>> array_decl(array_name);
  const Decl<Int> index_decl("i");
  const Array<Int, Bool> array_term = constant(array_decl);
  const Int index_term = constant(index_decl);
  const ArraySelectExpr e0(array_term, index_term);

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

  const Decl<Array<Int, Int>> array_decl("array");
  const Decl<Int> index_decl("i");
  const Array<Int, Int> array_term = constant(array_decl);
  const Int index_term = constant(index_decl);
  const Int value_term(make_shared_expr<LiteralExpr<int>>(
    internal::sort<Int>(), 7));
  const ArrayStoreExpr e0(array_term, index_term, value_term);

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

  const Bv<long> e0_term = any<Bv<long>>("x");
  s.add(0 < e0_term);

  const Int e1_term = any<Int>("y");
  s.add(0 < e1_term);

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

  Bv<int8_t> x = any<Bv<int8_t>>("x");
  solver.add('\0' < x);

  std::stringstream out;
  out << solver.expr();
  EXPECT_EQ("(bvslt #x00 x)", out.str());
}

TEST(SmtZ3Test, BinaryBvUnsignedOperatorLSS)
{
  Z3Solver solver;

  Bv<uint8_t> x = any<Bv<uint8_t>>("x");
  solver.add('\0' < x);

  std::stringstream out;
  out << solver.expr();
  EXPECT_EQ("(bvult #x00 x)", out.str());
}

TEST(SmtZ3Test, BinaryBvSignedOperatorGTR)
{
  Z3Solver solver;

  Bv<int8_t> x = any<Bv<int8_t>>("x");
  solver.add('\0' > x);

  std::stringstream out;
  out << solver.expr();
  EXPECT_EQ("(bvsgt #x00 x)", out.str());
}

TEST(SmtZ3Test, BinaryBvUnsignedOperatorGTR)
{
  Z3Solver solver;

  Bv<uint8_t> x = any<Bv<uint8_t>>("x");
  solver.add('\0' > x);

  std::stringstream out;
  out << solver.expr();
  EXPECT_EQ("(bvugt #x00 x)", out.str());
}

TEST(SmtZ3Test, BinaryBvSignedOperatorNEQ)
{
  Z3Solver solver;

  Bv<int8_t> x = any<Bv<int8_t>>("x");
  solver.add('\0' != x);

  std::stringstream out;
  out << solver.expr();
  EXPECT_EQ("(distinct #x00 x)", out.str());
}

TEST(SmtZ3Test, BinaryBvUnsignedOperatorNEQ)
{
  Z3Solver solver;

  Bv<uint8_t> x = any<Bv<uint8_t>>("x");
  solver.add('\0' != x);

  std::stringstream out;
  out << solver.expr();
  EXPECT_EQ("(distinct #x00 x)", out.str());
}

TEST(SmtZ3Test, BinaryBvSignedOperatorLEQ)
{
  Z3Solver solver;

  Bv<int8_t> x = any<Bv<int8_t>>("x");
  solver.add('\0' <= x);

  std::stringstream out;
  out << solver.expr();
  EXPECT_EQ("(bvsle #x00 x)", out.str());
}

TEST(SmtZ3Test, BinaryBvUnsignedOperatorLEQ)
{
  Z3Solver solver;

  Bv<uint8_t> x = any<Bv<uint8_t>>("x");
  solver.add('\0' <= x);

  std::stringstream out;
  out << solver.expr();
  EXPECT_EQ("(bvule #x00 x)", out.str());
}

TEST(SmtZ3Test, BinaryBvSignedOperatorGEQ)
{
  Z3Solver solver;

  Bv<int8_t> x = any<Bv<int8_t>>("x");
  solver.add('\0' >= x);

  std::stringstream out;
  out << solver.expr();
  EXPECT_EQ("(bvsge #x00 x)", out.str());
}

TEST(SmtZ3Test, BinaryBvUnsignedOperatorGEQ)
{
  Z3Solver solver;

  Bv<uint8_t> x = any<Bv<uint8_t>>("x");
  solver.add('\0' >= x);

  std::stringstream out;
  out << solver.expr();
  EXPECT_EQ("(bvuge #x00 x)", out.str());
}

TEST(SmtZ3Test, BinaryIntOperatorLSS)
{
  Z3Solver solver;

  Int x = any<Int>("x");
  solver.add(0 < x);

  std::stringstream out;
  out << solver.expr();
  EXPECT_EQ("(< 0 x)", out.str());
}

TEST(SmtZ3Test, BinaryIntOperatorGTR)
{
  Z3Solver solver;

  Int x = any<Int>("x");
  solver.add(0 > x);

  std::stringstream out;
  out << solver.expr();
  EXPECT_EQ("(> 0 x)", out.str());
}

TEST(SmtZ3Test, BinaryIntOperatorNEQ)
{
  Z3Solver solver;

  Int x = any<Int>("x");
  solver.add(0 != x);

  std::stringstream out;
  out << solver.expr();
  EXPECT_EQ("(distinct 0 x)", out.str());
}

TEST(SmtZ3Test, BinaryIntOperatorLEQ)
{
  Z3Solver solver;

  Int x = any<Int>("x");
  solver.add(0 <= x);

  std::stringstream out;
  out << solver.expr();
  EXPECT_EQ("(<= 0 x)", out.str());
}

TEST(SmtZ3Test, BinaryIntOperatorGEQ)
{
  Z3Solver solver;

  Int x = any<Int>("x");
  solver.add(0 >= x);

  std::stringstream out;
  out << solver.expr();
  EXPECT_EQ("(>= 0 x)", out.str());
}

TEST(SmtZ3Test, AutoConfig)
{
  Z3Solver solver;

  auto x = any<Bv<long>>("x");
  solver.add(0 < x);

  auto y = any<Int>("y");
  solver.add(0 < y);

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

TEST(SmtZ3Test, QF_BV)
{
  Z3Solver solver(QF_BV_LOGIC);

  auto x = any<Bv<long>>("x");
  solver.add(0 < x);

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
}

TEST(SmtZ3Test, QF_IDL)
{
  Z3Solver solver(QF_IDL_LOGIC);

  auto y = any<Int>("y");
  solver.add(0 < y);

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
  s.add(literal<Bool>(false));
  EXPECT_EQ(unsat, s.check());
  s.reset();
  EXPECT_EQ(sat, s.check());
}

TEST(SmtZ3Test, UnsafeAdd)
{
  Z3Solver s;

  const Sort& bv_sort = internal::sort<Bv<int64_t>>();
  const Sort& func_sort = internal::sort<Func<Bv<int64_t>, Bv<int64_t>>>();
  const UnsafeDecl const_decl("x", bv_sort);
  const UnsafeDecl func_decl("f", func_sort);
  const SharedExpr seven_term(literal(bv_sort, 7));
  const SharedExpr x_term(constant(const_decl));
  const SharedExpr app_term(apply(func_decl, seven_term));

  SharedExprs terms;
  terms.push_back(seven_term);
  terms.push_back(x_term);
  terms.push_back(app_term);

  const SharedExpr distinct_term(distinct(std::move(terms)));

  const Sort& array_sort = internal::sort<Array<Bv<uint32_t>, Bv<int64_t>>>();
  const Sort& index_sort = internal::sort<Bv<uint32_t>>();
  const UnsafeDecl array_decl("array", array_sort);
  const UnsafeDecl index_decl("index", index_sort);
  const SharedExpr array_term(constant(array_decl));
  const SharedExpr index_term(constant(index_decl));
  const SharedExpr store_term(store(array_term, index_term, app_term));
  const SharedExpr select_term(select(store_term, index_term));

  const SharedExpr eq_term(select_term == x_term);
  const SharedExpr and_term(eq_term && distinct_term);

  s.push();
  {
    s.unsafe_add(and_term);
    EXPECT_EQ(unsat, s.check());

    std::stringstream out;
    out << s.expr();
    EXPECT_EQ("(let ((a!1 "
                 "(= (select (store array index (f #x0000000000000007)) index) x)))\n  "
             "(and a!1 (distinct #x0000000000000007 x (f #x0000000000000007))))", out.str());
  }
  s.pop();

  s.push();
  {
    s.unsafe_add(seven_term != 7);
    EXPECT_EQ(unsat, s.check());
  }
  s.pop();

  s.push();
  {
    s.unsafe_add(7 == seven_term);
    EXPECT_EQ(sat, s.check());
  }
  s.pop();

  s.push();
  {
    s.unsafe_add(x_term == x_term + 1);
    EXPECT_EQ(unsat, s.check());
  }
  s.pop();

  s.push();
  {
    s.unsafe_add(x_term + 1 == x_term);
    EXPECT_EQ(unsat, s.check());
  }
  s.pop();
}

TEST(SmtZ3Test, BvSignExtend)
{
  Z3Solver s;

  Bv<int8_t> x = any<Bv<int8_t>>("x");
  Bv<int16_t> y = any<Bv<int16_t>>("y");
  Bv<uint16_t> z = any<Bv<uint16_t>>("z");

  s.push();
  {
    s.add(x == 0x07);
    s.add(y == bv_cast<int16_t>(x));

    EXPECT_EQ(sat, s.check());

    std::stringstream out;
    out << s.solver().get_model();
    EXPECT_EQ("(define-fun y () (_ BitVec 16)\n  #x0007)\n(define-fun x () (_ BitVec 8)\n  #x07)", out.str());
  }
  s.pop();

  s.push();
  {
    s.add(x == 0x87);
    s.add(y == bv_cast<int16_t>(x));

    EXPECT_EQ(sat, s.check());

    std::stringstream out;
    out << s.solver().get_model();
    EXPECT_EQ("(define-fun y () (_ BitVec 16)\n  #xff87)\n(define-fun x () (_ BitVec 8)\n  #x87)", out.str());
  }
  s.pop();

  s.push();
  {
    s.add(x == 0x87);

    // we cast from a signed to an unsigned integer so sign extension is required,
    // see inline comments in bv_cast<T>(const Bv<S>&) about C++ specification
    s.add(z == bv_cast<uint16_t>(x));

    EXPECT_EQ(sat, s.check());

    std::stringstream out;
    out << s.solver().get_model();
    EXPECT_EQ("(define-fun z () (_ BitVec 16)\n  #xff87)\n(define-fun x () (_ BitVec 8)\n  #x87)", out.str());
  }
  s.pop();
}

TEST(SmtZ3Test, BvZeroExtend)
{
  Z3Solver s;

  Bv<uint8_t> x = any<Bv<uint8_t>>("x");
  Bv<int16_t> y = any<Bv<int16_t>>("y");
  Bv<uint16_t> z = any<Bv<uint16_t>>("z");

  s.push();
  {
    s.add(x == 0x07);
    s.add(y == bv_cast<int16_t>(x));

    EXPECT_EQ(sat, s.check());

    std::stringstream out;
    out << s.solver().get_model();
    EXPECT_EQ("(define-fun y () (_ BitVec 16)\n  #x0007)\n(define-fun x () (_ BitVec 8)\n  #x07)", out.str());
  }
  s.pop();

  s.push();
  {
    s.add(x == 0x87);

    // we cast from an unsigned to a signed integer so extend by zeros.
    s.add(y == bv_cast<int16_t>(x));

    EXPECT_EQ(sat, s.check());

    std::stringstream out;
    out << s.solver().get_model();
    EXPECT_EQ("(define-fun y () (_ BitVec 16)\n  #x0087)\n(define-fun x () (_ BitVec 8)\n  #x87)", out.str());
  }
  s.pop();

  s.push();
  {
    s.add(x == 0x87);
    s.add(z == bv_cast<uint16_t>(x));

    EXPECT_EQ(sat, s.check());

    std::stringstream out;
    out << s.solver().get_model();
    EXPECT_EQ("(define-fun z () (_ BitVec 16)\n  #x0087)\n(define-fun x () (_ BitVec 8)\n  #x87)", out.str());
  }
  s.pop();
}

TEST(SmtZ3Test, BvTruncate)
{
  Z3Solver s;

  Bv<int16_t> x = any<Bv<int16_t>>("x");
  Bv<int8_t> y = any<Bv<int8_t>>("y");
  Bv<uint8_t> z = any<Bv<uint8_t>>("z");

  s.push();
  {
    s.add(x == 0xbeef);
    s.add(y == bv_cast<int8_t>(x));

    EXPECT_EQ(sat, s.check());

    std::stringstream out;
    out << s.solver().get_model();
    EXPECT_EQ("(define-fun y () (_ BitVec 8)\n  #xef)\n(define-fun x () (_ BitVec 16)\n  #xbeef)", out.str());
  }
  s.pop();

  s.push();
  {
    s.add(x == 0xbeef);
    s.add(z == bv_cast<uint8_t>(x));

    EXPECT_EQ(sat, s.check());

    std::stringstream out;
    out << s.solver().get_model();
    EXPECT_EQ("(define-fun z () (_ BitVec 8)\n  #xef)\n(define-fun x () (_ BitVec 16)\n  #xbeef)", out.str());
  }
  s.pop();
}

TEST(SmtZ3Test, CheckAssumptions)
{
  Z3Solver s;
  std::pair<CheckResult, Bools::SizeType> r;

  // ignore
  Bools unsat_core;
  unsat_core.resize(0);

  Bool a;
  Bool b;
  Bool c;

  Int x = any<Int>("x");

  {
    a = x < 7;
    b = !a;

    Bools assumptions;
    assumptions.push_back(a);
    assumptions.push_back(b);

    r = s.check_assumptions(assumptions, unsat_core);
    EXPECT_EQ(unsat, r.first);

    assumptions.pop_back();
    assumptions.push_back(a);
    r = s.check_assumptions(assumptions, unsat_core);
    EXPECT_EQ(sat, r.first);
  }

  s.reset();

  {
    a = x < 7;
    b = !a;

    Bools assumptions;
    assumptions.push_back(b);

    s.add(a);
    r = s.check_assumptions(assumptions, unsat_core);
    EXPECT_EQ(unsat, r.first);

    assumptions.pop_back();
    assumptions.push_back(a);
    r = s.check_assumptions(assumptions, unsat_core);
    EXPECT_EQ(sat, r.first);
  }
}

TEST(SmtZ3Test, UnsatCore)
{
  Z3Solver s;
  std::pair<CheckResult, Bools::SizeType> r;

  Bool a = any<Bool>("a");
  Bool b = any<Bool>("b");
  Bool c = any<Bool>("c");
  Bool not_b = not b;
  Bool d = any<Bool>("d");

  Int x = any<Int>("x");
  Int y = any<Int>("y");
  Int z = any<Int>("z");

  Bools unsat_core;

  {
    Bools assumptions;
    assumptions.push_back(a);
    assumptions.push_back(b);
    assumptions.push_back(not_b);
    assumptions.push_back(d);

    unsat_core.resize(7);
    r = s.check_assumptions(assumptions, unsat_core);

    EXPECT_EQ(unsat, r.first);
    EXPECT_EQ(2, r.second);

    EXPECT_EQ(not_b.addr(), unsat_core.at(unsat_core.size() - 1).addr());
    EXPECT_EQ(b.addr(), unsat_core.at(unsat_core.size() - 2).addr());

    // singleton
    unsat_core.resize(1);
    r = s.check_assumptions(assumptions, unsat_core);
    EXPECT_EQ(unsat, r.first);
    EXPECT_EQ(1, r.second);
    EXPECT_EQ(not_b.addr(), unsat_core.back().addr());
  }

  s.reset();

  {
    // assertion will contradict assumption
    s.add(b);

    Bools assumptions;
    assumptions.push_back(a);
    assumptions.push_back(not_b);
    assumptions.push_back(c);
    assumptions.push_back(d);

    unsat_core.resize(7);
    r = s.check_assumptions(assumptions, unsat_core);

    EXPECT_EQ(unsat, r.first);
    EXPECT_EQ(1, r.second);

    EXPECT_EQ(not_b.addr(), unsat_core.back().addr());

    // singleton
    unsat_core.resize(1);
    r = s.check_assumptions(assumptions, unsat_core);
    EXPECT_EQ(unsat, r.first);
    EXPECT_EQ(1, r.second);
    EXPECT_EQ(not_b.addr(), unsat_core.back().addr());
  }

  s.reset();

  {
    // duplicate in assumption
    Bools assumptions;
    assumptions.push_back(a);
    assumptions.push_back(b);
    assumptions.push_back(not_b);
    assumptions.push_back(b);
    assumptions.push_back(d);

    unsat_core.resize(7);
    r = s.check_assumptions(assumptions, unsat_core);

    EXPECT_EQ(unsat, r.first);
    EXPECT_EQ(2, r.second);

    EXPECT_EQ(not_b.addr(), unsat_core.at(unsat_core.size() - 1).addr());
    EXPECT_EQ(b.addr(), unsat_core.at(unsat_core.size() - 2).addr());

    // singleton
    unsat_core.resize(1);
    r = s.check_assumptions(assumptions, unsat_core);
    EXPECT_EQ(unsat, r.first);
    EXPECT_EQ(1, r.second);
    EXPECT_EQ(not_b.addr(), unsat_core.back().addr());
  }

  s.reset();

  {
    s.add(smt::implies(a, x < 5));
    s.add(smt::implies(b, y < x));
    s.add(smt::implies(c, z < 2));
    s.add(smt::implies(d, 5 < y));

    Bools assumptions;
    assumptions.push_back(a);
    assumptions.push_back(b);
    assumptions.push_back(c);
    assumptions.push_back(d);

    unsat_core.resize(7);
    r = s.check_assumptions(assumptions, unsat_core);

    EXPECT_EQ(smt::unsat, r.first);

    unsat_core.resize(7);
    r = s.check_assumptions(assumptions, unsat_core);

    EXPECT_EQ(3, r.second);
    EXPECT_EQ(d.addr(), unsat_core.at(unsat_core.size() - 1).addr());
    EXPECT_EQ(b.addr(), unsat_core.at(unsat_core.size() - 2).addr());
    EXPECT_EQ(a.addr(), unsat_core.at(unsat_core.size() - 3).addr());

    // singleton
    unsat_core.resize(1);
    r = s.check_assumptions(assumptions, unsat_core);
    EXPECT_EQ(unsat, r.first);
    EXPECT_EQ(1, r.second);
    EXPECT_EQ(d.addr(), unsat_core.back().addr());
  }

  s.reset();

  {
    a = x < 5;
    b = y < x;
    c = z < 2;
    d = 5 < y;

    Bools assumptions;
    assumptions.push_back(a);
    assumptions.push_back(b);
    assumptions.push_back(c);
    assumptions.push_back(d);

    unsat_core.resize(7);
    r = s.check_assumptions(assumptions, unsat_core);

    EXPECT_EQ(smt::unsat, r.first);

    unsat_core.resize(7);
    r = s.check_assumptions(assumptions, unsat_core);

    EXPECT_EQ(3, r.second);
    EXPECT_EQ(d.addr(), unsat_core.at(unsat_core.size() - 1).addr());
    EXPECT_EQ(b.addr(), unsat_core.at(unsat_core.size() - 2).addr());
    EXPECT_EQ(a.addr(), unsat_core.at(unsat_core.size() - 3).addr());

    // singleton
    unsat_core.resize(1);
    r = s.check_assumptions(assumptions, unsat_core);
    EXPECT_EQ(unsat, r.first);
    EXPECT_EQ(1, r.second);
    EXPECT_EQ(d.addr(), unsat_core.back().addr());
  }

  s.reset();

  {
    a = x < 7;
    b = !(x < 7);
    c = !(x < 4);

    Bools assumptions;
    assumptions.push_back(b);
    assumptions.push_back(c);

    s.add(a);

    unsat_core.resize(7);
    r = s.check_assumptions(assumptions, unsat_core);

    EXPECT_EQ(unsat, r.first);
    EXPECT_EQ(1, r.second);
    EXPECT_EQ(b.addr(), unsat_core.back().addr());

    // singleton
    unsat_core.resize(1);
    r = s.check_assumptions(assumptions, unsat_core);

    EXPECT_EQ(unsat, r.first);
    EXPECT_EQ(1, r.second);
    EXPECT_EQ(b.addr(), unsat_core.back().addr());
  }

  Bv<char> letter = any<Bv<char>>("letter");

  s.reset();

  {
    a = letter <= 'A';
    b = 'Z' <= letter;
    c = 'Z' <= letter;
    Bools assumptions;
    assumptions.push_back(a);
    assumptions.push_back(b);
    assumptions.push_back(c);

    unsat_core.resize(7);
    r = s.check_assumptions(assumptions, unsat_core);

    EXPECT_EQ(unsat, r.first);
    EXPECT_EQ(2, r.second);
    EXPECT_EQ(b.addr(), unsat_core.back().addr());
  }

  s.reset();

  {
    a = letter <= 'A';
    b = 'Z' <= letter;
    c = 'Z' <= letter;
    Bools assumptions;
    assumptions.push_back(a);
    assumptions.push_back(b);
    assumptions.push_back(c);

    unsat_core.resize(2);
    r = s.check_assumptions(assumptions, unsat_core);

    EXPECT_EQ(unsat, r.first);
    EXPECT_EQ(2, r.second);
    EXPECT_EQ(b.addr(), unsat_core.back().addr());
  }

  s.reset();

  {
    Bool d;

    a = letter <= 'A';
    b = letter <= 'Z';
    c = (letter + '\1') > 'Z';
    d = (letter + '\2') > 'Z';

    Bools assumptions;
    assumptions.push_back(a);
    assumptions.push_back(b);
    assumptions.push_back(c);
    assumptions.push_back(d);

    unsat_core.resize(7);
    r = s.check_assumptions(assumptions, unsat_core);

    // ideally the solver would only return an unsat core
    // of size two such that unsat_core.back() is "c" as
    // in MathSAT5, for example.
    EXPECT_EQ(unsat, r.first);
    EXPECT_EQ(4, r.second);
    EXPECT_EQ(d.addr(), unsat_core.back().addr());
  }

  s.reset();

  {
    Bool d;

    a = letter <= 'A';
    b = letter <= 'Z';
    c = (letter + '\1') > 'Z';
    d = (letter + '\1') > 'Z';

    Bools assumptions;
    assumptions.push_back(a);
    assumptions.push_back(b);
    assumptions.push_back(c);
    assumptions.push_back(d);

    unsat_core.resize(7);
    r = s.check_assumptions(assumptions, unsat_core);

    EXPECT_EQ(unsat, r.first);
    EXPECT_EQ(3, r.second);
    EXPECT_EQ(c.addr(), unsat_core.back().addr());
  }

  s.reset();

  {
    Bool d, e;

    a = letter <= 'A';
    b = letter <= 'Z';
    c = (letter + '\1') > 'Z';
    d = (letter + '\2') > 'Z';
    e = (letter + '\2') > 'Z';

    Bools assumptions;
    assumptions.push_back(a);
    assumptions.push_back(b);
    assumptions.push_back(c);
    assumptions.push_back(d);
    assumptions.push_back(e);

    unsat_core.resize(7);
    r = s.check_assumptions(assumptions, unsat_core);

    EXPECT_EQ(unsat, r.first);
    EXPECT_EQ(4, r.second);
    EXPECT_EQ(e.addr(), unsat_core.back().addr());
  }

  s.reset();

  {
    Bool d, e;

    a = !('A' < letter);
    b = letter < 'Z';
    c = (letter + '\1') < 'Z';
    d = (letter + '\2') > 'Z';
    e = (letter + '\2') > 'Z';

    Bools assumptions;
    assumptions.push_back(a);
    assumptions.push_back(b);
    assumptions.push_back(c);
    assumptions.push_back(d);
    assumptions.push_back(e);

    unsat_core.resize(7);
    r = s.check_assumptions(assumptions, unsat_core);

    /// unsat_core.back() should be ideally "d"
    EXPECT_EQ(unsat, r.first);
    EXPECT_EQ(3, r.second);
    EXPECT_EQ(e.addr(), unsat_core.back().addr());
  }
}

TEST(SmtZ3Test, LogicalShifts)
{
  Z3Solver s;

  Bv<unsigned> x = any<Bv<unsigned>>("x");
  Bv<unsigned> one = literal<Bv<unsigned>>(1);
  Bv<unsigned> two = literal<Bv<unsigned>>(2);

  s.push();
  {
    s.add(two * x != (x << one));
    EXPECT_EQ(unsat, s.check());
  }
  s.pop();

  s.push();
  {
    s.add(two * x == (x << one));
    EXPECT_EQ(sat, s.check());
  }
  s.pop();

  s.push();
  {
    s.add(x != ((x << one) >> one));
    EXPECT_EQ(sat, s.check());
  }
  s.pop();

  s.push();
  {
    s.add(x == ((x << one) >> one));
    EXPECT_EQ(sat, s.check());
  }
  s.pop();

  s.push();
  {
    s.add(one != (two >> one));
    EXPECT_EQ(unsat, s.check());
  }
  s.pop();

  s.push();
  {
    s.add(one == (two >> one));
    EXPECT_EQ(sat, s.check());
  }
  s.pop();
}
