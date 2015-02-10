#include <smt>
#include <cstdint>

// Include <gtest/gtest.h> _after_ <smt>
#include "gtest/gtest.h"

TEST(SmtFunctionalTest, DeMorgan)
{
  const smt::Bool x = smt::any<smt::Bool>("x");
  const smt::Bool y = smt::any<smt::Bool>("y");
  const smt::Bool lhs = !(x && y);
  const smt::Bool rhs = !x || !y;

  smt::CVC4Solver cvc4_solver(smt::QF_AUFBV_LOGIC);
  cvc4_solver.add(lhs != rhs);
  EXPECT_EQ(smt::unsat, cvc4_solver.check());
}

TEST(SmtFunctionalTest, SeparateDecls)
{
  const smt::Decl<smt::Bool> x_decl("x");
  const smt::Decl<smt::Bool> y_decl("y");
  const smt::Bool x = smt::constant(x_decl);
  const smt::Bool y = smt::constant(y_decl);
  const smt::Bool lhs = !(x && y);
  const smt::Bool rhs = !x || !y;

  smt::CVC4Solver cvc4_solver;
  cvc4_solver.add(lhs != rhs);
  EXPECT_EQ(smt::unsat, cvc4_solver.check());
}

TEST(SmtFunctionalTest, BitVectors)
{
  const smt::Bv<unsigned long> x = smt::any<smt::Bv<unsigned long>>("x");
  const smt::Bv<unsigned long> y = smt::any<smt::Bv<unsigned long>>("y");
  const smt::Bv<unsigned long> z = smt::any<smt::Bv<unsigned long>>("z");
  const smt::Bool equality = (x == y) && ((x & ~y) == z);

  smt::CVC4Solver cvc4_solver;
  cvc4_solver.add(equality);

  cvc4_solver.push();
  {
    cvc4_solver.add(z != 0L);
    EXPECT_EQ(smt::unsat, cvc4_solver.check());
  }
  cvc4_solver.pop();
  cvc4_solver.push();
  {
    cvc4_solver.add(z == 0L);
    EXPECT_EQ(smt::sat, cvc4_solver.check());
  }
  cvc4_solver.pop();
}

TEST(SmtFunctionalTest, UnsafeExpr)
{
  const smt::UnsafeDecl unsafe_decl("x", smt::bv_sort(true, sizeof(int) * 8));
  const smt::SharedExpr x = smt::constant(unsafe_decl);
  const smt::SharedExpr equality = (x & smt::literal<smt::Bv<int>>(3)) != x;

  smt::CVC4Solver cvc4_solver;
  cvc4_solver.unsafe_add(equality);
  EXPECT_EQ(smt::sat, cvc4_solver.check());
}

TEST(SmtFunctionalTest, Reflection)
{
  constexpr size_t bv_int_size = sizeof(int) * 8;
  EXPECT_EQ(smt::bv_sort(true, bv_int_size), smt::literal<smt::Bv<int>>(3).sort());

  const smt::Bv<uint32_t> x = smt::any<smt::Bv<uint32_t>>("x");
  EXPECT_TRUE(x.sort().is_bv());
  EXPECT_FALSE(x.sort().is_signed());
  EXPECT_EQ(32, x.sort().bv_size());

  typedef smt::Func<smt::Int, smt::Real, smt::Bv<char>> SomeFunc;
  const SomeFunc f = smt::any<SomeFunc>("f");
  EXPECT_TRUE(f.sort().is_func());
  EXPECT_EQ(3, f.sort().sorts_size());
  EXPECT_TRUE(f.sort().sorts(0).is_int());
  EXPECT_TRUE(f.sort().sorts(1).is_real());
  EXPECT_TRUE(f.sort().sorts(2).is_bv());
  EXPECT_EQ(sizeof(char) * 8, f.sort().sorts(2).bv_size());
}

TEST(SmtFunctionalTest, Array)
{
  typedef smt::Array<smt::Int, smt::Bv<char>> IntToCharArray;
  const smt::Decl<IntToCharArray> array_decl("array");

  IntToCharArray array, new_array;
  smt::Int index;
  smt::Bv<char> value;

  array = smt::constant(array_decl);
  index = smt::any<smt::Int>("index");
  value = smt::literal<smt::Bv<char>>('p');

  new_array = smt::store(array, index, value);

  smt::CVC4Solver cvc4_solver;
  cvc4_solver.add(smt::select(new_array, index) != value);
  EXPECT_EQ(smt::unsat, cvc4_solver.check());
}

TEST(SmtFunctionalTest, BvArray)
{
  typedef smt::Array<smt::Bv<unsigned>, smt::Bv<char>> UnsignedToCharArray;
  const smt::Decl<UnsignedToCharArray> array_decl("array");

  UnsignedToCharArray array, new_array;
  smt::Bv<unsigned> index;
  smt::Bv<char> value;

  array = smt::constant(array_decl);
  index = smt::any<smt::Bv<unsigned>>("index");
  value = smt::literal<smt::Bv<char>>('p');

  new_array = smt::store(array, index, value);

  smt::CVC4Solver cvc4_solver;
  cvc4_solver.add(smt::select(new_array, index) != value);
  EXPECT_EQ(smt::unsat, cvc4_solver.check());
}

TEST(SmtFunctionalTest, Function)
{
  const smt::Decl<smt::Func<smt::Int, smt::Int>> func_decl("f");
  const smt::Int x = smt::any<smt::Int>("x");
  const smt::Bool formula =
    smt::apply(func_decl, 3) == 7 && x == smt::apply(func_decl, 3);

  smt::CVC4Solver cvc4_solver;
  cvc4_solver.add(formula && x != 7);
  EXPECT_EQ(smt::unsat, cvc4_solver.check());
}

TEST(SmtFunctionalTest, Stats)
{
  const smt::Decl<smt::Func<smt::Int, smt::Int>> func_decl("f");
  const smt::Int x = smt::any<smt::Int>("x");
  const smt::Bool formula = x < 3 && x == smt::apply(func_decl, 3);

  smt::CVC4Solver cvc4_solver;
  cvc4_solver.add(formula);

  EXPECT_EQ(2, cvc4_solver.stats().constants);
  EXPECT_EQ(1, cvc4_solver.stats().func_apps);
  EXPECT_EQ(0, cvc4_solver.stats().array_selects);
  EXPECT_EQ(0, cvc4_solver.stats().array_stores);
  EXPECT_EQ(0, cvc4_solver.stats().unary_ops);
  EXPECT_EQ(3, cvc4_solver.stats().binary_ops);
  EXPECT_EQ(0, cvc4_solver.stats().nary_ops);
  EXPECT_EQ(1, cvc4_solver.stats().equalities);
  EXPECT_EQ(0, cvc4_solver.stats().disequalities);
  EXPECT_EQ(1, cvc4_solver.stats().inequalities);
  EXPECT_EQ(0, cvc4_solver.stats().implications);
  EXPECT_EQ(1, cvc4_solver.stats().conjunctions);
  EXPECT_EQ(0, cvc4_solver.stats().disjunctions);
}
