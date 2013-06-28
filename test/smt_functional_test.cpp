#include <smt>
#include <cstdint>

// Include <gtest/gtest.h> _after_ <smt>
#include "gtest/gtest.h"

// Only access global solver through a function that has a static local object!
smt::Solver& global_solver()
{
  static smt::MsatSolver s_msat_solver;
  return s_msat_solver;
}

TEST(SmtFunctionalTest, Reset)
{
  global_solver().reset();
}

TEST(SmtFunctionalTest, DeMorgan)
{
  const smt::Bool x = smt::any<smt::Bool>("x");
  const smt::Bool y = smt::any<smt::Bool>("y");
  const smt::Bool lhs = !(x && y);
  const smt::Bool rhs = !x || !y;

  smt::Z3Solver z3_solver;
  z3_solver.add(lhs != rhs);
  EXPECT_EQ(smt::unsat, z3_solver.check());

  // Should always explicitly specify the logic!
  smt::MsatSolver msat_solver(smt::QF_BV_LOGIC);
  msat_solver.add(lhs != rhs);
  EXPECT_EQ(smt::unsat, msat_solver.check());

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

  smt::Z3Solver z3_solver;
  z3_solver.add(lhs != rhs);
  EXPECT_EQ(smt::unsat, z3_solver.check());

  smt::MsatSolver msat_solver;
  msat_solver.add(lhs != rhs);
  EXPECT_EQ(smt::unsat, msat_solver.check());

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

  smt::Z3Solver z3_solver;
  z3_solver.add(equality);

  z3_solver.push();
  {
    z3_solver.add(z != 0L);
    EXPECT_EQ(smt::unsat, z3_solver.check());
  }
  z3_solver.pop();
  z3_solver.push();
  {
    z3_solver.add(z == 0L);
    EXPECT_EQ(smt::sat, z3_solver.check());
  }
  z3_solver.pop();

  smt::MsatSolver msat_solver;
  msat_solver.add(equality);

  msat_solver.push();
  {
    msat_solver.add(z != 0L);
    EXPECT_EQ(smt::unsat, msat_solver.check());
  }
  msat_solver.pop();
  msat_solver.push();
  {
    msat_solver.add(z == 0L);
    EXPECT_EQ(smt::sat, msat_solver.check());
  }
  msat_solver.pop();

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
  const smt::UnsafeTerm x = smt::constant(unsafe_decl);
  const smt::UnsafeTerm equality = (x & smt::literal<smt::Bv<int>>(3)) != x;

  smt::Z3Solver z3_solver;
  z3_solver.unsafe_add(equality);
  EXPECT_EQ(smt::sat, z3_solver.check());

  smt::MsatSolver msat_solver;
  msat_solver.unsafe_add(equality);
  EXPECT_EQ(smt::sat, msat_solver.check());

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

  smt::Z3Solver z3_solver;
  z3_solver.add(smt::select(new_array, index) != value);
  EXPECT_EQ(smt::unsat, z3_solver.check());

  smt::MsatSolver msat_solver;
  msat_solver.add(smt::select(new_array, index) != value);
  EXPECT_EQ(smt::unsat, msat_solver.check());

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

  smt::Z3Solver z3_solver;
  z3_solver.add(formula && x != smt::literal<smt::Int>(7));
  EXPECT_EQ(smt::unsat, z3_solver.check());

  smt::MsatSolver msat_solver;
  msat_solver.add(formula && x != 7);
  EXPECT_EQ(smt::unsat, msat_solver.check());

  smt::CVC4Solver cvc4_solver;
  cvc4_solver.add(formula && x != 7);
  EXPECT_EQ(smt::unsat, cvc4_solver.check());
}

TEST(SmtFunctionalTest, Stats)
{
  const smt::Decl<smt::Func<smt::Int, smt::Int>> func_decl("f");
  const smt::Int x = smt::any<smt::Int>("x");
  const smt::Bool formula = x < 3 && x == smt::apply(func_decl, 3);

  smt::Z3Solver z3_solver;
  z3_solver.add(formula);

  EXPECT_EQ(2, z3_solver.stats().constants);
  EXPECT_EQ(1, z3_solver.stats().func_apps);
  EXPECT_EQ(0, z3_solver.stats().array_selects);
  EXPECT_EQ(0, z3_solver.stats().array_stores);
  EXPECT_EQ(0, z3_solver.stats().unary_ops);
  EXPECT_EQ(3, z3_solver.stats().binary_ops);
  EXPECT_EQ(0, z3_solver.stats().nary_ops);
  EXPECT_EQ(1, z3_solver.stats().equalities);
  EXPECT_EQ(0, z3_solver.stats().disequalities);
  EXPECT_EQ(1, z3_solver.stats().inequalities);
  EXPECT_EQ(0, z3_solver.stats().implications);
  EXPECT_EQ(1, z3_solver.stats().conjunctions);
  EXPECT_EQ(0, z3_solver.stats().disjunctions);

  smt::MsatSolver msat_solver;
  msat_solver.add(formula);

  EXPECT_EQ(2, msat_solver.stats().constants);
  EXPECT_EQ(1, msat_solver.stats().func_apps);
  EXPECT_EQ(0, msat_solver.stats().array_selects);
  EXPECT_EQ(0, msat_solver.stats().array_stores);
  EXPECT_EQ(0, msat_solver.stats().unary_ops);
  EXPECT_EQ(3, msat_solver.stats().binary_ops);
  EXPECT_EQ(0, msat_solver.stats().nary_ops);
  EXPECT_EQ(1, msat_solver.stats().equalities);
  EXPECT_EQ(0, msat_solver.stats().disequalities);
  EXPECT_EQ(1, msat_solver.stats().inequalities);
  EXPECT_EQ(0, msat_solver.stats().implications);
  EXPECT_EQ(1, msat_solver.stats().conjunctions);
  EXPECT_EQ(0, msat_solver.stats().disjunctions);

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
