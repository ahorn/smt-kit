#include "gtest/gtest.h"

#include <smt>
#include <cstdint>

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
  const smt::Term<smt::Bool> x = smt::any<smt::Bool>("x");
  const smt::Term<smt::Bool> y = smt::any<smt::Bool>("y");
  const smt::Term<smt::Bool> lhs = !(x && y);
  const smt::Term<smt::Bool> rhs = !x || !y;

  smt::Z3Solver z3_solver;
  z3_solver.add(lhs != rhs);
  EXPECT_EQ(smt::unsat, z3_solver.check());

  smt::MsatSolver msat_solver;
  msat_solver.add(lhs != rhs);
  EXPECT_EQ(smt::unsat, msat_solver.check());
}

TEST(SmtFunctionalTest, SeparateDecls)
{
  const smt::Decl<smt::Bool> x_decl("x");
  const smt::Decl<smt::Bool> y_decl("y");
  const smt::Term<smt::Bool> x = smt::constant(x_decl);
  const smt::Term<smt::Bool> y = smt::constant(y_decl);
  const smt::Term<smt::Bool> lhs = !(x && y);
  const smt::Term<smt::Bool> rhs = !x || !y;

  smt::Z3Solver z3_solver;
  z3_solver.add(lhs != rhs);
  EXPECT_EQ(smt::unsat, z3_solver.check());

  smt::MsatSolver msat_solver;
  msat_solver.add(lhs != rhs);
  EXPECT_EQ(smt::unsat, msat_solver.check());
}

TEST(SmtFunctionalTest, BitVectors)
{
  const smt::Term<unsigned long> x = smt::any<unsigned long>("x");
  const smt::Term<unsigned long> y = smt::any<unsigned long>("y");
  const smt::Term<unsigned long> z = smt::any<unsigned long>("z");
  const smt::Term<smt::Bool> equality = (x == y) && ((x & ~y) == z);

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
}

TEST(SmtFunctionalTest, UnsafeExpr)
{
  const smt::UnsafeDecl unsafe_decl("x", smt::bv_sort(true, sizeof(int) * 8));
  const smt::UnsafeTerm x = smt::constant(unsafe_decl);
  const smt::UnsafeTerm equality = (x & smt::literal<int>(3)) != x;

  smt::Z3Solver z3_solver;
  z3_solver.unsafe_add(equality);
  EXPECT_EQ(smt::sat, z3_solver.check());

  smt::MsatSolver msat_solver;
  msat_solver.unsafe_add(equality);
  EXPECT_EQ(smt::sat, msat_solver.check());
}

TEST(SmtFunctionalTest, Reflection)
{
  constexpr size_t bv_int_size = sizeof(int) * 8;
  EXPECT_EQ(smt::bv_sort(true, bv_int_size), smt::literal<int>(3).sort());

  const smt::Term<uint32_t> x = smt::any<uint32_t>("x");
  EXPECT_TRUE(x.sort().is_bv());
  EXPECT_FALSE(x.sort().is_signed());
  EXPECT_EQ(32, x.sort().bv_size());

  typedef smt::Func<smt::Int, smt::Real, char> SomeFunc;
  const smt::Term<SomeFunc> f = smt::any<SomeFunc>("f");
  EXPECT_TRUE(f.sort().is_func());
  EXPECT_EQ(3, f.sort().sorts_size());
  EXPECT_TRUE(f.sort().sorts(0).is_int());
  EXPECT_TRUE(f.sort().sorts(1).is_real());
  EXPECT_TRUE(f.sort().sorts(2).is_bv());
  EXPECT_EQ(sizeof(char) * 8, f.sort().sorts(2).bv_size());
}

TEST(SmtFunctionalTest, Array)
{
  typedef smt::Array<smt::Int, char> IntToCharArray;
  const smt::Decl<IntToCharArray> array_decl("array");

  smt::Term<IntToCharArray> array, new_array;
  smt::Term<smt::Int> index;
  smt::Term<char> value;

  array = smt::constant(array_decl);
  index = smt::any<smt::Int>("index");
  value = smt::literal<char>('p');

  new_array = smt::store(array, index, value);

  smt::Z3Solver z3_solver;
  z3_solver.add(smt::select(new_array, index) != value);
  EXPECT_EQ(smt::unsat, z3_solver.check());

  smt::MsatSolver msat_solver;
  msat_solver.add(smt::select(new_array, index) != value);
  EXPECT_EQ(smt::unsat, msat_solver.check());
}

TEST(SmtFunctionalTest, Function)
{
  const smt::Decl<smt::Func<smt::Int, smt::Int>> func_decl("f");
  const smt::Term<smt::Int> x = smt::any<smt::Int>("x");
  const smt::Term<smt::Bool> formula =
    smt::apply(func_decl, 3) == 7 && x == smt::apply(func_decl, 3);

  smt::Z3Solver z3_solver;
  z3_solver.add(formula && x != smt::literal<smt::Int>(7));
  EXPECT_EQ(smt::unsat, z3_solver.check());

  smt::MsatSolver msat_solver;
  msat_solver.add(formula && x != 7);
  EXPECT_EQ(smt::unsat, msat_solver.check());
}

TEST(SmtFunctionalTest, Stats)
{
  const smt::Decl<smt::Func<smt::Int, smt::Int>> func_decl("f");
  const smt::Term<smt::Int> x = smt::any<smt::Int>("x");
  const smt::Term<smt::Bool> formula = x < 3 && x == smt::apply(func_decl, 3);

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
}
