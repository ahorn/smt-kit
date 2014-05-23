#include "gtest/gtest.h"

#include "smt_deduce.h"

using namespace smt;

TEST(SmtDeduceTest, Literal)
{
  DeduceSolver s;

  smt::Bool true_literal = smt::literal<smt::Bool>(true);
  smt::Bool false_literal = smt::literal<smt::Bool>(false);

  s.push();
  {
    s.add(true_literal);
    EXPECT_EQ(smt::unknown, s.check());
  }
  s.pop();

  s.push();
  {
    s.add(false_literal);
    EXPECT_EQ(smt::unsat, s.check());
  }
  s.pop();
}

TEST(SmtDeduceTest, Bools)
{
  DeduceSolver s;
  smt::Bool x = smt::any<smt::Bool>("x");
  smt::Bool y = smt::any<smt::Bool>("y");
  smt::Bool z = smt::any<smt::Bool>("z");

  s.push();
  {
    s.add(x and not x);
    EXPECT_EQ(smt::unsat, s.check());
  }
  s.pop();

  s.push();
  {
    s.add(not x and not x);
    EXPECT_EQ(smt::unknown, s.check());
  }
  s.pop();

  s.push();
  {
    s.add(y);
    s.add(not y);
    EXPECT_EQ(smt::unsat, s.check());
  }
  s.pop();

  // increase precision
  s.push();
  {
    smt::Bool ite = (x and y) or (not x and y);
    s.add(ite and not y);
    EXPECT_EQ(smt::unknown, s.check());
  }
  s.pop();

  s.push();
  {
    s.add(x and y);
    EXPECT_EQ(smt::unknown, s.check());
  }
  s.pop();

  s.push();
  {
    s.add(x and not y);
    EXPECT_EQ(smt::unknown, s.check());
  }
  s.pop();

  s.push();
  {
    s.add(x and x);
    EXPECT_EQ(smt::unknown, s.check());
  }
  s.pop();

  s.push();
  {
    s.add((x or y) and z);
    EXPECT_EQ(smt::unknown, s.check());
  }
  s.pop();
}

TEST(SmtDeduceTest, Abstraction)
{
  DeduceSolver s;
  smt::Int a = smt::any<smt::Int>("a");
  smt::Int b = smt::any<smt::Int>("b");
  smt::Int c = smt::any<smt::Int>("c");

  smt::Bool x = a < b;
  smt::Bool y = b < c;
  smt::Bool z = a < c;

  s.push();
  {
    s.add(x and not x);
    EXPECT_EQ(smt::unsat, s.check());
  }
  s.pop();

  s.push();
  {
    s.add(not x and not x);
    EXPECT_EQ(smt::unknown, s.check());
  }
  s.pop();

  s.push();
  {
    s.add(y);
    s.add(not y);
    EXPECT_EQ(smt::unsat, s.check());
  }
  s.pop();

  // increase precision
  s.push();
  {
    smt::Bool ite = (x and y) or (not x and y);
    s.add(ite and not y);
    EXPECT_EQ(smt::unknown, s.check());
  }
  s.pop();

  s.push();
  {
    s.add(x and y);
    EXPECT_EQ(smt::unknown, s.check());
  }
  s.pop();

  s.push();
  {
    s.add(x and not y);
    EXPECT_EQ(smt::unknown, s.check());
  }
  s.pop();

  s.push();
  {
    s.add(x and x);
    EXPECT_EQ(smt::unknown, s.check());
  }
  s.pop();

  s.push();
  {
    s.add((x or y) and z);
    EXPECT_EQ(smt::unknown, s.check());
  }
  s.pop();
}

TEST(SmtDeduceTest, Reset)
{
  DeduceSolver s;
  smt::Bool x = smt::any<smt::Bool>("x");

  s.add(x and not x);
  EXPECT_EQ(smt::unsat, s.check());

  s.reset();

  s.add(x);
  EXPECT_EQ(smt::unknown, s.check());
}
