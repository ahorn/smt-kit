#include "nse_sequential.h"

// Include <gtest/gtest.h> _after_ "nse_sequential.h.h"
#include "gtest/gtest.h"

using namespace crv;

TEST(NseSequentialTest, SequentialDfsChecker)
{
  SequentialDfsChecker checker;

  // if (a < 7) { skip } ; if (a < 4)  { skip }
  Internal<int> a;
  EXPECT_FALSE(checker.branch(a < 7));
  EXPECT_FALSE(checker.branch(a < 4));
  EXPECT_TRUE(checker.find_next_path());

  EXPECT_FALSE(checker.branch(a < 7));
  EXPECT_TRUE(checker.branch(a < 4));

  // ignored because "a >= 7 and a < 4" is unsat
  EXPECT_FALSE(checker.branch(a < 1));
  EXPECT_FALSE(checker.branch(a < 2));
  EXPECT_FALSE(checker.branch(a < 3));
  EXPECT_TRUE(checker.find_next_path());

  EXPECT_TRUE(checker.branch(a < 7));
  EXPECT_FALSE(checker.branch(a < 4));
  EXPECT_TRUE(checker.find_next_path());

  EXPECT_TRUE(checker.branch(a < 7));
  EXPECT_TRUE(checker.branch(a < 4));
  EXPECT_FALSE(checker.find_next_path());

  checker.reset();

  Internal<int> b;
  checker.add_assertion(b < 7);
  EXPECT_TRUE(checker.branch(b < 7));
  EXPECT_FALSE(checker.branch(b < 4));
  EXPECT_TRUE(checker.find_next_path());

  checker.add_assertion(b < 7);
  EXPECT_TRUE(checker.branch(b < 7));
  EXPECT_TRUE(checker.branch(b < 4));
  EXPECT_FALSE(checker.find_next_path());

  checker.reset();

  Internal<int> c;
  checker.add_assertion(c < 4);
  EXPECT_TRUE(checker.branch(c < 7));
  EXPECT_TRUE(checker.branch(c < 4));
  EXPECT_FALSE(checker.find_next_path());
}

TEST(NseSequentialTest, Backtrack)
{
  BacktrackDfsChecker checker;

  // if (a < 7) { skip } ; if (a < 4)  { skip }
  Internal<int> a;
  EXPECT_FALSE(checker.branch(a < 7));
  EXPECT_FALSE(checker.branch(a < 4));
  EXPECT_TRUE(checker.find_next_path());

  EXPECT_FALSE(checker.branch(a < 7));
  EXPECT_TRUE(checker.branch(a < 4));

  // ignored because "a >= 7 and a < 4" is unsat
  EXPECT_FALSE(checker.branch(a < 1));
  EXPECT_FALSE(checker.branch(a < 2));
  EXPECT_FALSE(checker.branch(a < 3));
  EXPECT_TRUE(checker.find_next_path());

  EXPECT_TRUE(checker.branch(a < 7));
  EXPECT_FALSE(checker.branch(a < 4));
  EXPECT_TRUE(checker.find_next_path());

  EXPECT_TRUE(checker.branch(a < 7));
  EXPECT_TRUE(checker.branch(a < 4));
  EXPECT_FALSE(checker.find_next_path());

  checker.reset();

  // BacktrackDfsChecker may not prune as
  // many paths as SequentialDfsChecker
  Internal<int> b;
  checker.add_assertion(b < 7);
  EXPECT_FALSE(checker.branch(b < 7));
  EXPECT_FALSE(checker.branch(b < 4));
  EXPECT_TRUE(checker.find_next_path());

  checker.add_assertion(b < 7);
  EXPECT_TRUE(checker.branch(b < 7));
  EXPECT_FALSE(checker.branch(b < 4));
  EXPECT_TRUE(checker.find_next_path());

  checker.add_assertion(b < 7);
  EXPECT_TRUE(checker.branch(b < 7));
  EXPECT_TRUE(checker.branch(b < 4));
  EXPECT_FALSE(checker.find_next_path());

  checker.reset();

  // assertion at the end
  EXPECT_FALSE(checker.branch(b < 7));
  EXPECT_FALSE(checker.branch(b < 4));
  checker.add_assertion(a < 7);
  checker.add_assertion(b < 7);
  EXPECT_TRUE(checker.find_next_path());

  EXPECT_TRUE(checker.branch(b < 7));
  EXPECT_FALSE(checker.branch(b < 4));
  checker.add_assertion(a < 7);
  checker.add_assertion(b < 7);
  EXPECT_TRUE(checker.find_next_path());

  EXPECT_TRUE(checker.branch(b < 7));
  EXPECT_TRUE(checker.branch(b < 4));
  checker.add_assertion(a < 7);
  checker.add_assertion(b < 7);
  EXPECT_FALSE(checker.find_next_path());
}
