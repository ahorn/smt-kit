#include "nse_sequential.h"

// Include <gtest/gtest.h> _after_ "nse_sequential.h.h"
#include "gtest/gtest.h"

using namespace crv;

TEST(NseSequentialTest, Pointer)
{
  Internal<char[]> array;
  Internal<size_t> index;

  index = 1;

  array[0] = 'A';
  array[1] = 'B';
  array[2] = 'C';

  Internal<char*> ptr = array;

  EXPECT_TRUE(ptr[0].is_literal());
  EXPECT_EQ('A', ptr[0].literal());

  EXPECT_TRUE((*ptr).is_literal());
  EXPECT_EQ('A', (*ptr).literal());

  EXPECT_TRUE(ptr[1].is_literal());
  EXPECT_EQ('B', ptr[1].literal());

  EXPECT_TRUE(ptr[index].is_literal());
  EXPECT_EQ('B', ptr[index].literal());

  ptr++;

  EXPECT_TRUE(ptr[0].is_literal());
  EXPECT_EQ('B', ptr[0].literal());

  EXPECT_TRUE((*ptr).is_literal());
  EXPECT_EQ('B', (*ptr).literal());

  EXPECT_TRUE(ptr[1].is_literal());
  EXPECT_EQ('C', ptr[1].literal());

  EXPECT_TRUE(ptr[index].is_literal());
  EXPECT_EQ('C', ptr[index].literal());

  ptr--;

  EXPECT_TRUE(ptr[0].is_literal());
  EXPECT_EQ('A', ptr[0].literal());

  EXPECT_TRUE((*ptr).is_literal());
  EXPECT_EQ('A', (*ptr).literal());

  EXPECT_TRUE(ptr[1].is_literal());
  EXPECT_EQ('B', ptr[1].literal());

  EXPECT_TRUE(ptr[index].is_literal());
  EXPECT_EQ('B', ptr[index].literal());

  Internal<char*> ptr_copy(ptr);
  ++ptr_copy;

  EXPECT_TRUE(ptr_copy[0].is_literal());
  EXPECT_EQ('B', ptr_copy[0].literal());

  EXPECT_TRUE((*ptr_copy).is_literal());
  EXPECT_EQ('B', (*ptr_copy).literal());

  EXPECT_TRUE(ptr_copy[1].is_literal());
  EXPECT_EQ('C', ptr_copy[1].literal());

  EXPECT_TRUE(ptr_copy[index].is_literal());
  EXPECT_EQ('C', ptr_copy[index].literal());

  constexpr size_t N = 5;
  Internal<char[N]> n_array;

  n_array[0] = 'A';
  n_array[1] = 'B';
  n_array[2] = 'C';

  Internal<char*> n_ptr = n_array;

  EXPECT_TRUE(n_ptr[0].is_literal());
  EXPECT_EQ('A', n_ptr[0].literal());

  EXPECT_TRUE((*n_ptr).is_literal());
  EXPECT_EQ('A', (*n_ptr).literal());

  EXPECT_TRUE(n_ptr[1].is_literal());
  EXPECT_EQ('B', n_ptr[1].literal());

  EXPECT_TRUE(n_ptr[index].is_literal());
  EXPECT_EQ('B', n_ptr[index].literal());

  array[1] = 'Y';
  n_array[1] = 'Y';

   // assignment operators
  n_ptr = n_array;
  EXPECT_EQ('Y', (*(++n_ptr)).literal());

  ptr = array;
  EXPECT_EQ('Y', (*(++ptr)).literal());
}

TEST(NseSequentialTest, UnaryIncrement)
{
  Internal<int> a = 5;
  Internal<int> b = a++;
  Internal<int> c = ++a;

  EXPECT_TRUE(a.is_literal());
  EXPECT_TRUE(b.is_literal());
  EXPECT_TRUE(c.is_literal());

  EXPECT_EQ(7, a.literal());
  EXPECT_EQ(5, b.literal());
  EXPECT_EQ(7, c.literal());
}

TEST(NseSequentialTest, UnaryDecrement)
{
  Internal<int> a = 5;
  Internal<int> b = a--;
  Internal<int> c = --a;

  EXPECT_TRUE(a.is_literal());
  EXPECT_TRUE(b.is_literal());
  EXPECT_TRUE(c.is_literal());

  EXPECT_EQ(3, a.literal());
  EXPECT_EQ(5, b.literal());
  EXPECT_EQ(3, c.literal());
}

TEST(NseSequentialTest, MakeZero)
{
  Internal<int> a = 5;
  Internal<int[3]> b;

  make_zero(a);
  EXPECT_TRUE(a.is_literal());
  EXPECT_EQ(0, a.literal());

  make_zero(b);

  EXPECT_TRUE(b[0].is_literal());
  EXPECT_TRUE(b[1].is_literal());
  EXPECT_TRUE(b[2].is_literal());

  EXPECT_EQ(0, b[0].literal());
  EXPECT_EQ(0, b[1].literal());
  EXPECT_EQ(0, b[2].literal());
}

TEST(NseSequentialTest, PointerChecks)
{
  SequentialDfsChecker c0;

  Internal<char[]> array;
  Internal<char*> ptr = array;

  EXPECT_FALSE(c0.branch(ptr[3] == 'D'));
  c0.add_error(ptr[3] == 'D');
  EXPECT_EQ(smt::unsat, c0.check());
  EXPECT_TRUE(c0.find_next_path());

  EXPECT_TRUE(c0.branch(ptr[3] == 'D'));
  c0.add_error(ptr[3] == 'D');
  EXPECT_EQ(smt::sat, c0.check());
  EXPECT_FALSE(c0.find_next_path());

  BacktrackDfsChecker c1;

  make_any(array);
  ptr = array;

  EXPECT_FALSE(c1.branch(ptr[3] == 'D'));
  c1.add_error(ptr[3] == 'D');
  EXPECT_EQ(smt::unsat, c1.check());
  EXPECT_TRUE(c1.find_next_path());

  EXPECT_TRUE(c1.branch(ptr[3] == 'D'));
  c1.add_error(ptr[3] == 'D');
  EXPECT_EQ(smt::sat, c1.check());
  EXPECT_FALSE(c1.find_next_path());
}

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
