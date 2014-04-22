#include "crv.h"

// Include <gtest/gtest.h> _after_ "crv.h"
#include "gtest/gtest.h"

#include <chrono>

TEST(CrvPerformanceTest, ConstantPropagationInCommutativeMonoid)
{
  /* 2^16 */
  constexpr unsigned N = 65536;
  auto start = std::chrono::system_clock::now();

  crv::tracer().reset();
  crv::dfs_checker().reset();
  crv::Encoder encoder; 

  crv::Internal<unsigned> k = 0;
  for (unsigned i = 1; i <= N; i++)
    k = k + i;

  EXPECT_TRUE(k.is_literal());
  EXPECT_EQ(2147516416U, k.literal());

  EXPECT_EQ(smt::unsat, encoder.check(!(k == 2147516416U), crv::tracer(), crv::dfs_checker()));
  EXPECT_EQ(smt::sat, encoder.check(k == 2147516416U, crv::tracer(), crv::dfs_checker()));

  auto end = std::chrono::system_clock::now();
  std::chrono::seconds sec = std::chrono::duration_cast<std::chrono::seconds>(end - start);
  EXPECT_TRUE(sec.count() < 1);
}

TEST(CrvPerformanceTest, PruneBranchesWithConstantPropagation)
{
  /* 2^16 */
  constexpr unsigned N = 65536;
  auto start = std::chrono::system_clock::now();

  crv::tracer().reset();
  crv::dfs_checker().reset();
  crv::Encoder encoder; 

  crv::Internal<unsigned> k = 0;
  crv::Internal<unsigned> i = 0;
  for (; crv::dfs_checker().branch(i < N); i = i + 1)
  {
    if(crv::dfs_checker().branch(k == 7))
      k = 0;

    k = k + 1;
  }
  EXPECT_FALSE(crv::dfs_checker().find_next_path());
  EXPECT_TRUE(i.is_literal());
  EXPECT_TRUE(k.is_literal());

  crv::Internal<bool> less(k < 8);
  EXPECT_TRUE(less.is_literal());
  EXPECT_TRUE(less.literal());

  crv::Internal<bool> rem(k == (N % 7));
  EXPECT_TRUE(rem.is_literal());
  EXPECT_TRUE(rem.literal());

  EXPECT_EQ(smt::sat, encoder.check(k < 8, crv::tracer(), crv::dfs_checker()));
  EXPECT_EQ(smt::unsat, encoder.check(!(k < 8), crv::tracer(), crv::dfs_checker()));

  EXPECT_EQ(smt::sat, encoder.check(k == (N % 7), crv::tracer(), crv::dfs_checker()));
  EXPECT_EQ(smt::unsat, encoder.check(k != (N % 7), crv::tracer(), crv::dfs_checker()));

  auto end = std::chrono::system_clock::now();
  std::chrono::seconds sec = std::chrono::duration_cast<std::chrono::seconds>(end - start);
  EXPECT_TRUE(sec.count() < 1);
}

TEST(CrvPerformanceTest, SafeSequentialSymbolicModulus)
{
  constexpr unsigned N = 64;
  constexpr unsigned K = 7;
  auto start = std::chrono::system_clock::now();

  crv::tracer().reset();
  crv::dfs_checker().reset();
  crv::Encoder encoder; 

  do
  {
    crv::External<unsigned> any_int;
    crv::Internal<unsigned> k = any_int;

    crv::dfs_checker().add_assertion(0 <= k && k < K);
    for (crv::Internal<unsigned> n = 0; crv::dfs_checker().branch(n < N); n = n + 1)
    {
      k = k + 1;
      if (crv::dfs_checker().branch(k == K))
      {
        k = 0;
      }
    }

    // expect k to be always strictly less than K
    EXPECT_EQ(smt::unsat, encoder.check(!(k < K), crv::tracer(), crv::dfs_checker()));
  }
  while (crv::dfs_checker().find_next_path());

  auto end = std::chrono::system_clock::now();
  std::chrono::seconds sec = std::chrono::duration_cast<std::chrono::seconds>(end - start);
  EXPECT_TRUE(sec.count() < 1);
}

// depth-first search finds bug very quickly, so large N is OK
TEST(CrvPerformanceTest, UnsafeSequentialSymbolicModulus)
{
  constexpr unsigned N = 1024;
  constexpr unsigned K = 7;
  auto start = std::chrono::system_clock::now();

  crv::tracer().reset();
  crv::dfs_checker().reset();
  crv::Encoder encoder; 

  bool found_bug = false;
  do
  {
    crv::External<unsigned> any_int;
    crv::Internal<unsigned> k = any_int;

    crv::dfs_checker().add_assertion(0 <= k && k < K);
    for (crv::Internal<unsigned> n = 0; crv::dfs_checker().branch(n < N); n = n + 1)
    {
      if (crv::dfs_checker().branch(k == K))
      {
        k = 0;
      }
      k = k + 1;
    }

    // there exists at least one path such that
    // k fails to be strictly less than K
    found_bug |= smt::unsat == encoder.check(!(k < K), crv::tracer(), crv::dfs_checker());
  }
  while (!found_bug && crv::dfs_checker().find_next_path());
  EXPECT_TRUE(found_bug);

  auto end = std::chrono::system_clock::now();
  std::chrono::seconds sec = std::chrono::duration_cast<std::chrono::seconds>(end - start);
  EXPECT_TRUE(sec.count() < 1);
}
