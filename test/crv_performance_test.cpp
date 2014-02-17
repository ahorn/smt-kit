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
  crv::Encoder encoder; 

  crv::Internal<unsigned> k = 0;
  for (unsigned i = 1; i <= N; i++)
    k = k + i;

  EXPECT_TRUE(k.is_literal());
  EXPECT_EQ(2147516416U, k.literal());

  EXPECT_EQ(smt::unsat, encoder.check(!(k == 2147516416U), crv::tracer()));
  EXPECT_EQ(smt::sat, encoder.check(k == 2147516416U, crv::tracer()));

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
  crv::Encoder encoder; 

  crv::Internal<unsigned> k = 0;
  crv::Internal<unsigned> i = 0;
  for (; crv::tracer().decide_flip(i < N); i = i + 1)
  {
    if(crv::tracer().decide_flip(k == 7))
      k = 0;

    k = k + 1;
  }
  EXPECT_FALSE(crv::tracer().flip());
  EXPECT_TRUE(i.is_literal());
  EXPECT_TRUE(k.is_literal());

  crv::Internal<bool> less(k < 8);
  EXPECT_TRUE(less.is_literal());
  EXPECT_TRUE(less.literal());

  crv::Internal<bool> rem(k == (N % 7));
  EXPECT_TRUE(rem.is_literal());
  EXPECT_TRUE(rem.literal());

  EXPECT_EQ(smt::sat, encoder.check(k < 8, crv::tracer()));
  EXPECT_EQ(smt::unsat, encoder.check(!(k < 8), crv::tracer()));

  EXPECT_EQ(smt::sat, encoder.check(k == (N % 7), crv::tracer()));
  EXPECT_EQ(smt::unsat, encoder.check(k != (N % 7), crv::tracer()));

  auto end = std::chrono::system_clock::now();
  std::chrono::seconds sec = std::chrono::duration_cast<std::chrono::seconds>(end - start);
  EXPECT_TRUE(sec.count() < 1);
}

