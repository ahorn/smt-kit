#include "crv.h"

// Include <gtest/gtest.h> _after_ "crv.h"
#include "gtest/gtest.h"

TEST(CrvFunctionalTest, SafeIf)
{
  crv::tracer().reset();
  crv::Encoder encoder;

  bool error = false;
  do
  {
    crv::External<char> x('A');
    if (crv::tracer().append_guard(x == '?'))
      x = 'B';
    crv::Internal<char> a(x);

    crv::tracer().add_assertion(!(a == 'B' || a == 'A'));

    if (!crv::tracer().assertions().empty() &&
        smt::sat == encoder.check_assertions(crv::tracer()))
      error = true;
  }
  while (crv::tracer().flip());
  EXPECT_FALSE(error);
}

void fib_t0(
  const unsigned N,
  crv::External<int>& i,
  crv::External<int>& j)
{
  int k;
  for (k = 0; k < N; k++)
  {
    i = i + j;
  }
}

void fib_t1(
  const unsigned N,
  crv::External<int>& i,
  crv::External<int>& j)
{
  int k;
  for (k = 0; k < N; k++)
  {
    j = j + i;
  }
}

// Adapted from SV-COMP'13 benchmark:
//   https://svn.sosy-lab.org/software/sv-benchmarks/trunk/c/pthread/fib_bench_longer_true.c
TEST(CrvFunctionalTest, UnsatFib6)
{
  constexpr unsigned N = 6;

  crv::tracer().reset();
  crv::Encoder encoder;

  crv::External<int> i = 1, j = 1;
  crv::Thread t0(fib_t0, N, i, j);
  crv::Thread t1(fib_t1, N, i, j);

  crv::tracer().add_assertion(377 < i || 377 < j);

  t0.join();
  t1.join();

  EXPECT_FALSE(crv::tracer().assertions().empty());
  EXPECT_TRUE(smt::unsat == encoder.check_assertions(crv::tracer()));
  EXPECT_FALSE(crv::tracer().flip());
}

// Adapted from SV-COMP'13 benchmark:
//  https://svn.sosy-lab.org/software/sv-benchmarks/trunk/c/pthread/fib_bench_longer_false-unreach-label.c
TEST(CrvFunctionalTest, SatFib6)
{
  constexpr unsigned N = 6;

  crv::tracer().reset();
  crv::Encoder encoder;

  crv::External<int> i = 1, j = 1;
  crv::Thread t0(fib_t0, N, i, j);
  crv::Thread t1(fib_t1, N, i, j);

  crv::tracer().add_assertion(377 <= i || 377 <= j);

  t0.join();
  t1.join();

  EXPECT_FALSE(crv::tracer().assertions().empty());
  EXPECT_TRUE(smt::sat == encoder.check_assertions(crv::tracer()));
  EXPECT_FALSE(crv::tracer().flip());
}

