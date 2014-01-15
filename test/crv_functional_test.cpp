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

    crv::tracer().add_error(!(a == 'B' || a == 'A'));

    if (!crv::tracer().errors().empty() &&
        smt::sat == encoder.check(crv::tracer()))
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

  crv::tracer().add_error(377 < i || 377 < j);

  t0.join();
  t1.join();

  EXPECT_TRUE(crv::tracer().assertions().empty());
  EXPECT_FALSE(crv::tracer().errors().empty());
  EXPECT_TRUE(smt::unsat == encoder.check(crv::tracer()));
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

  crv::tracer().add_error(377 <= i || 377 <= j);

  t0.join();
  t1.join();

  EXPECT_TRUE(crv::tracer().assertions().empty());
  EXPECT_FALSE(crv::tracer().errors().empty());
  EXPECT_TRUE(smt::sat == encoder.check(crv::tracer()));
  EXPECT_FALSE(crv::tracer().flip());
}

void stateful_t0(
  crv::Mutex& mutex,
  crv::External<int>& i,
  crv::External<int>& j)
{
  mutex.lock();
  i = i + 1;
  mutex.unlock();

  mutex.lock();
  j = j + 1;
  mutex.unlock();
}

void stateful_t1(
  crv::Mutex& mutex,
  crv::External<int>& i,
  crv::External<int>& j)
{
  mutex.lock();
  i = i + 5;
  mutex.unlock();

  mutex.lock();
  j = j - 6;
  mutex.unlock();
}

// Adapted from SV-COMP'13 benchmark:
//  https://svn.sosy-lab.org/software/sv-benchmarks/trunk/c/pthread/stateful01_true.c
TEST(CrvFunctionalTest, UnsatStateful)
{
  crv::tracer().reset();
  crv::Encoder encoder;

  crv::Mutex mutex;
  crv::External<int> i(10), j(10);

  bool error = false;
  do
  {
    crv::Thread t0(stateful_t0, mutex, i, j);
    crv::Thread t1(stateful_t1, mutex, i, j);

    t0.join();
    t1.join();

    crv::tracer().add_error(i != 16 || j != 5);

    if (!crv::tracer().errors().empty() &&
        smt::sat == encoder.check(crv::tracer()))
      error = true;
  }
  while (crv::tracer().flip());
  EXPECT_FALSE(error);
}

// Adapted from SV-COMP'13 benchmark:
//  https://svn.sosy-lab.org/software/sv-benchmarks/trunk/c/pthread/stateful01_false-unreach-label.c
TEST(CrvFunctionalTest, SatStateful)
{
  crv::tracer().reset();
  crv::Encoder encoder;

  crv::Mutex mutex;
  crv::External<int> i(10), j(10);

  bool error = false;
  do
  {
    crv::Thread t0(stateful_t0, mutex, i, j);
    crv::Thread t1(stateful_t1, mutex, i, j);

    t0.join();
    t1.join();

    crv::tracer().add_error(i == 16 && j == 5);

    if (!crv::tracer().errors().empty() &&
        smt::sat == encoder.check(crv::tracer()))
      error = true;
  }
  while (crv::tracer().flip());
  EXPECT_TRUE(error);
}

void sat_stack_t0(
  const unsigned N,
  crv::Mutex& mutex,
  crv::External<unsigned int>& top,
  crv::External<int>& flag)
{
  int i;
  for (i = 0; i < N; i++)
  {
    mutex.lock();
    top = top + 1U;
    flag = 1;
    mutex.unlock();
  }
}

void sat_stack_t1(
const unsigned N,
  crv::Mutex& mutex,
  crv::External<unsigned int>& top,
  crv::External<int>& flag)
{
  int i;
  for (i = 0; i < N; i++)
  {
    mutex.lock();
    if (crv::tracer().append_guard(flag == 1))
    {
      crv::tracer().add_error(top == 0U);
      top = top - 1U;
    }
    mutex.unlock();
  }
}

TEST(CrvFunctionalTest, SatStack)
{
  constexpr unsigned N = 5;

  crv::tracer().reset();
  crv::Encoder encoder;

  crv::Mutex mutex;
  crv::External<unsigned int> top(0U);
  crv::External<int> flag(0);

  bool error = false;
  do
  {
    crv::Thread t0(sat_stack_t0, N, mutex, top, flag);
    crv::Thread t1(sat_stack_t1, N, mutex, top, flag);

    if (!crv::tracer().errors().empty() &&
        smt::sat == encoder.check(crv::tracer()))
      error = true;
  }
  while (crv::tracer().flip());
  EXPECT_TRUE(error);
}

void unsat_stack_t0(
  const unsigned N,
  crv::Mutex& mutex,
  crv::External<unsigned int>& top)
{
  int i;
  for (i = 0; i < N; i++)
  {
    mutex.lock();
    top = top + 1U;
    mutex.unlock();
  }
}

void unsat_stack_t1(
  const unsigned N,
  crv::Mutex& mutex,
  crv::External<unsigned int>& top)
{
  int i;
  for (i = 0; i < N; i++)
  {
    mutex.lock();
    if (crv::tracer().append_guard(0U < top))
    {
      crv::tracer().add_error(top == 0U);
      top = top - 1U;
    }
    mutex.unlock();
  }
}

TEST(CrvFunctionalTest, UnsatStack)
{
  constexpr unsigned N = 5;

  crv::tracer().reset();
  crv::Encoder encoder;

  crv::Mutex mutex;
  crv::External<unsigned int> top(0U);

  bool error = false;
  do
  {
    crv::Thread t0(unsat_stack_t0, N, mutex, top);
    crv::Thread t1(unsat_stack_t1, N, mutex, top);

    if (!crv::tracer().errors().empty() &&
        smt::sat == encoder.check(crv::tracer()))
      error = true;
  }
  while (crv::tracer().flip());
  EXPECT_FALSE(error);
}

void sat_communication_f(crv::Channel<int>& s, crv::Channel<int>& t)
{
  t.send(1);
  crv::Internal<int> r(s.recv());
  s.send(r);
}

void sat_communication_g(crv::Channel<int>& s, crv::Channel<int>& t)
{
  crv::Internal<int> r(t.recv());
  s.send(r);
}

void sat_communication_h(crv::Channel<int>& s)
{
  s.recv();
}

TEST(CrvFunctionalTest, SatCommunication)
{
  crv::tracer().reset();
  crv::Encoder encoder;

  crv::Channel<int> s, t;
  crv::Thread f(sat_communication_f, s, t);
  crv::Thread g(sat_communication_g, s, t);
  crv::Thread h(sat_communication_h, s);

  EXPECT_TRUE(crv::tracer().errors().empty());
  EXPECT_EQ(smt::sat, encoder.check_deadlock(crv::tracer()));
}

void sat_communication_g_prime(crv::Channel<int>& s, crv::Channel<int>& t)
{
  crv::Internal<int> r(t.recv());
  s.send(r);
  s.recv();
}

TEST(CrvFunctionalTest, UnsatCommunication)
{
  crv::tracer().reset();
  crv::Encoder encoder;

  crv::Channel<int> s, t;
  crv::Thread f(sat_communication_f, s, t);
  crv::Thread g_prime(sat_communication_g_prime, s, t);

  EXPECT_TRUE(crv::tracer().errors().empty());
  EXPECT_EQ(smt::unsat, encoder.check_deadlock(crv::tracer()));
}

void unsat_communication_deadlock_with_guard_f(crv::Channel<int>& c)
{
  EXPECT_TRUE(crv::tracer().append_guard(6 == c.recv()));
  c.send(7);
}

void unsat_communication_deadlock_with_guard_g(crv::Channel<int>& c)
{
  c.send(6);
  c.recv();
}

TEST(CrvFunctionalTest, UnsatCommunicationDeadlockWithGuard)
{
  crv::tracer().reset();
  crv::Encoder encoder;

  crv::Channel<int> c;
  crv::Thread f(unsat_communication_deadlock_with_guard_f, c);
  crv::Thread g(unsat_communication_deadlock_with_guard_g, c);

  EXPECT_EQ(smt::unsat, encoder.check_deadlock(crv::tracer()));
}

void sat_communication_deadlock_with_guard_f(crv::Channel<int>& c)
{
  EXPECT_TRUE(crv::tracer().append_guard(6 != c.recv()));
  c.send(7);
}

void sat_communication_deadlock_with_guard_g(crv::Channel<int>& c)
{
  c.send(6);
  c.recv();
}

TEST(CrvFunctionalTest, SatCommunicationDeadlockWithGuard)
{
  crv::tracer().reset();
  crv::Encoder encoder;

  crv::Channel<int> c;
  crv::Thread f(sat_communication_deadlock_with_guard_f, c);
  crv::Thread g(sat_communication_deadlock_with_guard_g, c);

  EXPECT_EQ(smt::sat, encoder.check_deadlock(crv::tracer()));
}

