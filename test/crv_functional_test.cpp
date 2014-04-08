#include "crv.h"

// Include <gtest/gtest.h> _after_ "crv.h"
#include "gtest/gtest.h"
#include <array>

TEST(CrvFunctionalTest, SafeIf)
{
  crv::tracer().reset();
  crv::Encoder encoder;

  bool error = false;
  do
  {
    crv::External<char> x('A');
    if (crv::tracer().decide_flip(x == '?'))
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

TEST(CrvFunctionalTest, MultipathSafeIf)
{
  crv::tracer().reset();
  crv::Encoder encoder;

  crv::External<char> x('A');
  crv::tracer().scope_then(x == '?');
  x = 'B';
  crv::tracer().scope_end();
  crv::Internal<char> a(x);
  crv::tracer().add_error(!(a == 'B' || a == 'A'));
  EXPECT_EQ(smt::unsat, encoder.check(crv::tracer()));
}

// For more explanations, see Section 2.2 (Sums and Recurrences)
// in "Concrete Mathematics", Second Edition, by Ronald L. Graham,
// Donald E. Knuth, and Oren Patashnik
crv::Internal<int> sumR(
  crv::Internal<int> a,
  crv::Internal<int> b,
  crv::Internal<int> k)
{
  crv::Internal<int> sum = a + b*k;
  if (crv::tracer().decide_flip(k > 0))
    return sum + sumR(a, b, k-1);
  else
    return sum;
}

// uses reals, so no overflow detection
TEST(CrvFunctionalTest, SafeRecurrenceSum)
{
  // N must be even
  constexpr unsigned N = 4;

  crv::tracer().reset();
  crv::Encoder encoder;

  crv::External<int> x;
  crv::External<int> y;
  crv::Internal<int> a = x;
  crv::Internal<int> b = y;
  crv::Internal<int> result = sumR(a, b, N);
  crv::tracer().add_error(result != ((a*(N+1)) + (b*(N+1)*(N/2))));
  EXPECT_EQ(smt::unsat, encoder.check(crv::tracer()));
}

TEST(CrvFunctionalTest, UnsafeRecurrenceSum)
{
  // N must be even
  constexpr unsigned N = 4;

  crv::tracer().reset();
  crv::Encoder encoder;

  crv::External<int> x;
  crv::External<int> y;
  crv::Internal<int> a = x;
  crv::Internal<int> b = y;
  crv::Internal<int> result = sumR(a, b, N);
  crv::tracer().add_error(result == ((a*(N+1)) + (b*(N+1)*(N/2))));
  EXPECT_EQ(smt::sat, encoder.check(crv::tracer()));
}

void unsafe_simple_assign_1(crv::External<int>& i)
{
  i = 1;
  crv::tracer().add_error(i != 1);
}

void unsafe_simple_assign_2(crv::External<int>& i)
{
  i = 2;
}

TEST(CrvFunctionalTest, UnsafeThreads)
{
  crv::tracer().reset();
  crv::Encoder encoder;

  crv::External<int> i = 0;
  crv::Thread t1(unsafe_simple_assign_1, i);
  crv::Thread t2(unsafe_simple_assign_2, i);

  EXPECT_EQ(smt::sat, encoder.check(crv::tracer()));
}

void safe_simple_assign_1(crv::External<int>& i)
{
  i = 1;
  crv::Internal<int> r = i;
  crv::tracer().add_error(r != 0 && r != 1 && r != 2);
}

void safe_simple_assign_2(crv::External<int>& i)
{
  i = 2;
}

TEST(CrvFunctionalTest, SafeThreads)
{
  crv::tracer().reset();
  crv::Encoder encoder;

  crv::External<int> i = 0;
  crv::Thread t1(safe_simple_assign_1, i);
  crv::Thread t2(safe_simple_assign_2, i);

  EXPECT_EQ(smt::unsat, encoder.check(crv::tracer()));
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
    if (crv::tracer().decide_flip(flag == 1))
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
    if (crv::tracer().decide_flip(0U < top))
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
  EXPECT_TRUE(crv::tracer().decide_flip(6 == c.recv()));
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
  EXPECT_TRUE(crv::tracer().decide_flip(6 != c.recv()));
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

// N is the number of philosophers

// For comparison, the equivalent CSP code of
// {Sat,Unsat}DiningPhilosophersDeadlock:
//
// N = 5
// 
// FORK_ID = {0..N-1}
// PHIL_ID = {0..N-1}
// 
// channel picksup, putsdown:FORK_ID.PHIL_ID
// 
// PHIL(i) = picksup!i!i -> picksup!((i+1)%N)!i ->
//   putsdown!((i+1)%N)!i -> putsdown!i!i -> PHIL(i)
// 
// FORK(i) = picksup!i?j -> putsdown!i!j -> FORK(i)
// 
// PHILS = ||| i:PHIL_ID@ PHIL(i)
// FORKS = ||| i:FORK_ID@ FORK(i)
// 
// SAT_SYSTEM = PHILS[|{|picksup, putsdown|}|]FORKS
// assert SAT_SYSTEM :[deadlock free [F]]
// 
// LPHIL(i) = picksup!((i+1)%N)!i -> picksup!i!i ->
//   putsdown!((i+1)%N)!i -> putsdown!i!i -> LPHIL(i)
// 
// PHILS' = ||| i:PHIL_ID @ if i==0 then LPHIL(0) else PHIL(i)
// 
// UNSAT_SYSTEM = PHILS'[|{|picksup, putsdown|}|]FORKS
// assert UNSAT_SYSTEM :[deadlock free [F]]
template<size_t N>
struct DiningTable
{
  std::array<crv::Channel<int>, N> picksup;
  std::array<crv::Channel<int>, N> putsdown;
};

// Allow fork to be used twice, so it can be picked up and put
// down by the person to the fork's right and left
template<size_t N>
void phil_fork(size_t i, DiningTable<N>& t)
{
  t.picksup.at(i).recv();
  t.putsdown.at(i).recv();
  t.picksup.at(i).recv();
  t.putsdown.at(i).recv();
}

// Picks up left and then right fork;
// finally, puts down both forks
template<size_t N>
void phil_person(size_t i, DiningTable<N>& t)
{
  t.picksup.at(i).send(i);
  t.picksup.at((i + 1) % N).send(i);
  t.putsdown.at(i).send(i);
  t.putsdown.at((i + 1) % N).send(i);
}

// Picks up right fork then left fork;
// finally, puts down both forks
template<size_t N>
void phil_different_person(size_t i, DiningTable<N>& t)
{
  t.picksup.at((i + 1) % N).send(i);
  t.picksup.at(i).send(i);
  t.putsdown.at(i).send(i);
  t.putsdown.at((i + 1) % N).send(i);
}

TEST(CrvFunctionalTest, UnsatDiningPhilosophersDeadlock)
{
  crv::tracer().reset();
  crv::Encoder encoder;

  constexpr size_t N = 5;
  DiningTable<N> t;

  for (int i = 0; i < N; i++)
  {
    crv::Thread fork(phil_fork<N>, i, t);

    if (i == 0)
      crv::Thread person(phil_different_person<N>, i, t);
    else
      crv::Thread person(phil_person<N>, i, t);
  }

  EXPECT_EQ(smt::unsat, encoder.check_deadlock(crv::tracer()));
}

TEST(CrvFunctionalTest, SatDiningPhilosophersDeadlock)
{
  crv::tracer().reset();
  crv::Encoder encoder;

  constexpr size_t N = 2;
  DiningTable<N> t;

  for (int i = 0; i < N; i++)
  {
    crv::Thread fork(phil_fork<N>, i, t);
    crv::Thread person(phil_person<N>, i, t);
  }

  EXPECT_EQ(smt::sat, encoder.check_deadlock(crv::tracer()));
}

void barrier_test_f(crv::External<int>& i)
{
  i = 1;
  i = 2;
  crv::tracer().barrier();
}

void barrier_test_g(const crv::External<int>& i)
{
  crv::tracer().barrier();
  crv::tracer().add_error(i == 1);
}

void barrier_test_h(const crv::External<int>& i)
{
  crv::tracer().add_error(i == 2);
}

TEST(CrvFunctionalTest, UnsatBarrier)
{
  crv::tracer().reset();
  crv::Encoder encoder;

  crv::External<int> i(0);
  crv::Thread f(barrier_test_f, i);
  crv::Thread g(barrier_test_g, i);

  EXPECT_EQ(smt::unsat, encoder.check(crv::tracer()));

  crv::tracer().barrier();
  EXPECT_EQ(smt::unsat, encoder.check(i == 0, crv::tracer()));
  EXPECT_EQ(smt::unsat, encoder.check(i == 1, crv::tracer()));
  EXPECT_EQ(smt::sat, encoder.check(i == 2, crv::tracer()));
}

TEST(CrvFunctionalTest, SatBarrier)
{
  crv::tracer().reset();
  crv::Encoder encoder;

  crv::External<int> i(0);
  crv::Thread f(barrier_test_f, i);
  crv::Thread h(barrier_test_h, i);

  EXPECT_EQ(smt::sat, encoder.check(crv::tracer()));

  // no barrier in main thread
  EXPECT_EQ(smt::sat, encoder.check(i == 0, crv::tracer()));
  EXPECT_EQ(smt::sat, encoder.check(i == 1, crv::tracer()));
  EXPECT_EQ(smt::sat, encoder.check(i == 2, crv::tracer()));
}

TEST(CrvFunctionalTest, MpiDeadlockFree)
{
  crv::tracer().reset();
  crv::Encoder encoder;

  const char some_data = 'A';

  // 2
  crv::tracer().append_thread_begin_event();
  crv::Message::send(3, some_data);
  crv::tracer().append_thread_end_event();

  // 3
  crv::tracer().append_thread_begin_event();
  crv::Message::recv_any<char>();
  crv::tracer().append_thread_end_event();

  EXPECT_EQ(smt::unsat, encoder.check_deadlock(crv::tracer()));
}

// See dtg.c benchmark for MOPPER, http://www.cprover.org/mpi/
TEST(CrvFunctionalTest, DtgMpiDeadlock)
{
  crv::tracer().reset();
  crv::Encoder encoder;

  const char some_data = 'A';

  // 2
  crv::tracer().append_thread_begin_event();
  crv::Message::recv_any<char>();
  crv::Message::send(5, some_data);
  crv::Message::recv_any<char>();
  crv::tracer().append_thread_end_event();

  // 3
  crv::tracer().append_thread_begin_event();
  crv::Message::send(2, some_data);
  crv::Message::send(5, some_data);
  crv::tracer().append_thread_end_event();

  // 4
  crv::tracer().append_thread_begin_event();
  crv::Message::recv_any<char>();
  crv::Message::send(2, some_data);
  crv::tracer().append_thread_end_event();

  // 5
  crv::tracer().append_thread_begin_event();
  crv::Message::recv<char>(3);
  crv::Message::recv<char>(2);
  crv::tracer().append_thread_end_event();

  // 6
  crv::tracer().append_thread_begin_event();
  crv::Message::send(4, some_data);
  crv::tracer().append_thread_end_event();

  EXPECT_EQ(smt::sat, encoder.check_deadlock(crv::tracer()));
}

