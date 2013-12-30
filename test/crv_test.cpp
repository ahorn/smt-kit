#include "crv.h"

// Include <gtest/gtest.h> _after_ "crv.h"
#include "gtest/gtest.h"

using namespace crv;

template<typename T>
static Internal<T> make_temporary_internal()
{
  static unsigned s_symbol_cnt = 0;
  return Internal<T>(smt::any<typename Smt<T>::Sort>(
    std::to_string(s_symbol_cnt++)));
}

TEST(CrvTest, Event)
{
  tracer().reset();

  EXPECT_TRUE(tracer().events().empty());
  Event e(READ_EVENT, 2, 3, 5, smt::literal<smt::Bool>(true),
    smt::any<smt::Bv<char>>("a"), smt::Bv<size_t>());
  EXPECT_EQ(READ_EVENT, e.kind);
  EXPECT_EQ(2, e.event_id);
  EXPECT_EQ(3, e.thread_id);
  EXPECT_EQ(5, e.address);
  EXPECT_FALSE(e.guard.is_null());
  EXPECT_FALSE(e.term.is_null());
  EXPECT_TRUE(e.offset_term.is_null());
  EXPECT_TRUE(tracer().events().empty());
}

TEST(CrvTest, Tracer)
{
  // counter for event identifiers is static
  tracer().reset();

  Tracer tracer;
  EXPECT_TRUE(tracer.events().empty());

  External<long> external0;
  External<long> external1(external0 + 3);

  // External<T> uses tracer() extern function
  EXPECT_TRUE(tracer.events().empty());

  tracer.append_nondet_write_event(external0);
  EXPECT_EQ(1, tracer.events().size());
  EXPECT_EQ(1, tracer.per_address_map().size());
  EXPECT_EQ(0, tracer.per_address_map().at(external0.address).reads().size());
  EXPECT_EQ(1, tracer.per_address_map().at(external0.address).writes().size());

  tracer.append_read_event(external0);
  EXPECT_EQ(2, tracer.events().size());
  EXPECT_EQ(1, tracer.per_address_map().size());
  EXPECT_EQ(1, tracer.per_address_map().at(external0.address).reads().size());
  EXPECT_EQ(1, tracer.per_address_map().at(external0.address).writes().size());

  tracer.append_write_event(external1);
  EXPECT_EQ(3, tracer.events().size());
  EXPECT_EQ(2, tracer.per_address_map().size());

  EXPECT_EQ(1, tracer.per_address_map().at(external0.address).reads().size());
  EXPECT_EQ(1, tracer.per_address_map().at(external0.address).reads().front()->event_id);

  EXPECT_EQ(1, tracer.per_address_map().at(external0.address).writes().size());
  EXPECT_EQ(0, tracer.per_address_map().at(external0.address).writes().front()->event_id);

  EXPECT_EQ(0, tracer.per_address_map().at(external1.address).reads().size());

  EXPECT_EQ(1, tracer.per_address_map().at(external1.address).writes().size());
  EXPECT_EQ(2, tracer.per_address_map().at(external1.address).writes().front()->event_id);

  const ThreadIdentifier new_thread_id(tracer.append_thread_begin_event());
  EXPECT_EQ(1, new_thread_id);
  EXPECT_EQ(5, tracer.events().size());

  EventList::const_iterator iter = --tracer.events().cend();
  EXPECT_EQ(new_thread_id, iter->thread_id);

  iter--;
  EXPECT_EQ(3, iter->event_id);
  EXPECT_EQ(new_thread_id - 1, iter->thread_id);

  const ThreadIdentifier old_thread_id(tracer.append_thread_end_event());
  EXPECT_EQ(0, old_thread_id);
  EXPECT_EQ(6, tracer.events().size());

  iter = --tracer.events().cend();
  EXPECT_EQ(4, iter->event_id);
  EXPECT_EQ(new_thread_id, iter->thread_id);

  __External<char> external2(static_cast<Address>(42),
    smt::any<typename Smt<size_t>::Sort>("42's_offset"));

  external2.term = tracer.append_load_event(external2);
  EXPECT_EQ(7, tracer.events().size());
  EXPECT_EQ(1, tracer.per_address_map().at(external2.address).loads().size());
  EXPECT_EQ(5, tracer.per_address_map().at(external2.address).loads().front()->event_id);
  EXPECT_EQ(0, tracer.per_address_map().at(external2.address).stores().size());

  tracer.append_store_event(external2);
  EXPECT_EQ(8, tracer.events().size());
  EXPECT_EQ(1, tracer.per_address_map().at(external2.address).loads().size());
  EXPECT_EQ(1, tracer.per_address_map().at(external2.address).stores().size());
  EXPECT_EQ(6, tracer.per_address_map().at(external2.address).stores().front()->event_id);
}

TEST(CrvTest, Flip)
{
  Tracer tracer;
  External<long> v;

  // if (v < 0) { if (v < 1)  { skip } }
  EXPECT_TRUE(tracer.append_guard(v < 0));
  EXPECT_TRUE(tracer.append_guard(v < 1));

  EXPECT_TRUE(tracer.flip());
  EXPECT_TRUE(tracer.append_guard(v < 0));
  EXPECT_FALSE(tracer.append_guard(v < 1));

  EXPECT_TRUE(tracer.flip());
  EXPECT_FALSE(tracer.append_guard(v < 0));

  EXPECT_FALSE(tracer.flip());
  EXPECT_EQ(2, tracer.flip_cnt());

  tracer.reset();

  // if (v < 0) { skip } ; if (v < 1)  { skip }
  EXPECT_TRUE(tracer.append_guard(v < 0));
  EXPECT_TRUE(tracer.append_guard(v < 1));

  EXPECT_TRUE(tracer.flip());
  EXPECT_TRUE(tracer.append_guard(v < 0));
  EXPECT_FALSE(tracer.append_guard(v < 1));

  EXPECT_TRUE(tracer.flip());
  EXPECT_FALSE(tracer.append_guard(v < 0));
  EXPECT_TRUE(tracer.append_guard(v < 1));

  EXPECT_TRUE(tracer.flip());
  EXPECT_FALSE(tracer.append_guard(v < 0));
  EXPECT_FALSE(tracer.append_guard(v < 1));

  EXPECT_FALSE(tracer.flip());
  EXPECT_EQ(3, tracer.flip_cnt());
}

TEST(CrvTest, Value)
{
  tracer().reset();

  EXPECT_EQ(0, tracer().events().size());
  External<int> v0;
  EXPECT_EQ(1, tracer().events().size());
  {
    make_temporary_internal<int>() + make_temporary_internal<long>();
  }
  EXPECT_EQ(1, tracer().events().size());
  {
    External<long> v1 = make_temporary_internal<int>() + make_temporary_internal<long>();
  }
  EXPECT_EQ(2, tracer().events().size());
  {
    make_temporary_internal<long>() + 7;
  }
  EXPECT_EQ(2, tracer().events().size());
  {
    7 + make_temporary_internal<long>();
  }
  EXPECT_EQ(2, tracer().events().size());
  {
    make_temporary_internal<long>() + v0;
  }
  EXPECT_EQ(3, tracer().events().size());
  {
    v0 + make_temporary_internal<long>();
  }
  EXPECT_EQ(4, tracer().events().size());
  {
    v0 + v0;
  }
  EXPECT_EQ(6, tracer().events().size());
  {
    v0 + 7;
  }
  EXPECT_EQ(7, tracer().events().size());
  {
    7 + v0;
  }
  EXPECT_EQ(8, tracer().events().size());
  {
    v0 = v0 + 3;
  }
  EXPECT_EQ(10, tracer().events().size());
  {
    v0 = 5;
  }
  EXPECT_EQ(11, tracer().events().size());
  {
    // assignment operator with another external
    v0 = v0;
  }
  EXPECT_EQ(13, tracer().events().size());
  {
    // copy constructor
    External<int> v1 = v0;
  }
  EXPECT_EQ(15, tracer().events().size());
  {
    External<int> v1 = 1;
  }
  EXPECT_EQ(16, tracer().events().size());
  {
    Internal<bool> c(v0 < 0);
    !std::move(c);
  }
  EXPECT_EQ(17, tracer().events().size());
  {
    Internal<int> internal(2);
    internal = 3;
  }
  EXPECT_EQ(17, tracer().events().size());
  {
    Internal<int> internal(v0);
  }
  EXPECT_EQ(18, tracer().events().size());
  {
    Internal<int> internal(2);
    internal = v0;
  }
  EXPECT_EQ(19, tracer().events().size());
  {
    Internal<int> internal(2);
    internal = internal;
  }
  EXPECT_EQ(19, tracer().events().size());
  {
    Internal<long> internal(2L);
    internal = make_temporary_internal<long>();
  }
  EXPECT_EQ(19, tracer().events().size());
  {
    Internal<long> lhs(2L);
    Internal<int> rhs(7);
    Internal<int> rhs_(rhs);
    lhs + rhs;
    lhs + make_temporary_internal<int>();
    make_temporary_internal<int>() + rhs;
    lhs + 3;
    3L + rhs;
    -lhs;
  }
  EXPECT_EQ(19, tracer().events().size());
  {
    Internal<long> internal(2L);
    v0 + internal;
  }
  EXPECT_EQ(20, tracer().events().size());
  {
    Internal<int> internal(2L);
    internal + v0;
  }
  EXPECT_EQ(21, tracer().events().size());

  EventIdentifier event_id = 0;
  for(const Event& e : tracer().events())
  {
    EXPECT_EQ(event_id++, e.event_id);
  }
}

TEST(CrvTest, SatInsideThread)
{
  tracer().reset();
  Encoder encoder;

  External<int> i = 1;
  i = 2;
  tracer().append_thread_begin_event();
  encoder.add(i == 2);
  tracer().append_thread_end_event();

  encoder.encode(tracer());
  EXPECT_EQ(smt::sat, encoder.solver().check());
}

TEST(CrvTest, UnsatInsideThread)
{
  tracer().reset();
  Encoder encoder;

  External<int> i = 1;
  i = 2;
  tracer().append_thread_begin_event();
  encoder.add(i == 3);
  tracer().append_thread_end_event();

  encoder.encode(tracer());
  EXPECT_EQ(smt::unsat, encoder.solver().check());
}

TEST(CrvTest, Guard)
{
  tracer().reset();
  Encoder encoder;

  External<int> i;
  tracer().append_guard(i < 3);

  EXPECT_EQ(smt::unsat, encoder.check(i == 3, tracer()));
  EXPECT_EQ(smt::sat, encoder.check(i == 2, tracer()));
}

TEST(CrvTest, ThinAir) {
  Encoder encoder;
  tracer().reset();

  External<int> x(3);

  EXPECT_EQ(smt::unsat, encoder.check(x == 42, tracer()));
  EXPECT_EQ(smt::sat, encoder.check(x == 3, tracer()));
  EXPECT_EQ(3, tracer().events().size());
}

TEST(CrvTest, ThinAirWithThread) {
  Encoder encoder;
  tracer().reset();

  External<int> x(3);
  tracer().append_thread_begin_event();
  x = 7;
  tracer().append_thread_end_event();

  EXPECT_EQ(smt::unsat, encoder.check(x == 42, tracer()));
  EXPECT_EQ(smt::sat, encoder.check(x == 7, tracer()));
  EXPECT_EQ(smt::sat, encoder.check(x == 3, tracer()));
  EXPECT_EQ(8, tracer().events().size());
}

TEST(CrvTest, Fib5)
{
  constexpr unsigned N = 5;

  tracer().reset();
  Encoder encoder;
  int k;

  External<int> i = 1, j = 1;
  tracer().append_thread_begin_event();
  for (k = 0; k < N; k++) {
    i = i + j;
  }
  tracer().append_thread_end_event();

  tracer().append_thread_begin_event();
  for (k = 0; k < N; k++) {
    j = j + i;
  }
  tracer().append_thread_end_event();

  EXPECT_EQ(smt::unsat, encoder.check(144 < i || 144 < j, tracer()));
  EXPECT_EQ(smt::sat, encoder.check(
    144 < i || 144 == i || 144 < j || 144 == j, tracer()));
}

TEST(CrvTest, StackApi)
{
  tracer().reset();
  Encoder encoder;

  External<int> v;
  v = 3;
  tracer().append_push_event(v);

  const Internal<int> internal(tracer().append_pop_event(v));
  EXPECT_EQ(smt::unsat, encoder.check(3 != internal, tracer()));
  EXPECT_EQ(smt::sat, encoder.check(3 == internal, tracer()));
}

TEST(CrvTest, StackLifo1)
{
  tracer().reset();
  Encoder encoder;

  External<int> v;
  v = 3;
  tracer().append_push_event(v);
  v = 5;
  tracer().append_push_event(v);

  const Internal<int> internal(tracer().append_pop_event(v));
  EXPECT_EQ(smt::unsat, encoder.check(3 == internal, tracer()));
  EXPECT_EQ(smt::sat, encoder.check(5 == internal, tracer()));
}

TEST(CrvTest, StackLifo2)
{
  tracer().reset();
  Encoder encoder;

  External<int> v;
  v = 3;
  tracer().append_push_event(v);
  v = 5;
  tracer().append_push_event(v);
  tracer().append_pop_event(v);

  const Internal<int> internal(tracer().append_pop_event(v));
  EXPECT_EQ(smt::unsat, encoder.check(3 != internal, tracer()));
  EXPECT_EQ(smt::sat, encoder.check(3 == internal, tracer()));
}

TEST(CrvTest, ThreeThreadsReadWriteExternal)
{
  tracer().reset();
  Encoder encoder;

  // Declare shared variable initialized by the main thread
  External<char> x('\0');

  // Record first child thread
  tracer().append_thread_begin_event();

  x = 'P';

  tracer().append_thread_end_event();

  // Record second child thread
  tracer().append_thread_begin_event();

  x = 'Q';

  tracer().append_thread_end_event();

  Internal<char> a(x);
  EXPECT_EQ(smt::unsat, encoder.check(!(a == '\0' || a == 'P' || a == 'Q'), tracer()));
  EXPECT_EQ(smt::sat, encoder.check(!(a == '\0'), tracer()));
  EXPECT_EQ(smt::sat, encoder.check(!(a == 'P'), tracer()));
  EXPECT_EQ(smt::sat, encoder.check(!(a == 'Q'), tracer()));
  EXPECT_EQ(smt::sat, encoder.check(!(a == 'P' || a == 'Q'), tracer()));
  EXPECT_EQ(smt::sat, encoder.check(!(a == '\0' || a == 'P'), tracer()));
  EXPECT_EQ(smt::sat, encoder.check(!(a == '\0' || a == 'Q'), tracer()));
}

TEST(CrvTest, SingleThreadWithExternal1)
{
  tracer().reset();
  Encoder encoder;

  External<char> x;
  Internal<char> a('\0');

  x = 'A';
  a = x;

  EXPECT_EQ(smt::unsat, encoder.check(a != 'A', tracer()));
  EXPECT_EQ(smt::sat, encoder.check(a == 'A', tracer()));
}

TEST(CrvTest, SingleThreadWithExternal2)
{
  tracer().reset();
  Encoder encoder;

  External<char> x;
  Internal<char> a('\0');

  x = 'A';
  x = 'B';
  a = x;

  EXPECT_EQ(smt::unsat, encoder.check(a == 'A', tracer()));
  EXPECT_EQ(smt::sat, encoder.check(a == 'B', tracer()));
}

TEST(CrvTest, CopyInternaltoInternal)
{
  tracer().reset();
  Encoder encoder;

  Internal<char> a = 'A';
  Internal<char> b = a;

  EXPECT_EQ(smt::unsat, encoder.check(!(b == 'A'), tracer()));
  EXPECT_EQ(smt::unsat, encoder.check(!(b == a), tracer()));

  a = 'B';
  EXPECT_EQ(smt::sat, encoder.check(!(b == a), tracer()));
}

TEST(CrvTest, CopyExternaltoInternal)
{
  tracer().reset();
  Encoder encoder;

  External<char> a = 'A';
  Internal<char> b = a;

  EXPECT_EQ(smt::unsat, encoder.check(!(b == 'A'), tracer()));
  EXPECT_EQ(smt::sat, encoder.check(b == 'A', tracer()));

  a = 'B';
  EXPECT_EQ(smt::unsat, encoder.check(!(b == 'A'), tracer()));
  EXPECT_EQ(smt::sat, encoder.check(b == 'A', tracer()));
}

TEST(CrvTest, Array)
{
  tracer().reset();

  EXPECT_TRUE(tracer().events().empty());

  External<char[]> xs;
  EXPECT_EQ(1, tracer().events().size());

  External<char[5]> ys;
  EXPECT_EQ(2, tracer().events().size());

  Internal<size_t> i(3);
  EXPECT_EQ(2, tracer().events().size());

  External<size_t> j(4);
  EXPECT_EQ(3, tracer().events().size());

  xs[2];
  EXPECT_EQ(3, tracer().events().size());

  xs[i];
  EXPECT_EQ(3, tracer().events().size());

  External<char> x0(xs[2]);
  EXPECT_EQ(5, tracer().events().size());
  EXPECT_NE(xs.address, x0.address);
  EXPECT_EQ(0, tracer().per_address_map().at(x0.address).reads().size());
  EXPECT_EQ(1, tracer().per_address_map().at(x0.address).writes().size());
  EXPECT_EQ(1, tracer().per_address_map().at(xs.address).loads().size());
  EXPECT_EQ(0, tracer().per_address_map().at(xs.address).stores().size());
  EXPECT_FALSE(x0.term.is_null());
  EXPECT_TRUE(x0.offset_term.is_null());

  x0 = xs[i];
  EXPECT_EQ(7, tracer().events().size());
  EXPECT_NE(xs.address, x0.address);
  EXPECT_EQ(0, tracer().per_address_map().at(x0.address).reads().size());
  EXPECT_EQ(2, tracer().per_address_map().at(x0.address).writes().size());
  EXPECT_EQ(2, tracer().per_address_map().at(xs.address).loads().size());
  EXPECT_EQ(0, tracer().per_address_map().at(xs.address).stores().size());
  EXPECT_FALSE(x0.term.is_null());
  EXPECT_TRUE(x0.offset_term.is_null());

  External<char> x1(xs[j]);
  EXPECT_EQ(10, tracer().events().size());
  EXPECT_NE(xs.address, x1.address);
  EXPECT_NE(x0.address, x1.address);
  EXPECT_EQ(1, tracer().per_address_map().at(j.address).reads().size());
  EXPECT_EQ(0, tracer().per_address_map().at(x0.address).reads().size());
  EXPECT_EQ(2, tracer().per_address_map().at(x0.address).writes().size());
  EXPECT_EQ(0, tracer().per_address_map().at(x1.address).reads().size());
  EXPECT_EQ(1, tracer().per_address_map().at(x1.address).writes().size());
  EXPECT_EQ(3, tracer().per_address_map().at(xs.address).loads().size());
  EXPECT_EQ(0, tracer().per_address_map().at(xs.address).stores().size());
  EXPECT_FALSE(x1.term.is_null());
  EXPECT_TRUE(x1.offset_term.is_null());

  xs[j];
  EXPECT_EQ(11, tracer().events().size());

  x1 = xs[j];
  EXPECT_EQ(14, tracer().events().size());
  EXPECT_NE(xs.address, x1.address);
  EXPECT_NE(x0.address, x1.address);
  EXPECT_EQ(3, tracer().per_address_map().at(j.address).reads().size());
  EXPECT_EQ(0, tracer().per_address_map().at(x0.address).reads().size());
  EXPECT_EQ(2, tracer().per_address_map().at(x0.address).writes().size());
  EXPECT_EQ(0, tracer().per_address_map().at(x1.address).reads().size());
  EXPECT_EQ(2, tracer().per_address_map().at(x1.address).writes().size());
  EXPECT_EQ(4, tracer().per_address_map().at(xs.address).loads().size());
  EXPECT_EQ(0, tracer().per_address_map().at(xs.address).stores().size());
  EXPECT_FALSE(x1.term.is_null());
  EXPECT_TRUE(x1.offset_term.is_null());

  xs[make_temporary_internal<size_t>()];
  EXPECT_EQ(14, tracer().events().size());

  External<char> x2(xs[make_temporary_internal<size_t>()]);
  EXPECT_NE(xs.address, x2.address);
  EXPECT_NE(x1.address, x2.address);
  EXPECT_NE(x0.address, x2.address);
  EXPECT_EQ(16, tracer().events().size());
  EXPECT_EQ(3, tracer().per_address_map().at(j.address).reads().size());
  EXPECT_EQ(0, tracer().per_address_map().at(x0.address).reads().size());
  EXPECT_EQ(2, tracer().per_address_map().at(x0.address).writes().size());
  EXPECT_EQ(0, tracer().per_address_map().at(x1.address).reads().size());
  EXPECT_EQ(2, tracer().per_address_map().at(x1.address).writes().size());
  EXPECT_EQ(0, tracer().per_address_map().at(x2.address).reads().size());
  EXPECT_EQ(1, tracer().per_address_map().at(x2.address).writes().size());
  EXPECT_EQ(5, tracer().per_address_map().at(xs.address).loads().size());
  EXPECT_EQ(0, tracer().per_address_map().at(xs.address).stores().size());
  EXPECT_FALSE(x2.term.is_null());
  EXPECT_TRUE(x2.offset_term.is_null());

  x2 = xs[make_temporary_internal<size_t>()];
  EXPECT_NE(xs.address, x2.address);
  EXPECT_NE(x1.address, x2.address);
  EXPECT_NE(x0.address, x2.address);
  EXPECT_EQ(18, tracer().events().size());
  EXPECT_EQ(3, tracer().per_address_map().at(j.address).reads().size());
  EXPECT_EQ(0, tracer().per_address_map().at(x0.address).reads().size());
  EXPECT_EQ(2, tracer().per_address_map().at(x0.address).writes().size());
  EXPECT_EQ(0, tracer().per_address_map().at(x1.address).reads().size());
  EXPECT_EQ(2, tracer().per_address_map().at(x1.address).writes().size());
  EXPECT_EQ(0, tracer().per_address_map().at(x2.address).reads().size());
  EXPECT_EQ(2, tracer().per_address_map().at(x2.address).writes().size());
  EXPECT_EQ(6, tracer().per_address_map().at(xs.address).loads().size());
  EXPECT_EQ(0, tracer().per_address_map().at(xs.address).stores().size());
  EXPECT_FALSE(x2.term.is_null());
  EXPECT_TRUE(x2.offset_term.is_null());

  /*
   * Calls the following:
   *
   * - External(size_t)                   +1
   * - Internal<size_t>(External<size_t>) +1
   * - [](Internal<size_t>)
   * - External(offset, address)
   *
   * Thus, there are two new events (= 20 total).
   */
  xs[External<size_t>(3)];
  EXPECT_EQ(20, tracer().events().size());

  /*
   * Calls the following:
   *
   * - External(size_t)                   +1
   * - Internal<size_t>(External<size_t>) +1
   * - [](Internal<size_t>)
   * - External(offset, address)
   * - External<char>(External<char>)     +2
   *
   * Thus, there are four new events (= 24 total).
   */
  External<char> x3(xs[External<size_t>(4)]);
  EXPECT_NE(x2.address, x3.address);
  EXPECT_NE(x1.address, x3.address);
  EXPECT_NE(x0.address, x3.address);
  EXPECT_NE(xs.address, x3.address);
  EXPECT_EQ(24, tracer().events().size());
  EXPECT_EQ(3, tracer().per_address_map().at(j.address).reads().size());
  EXPECT_EQ(2, tracer().per_address_map().at(x0.address).writes().size());
  EXPECT_EQ(2, tracer().per_address_map().at(x1.address).writes().size());
  EXPECT_EQ(2, tracer().per_address_map().at(x2.address).writes().size());
  EXPECT_EQ(1, tracer().per_address_map().at(x3.address).writes().size());
  EXPECT_EQ(7, tracer().per_address_map().at(xs.address).loads().size());
  EXPECT_EQ(0, tracer().per_address_map().at(xs.address).stores().size());
  EXPECT_FALSE(x3.term.is_null());
  EXPECT_TRUE(x3.offset_term.is_null());

  x3 = xs[External<size_t>(4)];
  EXPECT_NE(xs.address, x3.address);
  EXPECT_NE(x2.address, x3.address);
  EXPECT_NE(x1.address, x3.address);
  EXPECT_NE(x0.address, x3.address);
  EXPECT_EQ(28, tracer().events().size());
  EXPECT_EQ(3, tracer().per_address_map().at(j.address).reads().size());
  EXPECT_EQ(2, tracer().per_address_map().at(x0.address).writes().size());
  EXPECT_EQ(2, tracer().per_address_map().at(x1.address).writes().size());
  EXPECT_EQ(2, tracer().per_address_map().at(x2.address).writes().size());
  EXPECT_EQ(2, tracer().per_address_map().at(x3.address).writes().size());
  EXPECT_EQ(8, tracer().per_address_map().at(xs.address).loads().size());
  EXPECT_EQ(0, tracer().per_address_map().at(xs.address).stores().size());
  EXPECT_FALSE(x3.term.is_null());
  EXPECT_TRUE(x3.offset_term.is_null());

  xs[i] = 'A';
  EXPECT_EQ(29, tracer().events().size());
  EXPECT_EQ(3, tracer().per_address_map().at(j.address).reads().size());
  EXPECT_EQ(2, tracer().per_address_map().at(x0.address).writes().size());
  EXPECT_EQ(2, tracer().per_address_map().at(x1.address).writes().size());
  EXPECT_EQ(2, tracer().per_address_map().at(x2.address).writes().size());
  EXPECT_EQ(2, tracer().per_address_map().at(x3.address).writes().size());
  EXPECT_EQ(8, tracer().per_address_map().at(xs.address).loads().size());
  EXPECT_EQ(1, tracer().per_address_map().at(xs.address).stores().size());

  Internal<char> p('A');
  xs[i] = p;
  EXPECT_EQ(30, tracer().events().size());
  EXPECT_EQ(3, tracer().per_address_map().at(j.address).reads().size());
  EXPECT_EQ(2, tracer().per_address_map().at(x0.address).writes().size());
  EXPECT_EQ(2, tracer().per_address_map().at(x1.address).writes().size());
  EXPECT_EQ(2, tracer().per_address_map().at(x2.address).writes().size());
  EXPECT_EQ(2, tracer().per_address_map().at(x3.address).writes().size());
  EXPECT_EQ(8, tracer().per_address_map().at(xs.address).loads().size());
  EXPECT_EQ(2, tracer().per_address_map().at(xs.address).stores().size());

  xs[i] = make_temporary_internal<char>();
  EXPECT_EQ(31, tracer().events().size());
  EXPECT_EQ(3, tracer().per_address_map().at(j.address).reads().size());
  EXPECT_EQ(2, tracer().per_address_map().at(x0.address).writes().size());
  EXPECT_EQ(2, tracer().per_address_map().at(x1.address).writes().size());
  EXPECT_EQ(2, tracer().per_address_map().at(x2.address).writes().size());
  EXPECT_EQ(2, tracer().per_address_map().at(x3.address).writes().size());
  EXPECT_EQ(8, tracer().per_address_map().at(xs.address).loads().size());
  EXPECT_EQ(3, tracer().per_address_map().at(xs.address).stores().size());

  External<char> q('B');
  EXPECT_EQ(32, tracer().events().size());
  EXPECT_EQ(3, tracer().per_address_map().at(j.address).reads().size());
  EXPECT_EQ(2, tracer().per_address_map().at(x0.address).writes().size());
  EXPECT_EQ(2, tracer().per_address_map().at(x1.address).writes().size());
  EXPECT_EQ(2, tracer().per_address_map().at(x2.address).writes().size());
  EXPECT_EQ(2, tracer().per_address_map().at(x3.address).writes().size());
  EXPECT_EQ(0, tracer().per_address_map().at(q.address).reads().size());
  EXPECT_EQ(1, tracer().per_address_map().at(q.address).writes().size());
  EXPECT_EQ(8, tracer().per_address_map().at(xs.address).loads().size());
  EXPECT_EQ(3, tracer().per_address_map().at(xs.address).stores().size());

  xs[i] = q;
  EXPECT_EQ(34, tracer().events().size());
  EXPECT_EQ(3, tracer().per_address_map().at(j.address).reads().size());
  EXPECT_EQ(2, tracer().per_address_map().at(x0.address).writes().size());
  EXPECT_EQ(2, tracer().per_address_map().at(x1.address).writes().size());
  EXPECT_EQ(2, tracer().per_address_map().at(x2.address).writes().size());
  EXPECT_EQ(2, tracer().per_address_map().at(x3.address).writes().size());
  EXPECT_EQ(1, tracer().per_address_map().at(q.address).reads().size());
  EXPECT_EQ(1, tracer().per_address_map().at(q.address).writes().size());
  EXPECT_EQ(8, tracer().per_address_map().at(xs.address).loads().size());
  EXPECT_EQ(4, tracer().per_address_map().at(xs.address).stores().size());
}

TEST(CrvTest, ExternalArrayWithLiteralOffset) {
  tracer().reset();
  Encoder encoder;

  External<char[5]> x;

  x[2] = 'Z';
  Internal<char> a(x[2]);
  EXPECT_EQ(smt::unsat, encoder.check(a != 'Z', tracer()));
  EXPECT_EQ(smt::sat, encoder.check(a == 'Z', tracer()));

  // initial array elements are zero
  Internal<char> b(x[3]);
  Internal<char> c(x[4]);
  EXPECT_EQ(smt::unsat, encoder.check(b != '\0', tracer()));
  EXPECT_EQ(smt::sat, encoder.check(b == '\0', tracer()));
  EXPECT_EQ(smt::unsat, encoder.check(c != '\0', tracer()));
  EXPECT_EQ(smt::sat, encoder.check(c == '\0', tracer()));
}

TEST(CrvTest, ExternalArrayWithExternalOffset)
{
  tracer().reset();
  Encoder encoder;

  External<char[3]> xs;
  External<size_t> index(1);
  Internal<char> a('\0');

  xs[index] = 'Y';
 
  index = index + static_cast<size_t>(1);
  xs[index] = 'Z';

  a = xs[0];
  EXPECT_EQ(smt::unsat, encoder.check(a == 'Z', tracer()));
  EXPECT_EQ(smt::sat, encoder.check(a != 'Z', tracer()));

  a = xs[1];
  EXPECT_EQ(smt::unsat, encoder.check(a == 'Z', tracer()));
  EXPECT_EQ(smt::sat, encoder.check(a != 'Z', tracer()));

  a = xs[2];
  EXPECT_EQ(smt::unsat, encoder.check(a != 'Z', tracer()));
  EXPECT_EQ(smt::sat, encoder.check(a == 'Z', tracer()));

  a = xs[index];
  EXPECT_EQ(smt::unsat, encoder.check(a != 'Z', tracer()));
  EXPECT_EQ(smt::sat, encoder.check(a == 'Z', tracer()));

  // Out of bound array access does not cause an error.
  index = index + static_cast<size_t>(1);
  a = xs[index];
  EXPECT_EQ(smt::unsat, encoder.check(a == 'Z', tracer()));
  EXPECT_EQ(smt::sat, encoder.check(a != 'Z', tracer()));
}

TEST(CrvTest, MultipleExternalArrayStoresWithLiteralOffset)
{
  tracer().reset();
  Encoder encoder;

  External<char[3]> xs;
  Internal<char> a('\0');

  xs[0] = 'A';
  xs[1] = 'B';

  a = xs[1];

  EXPECT_EQ(smt::unsat, encoder.check(a != 'B', tracer()));
  EXPECT_EQ(smt::sat, encoder.check(a == 'B', tracer()));
}

TEST(CrvTest, MultipleExternalArrayStoresWithExternalOffset)
{
  tracer().reset();
  Encoder encoder;

  External<char[3]> xs;
  External<size_t> index;
  Internal<char> a('\0');

  index = 0;
  xs[index] = 'A';

  index = index + static_cast<size_t>(1);
  xs[index] = 'B';

  a = xs[index];

  EXPECT_EQ(smt::unsat, encoder.check(a != 'B', tracer()));
  EXPECT_EQ(smt::sat, encoder.check(a == 'B', tracer()));
}

