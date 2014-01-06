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

  const ThreadIdentifier parent_thread_id(tracer.append_thread_begin_event());
  EXPECT_EQ(1, parent_thread_id);
  EXPECT_EQ(5, tracer.events().size());

  EventList::const_iterator iter = --tracer.events().cend();
  EXPECT_EQ(parent_thread_id + 1, iter->thread_id);

  iter--;
  EXPECT_EQ(3, iter->event_id);
  EXPECT_EQ(parent_thread_id, iter->thread_id);

  const ThreadIdentifier child_thread_id(tracer.append_thread_end_event());
  EXPECT_EQ(2, child_thread_id);
  EXPECT_EQ(6, tracer.events().size());

  iter = --tracer.events().cend();
  EXPECT_EQ(4, iter->event_id);
  EXPECT_EQ(child_thread_id, iter->thread_id);

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
  tracer().add_error(i == 2);
  tracer().append_thread_end_event();

  EXPECT_TRUE(tracer().assertions().empty());
  EXPECT_EQ(smt::sat, encoder.check(tracer()));
}

TEST(CrvTest, UnsatInsideThread)
{
  tracer().reset();
  Encoder encoder;

  External<int> i = 1;
  i = 2;
  tracer().append_thread_begin_event();
  tracer().add_error(i == 3);
  tracer().append_thread_end_event();

  EXPECT_TRUE(tracer().assertions().empty());
  EXPECT_EQ(smt::unsat, encoder.check(tracer()));
}

TEST(CrvTest, Assertions)
{
  tracer().reset();
  Encoder encoder;

  // satisfy precondition of Encoder::check(const Tracer&)
  tracer().add_error(true);

  EXPECT_TRUE(tracer().assertions().empty());
  External<int> i = 1;
  tracer().add_assertion(i == 1);
  EXPECT_FALSE(tracer().assertions().empty());
  EXPECT_EQ(smt::sat, encoder.check(tracer()));
  tracer().add_assertion(i == 3);
  EXPECT_FALSE(tracer().assertions().empty());

  // conjunction
  EXPECT_EQ(smt::unsat, encoder.check(tracer()));

  // idempotent
  EXPECT_FALSE(tracer().assertions().empty());
}

TEST(CrvTest, Errors)
{
  tracer().reset();
  Encoder encoder;

  EXPECT_TRUE(tracer().errors().empty());
  External<int> i = 1;
  tracer().add_error(i == 1);
  EXPECT_FALSE(tracer().errors().empty());
  EXPECT_EQ(smt::sat, encoder.check(tracer()));
  tracer().add_error(i == 3);
  EXPECT_FALSE(tracer().errors().empty());

  // disjunction
  EXPECT_EQ(smt::sat, encoder.check(tracer()));

  // idempotent
  EXPECT_FALSE(tracer().errors().empty());
}

TEST(CrvTest, Guard)
{
  tracer().reset();
  Encoder encoder;

  External<int> i;

  EXPECT_TRUE(tracer().append_guard(i < 3));

  EXPECT_EQ(smt::unsat, encoder.check(i == 3, tracer()));
  EXPECT_EQ(smt::sat, encoder.check(i == 2, tracer()));

  tracer().reset();

  EXPECT_EQ(smt::sat, encoder.check(true, tracer()));

  tracer().reset();
  EXPECT_EQ(smt::unsat, encoder.check(false, tracer()));

  tracer().reset();
  EXPECT_TRUE(tracer().append_guard(false));
  EXPECT_EQ(smt::unsat, encoder.check(true, tracer()));

  EXPECT_TRUE(tracer().flip());
  EXPECT_FALSE(tracer().append_guard(false));
  EXPECT_EQ(smt::sat, encoder.check(true, tracer()));

  tracer().reset();
  EXPECT_TRUE(tracer().append_guard(true));
  EXPECT_EQ(smt::sat, encoder.check(true, tracer()));

  EXPECT_TRUE(tracer().flip());
  EXPECT_FALSE(tracer().append_guard(true));
  EXPECT_EQ(smt::unsat, encoder.check(true, tracer()));

  tracer().reset();
  EXPECT_FALSE(tracer().append_guard(false, false));
  EXPECT_TRUE(tracer().append_guard(true, true));
  tracer().add_error(true);
  EXPECT_EQ(smt::sat, encoder.check(tracer()));

  tracer().reset();
  EXPECT_FALSE(tracer().append_guard(true, false));
  tracer().add_error(true);
  EXPECT_EQ(smt::unsat, encoder.check(tracer()));

  External<bool> false_bool;
  External<bool> true_bool;

  // Do not call reset_address(); otherwise,
  // we get that false_bool == true_bool.
  tracer().reset_events();
  tracer().reset_guard();
  tracer().reset_flips();
  false_bool = false;
  true_bool = true;
  EXPECT_EQ(smt::unsat, encoder.check(false_bool, tracer()));

  tracer().reset_events();
  tracer().reset_guard();
  tracer().reset_flips();
  false_bool = false;
  true_bool = true;
  EXPECT_TRUE(tracer().append_guard(false_bool));
  EXPECT_EQ(smt::unsat, encoder.check(true_bool, tracer()));

  EXPECT_TRUE(tracer().flip());
  false_bool = false;
  true_bool = true;
  EXPECT_FALSE(tracer().append_guard(false_bool));
  EXPECT_EQ(smt::sat, encoder.check(true_bool, tracer()));

  tracer().reset_events();
  tracer().reset_guard();
  tracer().reset_flips();
  false_bool = false;
  true_bool = true;
  EXPECT_TRUE(tracer().append_guard(true_bool));
  EXPECT_EQ(smt::sat, encoder.check(true_bool, tracer()));

  EXPECT_TRUE(tracer().flip());
  false_bool = false;
  true_bool = true;
  EXPECT_FALSE(tracer().append_guard(true_bool));
  EXPECT_EQ(smt::unsat, encoder.check(true_bool, tracer()));

  tracer().reset_events();
  tracer().reset_guard();
  tracer().reset_flips();
  false_bool = false;
  true_bool = true;
  EXPECT_TRUE(tracer().append_guard(false_bool));
  EXPECT_TRUE(tracer().append_guard(true_bool));
  EXPECT_EQ(smt::unsat, encoder.check(true_bool, tracer()));

  EXPECT_TRUE(tracer().flip());
  false_bool = false;
  true_bool = true;
  EXPECT_TRUE(tracer().append_guard(false_bool));
  EXPECT_FALSE(tracer().append_guard(true_bool));
  EXPECT_EQ(smt::unsat, encoder.check(true_bool, tracer()));

  EXPECT_TRUE(tracer().flip());
  false_bool = false;
  true_bool = true;
  EXPECT_FALSE(tracer().append_guard(false_bool));
  EXPECT_TRUE(tracer().append_guard(true_bool));
  EXPECT_EQ(smt::sat, encoder.check(true_bool, tracer()));

  tracer().reset_events();
  tracer().reset_guard();
  tracer().reset_flips();
  false_bool = false;
  true_bool = true;
  EXPECT_TRUE(tracer().append_guard(false_bool));
  tracer().add_error(true);
  EXPECT_TRUE(tracer().append_guard(true_bool));
  tracer().add_error(true);
  EXPECT_EQ(smt::unsat, encoder.check(tracer()));

  EXPECT_TRUE(tracer().flip());
  false_bool = false;
  true_bool = true;
  EXPECT_TRUE(tracer().append_guard(false_bool));
  tracer().add_error(true);
  EXPECT_FALSE(tracer().append_guard(true_bool));
  EXPECT_EQ(smt::unsat, encoder.check(tracer()));

  EXPECT_TRUE(tracer().flip());
  false_bool = false;
  true_bool = true;
  EXPECT_FALSE(tracer().append_guard(false_bool));
  EXPECT_TRUE(tracer().append_guard(true_bool));
  tracer().add_error(true);
  EXPECT_EQ(smt::sat, encoder.check(tracer()));
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

TEST(CrvTest, JoinThreads)
{
  tracer().reset();
  Encoder encoder;

  External<char> x('\0');

  const ThreadIdentifier parent_thread_id(tracer().append_thread_begin_event());
  EXPECT_EQ(1, parent_thread_id);
  EXPECT_EQ(parent_thread_id + 1, tracer().current_thread_id());

  x = 'A';

  const ThreadIdentifier child_thread_id(tracer().append_thread_end_event());
  EXPECT_EQ(2, child_thread_id);
  EXPECT_EQ(parent_thread_id, tracer().current_thread_id());

  EXPECT_EQ(smt::sat, encoder.check(x == '\0', tracer()));
  EXPECT_EQ(smt::sat, encoder.check(x == 'A', tracer()));

  tracer().append_join_event(child_thread_id);

  EXPECT_EQ(smt::unsat, encoder.check(x == '\0', tracer()));
  EXPECT_EQ(smt::sat, encoder.check(x == 'A', tracer()));
}

void array_t0(External<char[]>& array)
{
  array[0] = 'X';
}

void array_t1(External<char[]>& array)
{
  array[0] = 'Y';
}

TEST(CrvTest, ArrayWithJoinThreads)
{
  tracer().reset();
  Encoder encoder;

  External<char[]> array;

  Thread t1(array_t0, array);
  Thread t2(array_t1, array);
  t1.join();
  t2.join();
 
  EXPECT_TRUE(tracer().assertions().empty());
  EXPECT_TRUE(tracer().errors().empty());
  EXPECT_EQ(smt::unsat, encoder.check(array[0] != 'X' && array[0] != 'Y', tracer()));
  EXPECT_EQ(smt::sat, encoder.check(array[0] != 'X', tracer()));
  EXPECT_EQ(smt::sat, encoder.check(array[0] != 'Y', tracer()));
  EXPECT_EQ(smt::sat, encoder.check(array[0] == 'X', tracer()));
  EXPECT_EQ(smt::sat, encoder.check(array[0] == 'Y', tracer()));
  EXPECT_FALSE(tracer().flip());
}

void array_index(
  External<unsigned[]>& array,
  const External<size_t>& index)
{
  array[index] = 1;
}

TEST(CrvTest, ArrayIndex)
{
  tracer().reset();
  Encoder encoder;

  External<unsigned[]> array;
  External<size_t> index(0);

  Thread t1(array_index, array, index);
  index = index + 1;

  Thread t2(array_index, array, index);
  index = index + 1;

  Thread t3(array_index, array, index);

  t1.join();
  t2.join();
  t3.join();

  Internal<unsigned> sum(array[0] + array[1] + array[2]);
 
  EXPECT_TRUE(tracer().assertions().empty());
  EXPECT_TRUE(tracer().errors().empty());
  EXPECT_EQ(smt::unsat, encoder.check(sum == 4, tracer()));
  EXPECT_EQ(smt::sat, encoder.check(sum == 3, tracer()));
  EXPECT_EQ(smt::sat, encoder.check(sum != 3, tracer()));
  EXPECT_FALSE(tracer().flip());
}

TEST(CrvTest, SatFlipWithNondeterminsticGuardInSingleThread)
{
  tracer().reset();
  Encoder encoder;

  bool r0 = false;
  bool r1 = false;
  bool r2 = false;
  bool r3 = false;
  bool r4 = false;

  do
  {
    External<bool> nondet_bool;
    External<char> x;
    Internal<char> a('\0');

    x = 'A';
    if (tracer().append_guard(nondet_bool))
      x = 'B';
    else
      x = 'C';
    a = x;

    r0 |= smt::sat == encoder.check(a == 'B', tracer());
    r1 |= smt::sat == encoder.check(a != 'C', tracer());
    r2 |= smt::sat == encoder.check(a == 'B' && a != 'C', tracer());
    r3 |= smt::sat == encoder.check(a == 'C', tracer());
    r4 |= smt::sat == encoder.check(a != 'B' && a == 'C', tracer());
  }
  while (tracer().flip());

  EXPECT_EQ(1, tracer().flip_cnt());
  EXPECT_TRUE(r0);
  EXPECT_TRUE(r1);
  EXPECT_TRUE(r2);
  EXPECT_TRUE(r3);
  EXPECT_TRUE(r4);
}

TEST(CrvTest, SatFlipWithNondeterminsticGuardAndArrayInSingleThread)
{
  tracer().reset();
  Encoder encoder;

  bool r0 = false;
  bool r1 = false;
  bool r2 = false;
  bool r3 = false;
  bool r4 = false;

  do
  {
    External<bool> nondet_bool;
    External<char[3]> xs;
    Internal<char> a('\0');
  
    xs[2] = 'A';
    if (tracer().append_guard(nondet_bool))
      xs[2] = 'B';
    else
      xs[2] = 'C';
    a = xs[2];
  
    r0 |= smt::sat == encoder.check(a == 'B', tracer());
    r1 |= smt::sat == encoder.check(a != 'C', tracer());
    r2 |= smt::sat == encoder.check(a == 'B' && a != 'C', tracer());
    r3 |= smt::sat == encoder.check(a == 'C', tracer());
    r4 |= smt::sat == encoder.check(a != 'B' && a == 'C', tracer());
  }
  while (tracer().flip());

  EXPECT_EQ(1, tracer().flip_cnt());
  EXPECT_TRUE(r0);
  EXPECT_TRUE(r1);
  EXPECT_TRUE(r2);
  EXPECT_TRUE(r3);
  EXPECT_TRUE(r4);
}

TEST(CrvTest, SatFlipWithDeterminsticGuardAndArrayInSingleThread)
{
  tracer().reset();
  Encoder encoder;

  bool r0 = false;
  bool r1 = false;
  bool r2 = true;

  do
  {
    External<char[3]> x;
    Internal<char> p('\0');
    Internal<char> a('\0');
  
    p = '?';
    x[2] = 'A';
    if (tracer().append_guard(p == '?'))
      x[2] = 'B';
    else
      x[2] = 'C'; // unreachable
    a = x[2];
  

    r0 |= smt::sat == encoder.check(a == 'B', tracer());
    r1 |= smt::sat == encoder.check(a != 'C', tracer());
    r1 &= smt::unsat == encoder.check(a == 'C', tracer());
  }
  while (tracer().flip());

  EXPECT_EQ(1, tracer().flip_cnt());
  EXPECT_TRUE(r0);
  EXPECT_TRUE(r1);
  EXPECT_TRUE(r2);
}

TEST(CrvTest, UnsatFlipInSingleThread)
{
  tracer().reset();
  Encoder encoder;

  unsigned checks = 0;
  unsigned unchecks = 0;

  do
  {
    External<int> var;

    if (tracer().append_guard(0 < var))
      tracer().add_error(var == 0);

    if (!tracer().errors().empty())
    {
      checks++;
      EXPECT_EQ(smt::unsat, encoder.check(tracer()));
    }
    else
    {
      unchecks++;
    }
  }
  while (tracer().flip());

  EXPECT_EQ(1, tracer().flip_cnt());
  EXPECT_EQ(1, checks);
  EXPECT_EQ(1, unchecks);
}

TEST(CrvTest, UnsatFlipInMultipleThread)
{
  tracer().reset();
  Encoder encoder;

  unsigned checks = 0;
  unsigned unchecks = 0;

  do
  {
    External<int> var;

    tracer().append_thread_begin_event();
    if (tracer().append_guard(0 < var))
      tracer().add_error(var == 0);
    tracer().append_thread_end_event();

    if (!tracer().errors().empty())
    {
      checks++;
      EXPECT_EQ(smt::unsat, encoder.check(tracer()));
    }
    else
    {
      unchecks++;
    }
  }
  while (tracer().flip());

  EXPECT_EQ(1, tracer().flip_cnt());
  EXPECT_EQ(1, checks);
  EXPECT_EQ(1, unchecks);
}

TEST(CrvTest, UnsatFlipErrorConditionDueToFalseGuard)
{
  tracer().reset();
  Encoder encoder;

  unsigned checks = 0;
  unsigned unchecks = 0;

  do
  {
    External<bool> false_bool(false);
    if (tracer().append_guard(false_bool))
      tracer().add_error(true);

    if (!tracer().errors().empty())
    {
      checks++;
      EXPECT_EQ(smt::unsat, encoder.check(tracer()));
    }
    else
    {
      unchecks++;
    }
  }
  while (tracer().flip());

  EXPECT_EQ(1, tracer().flip_cnt());
  EXPECT_EQ(1, checks);
  EXPECT_EQ(1, unchecks);
}

TEST(CrvTest, FlipFour)
{
  tracer().reset();
  Encoder encoder;

  unsigned sat_checks = 0;
  unsigned unsat_checks = 0;
  unsigned unknown_checks = 0;
  unsigned unchecks = 0;

  smt::CheckResult expect;
  do
  {
    expect = smt::unknown;

    External<bool> false_bool(false);
    External<bool> true_bool(true);

    if (tracer().append_guard(false_bool))
    {
      expect = smt::unsat;
      tracer().add_error(true_bool);
    }

    if (tracer().append_guard(true_bool))
    {
      if (expect == smt::unknown)
        expect = smt::sat;
      tracer().add_error(true_bool);
    }

    if (!tracer().errors().empty())
    {
      switch (expect)
      {
      case smt::sat:     sat_checks++;     break;
      case smt::unsat:   unsat_checks++;   break;
      case smt::unknown: unknown_checks++; break;
      }
      EXPECT_EQ(expect, encoder.check(tracer()));
    }
    else
    {
      unchecks++;
    }
  }
  while (tracer().flip());

  EXPECT_EQ(3, tracer().flip_cnt());
  EXPECT_EQ(1, sat_checks);
  EXPECT_EQ(2, unsat_checks);
  EXPECT_EQ(0, unknown_checks);
  EXPECT_EQ(1, unchecks);
}

void thread_api_test(unsigned* ptr, unsigned i)
{
  EXPECT_EQ(2, ThisThread::thread_id());
  *ptr = i;
}

TEST(CrvTest, ThreadApi)
{
  tracer().reset();
  unsigned n = 0;

  EXPECT_EQ(1, ThisThread::thread_id());
  Thread t(thread_api_test, &n, 7);
  EXPECT_TRUE(t.joinable());
  EXPECT_EQ(7, n);
  EXPECT_EQ(1, ThisThread::thread_id());
  t.join();
  EXPECT_FALSE(t.joinable());
  EXPECT_EQ(1, ThisThread::thread_id());
}

TEST(CrvTest, MutexSatSingleWriter1)
{
  tracer().reset();
  Encoder encoder;

  External<int> shared_var(0);

  tracer().append_thread_begin_event();
  shared_var = 3;
  shared_var = shared_var + 1;
  tracer().append_thread_end_event();

  tracer().append_thread_begin_event();
  tracer().add_error(shared_var == 3);
  tracer().append_thread_end_event();

  EXPECT_TRUE(tracer().assertions().empty());
  EXPECT_FALSE(tracer().errors().empty());
  EXPECT_EQ(smt::sat, encoder.check(tracer()));
}

TEST(CrvTest, MutexUnsatSingleWriter1)
{
  tracer().reset();
  Encoder encoder;

  External<int> shared_var(0);
  Mutex mutex;

  tracer().append_thread_begin_event();
  mutex.lock();
  shared_var = 3;
  shared_var = shared_var + 1;
  mutex.unlock();
  tracer().append_thread_end_event();

  tracer().append_thread_begin_event();
  mutex.lock();
  tracer().add_error(shared_var == 3);
  mutex.unlock();
  tracer().append_thread_end_event();

  EXPECT_FALSE(tracer().assertions().empty());
  EXPECT_FALSE(tracer().errors().empty());
  EXPECT_EQ(smt::unsat, encoder.check(tracer()));
}

TEST(CrvTest, MutexSatSingleWriter2)
{
  tracer().reset();
  Encoder encoder;

  External<int> shared_var(0);

  tracer().append_thread_begin_event();
  shared_var = shared_var + 3;
  shared_var = shared_var + 1;
  tracer().append_thread_end_event();

  tracer().append_thread_begin_event();
  tracer().add_error(shared_var == 3);
  tracer().append_thread_end_event();

  EXPECT_TRUE(tracer().assertions().empty());
  EXPECT_FALSE(tracer().errors().empty());
  EXPECT_EQ(smt::sat, encoder.check(tracer()));
}

TEST(CrvTest, MutexUnsatSingleWriter2)
{
  tracer().reset();
  Encoder encoder;

  External<int> shared_var(0);
  Mutex mutex;

  tracer().append_thread_begin_event();
  mutex.lock();
  shared_var = shared_var + 3;
  shared_var = shared_var + 1;
  mutex.unlock();
  tracer().append_thread_end_event();

  tracer().append_thread_begin_event();
  mutex.lock();
  tracer().add_error(shared_var == 3);
  mutex.unlock();
  tracer().append_thread_end_event();

  EXPECT_FALSE(tracer().assertions().empty());
  EXPECT_FALSE(tracer().errors().empty());
  EXPECT_EQ(smt::unsat, encoder.check(tracer()));
}

TEST(CrvTest, MutexSatMultipleWriters1)
{
  tracer().reset();
  Encoder encoder;

  External<char> x('\0');
  External<char> y('\0');
  External<char> z('\0');

  Internal<char> a('X');
  Internal<char> b('Y');
  Internal<char> c('Z');

  Mutex mutex;

  tracer().append_thread_begin_event();
  x = 'A';
  y = 'B';
  z = 'C';
  tracer().append_thread_end_event();

  tracer().append_thread_begin_event();
  x = '\1';
  y = '\2';
  z = '\3';
  tracer().append_thread_end_event();

  a = x;
  b = y;
  c = z;

  EXPECT_EQ(smt::sat, encoder.check(a == 'A' && b == '\2' && c == 'C', tracer()));
  EXPECT_EQ(smt::sat, encoder.check(a == '\1' && b == 'B' && c == '\3', tracer()));
}

TEST(CrvTest, MutexSatMultipleWriters2)
{
  tracer().reset();
  Encoder encoder;

  External<char> x('\0');
  External<char> y('\0');
  External<char> z('\0');

  Internal<char> a('X');
  Internal<char> b('Y');
  Internal<char> c('Z');

  Mutex mutex;

  tracer().append_thread_begin_event();
  mutex.lock();
  x = 'A';
  y = 'B';
  z = 'C';
  mutex.unlock();
  tracer().append_thread_end_event();

  tracer().append_thread_begin_event();
  mutex.lock();
  x = '\1';
  y = '\2';
  z = '\3';
  mutex.unlock();
  tracer().append_thread_end_event();

  // since the main thread does not protect its reads,
  // by the mutex, it sees the non-atomic updates!
  a = x;
  b = y;
  c = z;

  EXPECT_EQ(smt::sat, encoder.check(a == 'A' && b == '\2' && c == 'C', tracer()));
  EXPECT_EQ(smt::sat, encoder.check(a == '\1' && b == 'B' && c == '\3', tracer()));
}

TEST(CrvTest, MutexUnsatMultipleWriters)
{
  tracer().reset();
  Encoder encoder;

  External<char> x('\0');
  External<char> y('\0');
  External<char> z('\0');

  Internal<char> a('X');
  Internal<char> b('Y');
  Internal<char> c('Z');

  Mutex mutex;

  tracer().append_thread_begin_event();
  mutex.lock();
  x = 'A';
  y = 'B';
  z = 'C';
  mutex.unlock();
  tracer().append_thread_end_event();

  tracer().append_thread_begin_event();
  mutex.lock();
  x = '\1';
  y = '\2';
  z = '\3';
  mutex.unlock();
  tracer().append_thread_end_event();

  mutex.lock();
  a = x;
  mutex.unlock();

  mutex.lock();
  b = y;
  mutex.unlock();

  mutex.lock();
  c = z;
  mutex.unlock();

  EXPECT_EQ(smt::unsat, encoder.check(a == 'A' && b == '\2' && c == 'C', tracer()));
  EXPECT_EQ(smt::unsat, encoder.check(a == '\1' && b == 'B' && c == '\3', tracer()));
}

TEST(CrvTest, MutexJoinMultipleWriters)
{
  tracer().reset();
  Encoder encoder;

  External<int> x(10);
  External<int> y(10);
  Mutex mutex;

  tracer().append_thread_begin_event();
  mutex.lock();
  x = x + 1;
  mutex.unlock();

  mutex.lock();
  y = y + 1;
  mutex.unlock();
  const ThreadIdentifier child_thread_id_1(
    tracer().append_thread_end_event());

  tracer().append_thread_begin_event();
  mutex.lock();
  x = x + 5;
  mutex.unlock();

  mutex.lock();
  y = y - 6;
  mutex.unlock();
  const ThreadIdentifier child_thread_id_2(
    tracer().append_thread_end_event());

  tracer().append_join_event(child_thread_id_1);
  tracer().append_join_event(child_thread_id_2);

  EXPECT_EQ(smt::sat, encoder.check(x == 16 && y == 5, tracer()));
  EXPECT_EQ(smt::unsat, encoder.check(!(x == 16 && y == 5), tracer()));
}

