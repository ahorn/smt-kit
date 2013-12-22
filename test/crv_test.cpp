#include "crv.h"

// Include <gtest/gtest.h> _after_ "crv.h"
#include "gtest/gtest.h"

using namespace crv;

template<typename T>
static Rvalue<T> make_temporary_rvalue()
{
  static unsigned s_symbol_cnt = 0;
  return Rvalue<T>(smt::any<typename Smt<T>::Sort>(
    std::to_string(s_symbol_cnt++)));
}

TEST(CrvTest, Event)
{
  tracer().reset();

  EXPECT_TRUE(tracer().events().empty());
  Event e(READ_EVENT, 2, 3, 5, smt::any<smt::Bv<char>>("a"),
    smt::literal<smt::Bool>(true));
  EXPECT_EQ(READ_EVENT, e.kind);
  EXPECT_EQ(2, e.event_id);
  EXPECT_EQ(3, e.thread_id);
  EXPECT_EQ(5, e.address);
  EXPECT_FALSE(e.term.is_null());
  EXPECT_FALSE(e.guard.is_null());
  EXPECT_TRUE(tracer().events().empty());
}

TEST(CrvTest, Tracer)
{
  // counter for event identifiers is static
  tracer().reset();

  Tracer tracer;
  EXPECT_TRUE(tracer.events().empty());

  Lvalue<long> lvalue0;
  Lvalue<long> lvalue1(lvalue0 + 3);

  // Lvalue<T> uses tracer() extern function
  EXPECT_TRUE(tracer.events().empty());

  tracer.append_nondet_write_event(lvalue0);
  EXPECT_EQ(1, tracer.events().size());
  EXPECT_EQ(1, tracer.per_address_map().size());
  EXPECT_EQ(0, tracer.per_address_map().at(lvalue0.address).reads.size());
  EXPECT_EQ(1, tracer.per_address_map().at(lvalue0.address).writes.size());

  tracer.append_read_event(lvalue0);
  EXPECT_EQ(2, tracer.events().size());
  EXPECT_EQ(1, tracer.per_address_map().size());
  EXPECT_EQ(1, tracer.per_address_map().at(lvalue0.address).reads.size());
  EXPECT_EQ(1, tracer.per_address_map().at(lvalue0.address).writes.size());

  tracer.append_write_event(lvalue1);
  EXPECT_EQ(3, tracer.events().size());
  EXPECT_EQ(2, tracer.per_address_map().size());

  EXPECT_EQ(1, tracer.per_address_map().at(lvalue0.address).reads.size());
  EXPECT_EQ(1, tracer.per_address_map().at(lvalue0.address).reads.front()->event_id);

  EXPECT_EQ(1, tracer.per_address_map().at(lvalue0.address).writes.size());
  EXPECT_EQ(0, tracer.per_address_map().at(lvalue0.address).writes.front()->event_id);

  EXPECT_EQ(0, tracer.per_address_map().at(lvalue1.address).reads.size());

  EXPECT_EQ(1, tracer.per_address_map().at(lvalue1.address).writes.size());
  EXPECT_EQ(2, tracer.per_address_map().at(lvalue1.address).writes.front()->event_id);

  const ThreadIdentifier new_thread_id(tracer.append_thread_begin_event());
  EXPECT_EQ(1, new_thread_id);
  EXPECT_EQ(5, tracer.events().size());

  EventList::const_iterator iter = --tracer.events().cend();
  const EventIdentifier event_id(iter->event_id);
  EXPECT_EQ(new_thread_id, iter->thread_id);

  iter--;
  EXPECT_EQ(event_id, iter->event_id);
  EXPECT_EQ(new_thread_id - 1, iter->thread_id);

  const ThreadIdentifier old_thread_id(tracer.append_thread_end_event());
  EXPECT_EQ(0, old_thread_id);
  EXPECT_EQ(6, tracer.events().size());

  iter = --tracer.events().cend();
  EXPECT_EQ(event_id + 1, iter->event_id);
  EXPECT_EQ(new_thread_id, iter->thread_id);
}

TEST(CrvTest, Flip)
{
  Tracer tracer;
  Lvalue<long> v;

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
  Lvalue<int> v0;
  EXPECT_EQ(1, tracer().events().size());
  {
    make_temporary_rvalue<int>() + make_temporary_rvalue<long>();
  }
  EXPECT_EQ(1, tracer().events().size());
  {
    Lvalue<long> v1 = make_temporary_rvalue<int>() + make_temporary_rvalue<long>();
  }
  EXPECT_EQ(2, tracer().events().size());
  {
    make_temporary_rvalue<long>() + 7;
  }
  EXPECT_EQ(2, tracer().events().size());
  {
    7 + make_temporary_rvalue<long>();
  }
  EXPECT_EQ(2, tracer().events().size());
  {
    make_temporary_rvalue<long>() + v0;
  }
  EXPECT_EQ(3, tracer().events().size());
  {
    v0 + make_temporary_rvalue<long>();
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
    // assignment operator with another lvalue
    v0 = v0;
  }
  EXPECT_EQ(13, tracer().events().size());
  {
    // copy constructor
    Lvalue<int> v1 = v0;
  }
  EXPECT_EQ(15, tracer().events().size());
  {
    Lvalue<int> v1 = 1;
  }
  EXPECT_EQ(16, tracer().events().size());
  {
    Rvalue<bool> c(v0 < 0);
    !std::move(c);
  }
  EXPECT_EQ(17, tracer().events().size());

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

  Lvalue<int> i = 1;
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

  Lvalue<int> i = 1;
  i = 2;
  tracer().append_thread_begin_event();
  encoder.add(i == 3);
  tracer().append_thread_end_event();

  encoder.encode(tracer());
  EXPECT_EQ(smt::unsat, encoder.solver().check());
}

TEST(CrvTest, SatGuard)
{
  tracer().reset();
  Encoder encoder;

  Lvalue<int> i;
  tracer().append_guard(i < 3);
  encoder.add(i == 2);

  encoder.encode(tracer());
  EXPECT_EQ(smt::sat, encoder.solver().check());
}

TEST(CrvTest, UnsatGuard)
{
  tracer().reset();
  Encoder encoder;

  Lvalue<int> i;
  tracer().append_guard(i < 3);
  encoder.add(i == 3);

  encoder.encode(tracer());
  EXPECT_EQ(smt::unsat, encoder.solver().check());
}

TEST(CrvTest, ThinAir) {
  Encoder encoder;
  tracer().reset();

  Lvalue<int> x(3);

  encoder.add(x == 42);
  encoder.encode(tracer());

  EXPECT_EQ(2, tracer().events().size());
  EXPECT_EQ(smt::unsat, encoder.solver().check());
}

TEST(CrvTest, ThinAirWithThread) {
  Encoder encoder;
  tracer().reset();

  Lvalue<int> x(3);
  tracer().append_thread_begin_event();
  x = 7;
  tracer().append_thread_end_event();

  encoder.add(x == 42);
  encoder.encode(tracer());

  EXPECT_EQ(6, tracer().events().size());
  EXPECT_EQ(smt::unsat, encoder.solver().check());
}

TEST(CrvTest, SatFib5)
{
  constexpr unsigned N = 5;

  tracer().reset();
  Encoder encoder;
  int k;

  Lvalue<int> i = 1, j = 1;
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
  encoder.add(144 < i || 144 == i || 144 < j || 144 == j);

  encoder.encode(tracer());
  EXPECT_EQ(smt::sat, encoder.solver().check());
}

TEST(CrvTest, UnsatFib5)
{
  constexpr unsigned N = 5;

  tracer().reset();
  Encoder encoder;
  int k;

  Lvalue<int> i = 1, j = 1;
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
  encoder.add(144 < i || 144 < j);

  encoder.encode(tracer());
  EXPECT_EQ(smt::unsat, encoder.solver().check());
}

TEST(CrvTest, SatStackApi)
{
  tracer().reset();
  Encoder encoder;

  Lvalue<int> v;
  v = 3;
  tracer().append_push_event(v);
  encoder.add(3 == tracer().append_pop_event(v));

  encoder.encode(tracer());
  EXPECT_EQ(smt::sat, encoder.solver().check());
}

TEST(CrvTest, UnsatStackApi)
{
  tracer().reset();
  Encoder encoder;

  Lvalue<int> v;
  v = 3;
  tracer().append_push_event(v);
  encoder.add(3 != tracer().append_pop_event(v));

  encoder.encode(tracer());
  EXPECT_EQ(smt::unsat, encoder.solver().check());
}

TEST(CrvTest, SatStackLifo1)
{
  tracer().reset();
  Encoder encoder;

  Lvalue<int> v;
  v = 3;
  tracer().append_push_event(v);
  v = 5;
  tracer().append_push_event(v);
  encoder.add(5 == tracer().append_pop_event(v));

  encoder.encode(tracer());
  EXPECT_EQ(smt::sat, encoder.solver().check());
}

TEST(CrvTest, UnsatStackLifo1)
{
  tracer().reset();
  Encoder encoder;

  Lvalue<int> v;
  v = 3;
  tracer().append_push_event(v);
  v = 5;
  tracer().append_push_event(v);
  encoder.add(3 == tracer().append_pop_event(v));

  encoder.encode(tracer());
  EXPECT_EQ(smt::unsat, encoder.solver().check());
}

TEST(CrvTest, SatStackLifo2)
{
  tracer().reset();
  Encoder encoder;

  Lvalue<int> v;
  v = 3;
  tracer().append_push_event(v);
  v = 5;
  tracer().append_push_event(v);
  tracer().append_pop_event(v);
  encoder.add(3 == tracer().append_pop_event(v));

  encoder.encode(tracer());
  EXPECT_EQ(smt::sat, encoder.solver().check());
}

TEST(CrvTest, UnsatStackLifo2)
{
  tracer().reset();
  Encoder encoder;

  Lvalue<int> v;
  v = 3;
  tracer().append_push_event(v);
  v = 5;
  tracer().append_push_event(v);
  tracer().append_pop_event(v);
  encoder.add(3 != tracer().append_pop_event(v));

  encoder.encode(tracer());
  EXPECT_EQ(smt::unsat, encoder.solver().check());
}

