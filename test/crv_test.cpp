#include "crv.h"

// Include <gtest/gtest.h> _after_ "crv.h"
#include "gtest/gtest.h"

using namespace crv;

TEST(CrvTest, EvalLnot)
{
  EXPECT_FALSE(internal::Eval<smt::LNOT>::eval(1));
  EXPECT_FALSE(internal::Eval<smt::LNOT>::eval(12));
  EXPECT_TRUE(internal::Eval<smt::LNOT>::eval(0));
  EXPECT_TRUE(internal::Eval<smt::LNOT>::eval(false));
}

TEST(CrvTest, EvalAdd)
{
  EXPECT_EQ(18, internal::Eval<smt::ADD>::eval(10, 8));
  EXPECT_EQ(18, internal::Eval<smt::ADD>::eval(8, 10));
}

TEST(CrvTest, EvalLand)
{
  EXPECT_TRUE(internal::Eval<smt::LAND>::eval(true, true));
  EXPECT_FALSE(internal::Eval<smt::LAND>::eval(false, true));
  EXPECT_FALSE(internal::Eval<smt::LAND>::eval(true, false));
  EXPECT_FALSE(internal::Eval<smt::LAND>::eval(false, false));
}

TEST(CrvTest, EvalLor)
{
  EXPECT_TRUE(internal::Eval<smt::LOR>::eval(true, true));
  EXPECT_TRUE(internal::Eval<smt::LOR>::eval(false, true));
  EXPECT_TRUE(internal::Eval<smt::LOR>::eval(true, false));
  EXPECT_FALSE(internal::Eval<smt::LOR>::eval(false, false));
}

TEST(CrvTest, EvalEql)
{
  EXPECT_TRUE(internal::Eval<smt::EQL>::eval(12, 0xc));
  EXPECT_TRUE(internal::Eval<smt::EQL>::eval(0xc, 12));
  EXPECT_FALSE(internal::Eval<smt::EQL>::eval(12, 13));
}

TEST(CrvTest, EvalLss)
{
  EXPECT_FALSE(internal::Eval<smt::LSS>::eval(12, 0xc));
  EXPECT_FALSE(internal::Eval<smt::LSS>::eval(0xc, 12));
  EXPECT_TRUE(internal::Eval<smt::LSS>::eval(12, 13));
  EXPECT_FALSE(internal::Eval<smt::LSS>::eval(13, 12));
}

#if __cplusplus <= 201103L
#define STATIC_EXPECT_TRUE(assertion) EXPECT_TRUE((assertion))
#define STATIC_EXPECT_FALSE(assertion) EXPECT_FALSE((assertion))
#else
#define STATIC_EXPECT_TRUE(assertion) static_assert((assertion), "")
#define STATIC_EXPECT_FALSE(assertion) static_assert(!(assertion), "")
#endif

TEST(CrvTest, ConstexprEvalLnot)
{
  STATIC_EXPECT_FALSE(internal::Eval<smt::LNOT>::const_eval(true));
  STATIC_EXPECT_TRUE(internal::Eval<smt::LNOT>::const_eval(false));

  STATIC_EXPECT_FALSE(internal::Eval<smt::LNOT>::const_eval(1));
  STATIC_EXPECT_FALSE(internal::Eval<smt::LNOT>::const_eval(12));
  STATIC_EXPECT_TRUE(internal::Eval<smt::LNOT>::const_eval(0));
}

TEST(CrvTest, ConstexprEvalAdd)
{
  STATIC_EXPECT_TRUE(18 == internal::Eval<smt::ADD>::const_eval(10, 8));
  STATIC_EXPECT_TRUE(18 == internal::Eval<smt::ADD>::const_eval(8, 10));
}

TEST(CrvTest, ConstexprEvalLand)
{
  STATIC_EXPECT_TRUE(internal::Eval<smt::LAND>::const_eval(true, true));
  STATIC_EXPECT_FALSE(internal::Eval<smt::LAND>::const_eval(false, true));
  STATIC_EXPECT_FALSE(internal::Eval<smt::LAND>::const_eval(true, false));
  STATIC_EXPECT_FALSE(internal::Eval<smt::LAND>::const_eval(false, false));
}

TEST(CrvTest, ConstexprEvalLor)
{
  STATIC_EXPECT_TRUE(internal::Eval<smt::LOR>::const_eval(true, true));
  STATIC_EXPECT_TRUE(internal::Eval<smt::LOR>::const_eval(false, true));
  STATIC_EXPECT_TRUE(internal::Eval<smt::LOR>::const_eval(true, false));
  STATIC_EXPECT_FALSE(internal::Eval<smt::LOR>::const_eval(false, false));
}

TEST(CrvTest, ConstexprEvalEql)
{
  STATIC_EXPECT_TRUE(internal::Eval<smt::EQL>::const_eval(12, 0xc));
  STATIC_EXPECT_TRUE(internal::Eval<smt::EQL>::const_eval(0xc, 12));
  STATIC_EXPECT_FALSE(internal::Eval<smt::EQL>::const_eval(12, 13));
}

TEST(CrvTest, ConstexprEvalLss)
{
  STATIC_EXPECT_FALSE(internal::Eval<smt::LSS>::const_eval(12, 0xc));
  STATIC_EXPECT_FALSE(internal::Eval<smt::LSS>::const_eval(0xc, 12));
  STATIC_EXPECT_TRUE(internal::Eval<smt::LSS>::const_eval(12, 13));
  STATIC_EXPECT_FALSE(internal::Eval<smt::LSS>::const_eval(13, 12));
}

TEST(CrvTest, ReturnType)
{
  STATIC_EXPECT_TRUE((std::is_same<unsigned long, typename internal::Return<smt::ADD,
    unsigned int, unsigned long>::Type>::value));

  STATIC_EXPECT_TRUE((std::is_same<bool, typename internal::Return<smt::LSS,
    int, int>::Type>::value));

  STATIC_EXPECT_TRUE((std::is_same<bool, typename internal::Return<smt::LNOT,
    unsigned int>::Type>::value));
}

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
  Event e(READ_EVENT, 2, 3, 4, 5, 6, smt::literal<smt::Bool>(true),
    smt::any<smt::Bv<char>>("a"), smt::Bv<size_t>());
  EXPECT_EQ(READ_EVENT, e.kind);
  EXPECT_EQ(2, e.event_id);
  EXPECT_EQ(3, e.thread_id);
  EXPECT_EQ(4, e.block_id);
  EXPECT_EQ(5, e.scope_level);
  EXPECT_EQ(6, e.address);
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
  EXPECT_EQ(1, tracer.per_address_index().size());
  EXPECT_EQ(0, tracer.per_address_index().at(external0.address).reads().size());
  EXPECT_EQ(1, tracer.per_address_index().at(external0.address).writes().size());

  tracer.append_read_event(external0);
  EXPECT_EQ(2, tracer.events().size());
  EXPECT_EQ(1, tracer.per_address_index().size());
  EXPECT_EQ(1, tracer.per_address_index().at(external0.address).reads().size());
  EXPECT_EQ(1, tracer.per_address_index().at(external0.address).writes().size());

  tracer.append_write_event(external1);
  EXPECT_EQ(3, tracer.events().size());
  EXPECT_EQ(2, tracer.per_address_index().size());

  EXPECT_EQ(1, tracer.per_address_index().at(external0.address).reads().size());
  EXPECT_EQ(1, tracer.per_address_index().at(external0.address).reads().front()->event_id);

  EXPECT_EQ(1, tracer.per_address_index().at(external0.address).writes().size());
  EXPECT_EQ(0, tracer.per_address_index().at(external0.address).writes().front()->event_id);

  EXPECT_EQ(0, tracer.per_address_index().at(external1.address).reads().size());

  EXPECT_EQ(1, tracer.per_address_index().at(external1.address).writes().size());
  EXPECT_EQ(2, tracer.per_address_index().at(external1.address).writes().front()->event_id);

  const ThreadIdentifier parent_thread_id(tracer.append_thread_begin_event());
  EXPECT_EQ(1, parent_thread_id);
  EXPECT_EQ(5, tracer.events().size());

  EventIter iter = std::prev(tracer.events().cend());
  EXPECT_EQ(parent_thread_id + 1, iter->thread_id);

  iter--;
  EXPECT_EQ(3, iter->event_id);
  EXPECT_EQ(parent_thread_id, iter->thread_id);

  const ThreadIdentifier child_thread_id(tracer.append_thread_end_event());
  EXPECT_EQ(2, child_thread_id);
  EXPECT_EQ(6, tracer.events().size());

  iter = std::prev(tracer.events().cend());
  EXPECT_EQ(4, iter->event_id);
  EXPECT_EQ(child_thread_id, iter->thread_id);

  __External<char> external2(static_cast<Address>(42),
    smt::any<typename Smt<size_t>::Sort>("42's_offset"));

  external2.term = tracer.append_load_event(external2);
  EXPECT_EQ(7, tracer.events().size());
  EXPECT_EQ(1, tracer.per_address_index().at(external2.address).loads().size());
  EXPECT_EQ(5, tracer.per_address_index().at(external2.address).loads().front()->event_id);
  EXPECT_EQ(0, tracer.per_address_index().at(external2.address).stores().size());

  tracer.append_store_event(external2);
  EXPECT_EQ(8, tracer.events().size());
  EXPECT_EQ(1, tracer.per_address_index().at(external2.address).loads().size());
  EXPECT_EQ(1, tracer.per_address_index().at(external2.address).stores().size());
  EXPECT_EQ(6, tracer.per_address_index().at(external2.address).stores().front()->event_id);
}

TEST(CrvTest, Barrier)
{
  Tracer tracer;

  tracer.append_thread_begin_event();
  tracer.barrier();
  tracer.barrier();
  const ThreadIdentifier tid0(tracer.append_thread_end_event());

  tracer.append_thread_begin_event();
  tracer.barrier();
  tracer.barrier();
  tracer.barrier();
  const ThreadIdentifier tid1(tracer.append_thread_end_event());

  tracer.append_thread_begin_event();
  tracer.barrier();
  tracer.barrier();
  tracer.barrier();
  tracer.barrier();
  const ThreadIdentifier tid2(tracer.append_thread_end_event());

  EXPECT_EQ(4, tracer.per_thread_map().at(tid0).size());
  for (unsigned i = 1; i <= 2; i++)
  {
    EXPECT_EQ(i, tracer.per_thread_map().at(tid0).at(i)->event_id);
    EXPECT_TRUE(tracer.per_thread_map().at(tid0).at(i)->is_barrier());
  }

  EXPECT_EQ(5, tracer.per_thread_map().at(tid1).size());
  for (unsigned i = 1; i <= 2; i++)
  {
    EXPECT_EQ(i, tracer.per_thread_map().at(tid1).at(i)->event_id);
    EXPECT_TRUE(tracer.per_thread_map().at(tid1).at(i)->is_barrier());
  }
  EXPECT_EQ(5, tracer.per_thread_map().at(tid1).at(3)->event_id);
  EXPECT_TRUE(tracer.per_thread_map().at(tid1).at(3)->is_barrier());

  EXPECT_EQ(6, tracer.per_thread_map().at(tid2).size());
  for (unsigned i = 1; i <= 2; i++)
  {
    EXPECT_EQ(i, tracer.per_thread_map().at(tid2).at(i)->event_id);
    EXPECT_TRUE(tracer.per_thread_map().at(tid2).at(i)->is_barrier());
  }
  EXPECT_EQ(5, tracer.per_thread_map().at(tid2).at(3)->event_id);
  EXPECT_TRUE(tracer.per_thread_map().at(tid2).at(3)->is_barrier());
  EXPECT_EQ(8, tracer.per_thread_map().at(tid2).at(4)->event_id);
  EXPECT_TRUE(tracer.per_thread_map().at(tid2).at(4)->is_barrier());
}

TEST(CrvTest, Flip)
{
  Tracer tracer;
  External<long> v;

  // if (v < 0) { if (v < 1)  { skip } }
  EXPECT_TRUE(tracer.decide_flip(v < 0));
  EXPECT_TRUE(tracer.decide_flip(v < 1));

  EXPECT_TRUE(tracer.flip());
  EXPECT_TRUE(tracer.decide_flip(v < 0));
  EXPECT_FALSE(tracer.decide_flip(v < 1));

  EXPECT_TRUE(tracer.flip());
  EXPECT_FALSE(tracer.decide_flip(v < 0));

  EXPECT_FALSE(tracer.flip());
  EXPECT_EQ(2, tracer.flip_cnt());

  tracer.reset();

  // if (v < 0) { skip } ; if (v < 1)  { skip }
  EXPECT_TRUE(tracer.decide_flip(v < 0));
  EXPECT_TRUE(tracer.decide_flip(v < 1));

  EXPECT_TRUE(tracer.flip());
  EXPECT_TRUE(tracer.decide_flip(v < 0));
  EXPECT_FALSE(tracer.decide_flip(v < 1));

  EXPECT_TRUE(tracer.flip());
  EXPECT_FALSE(tracer.decide_flip(v < 0));
  EXPECT_TRUE(tracer.decide_flip(v < 1));

  EXPECT_TRUE(tracer.flip());
  EXPECT_FALSE(tracer.decide_flip(v < 0));
  EXPECT_FALSE(tracer.decide_flip(v < 1));

  EXPECT_FALSE(tracer.flip());
  EXPECT_EQ(3, tracer.flip_cnt());

  tracer.reset();

  EXPECT_TRUE(tracer.decide_flip(v < 0));
  tracer.append_thread_begin_event();
  EXPECT_EQ(2, tracer.current_thread_id());
  tracer.append_thread_end_event();

  EXPECT_TRUE(tracer.flip());

  // thread identifiers are reset
  tracer.append_thread_begin_event();
  EXPECT_EQ(2, tracer.current_thread_id());
  tracer.append_thread_end_event();
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

  EXPECT_TRUE(tracer().decide_flip(i < 3));

  EXPECT_EQ(smt::unsat, encoder.check(i == 3, tracer()));
  EXPECT_EQ(smt::sat, encoder.check(i == 2, tracer()));

  tracer().reset();

  EXPECT_EQ(smt::sat, encoder.check(true, tracer()));

  tracer().reset();
  EXPECT_EQ(smt::unsat, encoder.check(false, tracer()));

  tracer().reset();
  EXPECT_TRUE(tracer().decide_flip(false));
  EXPECT_EQ(smt::unsat, encoder.check(true, tracer()));

  EXPECT_TRUE(tracer().flip());
  EXPECT_FALSE(tracer().decide_flip(false));
  EXPECT_EQ(smt::sat, encoder.check(true, tracer()));

  tracer().reset();
  EXPECT_TRUE(tracer().decide_flip(true));
  EXPECT_EQ(smt::sat, encoder.check(true, tracer()));

  EXPECT_TRUE(tracer().flip());
  EXPECT_FALSE(tracer().decide_flip(true));
  EXPECT_EQ(smt::unsat, encoder.check(true, tracer()));

  tracer().reset();
  EXPECT_FALSE(tracer().decide_flip(false, false));
  EXPECT_TRUE(tracer().decide_flip(true, true));
  tracer().add_error(true);
  EXPECT_EQ(smt::sat, encoder.check(tracer()));

  tracer().reset();
  EXPECT_FALSE(tracer().decide_flip(true, false));
  tracer().add_error(true);
  EXPECT_EQ(smt::unsat, encoder.check(tracer()));

  External<bool> false_bool;
  External<bool> true_bool;

  // Do not call reset_address(); otherwise,
  // we get that false_bool == true_bool.
  tracer().reset_events();
  tracer().reset_flips();
  false_bool = false;
  true_bool = true;
  EXPECT_EQ(smt::unsat, encoder.check(false_bool, tracer()));

  tracer().reset_events();
  tracer().reset_flips();
  false_bool = false;
  true_bool = true;
  EXPECT_TRUE(tracer().decide_flip(false_bool));
  EXPECT_EQ(smt::unsat, encoder.check(true_bool, tracer()));

  EXPECT_TRUE(tracer().flip());
  false_bool = false;
  true_bool = true;
  EXPECT_FALSE(tracer().decide_flip(false_bool));
  EXPECT_EQ(smt::sat, encoder.check(true_bool, tracer()));

  tracer().reset_events();
  tracer().reset_flips();
  false_bool = false;
  true_bool = true;
  EXPECT_TRUE(tracer().decide_flip(true_bool));
  EXPECT_EQ(smt::sat, encoder.check(true_bool, tracer()));

  EXPECT_TRUE(tracer().flip());
  false_bool = false;
  true_bool = true;
  EXPECT_FALSE(tracer().decide_flip(true_bool));
  EXPECT_EQ(smt::unsat, encoder.check(true_bool, tracer()));

  tracer().reset_events();
  tracer().reset_flips();
  false_bool = false;
  true_bool = true;
  EXPECT_TRUE(tracer().decide_flip(false_bool));
  EXPECT_TRUE(tracer().decide_flip(true_bool));
  EXPECT_EQ(smt::unsat, encoder.check(true_bool, tracer()));

  EXPECT_TRUE(tracer().flip());
  false_bool = false;
  true_bool = true;
  EXPECT_TRUE(tracer().decide_flip(false_bool));
  EXPECT_FALSE(tracer().decide_flip(true_bool));
  EXPECT_EQ(smt::unsat, encoder.check(true_bool, tracer()));

  EXPECT_TRUE(tracer().flip());
  false_bool = false;
  true_bool = true;
  EXPECT_FALSE(tracer().decide_flip(false_bool));
  EXPECT_TRUE(tracer().decide_flip(true_bool));
  EXPECT_EQ(smt::sat, encoder.check(true_bool, tracer()));

  tracer().reset_events();
  tracer().reset_flips();
  false_bool = false;
  true_bool = true;
  EXPECT_TRUE(tracer().decide_flip(false_bool));
  tracer().add_error(true);
  EXPECT_TRUE(tracer().decide_flip(true_bool));
  tracer().add_error(true);
  EXPECT_EQ(smt::unsat, encoder.check(tracer()));

  EXPECT_TRUE(tracer().flip());
  false_bool = false;
  true_bool = true;
  EXPECT_TRUE(tracer().decide_flip(false_bool));
  tracer().add_error(true);
  EXPECT_FALSE(tracer().decide_flip(true_bool));
  EXPECT_EQ(smt::unsat, encoder.check(tracer()));

  EXPECT_TRUE(tracer().flip());
  false_bool = false;
  true_bool = true;
  EXPECT_FALSE(tracer().decide_flip(false_bool));
  EXPECT_TRUE(tracer().decide_flip(true_bool));
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

TEST(CrvTest, Stack)
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

TEST(CrvTest, StackApi)
{
  tracer().reset();
  Encoder encoder;

  Stack<int> stack;
  External<int> external(5);
  Internal<int> internal(7);

  stack.push(3);
  stack.push(external);
  stack.push(internal);

  internal = stack.pop();
  EXPECT_EQ(smt::unsat, encoder.check(7 != internal, tracer()));
  EXPECT_EQ(smt::sat, encoder.check(7 == internal, tracer()));

  internal = stack.pop();
  EXPECT_EQ(smt::unsat, encoder.check(5 != internal, tracer()));
  EXPECT_EQ(smt::sat, encoder.check(5 == internal, tracer()));

  internal = stack.pop();
  EXPECT_EQ(smt::unsat, encoder.check(3 != internal, tracer()));
  EXPECT_EQ(smt::sat, encoder.check(3 == internal, tracer()));
}

TEST(CrvTest, StackApiWithSingleThread)
{
  tracer().reset();
  Encoder encoder;

  Stack<int> stack;

  tracer().append_thread_begin_event();
  stack.push(5);
  stack.push(7);
  tracer().append_thread_end_event();

  Internal<int> p0(stack.pop());
  EXPECT_EQ(smt::sat, encoder.check(5 == p0, tracer()));
  EXPECT_EQ(smt::sat, encoder.check(7 == p0, tracer()));

  Internal<int> p1(stack.pop());

  EXPECT_EQ(smt::sat, encoder.check(5 == p0, tracer()));
  EXPECT_EQ(smt::sat, encoder.check(7 == p0, tracer()));
  EXPECT_EQ(smt::sat, encoder.check(5 == p1, tracer()));
  EXPECT_EQ(smt::sat, encoder.check(7 == p1, tracer()));
  EXPECT_EQ(smt::sat, encoder.check(7 == p0 && 5 == p1, tracer()));
  EXPECT_EQ(smt::sat, encoder.check(5 == p0 && 7 == p1, tracer()));

  EXPECT_EQ(smt::unsat, encoder.check(!(5 != p0 || 7 == p1), tracer()));
  EXPECT_EQ(smt::sat, encoder.check(5 != p0 || 7 == p1, tracer()));

  EXPECT_EQ(smt::unsat, encoder.check(!(7 != p0 || 5 == p1), tracer()));
  EXPECT_EQ(smt::sat, encoder.check(7 != p0 || 5 == p1, tracer()));
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
  EXPECT_EQ(0, tracer().per_address_index().at(x0.address).reads().size());
  EXPECT_EQ(1, tracer().per_address_index().at(x0.address).writes().size());
  EXPECT_EQ(1, tracer().per_address_index().at(xs.address).loads().size());
  EXPECT_EQ(0, tracer().per_address_index().at(xs.address).stores().size());
  EXPECT_FALSE(x0.term.is_null());
  EXPECT_TRUE(x0.offset_term.is_null());

  x0 = xs[i];
  EXPECT_EQ(7, tracer().events().size());
  EXPECT_NE(xs.address, x0.address);
  EXPECT_EQ(0, tracer().per_address_index().at(x0.address).reads().size());
  EXPECT_EQ(2, tracer().per_address_index().at(x0.address).writes().size());
  EXPECT_EQ(2, tracer().per_address_index().at(xs.address).loads().size());
  EXPECT_EQ(0, tracer().per_address_index().at(xs.address).stores().size());
  EXPECT_FALSE(x0.term.is_null());
  EXPECT_TRUE(x0.offset_term.is_null());

  External<char> x1(xs[j]);
  EXPECT_EQ(10, tracer().events().size());
  EXPECT_NE(xs.address, x1.address);
  EXPECT_NE(x0.address, x1.address);
  EXPECT_EQ(1, tracer().per_address_index().at(j.address).reads().size());
  EXPECT_EQ(0, tracer().per_address_index().at(x0.address).reads().size());
  EXPECT_EQ(2, tracer().per_address_index().at(x0.address).writes().size());
  EXPECT_EQ(0, tracer().per_address_index().at(x1.address).reads().size());
  EXPECT_EQ(1, tracer().per_address_index().at(x1.address).writes().size());
  EXPECT_EQ(3, tracer().per_address_index().at(xs.address).loads().size());
  EXPECT_EQ(0, tracer().per_address_index().at(xs.address).stores().size());
  EXPECT_FALSE(x1.term.is_null());
  EXPECT_TRUE(x1.offset_term.is_null());

  xs[j];
  EXPECT_EQ(11, tracer().events().size());

  x1 = xs[j];
  EXPECT_EQ(14, tracer().events().size());
  EXPECT_NE(xs.address, x1.address);
  EXPECT_NE(x0.address, x1.address);
  EXPECT_EQ(3, tracer().per_address_index().at(j.address).reads().size());
  EXPECT_EQ(0, tracer().per_address_index().at(x0.address).reads().size());
  EXPECT_EQ(2, tracer().per_address_index().at(x0.address).writes().size());
  EXPECT_EQ(0, tracer().per_address_index().at(x1.address).reads().size());
  EXPECT_EQ(2, tracer().per_address_index().at(x1.address).writes().size());
  EXPECT_EQ(4, tracer().per_address_index().at(xs.address).loads().size());
  EXPECT_EQ(0, tracer().per_address_index().at(xs.address).stores().size());
  EXPECT_FALSE(x1.term.is_null());
  EXPECT_TRUE(x1.offset_term.is_null());

  xs[make_temporary_internal<size_t>()];
  EXPECT_EQ(14, tracer().events().size());

  External<char> x2(xs[make_temporary_internal<size_t>()]);
  EXPECT_NE(xs.address, x2.address);
  EXPECT_NE(x1.address, x2.address);
  EXPECT_NE(x0.address, x2.address);
  EXPECT_EQ(16, tracer().events().size());
  EXPECT_EQ(3, tracer().per_address_index().at(j.address).reads().size());
  EXPECT_EQ(0, tracer().per_address_index().at(x0.address).reads().size());
  EXPECT_EQ(2, tracer().per_address_index().at(x0.address).writes().size());
  EXPECT_EQ(0, tracer().per_address_index().at(x1.address).reads().size());
  EXPECT_EQ(2, tracer().per_address_index().at(x1.address).writes().size());
  EXPECT_EQ(0, tracer().per_address_index().at(x2.address).reads().size());
  EXPECT_EQ(1, tracer().per_address_index().at(x2.address).writes().size());
  EXPECT_EQ(5, tracer().per_address_index().at(xs.address).loads().size());
  EXPECT_EQ(0, tracer().per_address_index().at(xs.address).stores().size());
  EXPECT_FALSE(x2.term.is_null());
  EXPECT_TRUE(x2.offset_term.is_null());

  x2 = xs[make_temporary_internal<size_t>()];
  EXPECT_NE(xs.address, x2.address);
  EXPECT_NE(x1.address, x2.address);
  EXPECT_NE(x0.address, x2.address);
  EXPECT_EQ(18, tracer().events().size());
  EXPECT_EQ(3, tracer().per_address_index().at(j.address).reads().size());
  EXPECT_EQ(0, tracer().per_address_index().at(x0.address).reads().size());
  EXPECT_EQ(2, tracer().per_address_index().at(x0.address).writes().size());
  EXPECT_EQ(0, tracer().per_address_index().at(x1.address).reads().size());
  EXPECT_EQ(2, tracer().per_address_index().at(x1.address).writes().size());
  EXPECT_EQ(0, tracer().per_address_index().at(x2.address).reads().size());
  EXPECT_EQ(2, tracer().per_address_index().at(x2.address).writes().size());
  EXPECT_EQ(6, tracer().per_address_index().at(xs.address).loads().size());
  EXPECT_EQ(0, tracer().per_address_index().at(xs.address).stores().size());
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
  EXPECT_EQ(3, tracer().per_address_index().at(j.address).reads().size());
  EXPECT_EQ(2, tracer().per_address_index().at(x0.address).writes().size());
  EXPECT_EQ(2, tracer().per_address_index().at(x1.address).writes().size());
  EXPECT_EQ(2, tracer().per_address_index().at(x2.address).writes().size());
  EXPECT_EQ(1, tracer().per_address_index().at(x3.address).writes().size());
  EXPECT_EQ(7, tracer().per_address_index().at(xs.address).loads().size());
  EXPECT_EQ(0, tracer().per_address_index().at(xs.address).stores().size());
  EXPECT_FALSE(x3.term.is_null());
  EXPECT_TRUE(x3.offset_term.is_null());

  x3 = xs[External<size_t>(4)];
  EXPECT_NE(xs.address, x3.address);
  EXPECT_NE(x2.address, x3.address);
  EXPECT_NE(x1.address, x3.address);
  EXPECT_NE(x0.address, x3.address);
  EXPECT_EQ(28, tracer().events().size());
  EXPECT_EQ(3, tracer().per_address_index().at(j.address).reads().size());
  EXPECT_EQ(2, tracer().per_address_index().at(x0.address).writes().size());
  EXPECT_EQ(2, tracer().per_address_index().at(x1.address).writes().size());
  EXPECT_EQ(2, tracer().per_address_index().at(x2.address).writes().size());
  EXPECT_EQ(2, tracer().per_address_index().at(x3.address).writes().size());
  EXPECT_EQ(8, tracer().per_address_index().at(xs.address).loads().size());
  EXPECT_EQ(0, tracer().per_address_index().at(xs.address).stores().size());
  EXPECT_FALSE(x3.term.is_null());
  EXPECT_TRUE(x3.offset_term.is_null());

  xs[i] = 'A';
  EXPECT_EQ(29, tracer().events().size());
  EXPECT_EQ(3, tracer().per_address_index().at(j.address).reads().size());
  EXPECT_EQ(2, tracer().per_address_index().at(x0.address).writes().size());
  EXPECT_EQ(2, tracer().per_address_index().at(x1.address).writes().size());
  EXPECT_EQ(2, tracer().per_address_index().at(x2.address).writes().size());
  EXPECT_EQ(2, tracer().per_address_index().at(x3.address).writes().size());
  EXPECT_EQ(8, tracer().per_address_index().at(xs.address).loads().size());
  EXPECT_EQ(1, tracer().per_address_index().at(xs.address).stores().size());

  Internal<char> p('A');
  xs[i] = p;
  EXPECT_EQ(30, tracer().events().size());
  EXPECT_EQ(3, tracer().per_address_index().at(j.address).reads().size());
  EXPECT_EQ(2, tracer().per_address_index().at(x0.address).writes().size());
  EXPECT_EQ(2, tracer().per_address_index().at(x1.address).writes().size());
  EXPECT_EQ(2, tracer().per_address_index().at(x2.address).writes().size());
  EXPECT_EQ(2, tracer().per_address_index().at(x3.address).writes().size());
  EXPECT_EQ(8, tracer().per_address_index().at(xs.address).loads().size());
  EXPECT_EQ(2, tracer().per_address_index().at(xs.address).stores().size());

  xs[i] = make_temporary_internal<char>();
  EXPECT_EQ(31, tracer().events().size());
  EXPECT_EQ(3, tracer().per_address_index().at(j.address).reads().size());
  EXPECT_EQ(2, tracer().per_address_index().at(x0.address).writes().size());
  EXPECT_EQ(2, tracer().per_address_index().at(x1.address).writes().size());
  EXPECT_EQ(2, tracer().per_address_index().at(x2.address).writes().size());
  EXPECT_EQ(2, tracer().per_address_index().at(x3.address).writes().size());
  EXPECT_EQ(8, tracer().per_address_index().at(xs.address).loads().size());
  EXPECT_EQ(3, tracer().per_address_index().at(xs.address).stores().size());

  External<char> q('B');
  EXPECT_EQ(32, tracer().events().size());
  EXPECT_EQ(3, tracer().per_address_index().at(j.address).reads().size());
  EXPECT_EQ(2, tracer().per_address_index().at(x0.address).writes().size());
  EXPECT_EQ(2, tracer().per_address_index().at(x1.address).writes().size());
  EXPECT_EQ(2, tracer().per_address_index().at(x2.address).writes().size());
  EXPECT_EQ(2, tracer().per_address_index().at(x3.address).writes().size());
  EXPECT_EQ(0, tracer().per_address_index().at(q.address).reads().size());
  EXPECT_EQ(1, tracer().per_address_index().at(q.address).writes().size());
  EXPECT_EQ(8, tracer().per_address_index().at(xs.address).loads().size());
  EXPECT_EQ(3, tracer().per_address_index().at(xs.address).stores().size());

  xs[i] = q;
  EXPECT_EQ(34, tracer().events().size());
  EXPECT_EQ(3, tracer().per_address_index().at(j.address).reads().size());
  EXPECT_EQ(2, tracer().per_address_index().at(x0.address).writes().size());
  EXPECT_EQ(2, tracer().per_address_index().at(x1.address).writes().size());
  EXPECT_EQ(2, tracer().per_address_index().at(x2.address).writes().size());
  EXPECT_EQ(2, tracer().per_address_index().at(x3.address).writes().size());
  EXPECT_EQ(1, tracer().per_address_index().at(q.address).reads().size());
  EXPECT_EQ(1, tracer().per_address_index().at(q.address).writes().size());
  EXPECT_EQ(8, tracer().per_address_index().at(xs.address).loads().size());
  EXPECT_EQ(4, tracer().per_address_index().at(xs.address).stores().size());
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
  EXPECT_EQ(smt::sat, encoder.check(sum == 2, tracer()));
  EXPECT_EQ(smt::sat, encoder.check(sum != 2, tracer()));
  EXPECT_EQ(smt::sat, encoder.check(sum == 1, tracer()));
  EXPECT_EQ(smt::sat, encoder.check(sum != 1, tracer()));
  EXPECT_EQ(smt::unsat, encoder.check(sum == 0, tracer()));

  EXPECT_FALSE(tracer().flip());
}

TEST(CrvTest, SatScopeWithNondeterminsticGuardInSingleThread)
{
  tracer().reset();
  Encoder encoder;

  External<bool> nondet_bool;
  External<char> x;
  Internal<char> a('\0');

  x = 'A';
  tracer().scope_then(nondet_bool);
  x = 'B';
  tracer().scope_else();
  x = 'C';
  tracer().scope_end();
  a = x;

  EXPECT_EQ(smt::sat, encoder.check(a == 'B', tracer()));
  EXPECT_EQ(smt::sat, encoder.check(a != 'C', tracer()));
  EXPECT_EQ(smt::sat, encoder.check(a == 'B' && a != 'C', tracer()));
  EXPECT_EQ(smt::sat, encoder.check(a == 'C', tracer()));
  EXPECT_EQ(smt::sat, encoder.check(a != 'B' && a == 'C', tracer()));
}

TEST(CrvTest, SatScopeWithNondeterminsticGuardAndArrayInSingleThread)
{
  tracer().reset();
  Encoder encoder;

  External<bool> nondet_bool;
  External<char[3]> xs;
  Internal<char> a('\0');

  xs[2] = 'A';
  tracer().scope_then(nondet_bool);
  xs[2] = 'B';
  tracer().scope_else();
  xs[2] = 'C';
  tracer().scope_end();
  a = xs[2];

  EXPECT_EQ(smt::sat, encoder.check(a == 'B', tracer()));
  EXPECT_EQ(smt::sat, encoder.check(a != 'C', tracer()));
  EXPECT_EQ(smt::sat, encoder.check(a == 'B' && a != 'C', tracer()));
  EXPECT_EQ(smt::sat, encoder.check(a == 'C', tracer()));
  EXPECT_EQ(smt::sat, encoder.check(a != 'B' && a == 'C', tracer()));
}

TEST(CrvTest, SatScopeWithDeterminsticGuardAndArrayInSingleThread)
{
  tracer().reset();
  Encoder encoder;

  External<char[3]> x;
  Internal<char> p('\0');
  Internal<char> a('\0');
  
  p = '?';
  x[2] = 'A';
  tracer().scope_then(p == '?');
  x[2] = 'B';
  tracer().scope_else();
  x[2] = 'C'; // unreachable
  tracer().scope_end();
  a = x[2];

  EXPECT_EQ(smt::sat, encoder.check(a == 'B', tracer()));
  EXPECT_EQ(smt::sat, encoder.check(a != 'C', tracer()));
  EXPECT_EQ(smt::unsat, encoder.check(a == 'C', tracer()));
}

TEST(CrvTest, UnsatScopeInSingleThread)
{
  tracer().reset();
  Encoder encoder;

  External<int> var;

  tracer().scope_then(0 < var);
  tracer().add_error(var == 0);
  tracer().scope_end();

  EXPECT_EQ(smt::unsat, encoder.check(tracer()));
}

TEST(CrvTest, UnsatScopeInMultipleThread)
{
  tracer().reset();
  Encoder encoder;

  External<int> var;

  tracer().append_thread_begin_event();
  tracer().scope_then(0 < var);
  tracer().add_error(var == 0);
  tracer().scope_end();
  tracer().append_thread_end_event();

  EXPECT_EQ(smt::unsat, encoder.check(tracer()));
}

TEST(CrvTest, UnsatScopeErrorConditionDueToFalseGuard)
{
  tracer().reset();
  Encoder encoder;

  External<bool> false_bool(false);
  tracer().scope_then(false_bool);
  tracer().add_error(true);
  tracer().scope_end();

  EXPECT_EQ(smt::unsat, encoder.check(tracer()));
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
    if (tracer().decide_flip(nondet_bool))
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
    if (tracer().decide_flip(nondet_bool))
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
    if (tracer().decide_flip(p == '?'))
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

    if (tracer().decide_flip(0 < var))
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
    if (tracer().decide_flip(0 < var))
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
    if (tracer().decide_flip(false_bool))
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

    if (tracer().decide_flip(false_bool))
    {
      expect = smt::unsat;
      tracer().add_error(true_bool);
    }

    if (tracer().decide_flip(true_bool))
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

void thread_false_guard()
{
  tracer().decide_flip(false);
}

void thread_true_error()
{
  tracer().add_error(true);
}

TEST(CrvTest, ThreadGuard)
{
  tracer().reset();
  Encoder encoder;

  Thread f(thread_false_guard);
  Thread g(thread_true_error);

  EXPECT_FALSE(tracer().errors().empty());
  EXPECT_EQ(smt::sat, encoder.check(tracer()));

  tracer().reset();
  unsigned n = 0;

  tracer().decide_flip(false);
  Thread h(thread_api_test, &n, 7);
  tracer().add_error(true);

  EXPECT_EQ(7, n);
  EXPECT_EQ(smt::unsat, encoder.check(tracer()));
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

TEST(CrvTest, ImmediateDominator)
{
  Tracer tracer;
  EventIters e_iters;
  EventMap immediate_dominator_map;

  External<char> x('\0');

  tracer.append_thread_begin_event();
  tracer.append_write_event(x); // 1
  tracer.scope_then(true);
  tracer.append_write_event(x); // 2
  tracer.scope_end();
  tracer.append_write_event(x); // 3
  tracer.append_write_event(x); // 4
  tracer.append_thread_end_event();

  e_iters = tracer.per_thread_map().at(2);
  immediate_dominator_map = Encoder::immediate_dominator_map(tracer);

  EXPECT_EQ(6, e_iters.size());
  EXPECT_EQ(e_iters.at(0), immediate_dominator_map.at(e_iters.at(1)));
  EXPECT_EQ(e_iters.at(1), immediate_dominator_map.at(e_iters.at(2)));
  EXPECT_EQ(e_iters.at(1), immediate_dominator_map.at(e_iters.at(3)));
  EXPECT_EQ(e_iters.at(3), immediate_dominator_map.at(e_iters.at(4)));

  tracer.reset();

  tracer.append_thread_begin_event();
  tracer.append_write_event(x); // 1
  tracer.scope_then(true);
  tracer.append_write_event(x); // 2
  tracer.scope_else();
  tracer.append_write_event(x); // 3
  tracer.scope_end();
  tracer.append_write_event(x); // 4
  tracer.append_write_event(x); // 5
  tracer.append_thread_end_event();

  e_iters = tracer.per_thread_map().at(2);
  immediate_dominator_map = Encoder::immediate_dominator_map(tracer);

  EXPECT_EQ(7, e_iters.size());
  EXPECT_EQ(e_iters.at(0), immediate_dominator_map.at(e_iters.at(1)));
  EXPECT_EQ(e_iters.at(1), immediate_dominator_map.at(e_iters.at(2)));
  EXPECT_EQ(e_iters.at(1), immediate_dominator_map.at(e_iters.at(3)));
  EXPECT_EQ(e_iters.at(1), immediate_dominator_map.at(e_iters.at(4)));
  EXPECT_EQ(e_iters.at(4), immediate_dominator_map.at(e_iters.at(5)));

  tracer.reset();

  tracer.append_thread_begin_event();
  tracer.append_write_event(x); // 1
  tracer.scope_then(true);
  tracer.scope_then(true);
  tracer.append_write_event(x); // 2
  tracer.scope_end();
  tracer.scope_end();
  tracer.append_write_event(x); // 3
  tracer.append_thread_end_event();

  e_iters = tracer.per_thread_map().at(2);
  immediate_dominator_map = Encoder::immediate_dominator_map(tracer);

  EXPECT_EQ(5, e_iters.size());
  EXPECT_EQ(e_iters.at(0), immediate_dominator_map.at(e_iters.at(1)));
  EXPECT_EQ(e_iters.at(1), immediate_dominator_map.at(e_iters.at(2)));
  EXPECT_EQ(e_iters.at(1), immediate_dominator_map.at(e_iters.at(3)));

  tracer.reset();

  tracer.append_thread_begin_event();
  tracer.append_write_event(x); // 1
  tracer.scope_then(true);
  tracer.scope_then(true);
  tracer.append_write_event(x); // 2
  tracer.append_write_event(x); // 3
  tracer.scope_end();
  tracer.scope_end();
  tracer.append_write_event(x); // 4
  tracer.append_thread_end_event();

  e_iters = tracer.per_thread_map().at(2);
  immediate_dominator_map = Encoder::immediate_dominator_map(tracer);

  EXPECT_EQ(6, e_iters.size());
  EXPECT_EQ(e_iters.at(0), immediate_dominator_map.at(e_iters.at(1)));
  EXPECT_EQ(e_iters.at(1), immediate_dominator_map.at(e_iters.at(2)));
  EXPECT_EQ(e_iters.at(2), immediate_dominator_map.at(e_iters.at(3)));
  EXPECT_EQ(e_iters.at(1), immediate_dominator_map.at(e_iters.at(4)));

  tracer.reset();

  tracer.append_thread_begin_event();
  tracer.append_write_event(x); // 1
  tracer.scope_then(true);
  tracer.scope_then(true);
  tracer.append_write_event(x); // 2
  tracer.scope_end();
  tracer.scope_else();
  tracer.append_write_event(x); // 3
  tracer.scope_end();
  tracer.append_write_event(x); // 4
  tracer.append_thread_end_event();

  e_iters = tracer.per_thread_map().at(2);
  immediate_dominator_map = Encoder::immediate_dominator_map(tracer);

  EXPECT_EQ(6, e_iters.size());
  EXPECT_EQ(e_iters.at(0), immediate_dominator_map.at(e_iters.at(1)));
  EXPECT_EQ(e_iters.at(1), immediate_dominator_map.at(e_iters.at(2)));
  EXPECT_EQ(e_iters.at(1), immediate_dominator_map.at(e_iters.at(3)));
  EXPECT_EQ(e_iters.at(1), immediate_dominator_map.at(e_iters.at(4)));

  tracer.reset();

  tracer.append_thread_begin_event();
  tracer.append_write_event(x); // 1
  tracer.scope_then(true);
  tracer.scope_then(true);
  tracer.append_write_event(x); // 2
  tracer.scope_else();
  tracer.append_write_event(x); // 3
  tracer.scope_end();
  tracer.scope_end();
  tracer.append_write_event(x); // 4
  tracer.append_thread_end_event();

  e_iters = tracer.per_thread_map().at(2);
  immediate_dominator_map = Encoder::immediate_dominator_map(tracer);

  EXPECT_EQ(6, e_iters.size());
  EXPECT_EQ(e_iters.at(0), immediate_dominator_map.at(e_iters.at(1)));
  EXPECT_EQ(e_iters.at(1), immediate_dominator_map.at(e_iters.at(2)));
  EXPECT_EQ(e_iters.at(1), immediate_dominator_map.at(e_iters.at(3)));
  EXPECT_EQ(e_iters.at(1), immediate_dominator_map.at(e_iters.at(4)));

  tracer.reset();

  tracer.append_thread_begin_event();
  tracer.append_write_event(x); // 1
  tracer.scope_then(true);
  tracer.append_write_event(x); // 2
  tracer.scope_end();
  tracer.scope_then(true);
  tracer.append_write_event(x); // 3
  tracer.scope_end();
  tracer.append_thread_end_event();

  e_iters = tracer.per_thread_map().at(2);
  immediate_dominator_map = Encoder::immediate_dominator_map(tracer);

  EXPECT_EQ(5, e_iters.size());
  EXPECT_EQ(e_iters.at(0), immediate_dominator_map.at(e_iters.at(1)));
  EXPECT_EQ(e_iters.at(1), immediate_dominator_map.at(e_iters.at(2)));
  EXPECT_EQ(e_iters.at(1), immediate_dominator_map.at(e_iters.at(3)));

  tracer.reset();

  tracer.append_thread_begin_event();
  tracer.append_write_event(x); // 1
  tracer.scope_then(true);
  tracer.append_write_event(x); // 2
  tracer.scope_end();
  tracer.append_write_event(x); // 3
  tracer.scope_then(true);
  tracer.append_write_event(x); // 4
  tracer.scope_end();
  tracer.append_thread_end_event();

  e_iters = tracer.per_thread_map().at(2);
  immediate_dominator_map = Encoder::immediate_dominator_map(tracer);

  EXPECT_EQ(6, e_iters.size());
  EXPECT_EQ(e_iters.at(0), immediate_dominator_map.at(e_iters.at(1)));
  EXPECT_EQ(e_iters.at(1), immediate_dominator_map.at(e_iters.at(2)));
  EXPECT_EQ(e_iters.at(1), immediate_dominator_map.at(e_iters.at(3)));
  EXPECT_EQ(e_iters.at(3), immediate_dominator_map.at(e_iters.at(4)));

  tracer.reset();

  tracer.append_thread_begin_event();
  tracer.append_write_event(x); // 1
  tracer.scope_then(true);
  tracer.append_write_event(x); // 2
  tracer.scope_else();
  tracer.append_write_event(x); // 3
  tracer.scope_end();
  tracer.append_write_event(x); // 4
  tracer.scope_then(true);
  tracer.append_write_event(x); // 5
  tracer.scope_end();
  tracer.append_thread_end_event();

  e_iters = tracer.per_thread_map().at(2);
  immediate_dominator_map = Encoder::immediate_dominator_map(tracer);

  EXPECT_EQ(7, e_iters.size());
  EXPECT_EQ(e_iters.at(0), immediate_dominator_map.at(e_iters.at(1)));
  EXPECT_EQ(e_iters.at(1), immediate_dominator_map.at(e_iters.at(2)));
  EXPECT_EQ(e_iters.at(1), immediate_dominator_map.at(e_iters.at(3)));
  EXPECT_EQ(e_iters.at(1), immediate_dominator_map.at(e_iters.at(4)));
  EXPECT_EQ(e_iters.at(4), immediate_dominator_map.at(e_iters.at(5)));

  tracer.reset();

  tracer.append_thread_begin_event();
  tracer.append_write_event(x); // 1
  tracer.scope_then(true);
  tracer.append_write_event(x); // 2
  tracer.scope_end();
  tracer.append_write_event(x); // 3
  tracer.scope_then(true);
  tracer.append_write_event(x); // 4
  tracer.scope_else();
  tracer.append_write_event(x); // 5
  tracer.scope_end();
  tracer.append_thread_end_event();

  e_iters = tracer.per_thread_map().at(2);
  immediate_dominator_map = Encoder::immediate_dominator_map(tracer);

  EXPECT_EQ(7, e_iters.size());
  EXPECT_EQ(e_iters.at(0), immediate_dominator_map.at(e_iters.at(1)));
  EXPECT_EQ(e_iters.at(1), immediate_dominator_map.at(e_iters.at(2)));
  EXPECT_EQ(e_iters.at(1), immediate_dominator_map.at(e_iters.at(3)));
  EXPECT_EQ(e_iters.at(3), immediate_dominator_map.at(e_iters.at(4)));
  EXPECT_EQ(e_iters.at(3), immediate_dominator_map.at(e_iters.at(5)));

  tracer.reset();

  tracer.append_thread_begin_event();
  tracer.append_write_event(x); // 1
  tracer.scope_then(true);
  tracer.append_write_event(x); // 2
  tracer.scope_else();
  tracer.scope_end();
  tracer.append_write_event(x); // 3
  tracer.scope_then(true);
  tracer.append_write_event(x); // 4
  tracer.scope_end();
  tracer.append_thread_end_event();

  e_iters = tracer.per_thread_map().at(2);
  immediate_dominator_map = Encoder::immediate_dominator_map(tracer);

  EXPECT_EQ(6, e_iters.size());
  EXPECT_EQ(e_iters.at(0), immediate_dominator_map.at(e_iters.at(1)));
  EXPECT_EQ(e_iters.at(1), immediate_dominator_map.at(e_iters.at(2)));
  EXPECT_EQ(e_iters.at(1), immediate_dominator_map.at(e_iters.at(3)));
  EXPECT_EQ(e_iters.at(3), immediate_dominator_map.at(e_iters.at(4)));

  tracer.reset();

  tracer.append_thread_begin_event();
  tracer.append_write_event(x); // 1
  tracer.scope_then(true);
  tracer.append_write_event(x); // 2
  tracer.scope_end();
  tracer.append_write_event(x); // 3
  tracer.scope_then(true);
  tracer.append_write_event(x); // 4
  tracer.scope_else();
  tracer.scope_end();
  tracer.append_thread_end_event();

  e_iters = tracer.per_thread_map().at(2);
  immediate_dominator_map = Encoder::immediate_dominator_map(tracer);

  EXPECT_EQ(6, e_iters.size());
  EXPECT_EQ(e_iters.at(0), immediate_dominator_map.at(e_iters.at(1)));
  EXPECT_EQ(e_iters.at(1), immediate_dominator_map.at(e_iters.at(2)));
  EXPECT_EQ(e_iters.at(1), immediate_dominator_map.at(e_iters.at(3)));
  EXPECT_EQ(e_iters.at(3), immediate_dominator_map.at(e_iters.at(4)));

  tracer.reset();

  tracer.append_thread_begin_event();
  tracer.append_write_event(x); // 1
  tracer.scope_then(true);
  tracer.scope_else();
  tracer.append_write_event(x); // 2
  tracer.scope_end();
  tracer.append_write_event(x); // 3
  tracer.scope_then(true);
  tracer.append_write_event(x); // 4
  tracer.scope_end();
  tracer.append_thread_end_event();

  e_iters = tracer.per_thread_map().at(2);
  immediate_dominator_map = Encoder::immediate_dominator_map(tracer);

  EXPECT_EQ(6, e_iters.size());
  EXPECT_EQ(e_iters.at(0), immediate_dominator_map.at(e_iters.at(1)));
  EXPECT_EQ(e_iters.at(1), immediate_dominator_map.at(e_iters.at(2)));
  EXPECT_EQ(e_iters.at(1), immediate_dominator_map.at(e_iters.at(3)));
  EXPECT_EQ(e_iters.at(3), immediate_dominator_map.at(e_iters.at(4)));

  tracer.reset();

  tracer.append_thread_begin_event();
  tracer.append_write_event(x); // 1
  tracer.scope_then(true);
  tracer.append_write_event(x); // 2
  tracer.scope_end();
  tracer.append_write_event(x); // 3
  tracer.scope_then(true);
  tracer.scope_else();
  tracer.append_write_event(x); // 4
  tracer.scope_end();
  tracer.append_thread_end_event();

  e_iters = tracer.per_thread_map().at(2);
  immediate_dominator_map = Encoder::immediate_dominator_map(tracer);

  EXPECT_EQ(6, e_iters.size());
  EXPECT_EQ(e_iters.at(0), immediate_dominator_map.at(e_iters.at(1)));
  EXPECT_EQ(e_iters.at(1), immediate_dominator_map.at(e_iters.at(2)));
  EXPECT_EQ(e_iters.at(1), immediate_dominator_map.at(e_iters.at(3)));
  EXPECT_EQ(e_iters.at(3), immediate_dominator_map.at(e_iters.at(4)));

  tracer.reset();

  tracer.append_thread_begin_event();
  tracer.append_write_event(x); // 1
  tracer.scope_then(true);
  tracer.scope_else();
  tracer.append_write_event(x); // 2
  tracer.scope_end();
  tracer.scope_then(true);
  tracer.append_write_event(x); // 3
  tracer.scope_end();
  tracer.append_thread_end_event();

  e_iters = tracer.per_thread_map().at(2);
  immediate_dominator_map = Encoder::immediate_dominator_map(tracer);

  EXPECT_EQ(5, e_iters.size());
  EXPECT_EQ(e_iters.at(0), immediate_dominator_map.at(e_iters.at(1)));
  EXPECT_EQ(e_iters.at(1), immediate_dominator_map.at(e_iters.at(2)));
  EXPECT_EQ(e_iters.at(1), immediate_dominator_map.at(e_iters.at(3)));

  tracer.reset();

  tracer.append_thread_begin_event();
  tracer.append_write_event(x); // 1
  tracer.scope_then(true);
  tracer.append_write_event(x); // 2
  tracer.scope_end();
  tracer.scope_then(true);
  tracer.scope_else();
  tracer.append_write_event(x); // 3
  tracer.scope_end();
  tracer.append_thread_end_event();

  e_iters = tracer.per_thread_map().at(2);
  immediate_dominator_map = Encoder::immediate_dominator_map(tracer);

  EXPECT_EQ(5, e_iters.size());
  EXPECT_EQ(e_iters.at(0), immediate_dominator_map.at(e_iters.at(1)));
  EXPECT_EQ(e_iters.at(1), immediate_dominator_map.at(e_iters.at(2)));
  EXPECT_EQ(e_iters.at(1), immediate_dominator_map.at(e_iters.at(3)));

  tracer.reset();

  tracer.append_thread_begin_event();
  tracer.append_write_event(x); // 1
  tracer.scope_then(true);
  tracer.scope_then(true);
  tracer.append_write_event(x); // 2
  tracer.scope_end();
  tracer.scope_then(true);
  tracer.append_write_event(x); // 3
  tracer.scope_end();
  tracer.scope_end();
  tracer.append_thread_end_event();

  e_iters = tracer.per_thread_map().at(2);
  immediate_dominator_map = Encoder::immediate_dominator_map(tracer);

  EXPECT_EQ(5, e_iters.size());
  EXPECT_EQ(e_iters.at(0), immediate_dominator_map.at(e_iters.at(1)));
  EXPECT_EQ(e_iters.at(1), immediate_dominator_map.at(e_iters.at(2)));
  EXPECT_EQ(e_iters.at(1), immediate_dominator_map.at(e_iters.at(3)));

  tracer.reset();

  tracer.append_thread_begin_event();
  tracer.append_write_event(x); // 1
  tracer.scope_then(true);
  tracer.scope_then(true);
  tracer.scope_then(true);
  tracer.append_write_event(x); // 2
  tracer.scope_end();
  tracer.scope_then(true);
  tracer.append_write_event(x); // 3
  tracer.scope_end();
  tracer.scope_end();
  tracer.scope_end();
  tracer.append_thread_end_event();

  e_iters = tracer.per_thread_map().at(2);
  immediate_dominator_map = Encoder::immediate_dominator_map(tracer);

  EXPECT_EQ(5, e_iters.size());
  EXPECT_EQ(e_iters.at(0), immediate_dominator_map.at(e_iters.at(1)));
  EXPECT_EQ(e_iters.at(1), immediate_dominator_map.at(e_iters.at(2)));
  EXPECT_EQ(e_iters.at(1), immediate_dominator_map.at(e_iters.at(3)));

  tracer.reset();

  tracer.append_thread_begin_event();
  tracer.append_write_event(x); // 1
  tracer.scope_then(true);
  tracer.scope_then(true);
  tracer.append_write_event(x); // 2
  tracer.scope_end();
  tracer.scope_then(true);
  tracer.append_write_event(x); // 3
  tracer.scope_end();
  tracer.scope_end();
  tracer.append_write_event(x); // 4
  tracer.append_thread_end_event();

  e_iters = tracer.per_thread_map().at(2);
  immediate_dominator_map = Encoder::immediate_dominator_map(tracer);

  EXPECT_EQ(6, e_iters.size());
  EXPECT_EQ(e_iters.at(0), immediate_dominator_map.at(e_iters.at(1)));
  EXPECT_EQ(e_iters.at(1), immediate_dominator_map.at(e_iters.at(2)));
  EXPECT_EQ(e_iters.at(1), immediate_dominator_map.at(e_iters.at(3)));
  EXPECT_EQ(e_iters.at(1), immediate_dominator_map.at(e_iters.at(4)));

  tracer.reset();

  tracer.append_thread_begin_event();
  tracer.append_write_event(x); // 1
  EXPECT_TRUE(tracer.decide_flip(true));
  tracer.append_write_event(x); // 2
  EXPECT_TRUE(tracer.decide_flip(false));
  tracer.append_write_event(x); // 3
  tracer.append_thread_end_event();

  e_iters = tracer.per_thread_map().at(2);
  immediate_dominator_map = Encoder::immediate_dominator_map(tracer);

  EXPECT_EQ(5, e_iters.size());
  EXPECT_EQ(e_iters.at(0), immediate_dominator_map.at(e_iters.at(1)));
  EXPECT_EQ(e_iters.at(1), immediate_dominator_map.at(e_iters.at(2)));
  EXPECT_EQ(e_iters.at(2), immediate_dominator_map.at(e_iters.at(3)));

  tracer.reset();

  tracer.append_thread_begin_event();
  tracer.append_write_event(x); // 1
  tracer.append_write_event(x); // 2
  EXPECT_TRUE(tracer.decide_flip(true));
  tracer.append_write_event(x); // 3
  EXPECT_TRUE(tracer.decide_flip(false));
  tracer.append_write_event(x); // 4
  tracer.append_write_event(x); // 5
  tracer.append_thread_end_event();

  e_iters = tracer.per_thread_map().at(2);
  immediate_dominator_map = Encoder::immediate_dominator_map(tracer);

  EXPECT_EQ(7, e_iters.size());
  EXPECT_EQ(e_iters.at(0), immediate_dominator_map.at(e_iters.at(1)));
  EXPECT_EQ(e_iters.at(1), immediate_dominator_map.at(e_iters.at(2)));
  EXPECT_EQ(e_iters.at(2), immediate_dominator_map.at(e_iters.at(3)));
  EXPECT_EQ(e_iters.at(3), immediate_dominator_map.at(e_iters.at(4)));
  EXPECT_EQ(e_iters.at(4), immediate_dominator_map.at(e_iters.at(5)));

  tracer.reset();

  tracer.append_thread_begin_event();
  tracer.append_write_event(x); // 1
  EXPECT_TRUE(tracer.decide_flip(true));
  tracer.append_write_event(x); // 2
  tracer.append_write_event(x); // 3
  EXPECT_TRUE(tracer.decide_flip(false));
  tracer.append_write_event(x); // 4
  tracer.append_write_event(x); // 5
  tracer.append_thread_end_event();

  e_iters = tracer.per_thread_map().at(2);
  immediate_dominator_map = Encoder::immediate_dominator_map(tracer);

  EXPECT_EQ(7, e_iters.size());
  EXPECT_EQ(e_iters.at(0), immediate_dominator_map.at(e_iters.at(1)));
  EXPECT_EQ(e_iters.at(1), immediate_dominator_map.at(e_iters.at(2)));
  EXPECT_EQ(e_iters.at(2), immediate_dominator_map.at(e_iters.at(3)));
  EXPECT_EQ(e_iters.at(3), immediate_dominator_map.at(e_iters.at(4)));
  EXPECT_EQ(e_iters.at(4), immediate_dominator_map.at(e_iters.at(5)));
}

TEST(CrvTest, CommunicationImmediateDominator)
{
  tracer().reset();

  tracer().append_thread_begin_event();
  tracer().append_thread_end_event();

  EventMap cidom_map(Encoder::communication_immediate_dominator_map(tracer()));
  EXPECT_TRUE(cidom_map.empty());

  tracer().reset();

  Channel<int> c;
  tracer().append_thread_begin_event();
  External<int> x(0);
  x = c.recv();
  x = x + 1;
  c.send(x);
  tracer().append_thread_end_event();

  const PerThreadMap& per_thread_map = tracer().per_thread_map();
  cidom_map = Encoder::communication_immediate_dominator_map(tracer());
  EXPECT_FALSE(cidom_map.empty());

  EventIters event_iters;
  for (const EventIter e_iter : per_thread_map.at(2))
  {
    if (e_iter->is_channel_send() ||
        e_iter->is_channel_recv() || 
        e_iter->is_thread_end())
      event_iters.push_back(e_iter);
  }

  EXPECT_EQ(3, event_iters.size());

  EventIter e_iter(event_iters[2]);
  EXPECT_TRUE(e_iter->is_thread_end());

  EventIter e_prime_iter = event_iters[1];
  EXPECT_TRUE(e_prime_iter->is_channel_send());

  // look up predecessors of a THREAD_END_EVENT
  EXPECT_EQ(e_prime_iter, cidom_map.at(e_iter));

  e_iter = e_prime_iter;
  e_prime_iter = event_iters[0];
  EXPECT_TRUE(e_prime_iter->is_channel_recv());

  EXPECT_EQ(e_prime_iter, cidom_map.at(e_iter));
  EXPECT_EQ(cidom_map.cend(), cidom_map.find(e_prime_iter));
}

TEST(CrvTest, DeadlockSingleSend)
{
  tracer().reset();
  Encoder encoder;

  Channel<int> c;
  tracer().append_thread_begin_event();
  c.send(5);
  tracer().append_thread_end_event();

  EXPECT_EQ(smt::sat, encoder.check_deadlock(tracer()));

  tracer().append_thread_begin_event();
  c.recv();
  tracer().append_thread_end_event();

  EXPECT_EQ(smt::unsat, encoder.check_deadlock(tracer()));
}

TEST(CrvTest, DeadlockSingleRecv)
{
  tracer().reset();
  Encoder encoder;

  Channel<int> c;
  tracer().append_thread_begin_event();
  c.recv();
  tracer().append_thread_end_event();

  EXPECT_EQ(smt::sat, encoder.check_deadlock(tracer()));

  tracer().append_thread_begin_event();
  c.send(5);
  tracer().append_thread_end_event();

  EXPECT_EQ(smt::unsat, encoder.check_deadlock(tracer()));
}

TEST(CrvTest, Deadlock)
{
  tracer().reset();
  Encoder encoder;

  Channel<int> c;

  tracer().append_thread_begin_event();
  c.send(5);
  Internal<int> r = c.recv();
  c.send(Internal<int>(6));
  tracer().append_thread_end_event();

  tracer().append_thread_begin_event();
  External<int> seven(7);
  c.send(seven);
  c.recv();
  tracer().append_thread_end_event();

  tracer().append_thread_begin_event();
  c.recv();
  tracer().append_thread_end_event();

  EXPECT_EQ(smt::sat, encoder.check_deadlock(tracer()));
}

TEST(CrvTest, InitDeadlockFree)
{
  tracer().reset();
  Encoder encoder;

  Channel<int> c;

  tracer().append_thread_begin_event();
  c.send(5);
  tracer().append_thread_end_event();

  tracer().append_thread_begin_event();
  c.recv();
  tracer().append_thread_end_event();

  EXPECT_EQ(smt::unsat, encoder.check_deadlock(tracer()));
}

// Unlike CrvTest::InitDeadlockFree, this test also relies
// on the extension axiom implemented by Encoder
TEST(CrvTest, ExtensionDeadlockFree)
{
  tracer().reset();
  Encoder encoder;

  Channel<int> c;

  tracer().append_thread_begin_event();
  c.send(5);
  c.recv();
  tracer().append_thread_end_event();

  tracer().append_thread_begin_event();
  c.recv();
  c.send(6);
  tracer().append_thread_end_event();

  EXPECT_EQ(smt::unsat, encoder.check_deadlock(tracer()));
}

TEST(CrvTest, CommunicationValue)
{
  tracer().reset();
  Encoder encoder;

  Channel<int> c;

  tracer().append_thread_begin_event();
  c.send(5);
  Internal<int> r(c.recv());
  tracer().append_thread_end_event();

  tracer().append_thread_begin_event();
  c.recv();
  c.send(6);
  tracer().append_thread_end_event();

  EXPECT_EQ(smt::unsat, encoder.check(r != 6, tracer()));
  EXPECT_EQ(smt::sat, encoder.check(r == 6, tracer()));
}

TEST(CrvTest, CommunicationWithTrueGuard)
{
  tracer().reset();
  Encoder encoder;

  Channel<int> c;

  tracer().append_thread_begin_event();
  c.send(5);
  EXPECT_TRUE(tracer().decide_flip(6 == c.recv()));
  c.send(7);
  tracer().append_thread_end_event();

  tracer().append_thread_begin_event();
  c.recv();
  c.send(6);
  Internal<int> r(c.recv());
  tracer().append_thread_end_event();

  EXPECT_EQ(smt::unsat, encoder.check(r != 7, tracer()));
  EXPECT_EQ(smt::sat, encoder.check(r == 7, tracer()));
  EXPECT_EQ(smt::unsat, encoder.check_deadlock(tracer()));
}

TEST(CrvTest, CommunicationWithFalseGuard)
{
  tracer().reset();
  Encoder encoder;

  Channel<int> c;

  tracer().append_thread_begin_event();
  c.send(5);
  EXPECT_TRUE(tracer().decide_flip(6 != c.recv()));
  c.send(7);
  tracer().append_thread_end_event();

  tracer().append_thread_begin_event();
  c.recv();
  c.send(6);
  Internal<int> r(c.recv());
  tracer().append_thread_end_event();

  // if there is a deadlock (which there is), then receive
  // events can take on nondeterministic values.
  EXPECT_EQ(smt::sat, encoder.check(r != 7, tracer()));
  EXPECT_EQ(smt::sat, encoder.check(r == 7, tracer()));
  EXPECT_EQ(smt::sat, encoder.check_deadlock(tracer()));
}

TEST(CrvTest, ScopeCommunicationWithElse)
{
  tracer().reset();
  Encoder encoder;

  Channel<int> c;

  tracer().append_thread_begin_event();
  c.send(5);
  tracer().scope_then(6 == c.recv());
  c.send(7);
  tracer().scope_else();
  c.send(8);
  tracer().scope_end();
  tracer().append_thread_end_event();

  tracer().append_thread_begin_event();
  c.recv();
  c.send(6);
  Internal<int> r(c.recv());
  tracer().append_thread_end_event();

  EXPECT_EQ(smt::unsat, encoder.check(r != 7, tracer()));
  EXPECT_EQ(smt::sat, encoder.check(r == 7, tracer()));
  EXPECT_EQ(smt::unsat, encoder.check_deadlock(tracer()));
}

TEST(CrvTest, ScopeCommunicationWithFalseThen)
{
  tracer().reset();
  Encoder encoder;

  Channel<int> c;

  tracer().append_thread_begin_event();
  c.send(5);
  tracer().scope_then(6 != c.recv());
  c.send(7);
  tracer().scope_end();
  tracer().append_thread_end_event();

  tracer().append_thread_begin_event();
  c.recv();
  c.send(6);
  Internal<int> r(c.recv());
  tracer().append_thread_end_event();

  // if there is a deadlock (which there is), then receive
  // events can take on nondeterministic values.
  EXPECT_EQ(smt::sat, encoder.check(r != 7, tracer()));
  EXPECT_EQ(smt::sat, encoder.check(r == 7, tracer()));
  EXPECT_EQ(smt::sat, encoder.check_deadlock(tracer()));
}

template<smt::Opcode opcode, class T>
static T roperand(const Internal<T> arg)
{
  typename Smt<T>::Sort term(Internal<T>::term(arg));

  const smt::Expr& expr = term.ref();
  EXPECT_EQ(smt::BINARY_EXPR_KIND, expr.expr_kind());
  const smt::BinaryExpr<opcode>& binary_expr =
    dynamic_cast<const smt::BinaryExpr<opcode>&>(expr);

  const smt::Expr& roperand_expr = binary_expr.roperand().ref();
  EXPECT_EQ(smt::LITERAL_EXPR_KIND, roperand_expr.expr_kind());
  const smt::LiteralExpr<T>& literal_expr =
    dynamic_cast<const smt::LiteralExpr<T>&>(roperand_expr);
  return literal_expr.literal();
}

TEST(CrvTest, LazyInternal)
{
  tracer().reset();

  Internal<int> a(0);
  EXPECT_FALSE(a.is_lazy());
  EXPECT_EQ(Internal<int>::term(a).addr(), Internal<int>::term(a).addr());

  Internal<int> b(Internal<int>::fresh_lazy<smt::ADD>(a, 5));
  EXPECT_TRUE(b.is_lazy());
  EXPECT_NE(Internal<int>::term(b).addr(), Internal<int>::term(b).addr());
  EXPECT_EQ(5, roperand<smt::ADD>(b));

  Internal<int> c(Internal<int>::propagate<smt::ADD>(b, 3));
  EXPECT_TRUE(c.is_lazy());
  EXPECT_EQ(5 + 3, roperand<smt::ADD>(c));

  Internal<int> d(Internal<int>::refresh_lazy<smt::MUL>(c, 7));
  EXPECT_TRUE(d.is_lazy());
  EXPECT_EQ(7, roperand<smt::MUL>(d));

  Internal<int> e(Internal<int>::propagate<smt::MUL>(d, 8));
  EXPECT_TRUE(e.is_lazy());
  EXPECT_EQ(7 * 8, roperand<smt::MUL>(e));

  // rvalue reference arguments
  Internal<int> x(Internal<int>::fresh_lazy<smt::ADD>(std::move(a), 5));
  EXPECT_TRUE(x.is_lazy());
  EXPECT_NE(Internal<int>::term(x).addr(), Internal<int>::term(x).addr());
  EXPECT_EQ(5, roperand<smt::ADD>(x));

  Internal<int> y(Internal<int>::propagate<smt::ADD>(std::move(b), 3));
  EXPECT_TRUE(y.is_lazy());
  EXPECT_EQ(5 + 3, roperand<smt::ADD>(y));

  Internal<int> z(Internal<int>::refresh_lazy<smt::MUL>(std::move(c), 7));
  EXPECT_TRUE(z.is_lazy());
  EXPECT_EQ(7, roperand<smt::MUL>(z));
}

TEST(CrvTest, SimplifierLazyConstantPropagation)
{
  tracer().reset();
  Encoder encoder;

  External<int> a = 0;
  Internal<int> b = a;

  b = simplifier::Lazy::apply<smt::ADD>(b, 5);
  b = simplifier::Lazy::apply<smt::ADD>(b, 3);

  EXPECT_EQ(smt::unsat, encoder.check(!(b == 8), tracer()));
  EXPECT_EQ(smt::sat, encoder.check(b == 8, tracer()));
  EXPECT_EQ(8, roperand<smt::ADD>(b));

  // rvalue reference arguments
  Internal<int> c = a;
  Internal<int> d = simplifier::Lazy::apply<smt::ADD>(std::move(c), 5);
  Internal<int> e = simplifier::Lazy::apply<smt::ADD>(std::move(d), 3);

  EXPECT_EQ(smt::unsat, encoder.check(!(e == 8), tracer()));
  EXPECT_EQ(smt::sat, encoder.check(e == 8, tracer()));
  EXPECT_EQ(8, roperand<smt::ADD>(e));
}

TEST(CrvTest, SimplifyInternalOperations)
{
  tracer().reset();
  Encoder encoder;

  External<int> a = 0;
  Internal<int> b = a;
  b = b + 5; 
  b = b + 3; 

  EXPECT_EQ(smt::unsat, encoder.check(!(b == 8), tracer()));
  EXPECT_EQ(smt::sat, encoder.check(b == 8, tracer()));
  EXPECT_EQ(8, roperand<smt::ADD>(b));
}

