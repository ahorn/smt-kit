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
  STATIC_EXPECT_TRUE((std::is_same<int, typename internal::Return<smt::ADD,
    short, short>::Type>::value));

  STATIC_EXPECT_TRUE((std::is_same<unsigned long, typename internal::Return<smt::ADD,
    unsigned int, unsigned long>::Type>::value));

  STATIC_EXPECT_TRUE((std::is_same<bool, typename internal::Return<smt::LSS,
    int, int>::Type>::value));

  STATIC_EXPECT_TRUE((std::is_same<bool, typename internal::Return<smt::LNOT,
    unsigned int>::Type>::value));

  // language specification, 6.3.1.8
  STATIC_EXPECT_TRUE((std::is_same<unsigned int, typename internal::Return<smt::ADD,
    unsigned int, int>::Type>::value));

  // no warning since we are doing meta-programming
  STATIC_EXPECT_TRUE((std::is_same<bool, typename internal::Return<smt::LSS,
    unsigned int, int>::Type>::value));
}

TEST(CrvTest, Reflect)
{

  STATIC_EXPECT_FALSE((reflect<int>().is_int()));
  STATIC_EXPECT_TRUE((reflect<int>().is_bv()));
  STATIC_EXPECT_TRUE((reflect<int>().is_signed()));

  STATIC_EXPECT_FALSE((reflect<unsigned int>().is_int()));
  STATIC_EXPECT_TRUE((reflect<unsigned int>().is_bv()));
  STATIC_EXPECT_FALSE((reflect<unsigned int>().is_signed()));

  STATIC_EXPECT_FALSE((reflect<int[3]>().is_bv()));
  STATIC_EXPECT_FALSE((reflect<int[3]>().is_signed()));
  STATIC_EXPECT_TRUE((reflect<int[3]>().is_array()));

  STATIC_EXPECT_FALSE((reflect<int[3]>().sorts(0).is_int()));
  STATIC_EXPECT_TRUE((reflect<int[3]>().sorts(0).is_bv()));
  STATIC_EXPECT_FALSE((reflect<int[3]>().sorts(0).is_signed()));

  STATIC_EXPECT_FALSE((reflect<int[3]>().sorts(1).is_int()));
  STATIC_EXPECT_TRUE((reflect<int[3]>().sorts(1).is_bv()));
  STATIC_EXPECT_TRUE((reflect<int[3]>().sorts(1).is_signed()));
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
  Event e(READ_EVENT, 2, 3, 4, 5, 6, smt::internal::sort<smt::Bv<int>>(),
    smt::literal<smt::Bool>(true), smt::any<smt::Bv<char>>("a"), smt::Bv<size_t>());
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

TEST(CrvTest, Dfs)
{
  Dfs dfs;

  EXPECT_FALSE(dfs.has_next());
  dfs.append_flip();

  EXPECT_EQ(1, dfs.flips().size());
  EXPECT_FALSE(dfs.flips().back().direction);
  EXPECT_FALSE(dfs.flips().back().is_frozen);

  EXPECT_FALSE(dfs.has_next());
  dfs.append_flip();

  EXPECT_EQ(2, dfs.flips().size());
  EXPECT_FALSE(dfs.flips().back().direction);
  EXPECT_FALSE(dfs.flips().back().is_frozen);

  EXPECT_TRUE(dfs.find_next_path());

  EXPECT_TRUE(dfs.has_next());
  EXPECT_FALSE(dfs.next());

  EXPECT_TRUE(dfs.has_next());
  EXPECT_TRUE(dfs.next());

  EXPECT_FALSE(dfs.has_next());

  EXPECT_EQ(2, dfs.flips().size());
  EXPECT_TRUE(dfs.flips().back().direction);
  EXPECT_TRUE(dfs.flips().back().is_frozen);

  EXPECT_TRUE(dfs.find_next_path());

  EXPECT_TRUE(dfs.has_next());
  EXPECT_TRUE(dfs.next());

  EXPECT_FALSE(dfs.has_next());

  EXPECT_EQ(1, dfs.flips().size());
  EXPECT_TRUE(dfs.flips().back().direction);
  EXPECT_TRUE(dfs.flips().back().is_frozen);

  EXPECT_FALSE(dfs.find_next_path());
  EXPECT_TRUE(dfs.flips().empty());
}

TEST(CrvTest, DfsChecker)
{
  DfsChecker checker;
  External<long> v;

  // if (v < 0) { if (v < 1)  { skip } }
  EXPECT_FALSE(checker.branch(v < 0));
  EXPECT_TRUE(checker.find_next_path());

  EXPECT_TRUE(checker.branch(v < 0));
  EXPECT_FALSE(checker.branch(v < 1));
  EXPECT_TRUE(checker.find_next_path());

  EXPECT_TRUE(checker.branch(v < 0));
  EXPECT_TRUE(checker.branch(v < 1));
  EXPECT_FALSE(checker.find_next_path());

  EXPECT_EQ(2, checker.path_cnt());

  checker.reset();

  // if (v < 0) { skip } ; if (v < 1)  { skip }
  EXPECT_FALSE(checker.branch(v < 0));
  EXPECT_FALSE(checker.branch(v < 1));
  EXPECT_TRUE(checker.find_next_path());

  EXPECT_FALSE(checker.branch(v < 0));
  EXPECT_TRUE(checker.branch(v < 1));
  EXPECT_TRUE(checker.find_next_path());

  EXPECT_TRUE(checker.branch(v < 0));
  EXPECT_FALSE(checker.branch(v < 1));
  EXPECT_TRUE(checker.find_next_path());

  EXPECT_TRUE(checker.branch(v < 0));
  EXPECT_TRUE(checker.branch(v < 1));
  EXPECT_FALSE(checker.find_next_path());

  EXPECT_EQ(3, checker.path_cnt());

  checker.reset();
  tracer().reset();

  EXPECT_FALSE(checker.branch(v < 0));
  tracer().append_thread_begin_event();
  EXPECT_EQ(2, tracer().current_thread_id());
  tracer().append_thread_end_event();

  EXPECT_TRUE(checker.find_next_path());

  // thread identifiers are reset
  tracer().append_thread_begin_event();
  EXPECT_EQ(2, tracer().current_thread_id());
  tracer().append_thread_end_event();

  // with literal condition
  checker.reset();
  EXPECT_TRUE(checker.branch(true));
  EXPECT_FALSE(checker.find_next_path());

  checker.reset();
  EXPECT_FALSE(checker.branch(false));
  EXPECT_FALSE(checker.find_next_path());

  // ignore direction suggestion when condition is a literal
  checker.reset();
  EXPECT_TRUE(checker.branch(true, false));
  EXPECT_FALSE(checker.find_next_path());

  checker.reset();
  EXPECT_FALSE(checker.branch(false, true));
  EXPECT_FALSE(checker.find_next_path());
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
  DfsChecker checker;
  Encoder encoder;

  External<int> i = 1;
  i = 2;
  tracer().append_thread_begin_event();
  checker.add_error(i == 2);
  tracer().append_thread_end_event();

  EXPECT_TRUE(checker.assertions().empty());
  EXPECT_EQ(smt::sat, encoder.check(tracer(), checker));
}

TEST(CrvTest, UnsatInsideThread)
{
  tracer().reset();
  DfsChecker checker;
  Encoder encoder;

  External<int> i = 1;
  i = 2;
  tracer().append_thread_begin_event();
  checker.add_error(i == 3);
  tracer().append_thread_end_event();

  EXPECT_TRUE(checker.assertions().empty());
  EXPECT_EQ(smt::unsat, encoder.check(tracer(), checker));
}

TEST(CrvTest, Assertions)
{
  tracer().reset();
  DfsChecker checker;
  Encoder encoder;

  External<bool> true_bool(true);

  // satisfy precondition of Encoder::check(const Tracer&)
  checker.add_error(true_bool);

  EXPECT_TRUE(checker.assertions().empty());
  External<int> i = 1;
  checker.add_assertion(i == 1);
  EXPECT_FALSE(checker.assertions().empty());
  EXPECT_EQ(smt::sat, encoder.check(tracer(), checker));
  checker.add_assertion(i == 3);
  EXPECT_FALSE(checker.assertions().empty());

  // conjunction
  EXPECT_EQ(smt::unsat, encoder.check(tracer(), checker));

  // idempotent
  EXPECT_FALSE(checker.assertions().empty());
}

TEST(CrvTest, Errors)
{
  tracer().reset();
  DfsChecker checker;
  Encoder encoder;

  EXPECT_TRUE(checker.errors().empty());
  External<int> i = 1;
  checker.add_error(i == 1);
  EXPECT_FALSE(checker.errors().empty());
  EXPECT_EQ(smt::sat, encoder.check(tracer(), checker));
  checker.add_error(i == 3);
  EXPECT_FALSE(checker.errors().empty());

  // disjunction
  EXPECT_EQ(smt::sat, encoder.check(tracer(), checker));

  // idempotent
  EXPECT_FALSE(checker.errors().empty());
}

TEST(CrvTest, EncoderCheck)
{
  DfsChecker checker;
  Encoder encoder;

  tracer().reset();
  External<bool> true_bool(true);
  EXPECT_EQ(smt::sat, encoder.check(true_bool, tracer(), checker));

  // See comment in CrvTest::Guard
  tracer().reset_events();

  External<bool> false_bool(false);
  {
    EXPECT_EQ(smt::unsat, encoder.check(false_bool, tracer(), checker));
  }

  // with literal
  tracer().reset_events();

  {
    EXPECT_EQ(smt::sat, encoder.check(true, tracer(), checker));
  }

  tracer().reset_events();

  {
    EXPECT_EQ(smt::unsat, encoder.check(false, tracer(), checker));
  }
}

TEST(CrvTest, Guard)
{
  tracer().reset();
  DfsChecker checker;
  Encoder encoder;

  Internal<int> i;

  {
    EXPECT_FALSE(checker.branch(i < 3));
    EXPECT_EQ(smt::sat, encoder.check(i == 3, tracer(), checker));
    EXPECT_EQ(smt::unsat, encoder.check(i == 2, tracer(), checker));
    EXPECT_TRUE(checker.find_next_path());
    EXPECT_TRUE(checker.branch(i < 3));
    EXPECT_EQ(smt::unsat, encoder.check(i == 3, tracer(), checker));
    EXPECT_EQ(smt::sat, encoder.check(i == 2, tracer(), checker));
    EXPECT_FALSE(checker.find_next_path());
  }

  // We don't call tracer().reset() because MathSAT5 keeps
  // SMT terms even if push/pop is used. This is no problem
  // as long as we avoid calling reset_event_identifiers().
  tracer().reset_events();
  checker.reset();

  External<int> j;

  make_any(j);
  {
    EXPECT_FALSE(checker.branch(j < 3));
    EXPECT_EQ(smt::sat, encoder.check(j == 3, tracer(), checker));
    EXPECT_EQ(smt::unsat, encoder.check(j == 2, tracer(), checker));
    EXPECT_TRUE(checker.find_next_path());
  }

  make_any(j);
  {
    EXPECT_TRUE(checker.branch(j < 3));
    EXPECT_EQ(smt::unsat, encoder.check(j == 3, tracer(), checker));
    EXPECT_EQ(smt::sat, encoder.check(j == 2, tracer(), checker));
    EXPECT_FALSE(checker.find_next_path());
  }

  // see above
  tracer().reset_events();
  checker.reset();

  {
    EXPECT_FALSE(checker.branch(false, false));
    EXPECT_TRUE(checker.branch(true, true));
    checker.add_error(true);
    EXPECT_EQ(smt::sat, encoder.check(tracer(), checker));
    EXPECT_FALSE(checker.find_next_path());
  }

  // see above
  tracer().reset_events();
  checker.reset();

  {
    EXPECT_TRUE(checker.branch(true, false));
    checker.add_error(true);
    EXPECT_EQ(smt::sat, encoder.check(tracer(), checker));
    EXPECT_FALSE(checker.find_next_path());
  }

  // see above
  tracer().reset_events();
  checker.reset();

  External<bool> false_bool;
  External<bool> true_bool;

  {
    false_bool = false;
    true_bool = true;
    EXPECT_FALSE(checker.branch(false_bool));
    EXPECT_EQ(smt::sat, encoder.check(true_bool, tracer(), checker));
    EXPECT_TRUE(checker.find_next_path());
  }

  {
    false_bool = false;
    true_bool = true;
    EXPECT_TRUE(checker.branch(false_bool));
    EXPECT_EQ(smt::unsat, encoder.check(true_bool, tracer(), checker));
    EXPECT_FALSE(checker.find_next_path());
  }

  // see above
  tracer().reset_events();
  checker.reset();

  {
    false_bool = false;
    true_bool = true;
    EXPECT_FALSE(checker.branch(true_bool));
    EXPECT_EQ(smt::unsat, encoder.check(true_bool, tracer(), checker));
    EXPECT_TRUE(checker.find_next_path());
  }

  {
    false_bool = false;
    true_bool = true;
    EXPECT_TRUE(checker.branch(true_bool));
    EXPECT_EQ(smt::sat, encoder.check(true_bool, tracer(), checker));
    EXPECT_FALSE(checker.find_next_path());
  }

  // see above
  tracer().reset_events();
  checker.reset();

  {
    false_bool = false;
    true_bool = true;
    EXPECT_FALSE(checker.branch(false_bool));
    EXPECT_FALSE(checker.branch(true_bool));
    EXPECT_EQ(smt::unsat, encoder.check(true_bool, tracer(), checker));
    EXPECT_TRUE(checker.find_next_path());
  }

  {
    false_bool = false;
    true_bool = true;
    EXPECT_FALSE(checker.branch(false_bool));
    EXPECT_TRUE(checker.branch(true_bool));
    EXPECT_EQ(smt::sat, encoder.check(true_bool, tracer(), checker));
    EXPECT_TRUE(checker.find_next_path());
  }

  {
    false_bool = false;
    true_bool = true;
    EXPECT_TRUE(checker.branch(false_bool));
    checker.add_error(true_bool);
    EXPECT_FALSE(checker.branch(true_bool));
    EXPECT_EQ(smt::unsat, encoder.check(true_bool, tracer(), checker));
    EXPECT_TRUE(checker.find_next_path());
  }

  {
    false_bool = false;
    true_bool = true;
    EXPECT_TRUE(checker.branch(false_bool));
    EXPECT_TRUE(checker.branch(true_bool));
    EXPECT_EQ(smt::unsat, encoder.check(true_bool, tracer(), checker));
    EXPECT_FALSE(checker.find_next_path());
  }

  // see above
  tracer().reset_events();
  checker.reset();

  {
    false_bool = false;
    true_bool = true;
    EXPECT_FALSE(checker.branch(false_bool));
    EXPECT_FALSE(checker.branch(true_bool));
    EXPECT_EQ(smt::unsat, encoder.check(true_bool, tracer(), checker));
    EXPECT_TRUE(checker.find_next_path());
  }

  {
    false_bool = false;
    true_bool = true;
    EXPECT_FALSE(checker.branch(false_bool));
    EXPECT_TRUE(checker.branch(true_bool));
    checker.add_error(true_bool);
    EXPECT_EQ(smt::sat, encoder.check(tracer(), checker));
    EXPECT_TRUE(checker.find_next_path());
  }

  {
    false_bool = false;
    true_bool = true;
    EXPECT_TRUE(checker.branch(false_bool));
    checker.add_error(true_bool);
    EXPECT_FALSE(checker.branch(true_bool));
    EXPECT_EQ(smt::unsat, encoder.check(tracer(), checker));
    EXPECT_TRUE(checker.find_next_path());
  }

  {
    false_bool = false;
    true_bool = true;
    EXPECT_TRUE(checker.branch(false_bool));
    checker.add_error(true_bool);
    EXPECT_TRUE(checker.branch(true_bool));
    checker.add_error(true_bool);
    EXPECT_EQ(smt::unsat, encoder.check(tracer(), checker));
    EXPECT_FALSE(checker.find_next_path());
  }
}

TEST(CrvTest, ThinAir) {
  tracer().reset();
  DfsChecker checker;
  Encoder encoder;

  External<int> x(3);

  EXPECT_EQ(smt::unsat, encoder.check(x == 42, tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(x == 3, tracer(), checker));
  EXPECT_EQ(3, tracer().events().size());
}

TEST(CrvTest, ThinAirWithThread) {
  tracer().reset();
  DfsChecker checker;
  Encoder encoder;

  External<int> x(3);
  tracer().append_thread_begin_event();
  x = 7;
  tracer().append_thread_end_event();

  EXPECT_EQ(smt::unsat, encoder.check(x == 42, tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(x == 7, tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(x == 3, tracer(), checker));
  EXPECT_EQ(8, tracer().events().size());
}

#ifndef _BV_THEORY_

TEST(CrvTest, Fib5)
{
  constexpr unsigned N = 5;

  tracer().reset();
  DfsChecker checker;
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

  EXPECT_EQ(smt::unsat, encoder.check(144 < i || 144 < j, tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(
    144 < i || 144 == i || 144 < j || 144 == j, tracer(), checker));
}

#endif

TEST(CrvTest, Stack)
{
  tracer().reset();
  DfsChecker checker;
  Encoder encoder;

  External<int> v;
  v = 3;
  tracer().append_push_event(v);

  const Internal<int> internal(tracer().append_pop_event(v));
  EXPECT_EQ(smt::unsat, encoder.check(3 != internal, tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(3 == internal, tracer(), checker));
}

TEST(CrvTest, StackApi)
{
  tracer().reset();
  DfsChecker checker;
  Encoder encoder;

  Stack<int> stack;
  External<int> external(5);
  Internal<int> internal(7);

  stack.push(3);
  stack.push(external);
  stack.push(internal);

  internal = stack.pop();
  EXPECT_EQ(smt::unsat, encoder.check(7 != internal, tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(7 == internal, tracer(), checker));

  internal = stack.pop();
  EXPECT_EQ(smt::unsat, encoder.check(5 != internal, tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(5 == internal, tracer(), checker));

  internal = stack.pop();
  EXPECT_EQ(smt::unsat, encoder.check(3 != internal, tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(3 == internal, tracer(), checker));
}

TEST(CrvTest, StackApiWithSingleThread)
{
  tracer().reset();
  DfsChecker checker;
  Encoder encoder;

  Stack<int> stack;

  tracer().append_thread_begin_event();
  stack.push(5);
  stack.push(7);
  tracer().append_thread_end_event();

  Internal<int> p0(stack.pop());
  EXPECT_EQ(smt::sat, encoder.check(5 == p0, tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(7 == p0, tracer(), checker));

  Internal<int> p1(stack.pop());

  EXPECT_EQ(smt::sat, encoder.check(5 == p0, tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(7 == p0, tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(5 == p1, tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(7 == p1, tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(7 == p0 && 5 == p1, tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(5 == p0 && 7 == p1, tracer(), checker));

  EXPECT_EQ(smt::unsat, encoder.check(!(5 != p0 || 7 == p1), tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(5 != p0 || 7 == p1, tracer(), checker));

  EXPECT_EQ(smt::unsat, encoder.check(!(7 != p0 || 5 == p1), tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(7 != p0 || 5 == p1, tracer(), checker));
}

TEST(CrvTest, StackLifo1)
{
  tracer().reset();
  DfsChecker checker;
  Encoder encoder;

  External<int> v;
  v = 3;
  tracer().append_push_event(v);
  v = 5;
  tracer().append_push_event(v);

  const Internal<int> internal(tracer().append_pop_event(v));
  EXPECT_EQ(smt::unsat, encoder.check(3 == internal, tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(5 == internal, tracer(), checker));
}

TEST(CrvTest, StackLifo2)
{
  tracer().reset();
  DfsChecker checker;
  Encoder encoder;

  External<int> v;
  v = 3;
  tracer().append_push_event(v);
  v = 5;
  tracer().append_push_event(v);
  tracer().append_pop_event(v);

  const Internal<int> internal(tracer().append_pop_event(v));
  EXPECT_EQ(smt::unsat, encoder.check(3 != internal, tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(3 == internal, tracer(), checker));
}

TEST(CrvTest, ThreeThreadsReadWriteExternal)
{
  tracer().reset();
  DfsChecker checker;
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
  EXPECT_EQ(smt::unsat, encoder.check(!(a == '\0' || a == 'P' || a == 'Q'), tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(!(a == '\0'), tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(!(a == 'P'), tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(!(a == 'Q'), tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(!(a == 'P' || a == 'Q'), tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(!(a == '\0' || a == 'P'), tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(!(a == '\0' || a == 'Q'), tracer(), checker));
}

TEST(CrvTest, SingleThreadWithExternal1)
{
  tracer().reset();
  DfsChecker checker;
  Encoder encoder;

  External<char> x;
  Internal<char> a('\0');

  x = 'A';
  a = x;

  EXPECT_EQ(smt::unsat, encoder.check(a != 'A', tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(a == 'A', tracer(), checker));
}

TEST(CrvTest, SingleThreadWithExternal2)
{
  tracer().reset();
  DfsChecker checker;
  Encoder encoder;

  External<char> x;
  Internal<char> a('\0');

  x = 'A';
  x = 'B';
  a = x;

  EXPECT_EQ(smt::unsat, encoder.check(a == 'A', tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(a == 'B', tracer(), checker));
}

TEST(CrvTest, CopyInternaltoInternal)
{
  tracer().reset();
  DfsChecker checker;
  Encoder encoder;

  Internal<char> a = 'A';
  Internal<char> b = a;

  EXPECT_EQ(smt::unsat, encoder.check(!(b == 'A'), tracer(), checker));
  EXPECT_EQ(smt::unsat, encoder.check(!(b == a), tracer(), checker));

  a = 'B';
  EXPECT_EQ(smt::sat, encoder.check(!(b == a), tracer(), checker));
}

TEST(CrvTest, CopyExternaltoInternal)
{
  tracer().reset();
  DfsChecker checker;
  Encoder encoder;

  External<char> a = 'A';
  Internal<char> b = a;

  EXPECT_EQ(smt::unsat, encoder.check(!(b == 'A'), tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(b == 'A', tracer(), checker));

  a = 'B';
  EXPECT_EQ(smt::unsat, encoder.check(!(b == 'A'), tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(b == 'A', tracer(), checker));
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

TEST(CrvTest, CompareArrayElements)
{
  tracer().reset();
  DfsChecker checker;
  Encoder encoder;

  External<int[2]> a;

  make_any(a[0]);
  make_any(a[1]);

  EXPECT_EQ(smt::sat, encoder.check(a[0] < a[1], tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(a[0] <= a[1], tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(a[0] > a[1], tracer(), checker));

  checker.add_assertion(a[0] < a[1]);
  EXPECT_EQ(smt::sat, encoder.check(a[0] < a[1], tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(a[0] <= a[1], tracer(), checker));
  EXPECT_EQ(smt::unsat, encoder.check(a[0] > a[1], tracer(), checker));
}

TEST(CrvTest, SwapArrayElements)
{
  tracer().reset();
  DfsChecker checker;
  Encoder encoder;

  External<int[2]> a;
  make_any(a[0]);
  make_any(a[1]);

  checker.add_assertion(a[1] < a[0]);

  // swap
  Internal<int> t = a[0];
  a[0] = a[1];
  a[1] = t;

  EXPECT_EQ(smt::unsat, encoder.check(a[1] < a[0], tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(a[0] <= a[1], tracer(), checker));
}

// Future extension note: if another initialization value is
// sought (e.g. a nondeterministic value), then is is _not_
// enough to remove "ld.term == std::move(ld_zero)" inside
// Encoder::encode_load_from(const PerAddressIndex&) because
// it would give the wrong results for sequential code such
// as "a[0]; a[0]". Instead, the ld_zero term would have to
// be replaced by a function application "f(ld.offset_term)".
TEST(CrvTest, InitialArray)
{
  tracer().reset();
  DfsChecker checker;
  Encoder encoder;

  External<int[1]> a;

  // array elements are initialized to zero (see load_from)
  EXPECT_EQ(smt::unsat, encoder.check(a[0] != 0, tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(a[0] == 0, tracer(), checker));

  Internal<int> s = 42;
  checker.add_assertion(a[0] == s);
  Internal<int> t = a[0];

  // (incorrectly) SAT when "ld.term == std::move(ld_zero)"
  // in Encoder::encode_load_from() function is removed
  EXPECT_EQ(smt::unsat, encoder.check(t != s, tracer(), checker));

  // unsat due to zero initialization (see above)
  EXPECT_EQ(smt::unsat, encoder.check(t == s, tracer(), checker));
}

TEST(CrvTest, ExternalArrayWithLiteralOffset) {
  tracer().reset();
  DfsChecker checker;
  Encoder encoder;

  External<char[5]> x;

  x[2] = 'Z';
  Internal<char> a(x[2]);
  EXPECT_EQ(smt::unsat, encoder.check(a != 'Z', tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(a == 'Z', tracer(), checker));

  // initial array elements are zero
  Internal<char> b(x[3]);
  Internal<char> c(x[4]);
  EXPECT_EQ(smt::unsat, encoder.check(b != '\0', tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(b == '\0', tracer(), checker));
  EXPECT_EQ(smt::unsat, encoder.check(c != '\0', tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(c == '\0', tracer(), checker));
}

TEST(CrvTest, ExternalArrayWithExternalOffset)
{
  tracer().reset();
  DfsChecker checker;
  Encoder encoder;

  External<char[3]> xs;
  External<size_t> index(1);
  Internal<char> a('\0');

  xs[index] = 'Y';
 
  index = index + static_cast<size_t>(1);
  xs[index] = 'Z';

  a = xs[0];
  EXPECT_EQ(smt::unsat, encoder.check(a == 'Z', tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(a != 'Z', tracer(), checker));

  a = xs[1];
  EXPECT_EQ(smt::unsat, encoder.check(a == 'Z', tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(a != 'Z', tracer(), checker));

  a = xs[2];
  EXPECT_EQ(smt::unsat, encoder.check(a != 'Z', tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(a == 'Z', tracer(), checker));

  a = xs[index];
  EXPECT_EQ(smt::unsat, encoder.check(a != 'Z', tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(a == 'Z', tracer(), checker));

  // Out of bound array access does not cause an error.
  index = index + static_cast<size_t>(1);
  a = xs[index];
  EXPECT_EQ(smt::unsat, encoder.check(a == 'Z', tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(a != 'Z', tracer(), checker));
}

TEST(CrvTest, MultipleExternalArrayStoresWithLiteralOffset)
{
  tracer().reset();
  DfsChecker checker;
  Encoder encoder;

  External<char[3]> xs;
  Internal<char> a('\0');

  xs[0] = 'A';
  xs[1] = 'B';

  a = xs[1];

  EXPECT_EQ(smt::unsat, encoder.check(a != 'B', tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(a == 'B', tracer(), checker));
}

TEST(CrvTest, MultipleExternalArrayStoresWithExternalOffset)
{
  tracer().reset();
  DfsChecker checker;
  Encoder encoder;

  External<char[3]> xs;
  External<size_t> index;
  Internal<char> a('\0');

  index = 0;
  xs[index] = 'A';

  index = index + static_cast<size_t>(1);
  xs[index] = 'B';

  a = xs[index];

  EXPECT_EQ(smt::unsat, encoder.check(a != 'B', tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(a == 'B', tracer(), checker));
}

TEST(CrvTest, JoinThreads)
{
  tracer().reset();
  DfsChecker checker;
  Encoder encoder;

  External<char> x('\0');

  const ThreadIdentifier parent_thread_id(tracer().append_thread_begin_event());
  EXPECT_EQ(1, parent_thread_id);
  EXPECT_EQ(parent_thread_id + 1, tracer().current_thread_id());

  x = 'A';

  const ThreadIdentifier child_thread_id(tracer().append_thread_end_event());
  EXPECT_EQ(2, child_thread_id);
  EXPECT_EQ(parent_thread_id, tracer().current_thread_id());

  EXPECT_EQ(smt::sat, encoder.check(x == '\0', tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(x == 'A', tracer(), checker));

  tracer().append_join_event(child_thread_id);

  EXPECT_EQ(smt::unsat, encoder.check(x == '\0', tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(x == 'A', tracer(), checker));
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
  DfsChecker checker;
  Encoder encoder;

  External<char[]> array;

  Thread t1(array_t0, array);
  Thread t2(array_t1, array);
  t1.join();
  t2.join();
 
  EXPECT_TRUE(checker.assertions().empty());
  EXPECT_TRUE(checker.errors().empty());
  EXPECT_EQ(smt::unsat, encoder.check(array[0] != 'X' && array[0] != 'Y', tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(array[0] != 'X', tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(array[0] != 'Y', tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(array[0] == 'X', tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(array[0] == 'Y', tracer(), checker));
  EXPECT_FALSE(checker.find_next_path());
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
  DfsChecker checker;
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
 
  EXPECT_TRUE(checker.assertions().empty());
  EXPECT_TRUE(checker.errors().empty());
  EXPECT_EQ(smt::unsat, encoder.check(sum == 4, tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(sum == 3, tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(sum != 3, tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(sum == 2, tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(sum != 2, tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(sum == 1, tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(sum != 1, tracer(), checker));
  EXPECT_EQ(smt::unsat, encoder.check(sum == 0, tracer(), checker));

  EXPECT_FALSE(checker.find_next_path());
}

TEST(CrvTest, SatScopeWithNondeterminsticGuardInSingleThread)
{
  tracer().reset();
  DfsChecker checker;
  Encoder encoder;

  External<bool> nondet_bool;
  External<char> x;
  Internal<char> a('\0');

  x = 'A';
  checker.scope_then(nondet_bool);
  x = 'B';
  checker.scope_else();
  x = 'C';
  checker.scope_end();
  a = x;

  EXPECT_EQ(smt::sat, encoder.check(a == 'B', tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(a != 'C', tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(a == 'B' && a != 'C', tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(a == 'C', tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(a != 'B' && a == 'C', tracer(), checker));
}

TEST(CrvTest, SatScopeWithNondeterminsticGuardAndArrayInSingleThread)
{
  tracer().reset();
  DfsChecker checker;
  Encoder encoder;

  External<bool> nondet_bool;
  External<char[3]> xs;
  Internal<char> a('\0');

  xs[2] = 'A';
  checker.scope_then(nondet_bool);
  xs[2] = 'B';
  checker.scope_else();
  xs[2] = 'C';
  checker.scope_end();
  a = xs[2];

  EXPECT_EQ(smt::sat, encoder.check(a == 'B', tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(a != 'C', tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(a == 'B' && a != 'C', tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(a == 'C', tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(a != 'B' && a == 'C', tracer(), checker));
}

TEST(CrvTest, SatScopeWithDeterminsticGuardAndArrayInSingleThread)
{
  tracer().reset();
  DfsChecker checker;
  Encoder encoder;

  External<char[3]> x;
  External<char> p('\0');
  Internal<char> a('\0');
  
  p = '?';
  x[2] = 'A';
  checker.scope_then(p == '?');
  x[2] = 'B';
  checker.scope_else();
  x[2] = 'C'; // unreachable
  checker.scope_end();
  a = x[2];

  EXPECT_EQ(smt::sat, encoder.check(a == 'B', tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(a != 'C', tracer(), checker));
  EXPECT_EQ(smt::unsat, encoder.check(a == 'C', tracer(), checker));
}

TEST(CrvTest, UnsatScopeInSingleThread)
{
  tracer().reset();
  DfsChecker checker;
  Encoder encoder;

  External<int> var;

  checker.scope_then(0 < var);
  checker.add_error(var == 0);
  checker.scope_end();

  EXPECT_EQ(smt::unsat, encoder.check(tracer(), checker));
}

TEST(CrvTest, UnsatScopeInMultipleThread)
{
  tracer().reset();
  DfsChecker checker;
  Encoder encoder;

  External<int> var;

  tracer().append_thread_begin_event();
  checker.scope_then(0 < var);
  checker.add_error(var == 0);
  checker.scope_end();
  tracer().append_thread_end_event();

  EXPECT_EQ(smt::unsat, encoder.check(tracer(), checker));
}

TEST(CrvTest, UnsatScopeErrorConditionDueToFalseGuard)
{
  tracer().reset();
  DfsChecker checker;
  Encoder encoder;

  External<bool> true_bool(true);
  External<bool> false_bool(false);
  checker.scope_then(false_bool);
  checker.add_error(true_bool);
  checker.scope_end();

  EXPECT_EQ(smt::unsat, encoder.check(tracer(), checker));
}

TEST(CrvTest, SatFlipWithNondeterminsticGuardInSingleThread)
{
  tracer().reset();
  DfsChecker checker;
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
    if (checker.branch(nondet_bool))
      x = 'B';
    else
      x = 'C';
    a = x;

    r0 |= smt::sat == encoder.check(a == 'B', tracer(), checker);
    r1 |= smt::sat == encoder.check(a != 'C', tracer(), checker);
    r2 |= smt::sat == encoder.check(a == 'B' && a != 'C', tracer(), checker);
    r3 |= smt::sat == encoder.check(a == 'C', tracer(), checker);
    r4 |= smt::sat == encoder.check(a != 'B' && a == 'C', tracer(), checker);
  }
  while (checker.find_next_path());

  EXPECT_EQ(1, checker.path_cnt());
  EXPECT_TRUE(r0);
  EXPECT_TRUE(r1);
  EXPECT_TRUE(r2);
  EXPECT_TRUE(r3);
  EXPECT_TRUE(r4);
}

TEST(CrvTest, SatFlipWithNondeterminsticGuardAndArrayInSingleThread)
{
  tracer().reset();
  DfsChecker checker;
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
    if (checker.branch(nondet_bool))
      xs[2] = 'B';
    else
      xs[2] = 'C';
    a = xs[2];
  
    r0 |= smt::sat == encoder.check(a == 'B', tracer(), checker);
    r1 |= smt::sat == encoder.check(a != 'C', tracer(), checker);
    r2 |= smt::sat == encoder.check(a == 'B' && a != 'C', tracer(), checker);
    r3 |= smt::sat == encoder.check(a == 'C', tracer(), checker);
    r4 |= smt::sat == encoder.check(a != 'B' && a == 'C', tracer(), checker);
  }
  while (checker.find_next_path());

  EXPECT_EQ(1, checker.path_cnt());
  EXPECT_TRUE(r0);
  EXPECT_TRUE(r1);
  EXPECT_TRUE(r2);
  EXPECT_TRUE(r3);
  EXPECT_TRUE(r4);
}

TEST(CrvTest, SatFlipWithDeterminsticGuardAndArrayInSingleThread)
{
  tracer().reset();
  DfsChecker checker;
  Encoder encoder;

  bool r0 = false;
  bool r1 = false;
  bool r2 = true;

  do
  {
    External<char[3]> x;
    External<char> p('\0');
    Internal<char> a('\0');
  
    p = '?';
    x[2] = 'A';
    if (checker.branch(p == '?'))
      x[2] = 'B';
    else
      x[2] = 'C'; // unreachable
    a = x[2];
  

    r0 |= smt::sat == encoder.check(a == 'B', tracer(), checker);
    r1 |= smt::sat == encoder.check(a != 'C', tracer(), checker);
    r1 &= smt::unsat == encoder.check(a == 'C', tracer(), checker);
  }
  while (checker.find_next_path());

  EXPECT_EQ(1, checker.path_cnt());
  EXPECT_TRUE(r0);
  EXPECT_TRUE(r1);
  EXPECT_TRUE(r2);
}

TEST(CrvTest, UnsatFlipInSingleThread)
{
  tracer().reset();
  DfsChecker checker;
  Encoder encoder;

  unsigned checks = 0;
  unsigned unchecks = 0;

  do
  {
    External<int> var;

    if (checker.branch(0 < var))
      checker.add_error(var == 0);

    if (!checker.errors().empty())
    {
      checks++;
      EXPECT_EQ(smt::unsat, encoder.check(tracer(), checker));
    }
    else
    {
      unchecks++;
    }
  }
  while (checker.find_next_path());

  EXPECT_EQ(1, checker.path_cnt());
  EXPECT_EQ(1, checks);
  EXPECT_EQ(1, unchecks);
}

TEST(CrvTest, UnsatFlipInMultipleThread)
{
  tracer().reset();
  DfsChecker checker;
  Encoder encoder;

  unsigned checks = 0;
  unsigned unchecks = 0;

  do
  {
    External<int> var;

    tracer().append_thread_begin_event();
    if (checker.branch(0 < var))
      checker.add_error(var == 0);
    tracer().append_thread_end_event();

    if (!checker.errors().empty())
    {
      checks++;
      EXPECT_EQ(smt::unsat, encoder.check(tracer(), checker));
    }
    else
    {
      unchecks++;
    }
  }
  while (checker.find_next_path());

  EXPECT_EQ(1, checker.path_cnt());
  EXPECT_EQ(1, checks);
  EXPECT_EQ(1, unchecks);
}

TEST(CrvTest, UnsatFlipErrorConditionDueToFalseGuard)
{
  tracer().reset();
  DfsChecker checker;
  Encoder encoder;

  unsigned checks = 0;
  unsigned unchecks = 0;

  do
  {
    External<bool> true_bool(true);
    External<bool> false_bool(false);

    if (checker.branch(false_bool))
      checker.add_error(true_bool);

    if (!checker.errors().empty())
    {
      checks++;
      EXPECT_EQ(smt::unsat, encoder.check(tracer(), checker));
    }
    else
    {
      unchecks++;
    }
  }
  while (checker.find_next_path());

  EXPECT_EQ(1, checker.path_cnt());
  EXPECT_EQ(1, checks);
  EXPECT_EQ(1, unchecks);
}

TEST(CrvTest, FlipFour)
{
  tracer().reset();
  DfsChecker checker;
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

    if (checker.branch(false_bool))
    {
      expect = smt::unsat;
      checker.add_error(true_bool);
    }

    if (checker.branch(true_bool))
    {
      if (expect == smt::unknown)
        expect = smt::sat;
      checker.add_error(true_bool);
    }

    if (!checker.errors().empty())
    {
      switch (expect)
      {
      case smt::sat:     sat_checks++;     break;
      case smt::unsat:   unsat_checks++;   break;
      case smt::unknown: unknown_checks++; break;
      }
      EXPECT_EQ(expect, encoder.check(tracer(), checker));
    }
    else
    {
      unchecks++;
    }
  }
  while (checker.find_next_path());

  EXPECT_EQ(3, checker.path_cnt());
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

void thread_false_guard(DfsChecker& checker, const External<bool>& false_bool)
{
  checker.branch(false_bool);
}

void thread_true_error(DfsChecker& checker, const External<bool>& true_bool)
{
  checker.add_error(true_bool);
}

TEST(CrvTest, ThreadGuard)
{
  tracer().reset();
  DfsChecker checker;
  Encoder encoder;

  External<bool> true_bool(true);
  External<bool> false_bool(false);

  Thread f(thread_false_guard, checker, false_bool);
  Thread g(thread_true_error, checker, true_bool);

  EXPECT_FALSE(checker.errors().empty());
  EXPECT_EQ(smt::sat, encoder.check(tracer(), checker));

  tracer().reset();
  unsigned n = 0;

  checker.branch(false_bool);
  Thread h(thread_api_test, &n, 7);
  checker.add_error(true_bool);

  EXPECT_EQ(7, n);
  EXPECT_EQ(smt::unsat, encoder.check(tracer(), checker));
}

TEST(CrvTest, MutexSatSingleWriter1)
{
  tracer().reset();
  dfs_checker().reset();
  Encoder encoder;

  External<int> shared_var(0);

  tracer().append_thread_begin_event();
  shared_var = 3;
  shared_var = shared_var + 1;
  tracer().append_thread_end_event();

  tracer().append_thread_begin_event();
  dfs_checker().add_error(shared_var == 3);
  tracer().append_thread_end_event();

  EXPECT_TRUE(dfs_checker().assertions().empty());
  EXPECT_FALSE(dfs_checker().errors().empty());
  EXPECT_EQ(smt::sat, encoder.check(tracer(), dfs_checker()));
}

TEST(CrvTest, MutexUnsatSingleWriter1)
{
  tracer().reset();
  dfs_checker().reset();
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
  dfs_checker().add_error(shared_var == 3);
  mutex.unlock();
  tracer().append_thread_end_event();

  EXPECT_FALSE(dfs_checker().assertions().empty());
  EXPECT_FALSE(dfs_checker().errors().empty());
  EXPECT_EQ(smt::unsat, encoder.check(tracer(), dfs_checker()));
}

TEST(CrvTest, MutexSatSingleWriter2)
{
  tracer().reset();
  dfs_checker().reset();
  Encoder encoder;

  External<int> shared_var(0);

  tracer().append_thread_begin_event();
  shared_var = shared_var + 3;
  shared_var = shared_var + 1;
  tracer().append_thread_end_event();

  tracer().append_thread_begin_event();
  dfs_checker().add_error(shared_var == 3);
  tracer().append_thread_end_event();

  EXPECT_TRUE(dfs_checker().assertions().empty());
  EXPECT_FALSE(dfs_checker().errors().empty());
  EXPECT_EQ(smt::sat, encoder.check(tracer(), dfs_checker()));
}

TEST(CrvTest, MutexUnsatSingleWriter2)
{
  tracer().reset();
  dfs_checker().reset();
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
  dfs_checker().add_error(shared_var == 3);
  mutex.unlock();
  tracer().append_thread_end_event();

  EXPECT_FALSE(dfs_checker().assertions().empty());
  EXPECT_FALSE(dfs_checker().errors().empty());
  EXPECT_EQ(smt::unsat, encoder.check(tracer(), dfs_checker()));
}

TEST(CrvTest, MutexSatMultipleWriters1)
{
  tracer().reset();
  dfs_checker().reset();
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

  EXPECT_EQ(smt::sat, encoder.check(a == 'A' && b == '\2' && c == 'C', tracer(), dfs_checker()));
  EXPECT_EQ(smt::sat, encoder.check(a == '\1' && b == 'B' && c == '\3', tracer(), dfs_checker()));
}

TEST(CrvTest, MutexSatMultipleWriters2)
{
  tracer().reset();
  dfs_checker().reset();
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

  EXPECT_EQ(smt::sat, encoder.check(a == 'A' && b == '\2' && c == 'C', tracer(), dfs_checker()));
  EXPECT_EQ(smt::sat, encoder.check(a == '\1' && b == 'B' && c == '\3', tracer(), dfs_checker()));
}

TEST(CrvTest, MutexUnsatMultipleWriters)
{
  tracer().reset();
  dfs_checker().reset();
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

  EXPECT_EQ(smt::unsat, encoder.check(a == 'A' && b == '\2' && c == 'C', tracer(), dfs_checker()));
  EXPECT_EQ(smt::unsat, encoder.check(a == '\1' && b == 'B' && c == '\3', tracer(), dfs_checker()));
}

TEST(CrvTest, MutexJoinMultipleWriters)
{
  tracer().reset();
  dfs_checker().reset();
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

  EXPECT_EQ(smt::sat, encoder.check(x == 16 && y == 5, tracer(), dfs_checker()));
  EXPECT_EQ(smt::unsat, encoder.check(!(x == 16 && y == 5), tracer(), dfs_checker()));
}

TEST(CrvTest, ImmediateDominator)
{
  Tracer tracer;
  DfsChecker checker(tracer);
  EventIters e_iters;
  EventMap immediate_dominator_map;

  External<char> x('\0');
  External<bool> any_bool;

  tracer.append_thread_begin_event();
  tracer.append_write_event(x); // 1
  checker.scope_then(any_bool);
  tracer.append_write_event(x); // 2
  checker.scope_end();
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
  checker.scope_then(any_bool);
  tracer.append_write_event(x); // 2
  checker.scope_else();
  tracer.append_write_event(x); // 3
  checker.scope_end();
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
  checker.scope_then(any_bool);
  checker.scope_then(any_bool);
  tracer.append_write_event(x); // 2
  checker.scope_end();
  checker.scope_end();
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
  checker.scope_then(any_bool);
  checker.scope_then(any_bool);
  tracer.append_write_event(x); // 2
  tracer.append_write_event(x); // 3
  checker.scope_end();
  checker.scope_end();
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
  checker.scope_then(any_bool);
  checker.scope_then(any_bool);
  tracer.append_write_event(x); // 2
  checker.scope_end();
  checker.scope_else();
  tracer.append_write_event(x); // 3
  checker.scope_end();
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
  checker.scope_then(any_bool);
  checker.scope_then(any_bool);
  tracer.append_write_event(x); // 2
  checker.scope_else();
  tracer.append_write_event(x); // 3
  checker.scope_end();
  checker.scope_end();
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
  checker.scope_then(any_bool);
  tracer.append_write_event(x); // 2
  checker.scope_end();
  checker.scope_then(any_bool);
  tracer.append_write_event(x); // 3
  checker.scope_end();
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
  checker.scope_then(any_bool);
  tracer.append_write_event(x); // 2
  checker.scope_end();
  tracer.append_write_event(x); // 3
  checker.scope_then(any_bool);
  tracer.append_write_event(x); // 4
  checker.scope_end();
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
  checker.scope_then(any_bool);
  tracer.append_write_event(x); // 2
  checker.scope_else();
  tracer.append_write_event(x); // 3
  checker.scope_end();
  tracer.append_write_event(x); // 4
  checker.scope_then(any_bool);
  tracer.append_write_event(x); // 5
  checker.scope_end();
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
  checker.scope_then(any_bool);
  tracer.append_write_event(x); // 2
  checker.scope_end();
  tracer.append_write_event(x); // 3
  checker.scope_then(any_bool);
  tracer.append_write_event(x); // 4
  checker.scope_else();
  tracer.append_write_event(x); // 5
  checker.scope_end();
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
  checker.scope_then(any_bool);
  tracer.append_write_event(x); // 2
  checker.scope_else();
  checker.scope_end();
  tracer.append_write_event(x); // 3
  checker.scope_then(any_bool);
  tracer.append_write_event(x); // 4
  checker.scope_end();
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
  checker.scope_then(any_bool);
  tracer.append_write_event(x); // 2
  checker.scope_end();
  tracer.append_write_event(x); // 3
  checker.scope_then(any_bool);
  tracer.append_write_event(x); // 4
  checker.scope_else();
  checker.scope_end();
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
  checker.scope_then(any_bool);
  checker.scope_else();
  tracer.append_write_event(x); // 2
  checker.scope_end();
  tracer.append_write_event(x); // 3
  checker.scope_then(any_bool);
  tracer.append_write_event(x); // 4
  checker.scope_end();
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
  checker.scope_then(any_bool);
  tracer.append_write_event(x); // 2
  checker.scope_end();
  tracer.append_write_event(x); // 3
  checker.scope_then(any_bool);
  checker.scope_else();
  tracer.append_write_event(x); // 4
  checker.scope_end();
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
  checker.scope_then(any_bool);
  checker.scope_else();
  tracer.append_write_event(x); // 2
  checker.scope_end();
  checker.scope_then(any_bool);
  tracer.append_write_event(x); // 3
  checker.scope_end();
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
  checker.scope_then(any_bool);
  tracer.append_write_event(x); // 2
  checker.scope_end();
  checker.scope_then(any_bool);
  checker.scope_else();
  tracer.append_write_event(x); // 3
  checker.scope_end();
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
  checker.scope_then(any_bool);
  checker.scope_then(any_bool);
  tracer.append_write_event(x); // 2
  checker.scope_end();
  checker.scope_then(any_bool);
  tracer.append_write_event(x); // 3
  checker.scope_end();
  checker.scope_end();
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
  checker.scope_then(any_bool);
  checker.scope_then(any_bool);
  checker.scope_then(any_bool);
  tracer.append_write_event(x); // 2
  checker.scope_end();
  checker.scope_then(any_bool);
  tracer.append_write_event(x); // 3
  checker.scope_end();
  checker.scope_end();
  checker.scope_end();
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
  checker.scope_then(any_bool);
  checker.scope_then(any_bool);
  tracer.append_write_event(x); // 2
  checker.scope_end();
  checker.scope_then(any_bool);
  tracer.append_write_event(x); // 3
  checker.scope_end();
  checker.scope_end();
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
  tracer.append_write_event(x); // 2
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
  tracer.append_write_event(x); // 3
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
  tracer.append_write_event(x); // 2
  tracer.append_write_event(x); // 3
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
  DfsChecker checker;
  Encoder encoder;

  Channel<int> c;
  tracer().append_thread_begin_event();
  c.send(5);
  tracer().append_thread_end_event();

  EXPECT_EQ(smt::sat, encoder.check_deadlock(tracer(), checker));

  tracer().append_thread_begin_event();
  c.recv();
  tracer().append_thread_end_event();

  EXPECT_EQ(smt::unsat, encoder.check_deadlock(tracer(), checker));
}

TEST(CrvTest, DeadlockSingleRecv)
{
  tracer().reset();
  DfsChecker checker;
  Encoder encoder;

  Channel<int> c;
  tracer().append_thread_begin_event();
  c.recv();
  tracer().append_thread_end_event();

  EXPECT_EQ(smt::sat, encoder.check_deadlock(tracer(), checker));

  tracer().append_thread_begin_event();
  c.send(5);
  tracer().append_thread_end_event();

  EXPECT_EQ(smt::unsat, encoder.check_deadlock(tracer(), checker));
}

TEST(CrvTest, Deadlock)
{
  tracer().reset();
  DfsChecker checker;
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

  EXPECT_EQ(smt::sat, encoder.check_deadlock(tracer(), checker));
}

TEST(CrvTest, InitDeadlockFree)
{
  tracer().reset();
  DfsChecker checker;
  Encoder encoder;

  Channel<int> c;

  tracer().append_thread_begin_event();
  c.send(5);
  tracer().append_thread_end_event();

  tracer().append_thread_begin_event();
  c.recv();
  tracer().append_thread_end_event();

  EXPECT_EQ(smt::unsat, encoder.check_deadlock(tracer(), checker));
}

// Unlike CrvTest::InitDeadlockFree, this test also relies
// on the extension axiom implemented by Encoder
TEST(CrvTest, ExtensionDeadlockFree)
{
  tracer().reset();
  DfsChecker checker;
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

  EXPECT_EQ(smt::unsat, encoder.check_deadlock(tracer(), checker));
}

TEST(CrvTest, CommunicationValue)
{
  tracer().reset();
  DfsChecker checker;
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

  EXPECT_EQ(smt::unsat, encoder.check(r != 6, tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(r == 6, tracer(), checker));
}

TEST(CrvTest, CommunicationWithTrueGuard)
{
  tracer().reset();
  DfsChecker checker;
  Encoder encoder;

  Channel<int> c;

  tracer().append_thread_begin_event();
  c.send(5);
  EXPECT_FALSE(checker.branch(6 != c.recv()));
  c.send(7);
  tracer().append_thread_end_event();

  tracer().append_thread_begin_event();
  c.recv();
  c.send(6);
  Internal<int> r(c.recv());
  tracer().append_thread_end_event();

  EXPECT_EQ(smt::unsat, encoder.check(r != 7, tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(r == 7, tracer(), checker));
  EXPECT_EQ(smt::unsat, encoder.check_deadlock(tracer(), checker));
}

TEST(CrvTest, CommunicationWithFalseGuard)
{
  tracer().reset();
  DfsChecker checker;
  Encoder encoder;

  Channel<int> c;

  tracer().append_thread_begin_event();
  c.send(5);
  EXPECT_FALSE(checker.branch(6 == c.recv()));
  c.send(7);
  tracer().append_thread_end_event();

  tracer().append_thread_begin_event();
  c.recv();
  c.send(6);
  Internal<int> r(c.recv());
  tracer().append_thread_end_event();

  // if there is a deadlock (which there is), then receive
  // events can take on nondeterministic values.
  EXPECT_EQ(smt::sat, encoder.check(r != 7, tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(r == 7, tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check_deadlock(tracer(), checker));
}

TEST(CrvTest, ScopeCommunicationWithElse)
{
  tracer().reset();
  DfsChecker checker;
  Encoder encoder;

  Channel<int> c;

  tracer().append_thread_begin_event();
  c.send(5);
  checker.scope_then(6 == c.recv());
  c.send(7);
  checker.scope_else();
  c.send(8);
  checker.scope_end();
  tracer().append_thread_end_event();

  tracer().append_thread_begin_event();
  c.recv();
  c.send(6);
  Internal<int> r(c.recv());
  tracer().append_thread_end_event();

  EXPECT_EQ(smt::unsat, encoder.check(r != 7, tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(r == 7, tracer(), checker));
  EXPECT_EQ(smt::unsat, encoder.check_deadlock(tracer(), checker));
}

TEST(CrvTest, ScopeCommunicationWithFalseThen)
{
  tracer().reset();
  DfsChecker checker;
  Encoder encoder;

  Channel<int> c;

  tracer().append_thread_begin_event();
  c.send(5);
  checker.scope_then(6 != c.recv());
  c.send(7);
  checker.scope_end();
  tracer().append_thread_end_event();

  tracer().append_thread_begin_event();
  c.recv();
  c.send(6);
  Internal<int> r(c.recv());
  tracer().append_thread_end_event();

  // if there is a deadlock (which there is), then receive
  // events can take on nondeterministic values.
  EXPECT_EQ(smt::sat, encoder.check(r != 7, tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(r == 7, tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check_deadlock(tracer(), checker));
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

// Literals cannot be lazy
TEST(CrvTest, LazyInternal)
{
  tracer().reset();

  External<int> x;
  Internal<int> a(x);
  EXPECT_FALSE(a.is_lazy());
  EXPECT_FALSE(a.is_literal());
  EXPECT_EQ(Internal<int>::term(a).addr(), Internal<int>::term(a).addr());

  Internal<int> b(Internal<int>::make_lazy<smt::ADD>(a, 5));
  EXPECT_TRUE(b.is_lazy());
  EXPECT_FALSE(b.is_literal());
#ifdef ENABLE_HASH_CONS
  EXPECT_EQ(Internal<int>::term(b).addr(), Internal<int>::term(b).addr());
#else
  EXPECT_NE(Internal<int>::term(b).addr(), Internal<int>::term(b).addr());
#endif
  EXPECT_EQ(5, roperand<smt::ADD>(b));

  Internal<int> c(Internal<int>::propagate<smt::ADD>(b, 3));
  EXPECT_TRUE(c.is_lazy());
  EXPECT_FALSE(c.is_literal());
  EXPECT_EQ(5 + 3, roperand<smt::ADD>(c));

  Internal<int> d(Internal<int>::make_lazy<smt::MUL>(c, 7));
  EXPECT_TRUE(d.is_lazy());
  EXPECT_FALSE(d.is_literal());
  EXPECT_EQ(7, roperand<smt::MUL>(d));

  Internal<int> e(Internal<int>::propagate<smt::MUL>(d, 8));
  EXPECT_TRUE(e.is_lazy());
  EXPECT_FALSE(e.is_literal());
  EXPECT_EQ(7 * 8, roperand<smt::MUL>(e));

  // rvalue reference arguments
  Internal<int> f(Internal<int>::make_lazy<smt::ADD>(std::move(a), 5));
  EXPECT_TRUE(f.is_lazy());
  EXPECT_FALSE(f.is_literal());
#ifdef ENABLE_HASH_CONS
  EXPECT_EQ(Internal<int>::term(f).addr(), Internal<int>::term(f).addr());
#else
  EXPECT_NE(Internal<int>::term(f).addr(), Internal<int>::term(f).addr());
#endif
  EXPECT_EQ(5, roperand<smt::ADD>(f));

  Internal<int> g(Internal<int>::propagate<smt::ADD>(std::move(b), 3));
  EXPECT_TRUE(g.is_lazy());
  EXPECT_FALSE(g.is_literal());
  EXPECT_EQ(5 + 3, roperand<smt::ADD>(g));

  Internal<int> h(Internal<int>::make_lazy<smt::MUL>(std::move(c), 7));
  EXPECT_TRUE(h.is_lazy());
  EXPECT_FALSE(h.is_literal());
  EXPECT_EQ(7, roperand<smt::MUL>(h));
}

TEST(CrvTest, SimplifierMakeLazyAndConstantPropagation)
{
  tracer().reset();
  DfsChecker checker;
  Encoder encoder;

  External<int> x = 0;
  Internal<int> a = 1;
  Internal<int> b = x;
  EXPECT_FALSE(b.is_lazy());
  EXPECT_FALSE(b.is_literal());

  b = simplifier::Lazy::apply<smt::ADD>(b, 5);
  EXPECT_TRUE(b.is_lazy());
  EXPECT_FALSE(b.is_literal());

  b = simplifier::Lazy::apply<smt::ADD>(b, 3);
  EXPECT_TRUE(b.is_lazy());
  EXPECT_FALSE(b.is_literal());

  EXPECT_EQ(smt::unsat, encoder.check(!(b == 8), tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(b == 8, tracer(), checker));
  EXPECT_EQ(8, roperand<smt::ADD>(b));

  EXPECT_TRUE((a < 2).is_literal());
  EXPECT_TRUE((a < 2).literal());

  EXPECT_TRUE((2 < a).is_literal());
  EXPECT_FALSE((2 < a).literal());

  EXPECT_FALSE((b < 3).is_literal());
  EXPECT_TRUE((2 < a && b < 3).is_literal());
  EXPECT_FALSE((2 < a && b < 3).literal());
  EXPECT_TRUE((a < 2 || b < 3).is_literal());
  EXPECT_TRUE((a < 2 || b < 3).literal());

  // rvalue reference arguments
  Internal<int> c = x;
  EXPECT_FALSE(c.is_lazy());
  EXPECT_FALSE(c.is_literal());

  Internal<int> d = simplifier::Lazy::apply<smt::ADD>(std::move(c), 5);
  EXPECT_TRUE(d.is_lazy());
  EXPECT_FALSE(d.is_literal());

  Internal<int> e = simplifier::Lazy::apply<smt::ADD>(std::move(d), 3);
  EXPECT_TRUE(e.is_lazy());
  EXPECT_FALSE(e.is_literal());

  EXPECT_EQ(smt::unsat, encoder.check(!(e == 8), tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(e == 8, tracer(), checker));
  EXPECT_EQ(8, roperand<smt::ADD>(e));
}

TEST(CrvTest, SimplifierOnlyConstantPropagation)
{
  tracer().reset();
  DfsChecker checker;
  Encoder encoder;

  Internal<int> b(0);
  EXPECT_TRUE(b.is_literal());
  EXPECT_EQ(0, b.literal());

  b = simplifier::Lazy::apply<smt::ADD>(b, 5);
  EXPECT_TRUE(b.is_literal());
  EXPECT_EQ(5, b.literal());

  b = simplifier::Lazy::apply<smt::ADD>(b, 3);
  EXPECT_TRUE(b.is_literal());
  EXPECT_EQ(8, b.literal());

  EXPECT_EQ(smt::unsat, encoder.check(!(b == 8), tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(b == 8, tracer(), checker));

  // rvalue reference arguments, copy constructors and assignment operators
  Internal<int> c = b;
  EXPECT_TRUE(c.is_literal());
  EXPECT_EQ(8, c.literal());

  Internal<int> d = simplifier::Lazy::apply<smt::ADD>(std::move(c), 2);
  EXPECT_TRUE(d.is_literal());
  EXPECT_EQ(10, d.literal());

  Internal<int> e = simplifier::Lazy::apply<smt::ADD>(std::move(d), 4);
  EXPECT_TRUE(e.is_literal());
  EXPECT_EQ(14, e.literal());

  d = simplifier::Lazy::apply<smt::ADD>(std::move(b), 1);
  EXPECT_TRUE(d.is_literal());
  EXPECT_EQ(9, d.literal());

  EXPECT_EQ(smt::unsat, encoder.check(!(e == 14), tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(e == 14, tracer(), checker));

  EXPECT_EQ(smt::unsat, encoder.check(!(d == 9), tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(d == 9, tracer(), checker));
}

TEST(CrvTest, SimplifyInternalOperations)
{
  tracer().reset();
  DfsChecker checker;
  Encoder encoder;

  External<int> a = 0;
  Internal<int> b = a;
  EXPECT_FALSE(b.is_lazy());
  EXPECT_FALSE(b.is_literal());

  b = b + 5; 
  EXPECT_TRUE(b.is_lazy());
  EXPECT_FALSE(b.is_literal());

  b = b + 3; 
  EXPECT_TRUE(b.is_lazy());
  EXPECT_FALSE(b.is_literal());

  EXPECT_EQ(smt::unsat, encoder.check(!(b == 8), tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(b == 8, tracer(), checker));
  EXPECT_EQ(8, roperand<smt::ADD>(b));

  b = 8;
  EXPECT_FALSE(b.is_lazy());
  EXPECT_TRUE(b.is_literal());

  b = b + 2;
  EXPECT_FALSE(b.is_lazy());
  EXPECT_TRUE(b.is_literal());
  EXPECT_EQ(10, b.literal());

  b = b + 4;
  EXPECT_FALSE(b.is_lazy());
  EXPECT_TRUE(b.is_literal());
  EXPECT_EQ(14, b.literal());

  b = b * 2;
  EXPECT_FALSE(b.is_lazy());
  EXPECT_TRUE(b.is_literal());
  EXPECT_EQ(28, b.literal());

  // non-monoid operator
  b = b / 4;
  EXPECT_FALSE(b.is_lazy());
  EXPECT_TRUE(b.is_literal());
  EXPECT_EQ(7, b.literal());

  Internal<bool> true_relation(b == 7);
  EXPECT_FALSE(true_relation.is_lazy());
  EXPECT_TRUE(true_relation.is_literal());
  EXPECT_TRUE(true_relation.literal());

  Internal<bool> false_relation(b != 7);
  EXPECT_FALSE(false_relation.is_lazy());
  EXPECT_TRUE(false_relation.is_literal());
  EXPECT_FALSE(false_relation.literal());
}

TEST(CrvTest, CommutativeGroup)
{
  // nongroup since signed overflow is undefined
  static_assert(!simplifier::CommutativeGroupOp<smt::ADD, int>::is_group(), "");
  static_assert(simplifier::CommutativeGroupOp<smt::ADD, unsigned>::is_group(), "");

  // nongroup due to rounding
  static_assert(!simplifier::CommutativeGroupOp<smt::MUL, int>::is_group(), "");
  static_assert(!simplifier::CommutativeGroupOp<smt::MUL, unsigned>::is_group(), "");

  static_assert(!simplifier::CommutativeGroupOp<smt::GTR, bool>::is_group(), "");

  EXPECT_FALSE((simplifier::Op<smt::ADD, int>::op_ptr()->is_group()));
  EXPECT_TRUE((simplifier::Op<smt::ADD, unsigned>::op_ptr()->is_group()));

  EXPECT_FALSE((simplifier::Op<smt::MUL, int>::op_ptr()->is_group()));
  EXPECT_FALSE((simplifier::Op<smt::MUL, unsigned>::op_ptr()->is_group()));

  EXPECT_FALSE((simplifier::Op<smt::GTR, bool>::op_ptr()->is_group()));

  EXPECT_EQ(-2U, (simplifier::Op<smt::ADD, unsigned>::op_ptr()->inverse(2U)));
  EXPECT_EQ(5U, (simplifier::Op<smt::ADD, unsigned>::op_ptr()->right_cancel(5U, 2U)) + 2U);
  EXPECT_EQ(2U, (simplifier::Op<smt::ADD, unsigned>::op_ptr()->right_cancel(2U, 5U)) + 5U);
}

TEST(CrvTest, LazyGroup)
{
  tracer().reset();
  Encoder encoder;

  External<int> x;
  External<unsigned> y;

  // Since overflow of unsigned ints is undefined,
  // Internal<int> can never be a lazy group.
  Internal<int> a(3);
  Internal<int> a_lazy = x;
  EXPECT_FALSE(a.is_lazy());
  EXPECT_FALSE(a.is_lazy_group());

  a_lazy = a_lazy + 2;
  EXPECT_TRUE(a_lazy.is_lazy());
  EXPECT_FALSE(a_lazy.is_lazy_group());

  // still not lazy
  Internal<unsigned> b(3);
  EXPECT_FALSE(b.is_lazy());
  EXPECT_FALSE(b.is_lazy_group());

  // finally, lazy group
  Internal<unsigned> c = y;
  c = c + 2U;
  EXPECT_TRUE(c.is_lazy());
  EXPECT_TRUE(c.is_lazy_group());

  EXPECT_EQ(-5U, c.op().inverse(5U));
  EXPECT_EQ(2U, c.op().right_cancel(7U, 5U));
  EXPECT_EQ(-2U, c.op().right_cancel(5U, 7U));
}

TEST(CrvTest, PostIncrement)
{
  tracer().reset();
  DfsChecker checker;
  Encoder encoder;

  Internal<short> a(3);
  EXPECT_FALSE(a.is_lazy());
  EXPECT_TRUE(a.is_literal());
  EXPECT_EQ(3, a.literal());

  post_increment(a);
  EXPECT_FALSE(a.is_lazy());
  EXPECT_TRUE(a.is_literal());
  EXPECT_EQ(4, a.literal());

  External<short> b(7);
  post_increment(b);

  EXPECT_EQ(smt::unsat, encoder.check(!(b == 8), tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(b == 8, tracer(), checker));
}

#ifndef _BV_THEORY_
// Optional feature (beware it can hide bugs!)
TEST(CrvTest, BvApproximation)
{
  tracer().reset();
  DfsChecker checker; 
  Encoder encoder;

  External<unsigned int> star;
  Internal<unsigned int> n = star;
  Internal<unsigned int> x = n, y = 0u;
  checker.add_assertion(x <= 0u);

  encoder.encode_bv_approximation(tracer());
  EXPECT_EQ(smt::unsat, encoder.check(y != n, tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(y == n, tracer(), checker));

  tracer().reset();
  External<unsigned int> z = 0u;
  checker.add_error(z == 0u);
  z = z - 1u;

  // error is found as expected
  EXPECT_EQ(smt::sat, encoder.check(tracer(), checker));

  tracer().reset();
  External<unsigned int> w = 0u;
  checker.add_error(w == 0u);
  w = w - 1u;

  // error cannot be found any longer!
  encoder.encode_bv_approximation(tracer());
  EXPECT_EQ(smt::unsat, encoder.check(tracer(), checker));
}
#endif

TEST(CrvTest, InternalArray)
{
  tracer().reset();
  DfsChecker checker; 
  Encoder encoder;

  Internal<char[]> a;
  make_any(a);

  a[1] = 'A';

  Internal<char> b = a[1];
  EXPECT_EQ(smt::sat, encoder.check(b == 'A', tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(a[1] == 'A', tracer(), checker));
  EXPECT_EQ(smt::unsat, encoder.check(b != 'A', tracer(), checker));
  EXPECT_EQ(smt::unsat, encoder.check(a[1] != 'A', tracer(), checker));

  EXPECT_EQ(smt::sat, encoder.check(a[0] == 'B', tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(a[0] != 'B', tracer(), checker));
  EXPECT_EQ(smt::unsat, encoder.check(a[0] != a[0], tracer(), checker));

  EXPECT_EQ(smt::sat, encoder.check(a[2] == 'B', tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(a[2] != 'B', tracer(), checker));
  EXPECT_EQ(smt::unsat, encoder.check(a[2] != a[2], tracer(), checker));

  Internal<size_t> i;
  Internal<char> c = a[i];

  EXPECT_EQ(smt::sat, encoder.check(b == 'A', tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(a[1] == 'A', tracer(), checker));
  EXPECT_EQ(smt::unsat, encoder.check(b != 'A', tracer(), checker));
  EXPECT_EQ(smt::unsat, encoder.check(a[1] != 'A', tracer(), checker));

  EXPECT_EQ(smt::sat, encoder.check(a[0] == 'B', tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(a[0] != 'B', tracer(), checker));
  EXPECT_EQ(smt::unsat, encoder.check(a[0] != a[0], tracer(), checker));

  EXPECT_EQ(smt::sat, encoder.check(a[2] == 'B', tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(a[2] != 'B', tracer(), checker));
  EXPECT_EQ(smt::unsat, encoder.check(a[2] != a[2], tracer(), checker));

  EXPECT_EQ(smt::sat, encoder.check(c != 'A', tracer(), checker));
  EXPECT_EQ(smt::unsat, encoder.check(c != 'A' && i == 1, tracer(), checker));

  a[i] = 'B';

  EXPECT_EQ(smt::sat, encoder.check(b == 'A', tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(a[1] == 'A', tracer(), checker));
  EXPECT_EQ(smt::unsat, encoder.check(b != 'A', tracer(), checker));

  // satisfied by i equals 1
  EXPECT_EQ(smt::sat, encoder.check(a[1] != 'A', tracer(), checker));

  EXPECT_EQ(smt::sat, encoder.check(a[0] == 'B', tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(a[0] != 'B', tracer(), checker));
  EXPECT_EQ(smt::unsat, encoder.check(a[0] != a[0], tracer(), checker));

  EXPECT_EQ(smt::sat, encoder.check(a[2] == 'B', tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(a[2] != 'B', tracer(), checker));
  EXPECT_EQ(smt::unsat, encoder.check(a[2] != a[2], tracer(), checker));

  EXPECT_EQ(smt::sat, encoder.check(a[i] == 'B', tracer(), checker));
  EXPECT_EQ(smt::unsat, encoder.check(a[i] != 'B', tracer(), checker));

  EXPECT_EQ(smt::sat, encoder.check(c != 'A', tracer(), checker));
  EXPECT_EQ(smt::unsat, encoder.check(c != 'A' && i == 1, tracer(), checker));

  a[1] = a[i];

  EXPECT_EQ(smt::sat, encoder.check(b == 'A', tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(a[1] == 'B', tracer(), checker));
  EXPECT_EQ(smt::unsat, encoder.check(b != 'A', tracer(), checker));
  EXPECT_EQ(smt::unsat, encoder.check(a[1] != 'B', tracer(), checker));

  EXPECT_EQ(smt::sat, encoder.check(a[0] == 'B', tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(a[0] != 'B', tracer(), checker));
  EXPECT_EQ(smt::unsat, encoder.check(a[0] != a[0], tracer(), checker));

  EXPECT_EQ(smt::sat, encoder.check(a[2] == 'B', tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(a[2] != 'B', tracer(), checker));
  EXPECT_EQ(smt::unsat, encoder.check(a[2] != a[2], tracer(), checker));

  EXPECT_EQ(smt::sat, encoder.check(a[i] == 'B', tracer(), checker));
  EXPECT_EQ(smt::unsat, encoder.check(a[i] != 'B', tracer(), checker));

  EXPECT_EQ(smt::sat, encoder.check(c != 'A', tracer(), checker));
  EXPECT_EQ(smt::unsat, encoder.check(c != 'A' && i == 1, tracer(), checker));
}

TEST(CrvTest, InternalArrayWithExplicitSize)
{
  tracer().reset();
  DfsChecker checker; 
  Encoder encoder;

  Internal<char[5]> a;
  make_any(a);

  a[1] = 'A';

  Internal<char> b = a[1];
  EXPECT_EQ(smt::sat, encoder.check(b == 'A', tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(a[1] == 'A', tracer(), checker));
  EXPECT_EQ(smt::unsat, encoder.check(b != 'A', tracer(), checker));
  EXPECT_EQ(smt::unsat, encoder.check(a[1] != 'A', tracer(), checker));

  EXPECT_EQ(smt::sat, encoder.check(a[0] == 'B', tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(a[0] != 'B', tracer(), checker));
  EXPECT_EQ(smt::unsat, encoder.check(a[0] != a[0], tracer(), checker));

  EXPECT_EQ(smt::sat, encoder.check(a[2] == 'B', tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(a[2] != 'B', tracer(), checker));
  EXPECT_EQ(smt::unsat, encoder.check(a[2] != a[2], tracer(), checker));

  Internal<size_t> i;
  Internal<char> c = a[i];

  EXPECT_EQ(smt::sat, encoder.check(b == 'A', tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(a[1] == 'A', tracer(), checker));
  EXPECT_EQ(smt::unsat, encoder.check(b != 'A', tracer(), checker));
  EXPECT_EQ(smt::unsat, encoder.check(a[1] != 'A', tracer(), checker));

  EXPECT_EQ(smt::sat, encoder.check(a[0] == 'B', tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(a[0] != 'B', tracer(), checker));
  EXPECT_EQ(smt::unsat, encoder.check(a[0] != a[0], tracer(), checker));

  EXPECT_EQ(smt::sat, encoder.check(a[2] == 'B', tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(a[2] != 'B', tracer(), checker));
  EXPECT_EQ(smt::unsat, encoder.check(a[2] != a[2], tracer(), checker));

  EXPECT_EQ(smt::sat, encoder.check(c != 'A', tracer(), checker));
  EXPECT_EQ(smt::unsat, encoder.check(c != 'A' && i == 1, tracer(), checker));

  a[i] = 'B';

  EXPECT_EQ(smt::sat, encoder.check(b == 'A', tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(a[1] == 'A', tracer(), checker));
  EXPECT_EQ(smt::unsat, encoder.check(b != 'A', tracer(), checker));

  // satisfied by i equals 1
  EXPECT_EQ(smt::sat, encoder.check(a[1] != 'A', tracer(), checker));

  EXPECT_EQ(smt::sat, encoder.check(a[0] == 'B', tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(a[0] != 'B', tracer(), checker));
  EXPECT_EQ(smt::unsat, encoder.check(a[0] != a[0], tracer(), checker));

  EXPECT_EQ(smt::sat, encoder.check(a[2] == 'B', tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(a[2] != 'B', tracer(), checker));
  EXPECT_EQ(smt::unsat, encoder.check(a[2] != a[2], tracer(), checker));

  EXPECT_EQ(smt::sat, encoder.check(a[i] == 'B', tracer(), checker));
  EXPECT_EQ(smt::unsat, encoder.check(a[i] != 'B', tracer(), checker));

  EXPECT_EQ(smt::sat, encoder.check(c != 'A', tracer(), checker));
  EXPECT_EQ(smt::unsat, encoder.check(c != 'A' && i == 1, tracer(), checker));

  a[1] = a[i];

  EXPECT_EQ(smt::sat, encoder.check(b == 'A', tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(a[1] == 'B', tracer(), checker));
  EXPECT_EQ(smt::unsat, encoder.check(b != 'A', tracer(), checker));
  EXPECT_EQ(smt::unsat, encoder.check(a[1] != 'B', tracer(), checker));

  EXPECT_EQ(smt::sat, encoder.check(a[0] == 'B', tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(a[0] != 'B', tracer(), checker));
  EXPECT_EQ(smt::unsat, encoder.check(a[0] != a[0], tracer(), checker));

  EXPECT_EQ(smt::sat, encoder.check(a[2] == 'B', tracer(), checker));
  EXPECT_EQ(smt::sat, encoder.check(a[2] != 'B', tracer(), checker));
  EXPECT_EQ(smt::unsat, encoder.check(a[2] != a[2], tracer(), checker));

  EXPECT_EQ(smt::sat, encoder.check(a[i] == 'B', tracer(), checker));
  EXPECT_EQ(smt::unsat, encoder.check(a[i] != 'B', tracer(), checker));

  EXPECT_EQ(smt::sat, encoder.check(c != 'A', tracer(), checker));
  EXPECT_EQ(smt::unsat, encoder.check(c != 'A' && i == 1, tracer(), checker));
}
