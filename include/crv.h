// Copyright 2013, Alex Horn. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

#ifndef __CRV_H_
#define __CRV_H_

#include <smt>
#include <set>
#include <map>
#include <list>
#include <stack>
#include <string>
#include <limits>
#include <cassert>
#include <type_traits>

#ifdef __CRV_DEBUG__
#include <iostream>
#endif

namespace crv
{

enum EventKind : unsigned short
{
  READ_EVENT = 1,
  WRITE_EVENT,
  POP_EVENT,
  PUSH_EVENT,
  THREAD_BEGIN_EVENT = 8,
  THREAD_END_EVENT
};

// Positive unless sync event
typedef uintptr_t Address;
typedef unsigned long EventIdentifier;
typedef unsigned ThreadIdentifier;

class Event
{
public:
  const EventKind kind;
  const EventIdentifier event_id;
  const ThreadIdentifier thread_id;
  const Address address;
  const smt::UnsafeTerm term;
  const smt::Bool guard;

  Event(
    const EventKind kind_arg,
    const EventIdentifier event_id_arg,
    const ThreadIdentifier thread_id_arg,
    const Address address_arg,
    const smt::UnsafeTerm& term_arg,
    const smt::Bool guard_arg)
  : kind(kind_arg),
    event_id(event_id_arg),
    thread_id(thread_id_arg),
    address(address_arg),
    term(term_arg),
    guard(guard_arg)
  {
    assert(is_sync() || !term.is_null());
    assert(is_thread_begin() || is_thread_end() || 0 < address);
    assert(!guard.is_null());
  }

  bool is_read() const { return kind == READ_EVENT; }
  bool is_write() const { return kind == WRITE_EVENT; }
  bool is_pop() const { return kind == POP_EVENT; }
  bool is_push() const { return kind == PUSH_EVENT; }
  bool is_thread_begin() const { return kind == THREAD_BEGIN_EVENT; }
  bool is_thread_end() const { return kind == THREAD_END_EVENT; }
  bool is_sync() const { return 8 <= kind; }
};

typedef std::list<Event> EventList;
typedef EventList::const_iterator EventIter;
typedef std::vector<EventIter> EventIterList;

struct EventKinds
{
  EventIterList reads;
  EventIterList writes;
  EventIterList pops;
  EventIterList pushes;
};

typedef std::map<Address, EventKinds> PerAddressMap;
typedef std::map<ThreadIdentifier, EventIterList> PerThreadMap;

/// Control flow decision along symbolic path
struct Flip
{
  bool direction;
  bool is_flip;

  // Nonzero initialization!
  Flip()
  : direction(true),
    is_flip(false) {}
};

typedef std::list<Flip> FlipList;
typedef std::list<Flip>::const_iterator FlipIter;

template<typename T> class Lvalue;
template<typename T> class Rvalue;

// Use smt::Bv<T> for bit-precision
template<typename T>
struct Smt
{
  typedef typename std::conditional<
    /* if */ std::is_same<bool, T>::value,
    /* then */ smt::Bool,
    /* else */ smt::Int>::type Sort;
};

class Tracer
{
private:
  static const std::string s_value_prefix;

  EventIdentifier m_event_id_cnt;
  ThreadIdentifier m_thread_id_cnt;
  EventList m_events;

  // Index event list by various keys
  PerAddressMap m_per_address_map;
  PerThreadMap m_per_thread_map;

  // always nonempty
  std::stack<ThreadIdentifier> m_thread_id_stack;

  // never null
  smt::Bool m_guard;

  unsigned long long m_flip_cnt;
  FlipList m_flips;
  FlipIter m_flip_iter;

  template<typename T>
  typename Smt<T>::Sort make_value_symbol()
  {
    assert(m_event_id_cnt < std::numeric_limits<EventIdentifier>::max());
    return smt::any<typename Smt<T>::Sort>(s_value_prefix +
      std::to_string(m_event_id_cnt++));
  }

  void append_event(Event&& e)
  {
    assert(!m_guard.is_null());
    m_events.push_back(std::move(e));

    const EventIter e_iter(--m_events.cend());
    EventKinds& a(m_per_address_map[e_iter->address]);
    switch(e_iter->kind)
    {
    case READ_EVENT: 
      a.reads.push_back(e_iter);
      break;
    case WRITE_EVENT: 
      a.writes.push_back(e_iter);
      break;
    case POP_EVENT: 
      a.pops.push_back(e_iter);
      break;
    case PUSH_EVENT: 
      a.pushes.push_back(e_iter);
      break;
    case THREAD_BEGIN_EVENT: 
    case THREAD_END_EVENT: 
      break;
    default:
      assert(false);
    }

    m_per_thread_map[m_thread_id_stack.top()].push_back(e_iter);
  }

public:
  Tracer()
  : m_event_id_cnt(0),
    m_thread_id_cnt(0),
    m_events(),
    m_per_address_map(),
    m_per_thread_map(),
    m_thread_id_stack(),
    m_guard(smt::literal<smt::Bool>(true)),
    m_flip_cnt(0),
    m_flips(),
    m_flip_iter(m_flips.cbegin())
  {
    m_thread_id_stack.push(m_thread_id_cnt++);
  }

  const EventList& events() const
  {
    return m_events;
  }

  const PerAddressMap& per_address_map() const
  {
    return m_per_address_map;
  }

  const PerThreadMap& per_thread_map() const
  {
    return m_per_thread_map;
  }

  void reset()
  {
    m_event_id_cnt = 0;
    m_thread_id_cnt = 0;
    m_events.clear();
    m_per_address_map.clear();
    m_per_thread_map.clear();

    while (!m_thread_id_stack.empty())
    {
      m_thread_id_stack.pop();
    }
    m_thread_id_stack.push(m_thread_id_cnt++);
    m_guard = smt::literal<smt::Bool>(true);

    m_flip_cnt = 0;
    m_flips.clear();
    m_flip_iter = m_flips.cbegin();
  }

  /// Depth-first search strategy

  /// \return is there more to explore?
  bool flip()
  {
    m_guard = smt::literal<smt::Bool>(true);
    m_flip_iter = m_flips.cbegin();

    while (!m_flips.empty() && m_flips.back().is_flip)
    {
      m_flips.pop_back();
    }

    if (m_flips.empty())
      return false;

    Flip& flip = m_flips.back();
    flip.direction = !flip.direction;
    flip.is_flip = true;

    m_flip_cnt++;
    return true;
  }

  unsigned long long flip_cnt() const
  {
    return m_flip_cnt;
  }

  bool append_guard(const Rvalue<bool>& rvalue);

  ThreadIdentifier append_thread_begin_event()
  {
    const EventIdentifier event_id(m_event_id_cnt++);
    append_event(
      Event(THREAD_BEGIN_EVENT,
            event_id,
            m_thread_id_stack.top(),
            0,
            smt::UnsafeTerm(),
            m_guard));

    m_thread_id_stack.push(m_thread_id_cnt++);

    append_event(
      Event(THREAD_BEGIN_EVENT,
            event_id,
            m_thread_id_stack.top(),
            0,
            smt::UnsafeTerm(),
            m_guard));

    return m_thread_id_stack.top();
  }

  ThreadIdentifier append_thread_end_event()
  {
    append_event(
      Event(THREAD_END_EVENT,
            m_event_id_cnt++,
            m_thread_id_stack.top(),
            0,
            smt::UnsafeTerm(),
            m_guard));

    m_thread_id_stack.pop();

    return m_thread_id_stack.top();
  }

  void append_join_event(const ThreadIdentifier thread_id)
  {
    const EventIter e_iter = m_per_thread_map.at(thread_id).back();
    assert(e_iter->thread_id != m_thread_id_stack.top());

    append_event(
      Event(THREAD_END_EVENT,
            e_iter->event_id,
            m_thread_id_stack.top(),
            0,
            smt::UnsafeTerm(),
            m_guard));
  }

  /// Creates a new term for the read event
  template<typename T>
  Rvalue<T> append_read_event(const Lvalue<T>&);

  /// Creates a new term for the write event
  template<typename T>
  void append_nondet_write_event(const Lvalue<T>&);

  /// Uses lvalue's term for the new write event
  template<typename T>
  void append_write_event(const Lvalue<T>&);

  /// Creates a new term for the pop event
  template<typename T>
  Rvalue<T> append_pop_event(const Lvalue<T>&);

  /// Uses lvalue's term for the new push event
  template<typename T>
  void append_push_event(const Lvalue<T>&);
};

// Global for symbolic execution
extern Tracer& tracer();

namespace internal
{
  /// Evaluate built-in arithmetic and boolean expressions
  template<smt::Opcode opcode> class Eval;

  #define EVAL_UNARY_ONLY(op, opcode)                              \
    template<>                                                     \
    struct Eval<opcode>                                            \
    {                                                              \
      template<typename U>                                         \
      static inline auto eval(const U arg)                         \
      -> decltype(op arg) { return op arg; }                       \
                                                                   \
      template<typename U>                                         \
      static constexpr auto const_eval(const U arg)                \
      -> decltype(op arg) { return op arg; }                       \
    };

  #define EVAL_BINARY_ONLY(op, opcode)                             \
    template<>                                                     \
    struct Eval<opcode>                                            \
    {                                                              \
      template<typename U, typename V>                             \
      static inline auto eval(const U larg, const V rarg)          \
      -> decltype(larg op rarg) { return larg op rarg; }           \
                                                                   \
      template<typename U, typename V>                             \
      static constexpr auto const_eval(const U larg, const V rarg) \
      -> decltype(larg op rarg) { return larg op rarg; }           \
    };

  #define EVAL_UNARY_AND_BINARY(op, opcode)                        \
    template<>                                                     \
    struct Eval<opcode>                                            \
    {                                                              \
      template<typename U>                                         \
      static inline auto eval(const U arg)                         \
      -> decltype(op arg) { return op arg; }                       \
                                                                   \
      template<typename U>                                         \
      static constexpr auto const_eval(const U arg)                \
      -> decltype(op arg) { return op arg; }                       \
      template<typename U, typename V>                             \
                                                                   \
      static inline auto eval(const U larg, const V rarg)          \
      -> decltype(larg op rarg) { return larg op rarg; }           \
                                                                   \
      template<typename U, typename V>                             \
      static constexpr auto const_eval(const U larg, const V rarg) \
      -> decltype(larg op rarg) { return larg op rarg; }           \
    };

  EVAL_UNARY_ONLY       (!, smt::LNOT)
  EVAL_UNARY_ONLY       (~, smt::NOT)

  EVAL_BINARY_ONLY      (+, smt::ADD)
  EVAL_UNARY_AND_BINARY (-, smt::SUB)
  EVAL_BINARY_ONLY      (&&, smt::LAND)
  EVAL_BINARY_ONLY      (||, smt::LOR)
  EVAL_BINARY_ONLY      (==, smt::EQL)
  EVAL_BINARY_ONLY      (!=, smt::NEQ)
  EVAL_BINARY_ONLY      (<, smt::LSS)
  EVAL_BINARY_ONLY      (>, smt::GTR)
  EVAL_BINARY_ONLY      (<=, smt::LEQ)
  EVAL_BINARY_ONLY      (>=, smt::GEQ)
  EVAL_BINARY_ONLY      (*, smt::MUL)
  EVAL_BINARY_ONLY      (/, smt::QUO)
  EVAL_BINARY_ONLY      (%, smt::REM)
  EVAL_BINARY_ONLY      (&, smt::AND)
  EVAL_BINARY_ONLY      (|, smt::OR)
  EVAL_BINARY_ONLY      (^, smt::XOR)

  template<smt::Opcode opcode, typename ...U> struct Return;

  template<smt::Opcode opcode, typename U>
  struct Return<opcode, U>
  {
    typedef decltype(
      Eval<opcode>::template const_eval<U>(std::declval<U>()))
    Type;
  };

  template<smt::Opcode opcode, typename U, typename V>
  struct Return<opcode, U, V>
  {
    typedef decltype(
      Eval<opcode>::template const_eval<U, V>(std::declval<U>(), std::declval<V>()))
    Type;
  };
}

template<typename T>
class Rvalue
{
public:
  const typename Smt<T>::Sort term;

  Rvalue(Rvalue&& other)
  : term(std::move(other.term)) {}

  explicit Rvalue(typename Smt<T>::Sort&& term_arg)
  : term(std::move(term_arg)) {}
};

template<typename T>
class Lvalue
{
public:
  typename Smt<T>::Sort term;
  const Address address;

  Lvalue();
  Lvalue(T);
  Lvalue(Rvalue<T>&&);
  Lvalue(const Lvalue<T>&);

  Lvalue& operator=(T v)
  {
    term = smt::literal<typename Smt<T>::Sort>(v);
    tracer().append_write_event(*this);
    return *this;
  }

  Lvalue& operator=(Rvalue<T>&& other)
  {
    term = std::move(other.term);
    tracer().append_write_event(*this);
    return *this;
  }

  Lvalue& operator=(const Lvalue& other)
  {
    Rvalue<T> new_rvalue = tracer().append_read_event(other);
    term = std::move(new_rvalue.term);
    tracer().append_write_event(*this);
    return *this;
  }
};

bool Tracer::append_guard(const Rvalue<bool>& rvalue)
{
  bool direction = true;
  if (m_flip_iter == m_flips.cend())
  {
    m_flips.push_back(Flip());
    assert(m_flips.back().direction == direction);
  }
  else
  {
    direction = m_flip_iter->direction;
    m_flip_iter++;
  }

  if (direction)
    m_guard = m_guard and rvalue.term;
  else
    m_guard = m_guard and !rvalue.term;

  return direction;
}

template<typename T>
Rvalue<T> Tracer::append_read_event(const Lvalue<T>& lvalue)
{
  const EventIdentifier event_id(m_event_id_cnt);
  typename Smt<T>::Sort term(make_value_symbol<T>());
  // TODO: conversion to result type if necessary (e.g. smt::Bv<T>)
  append_event(
    Event(READ_EVENT,
          event_id,
          m_thread_id_stack.top(),
          lvalue.address,
          term,
          m_guard));

  return Rvalue<T>(std::move(term));
}

template<typename T>
void Tracer::append_nondet_write_event(const Lvalue<T>& lvalue)
{
  assert(lvalue.term.is_null());
  const EventIdentifier event_id(m_event_id_cnt);
  append_event(
    Event(WRITE_EVENT,
          event_id,
          m_thread_id_stack.top(),
          lvalue.address,
          make_value_symbol<T>(),
          m_guard));
}

template<typename T>
void Tracer::append_write_event(const Lvalue<T>& lvalue)
{
  append_event(
    Event(WRITE_EVENT,
          m_event_id_cnt++,
          m_thread_id_stack.top(),
          lvalue.address,
          lvalue.term,
          m_guard));
}

template<typename T>
Rvalue<T> Tracer::append_pop_event(const Lvalue<T>& lvalue)
{
  const EventIdentifier event_id(m_event_id_cnt);
  typename Smt<T>::Sort term(make_value_symbol<T>());
  // TODO: conversion to result type if necessary (e.g. smt::Bv<T>)
  append_event(
    Event(POP_EVENT,
          event_id,
          m_thread_id_stack.top(),
          lvalue.address,
          term,
          m_guard));

  return Rvalue<T>(std::move(term));
}

template<typename T>
void Tracer::append_push_event(const Lvalue<T>& lvalue)
{
  append_event(
    Event(PUSH_EVENT,
          m_event_id_cnt++,
          m_thread_id_stack.top(),
          lvalue.address,
          lvalue.term,
          m_guard));
}

template<typename T>
Lvalue<T>::Lvalue()
: term(),
  address(reinterpret_cast<Address>(this))
{
  tracer().append_nondet_write_event(*this);
}

template<typename T>
Lvalue<T>::Lvalue(T v)
: term(smt::literal<typename Smt<T>::Sort>(v)),
  address(reinterpret_cast<Address>(this))
{
  tracer().append_write_event(*this);
}

template<typename T>
Lvalue<T>::Lvalue(Rvalue<T>&& other)
: term(std::move(other.term)),
  address(reinterpret_cast<Address>(this))
{
  tracer().append_write_event(*this);
}

template<typename T>
Lvalue<T>::Lvalue(const Lvalue<T>& other)
: term(),
  address(reinterpret_cast<Address>(this))
{
  Rvalue<T> new_rvalue = tracer().append_read_event(other);
  term = std::move(new_rvalue.term);
  tracer().append_write_event(*this);
}

}

#define CRV_BUILTIN_UNARY_OP(op, opcode)                                        \
  template<typename T>                                                          \
  inline auto operator op(crv::Rvalue<T>&& arg)                                 \
  -> crv::Rvalue<typename crv::internal::Return<smt::opcode, T>::Type>          \
  {                                                                             \
    typedef typename crv::internal::Return<smt::opcode, T>::Type ReturnType;    \
    return crv::Rvalue<ReturnType>(op arg.term);                                \
  }                                                                             \
                                                                                \
  template<typename T>                                                          \
  inline auto operator op(const crv::Lvalue<T>& arg)                            \
  -> crv::Rvalue<typename crv::internal::Return<smt::opcode, T>::Type>          \
  {                                                                             \
    crv::Rvalue<T> arg_rvalue = crv::tracer().append_read_event(arg);           \
    return op std::move(arg_rvalue);                                            \
  }                                                                             \

CRV_BUILTIN_UNARY_OP(-, SUB)
CRV_BUILTIN_UNARY_OP(!, LNOT)

#ifdef __BIT_PRECISION__
CRV_BUILTIN_UNARY_OP(~, NOT)
#endif

#define CRV_BUILTIN_BINARY_OP(op, opcode)                                       \
  template<typename U, typename V>                                              \
  inline auto operator op(                                                      \
    crv::Rvalue<U>&& larg,                                                      \
    crv::Rvalue<V>&& rarg)                                                      \
  -> crv::Rvalue<typename crv::internal::Return<smt::opcode, U, V>::Type>       \
  {                                                                             \
    typedef typename crv::internal::Return<smt::opcode, U, V>::Type ReturnType; \
    return crv::Rvalue<ReturnType>(larg.term op rarg.term);                     \
  }                                                                             \
                                                                                \
  template<typename U, typename V,                                              \
    class Enable = typename std::enable_if<std::is_arithmetic<V>::value>::type> \
  inline auto operator op(                                                      \
    crv::Rvalue<U>&& larg,                                                      \
    V literal)                                                                  \
  -> crv::Rvalue<typename crv::internal::Return<smt::opcode, U, V>::Type>       \
  {                                                                             \
    typedef typename crv::internal::Return<smt::opcode, U, V>::Type ReturnType; \
    return crv::Rvalue<ReturnType>(larg.term op literal);                       \
  }                                                                             \
                                                                                \
  template<typename U, typename V,                                              \
    class Enable = typename std::enable_if<std::is_arithmetic<U>::value>::type> \
  inline auto operator op(                                                      \
    U literal,                                                                  \
    crv::Rvalue<V>&& rarg)                                                      \
  -> crv::Rvalue<typename crv::internal::Return<smt::opcode, U, V>::Type>       \
  {                                                                             \
    typedef typename crv::internal::Return<smt::opcode, U, V>::Type ReturnType; \
    return crv::Rvalue<ReturnType>(literal op rarg.term);                       \
  }                                                                             \
                                                                                \
  template<typename U, typename V>                                              \
  inline auto operator op(                                                      \
  const crv::Lvalue<U>& larg,                                                   \
  crv::Rvalue<V>&& rarg)                                                        \
  -> crv::Rvalue<typename crv::internal::Return<smt::opcode, U, V>::Type>       \
  {                                                                             \
    crv::Rvalue<U> larg_rvalue = crv::tracer().append_read_event(larg);         \
    return std::move(larg_rvalue) op std::move(rarg);                           \
  }                                                                             \
                                                                                \
  template<typename U, typename V>                                              \
  inline auto operator op(                                                      \
    crv::Rvalue<U>&& larg,                                                      \
    const crv::Lvalue<V>& rarg)                                                 \
  -> crv::Rvalue<typename crv::internal::Return<smt::opcode, U, V>::Type>       \
  {                                                                             \
    crv::Rvalue<V> rarg_rvalue = crv::tracer().append_read_event(rarg);         \
    return std::move(larg) op std::move(rarg_rvalue);                           \
  }                                                                             \
                                                                                \
  template<typename U, typename V>                                              \
  inline auto operator op(                                                      \
    const crv::Lvalue<U>& larg,                                                 \
    const crv::Lvalue<V>& rarg)                                                 \
  -> crv::Rvalue<typename crv::internal::Return<smt::opcode, U, V>::Type>       \
  {                                                                             \
    crv::Rvalue<U> larg_rvalue = crv::tracer().append_read_event(larg);         \
    crv::Rvalue<V> rarg_rvalue = crv::tracer().append_read_event(rarg);         \
    return std::move(larg_rvalue) op std::move(rarg_rvalue);                    \
  }                                                                             \
                                                                                \
  template<typename U, typename V,                                              \
    class Enable = typename std::enable_if<std::is_arithmetic<V>::value>::type> \
  inline auto operator op(                                                      \
    const crv::Lvalue<U>& larg,                                                 \
    V literal)                                                                  \
  -> crv::Rvalue<typename crv::internal::Return<smt::opcode, U, V>::Type>       \
  {                                                                             \
    const crv::Rvalue<U> larg_rvalue = crv::tracer().append_read_event(larg);   \
    typedef typename crv::internal::Return<smt::opcode, U, V>::Type ReturnType; \
    return crv::Rvalue<ReturnType>(larg_rvalue.term op literal);                \
  }                                                                             \
                                                                                \
  template<typename U, typename V,                                              \
    class Enable = typename std::enable_if<std::is_arithmetic<U>::value>::type> \
  inline auto operator op(                                                      \
    U literal,                                                                  \
    const crv::Lvalue<V>& rarg)                                                 \
  -> crv::Rvalue<typename crv::internal::Return<smt::opcode, U, V>::Type>       \
  {                                                                             \
    const crv::Rvalue<V> rarg_rvalue = crv::tracer().append_read_event(rarg);   \
    typedef typename crv::internal::Return<smt::opcode, U, V>::Type ReturnType; \
    return crv::Rvalue<ReturnType>(literal op rarg_rvalue.term);                \
  }                                                                             \

CRV_BUILTIN_BINARY_OP(-, SUB)
CRV_BUILTIN_BINARY_OP(+, ADD)
CRV_BUILTIN_BINARY_OP(*, MUL)
CRV_BUILTIN_BINARY_OP(/, QUO)
CRV_BUILTIN_BINARY_OP(%, REM)
CRV_BUILTIN_BINARY_OP(<, LSS)
CRV_BUILTIN_BINARY_OP(>, GTR)
CRV_BUILTIN_BINARY_OP(!=, NEQ)
CRV_BUILTIN_BINARY_OP(<=, LEQ)
CRV_BUILTIN_BINARY_OP(>=, GEQ)
CRV_BUILTIN_BINARY_OP(==, EQL)
CRV_BUILTIN_BINARY_OP(&&, LAND)
CRV_BUILTIN_BINARY_OP(||, LOR)

#ifdef __BIT_PRECISION__
CRV_BUILTIN_BINARY_OP(&, AND)
CRV_BUILTIN_BINARY_OP(|, OR)
CRV_BUILTIN_BINARY_OP(^, XOR)
#endif

namespace crv
{

#ifdef __BV_TIME__
typedef smt::Bv<unsigned short> TimeSort;
#else
typedef smt::Int TimeSort;
#endif

class Time
{
private:
  TimeSort m_term;

public:
  Time(const TimeSort& term)
  : m_term(term) {}

  Time(const Time& other)
  : m_term(other.m_term) {}

  Time(Time&& other)
  : m_term(std::move(other.m_term)) {}

  smt::Bool happens_before(const Time& t) const
  {
    return m_term < t.m_term;
  }

  smt::Bool simultaneous(const Time& t) const
  {
    return m_term == t.m_term;
  }

  smt::Bool simultaneous_or_happens_before(const Time& t) const
  {
    return m_term <= t.m_term;
  }

  const TimeSort& term() const
  {
    return m_term;
  }

  Time& operator=(const Time& other)
  {
    m_term = other.m_term;
    return *this;
  }
};

class Encoder
{
private:
  static const std::string s_time_prefix;
  static const std::string s_rf_prefix;
  static const std::string s_pf_prefix;

  static std::string prefix_event_id(
    const std::string& prefix,
    const Event& e)
  {
    return prefix + std::to_string(e.event_id);
  }

  // Returns `x == prefix!y`, e.g. `y` reads from `x`
  static smt::Bool flow_bool(
    const std::string& prefix,
    const Event& x,
    const Event& y)
  {
    // check that events oppose each other,
    // assuming data flow from x to y.
    assert(x.kind - 1 == y.kind);

    const TimeSort app(smt::any<TimeSort>(
      prefix_event_id(prefix, y)));
    return x.event_id == app;
  }

  smt::CVC4Solver m_solver;
  std::map<EventIdentifier, TimeSort> m_time_map;
  const Time m_epoch;

  /// Uses e's identifier to build a numerical SMT variable
  Time time(const Event& e)
  {
    TimeSort& time = m_time_map[e.event_id];
    if (time.is_null())
    {
      time = smt::any<TimeSort>(prefix_event_id(s_time_prefix, e));
      m_solver.add(m_epoch.happens_before(time));
    }

    return time;
  }

  void unsafe_add(const smt::UnsafeTerm& term)
  {
    m_solver.unsafe_add(term);
#ifdef __CRV_DEBUG__
    std::cout << "[crv::Encoder]: " << m_solver.expr() << std::endl;
#endif
  }

  void encode_read_from(const PerAddressMap& per_address_map)
  {
    smt::UnsafeTerm and_rf(smt::literal<smt::Bool>(true));
    for (const PerAddressMap::value_type& pair : per_address_map)
    {
      const EventKinds& a = pair.second;
      for (const EventIter r_iter : a.reads)
      {
        const Event& r = *r_iter;

        smt::UnsafeTerm or_rf(smt::literal<smt::Bool>(false));
        for (const EventIter w_iter : a.writes)
        {
          const Event& w = *w_iter;

          const smt::Bool wr_order(time(w).happens_before(time(r)));
          const smt::Bool rf_bool(flow_bool(s_rf_prefix, w, r));
          const smt::UnsafeTerm wr_equality(w.term == r.term);

          or_rf = rf_bool or or_rf;
          and_rf = and_rf and
            smt::implies(
              /* if */ rf_bool,
              /* then */ wr_order and w.guard and wr_equality);
        }
        and_rf = and_rf and r.guard and or_rf;
      }
    }
    unsafe_add(and_rf);
  }

  void encode_from_read(const PerAddressMap& per_address_map)
  {
    smt::UnsafeTerm and_fr(smt::literal<smt::Bool>(true));
    for (const PerAddressMap::value_type& pair : per_address_map)
    {
      const EventKinds& a = pair.second;
      for (const EventIter r_iter : a.reads)
      {
        const Event& r = *r_iter;

        for (EventIterList::const_iterator writes_iter = a.writes.cbegin();
             writes_iter != a.writes.cend();
             writes_iter++)
        {
          const Event& w = **writes_iter;

          EventIterList::const_iterator writes_prime_iter = writes_iter;
          for (writes_prime_iter++;
               writes_prime_iter != a.writes.cend();
               writes_prime_iter++)
          {
            const Event& w_prime = **writes_prime_iter;

            const smt::Bool rf_bool(flow_bool(s_rf_prefix, w, r));
            and_fr = and_fr and w.guard and
              smt::implies(
                /* if */ rf_bool and time(w).happens_before(time(w_prime)),
                /* then */ time(r).happens_before(time(w_prime)));
          }
        }
      }
    }
    unsafe_add(and_fr);
  }

  void encode_write_serialization(const PerAddressMap& per_address_map)
  {
    smt::UnsafeTerm and_ws(smt::literal<smt::Bool>(true));
    for (const PerAddressMap::value_type& pair : per_address_map)
    {
      const EventKinds& a = pair.second;
      if (a.writes.size() < 2)
        continue;

      smt::UnsafeTerms terms;
      terms.reserve(a.writes.size());
      for (const EventIter w_iter : a.writes)
      {
        const Event& w = *w_iter;
        terms.push_back(time(w).term());
      }

      and_ws = and_ws and smt::distinct(std::move(terms));
    }
    unsafe_add(and_ws);
  }

  void encode_memory_concurrency(const Tracer& tracer)
  {
    const PerAddressMap& per_address_map = tracer.per_address_map();
    encode_read_from(per_address_map);
    encode_from_read(per_address_map);
    encode_write_serialization(per_address_map);
  }

  void encode_pop_from(const PerAddressMap& per_address_map)
  {
    smt::UnsafeTerm and_pf(smt::literal<smt::Bool>(true));
    for (const PerAddressMap::value_type& pair : per_address_map)
    {
      const EventKinds& a = pair.second;
      for (const EventIter pop_iter : a.pops)
      {
        const Event& pop = *pop_iter;

        smt::UnsafeTerm or_pf(smt::literal<smt::Bool>(false));
        for (const EventIter push_iter : a.pushes)
        {
          const Event& push = *push_iter;
          const smt::Bool pf_bool(flow_bool(s_pf_prefix, push, pop));
          or_pf = pf_bool or or_pf;
          and_pf = and_pf and
            smt::implies(
              /* if */ pf_bool,
              /* then */ time(push).happens_before(time(pop)) and
                         push.guard and push.term == pop.term);
        }
        and_pf = and_pf and pop.guard and or_pf;
      }
    }
    unsafe_add(and_pf);
  }

  // Make sure "pop-from" is like an injective function
  void encode_pop_from_injectivity(const PerAddressMap& per_address_map)
  {
    smt::UnsafeTerm and_pop_excl(smt::literal<smt::Bool>(true));
    for (const PerAddressMap::value_type& pair : per_address_map)
    {
      const EventKinds& a = pair.second;
      if (a.pops.size() < 2)
        continue;

      smt::Terms<TimeSort> terms(a.pops.size());
      for (const EventIter pop_iter : a.pops)
      {
        const Event& pop = *pop_iter;
        terms.push_back(
          smt::any<TimeSort>(prefix_event_id(s_pf_prefix, pop)));
      }

      and_pop_excl = and_pop_excl and smt::distinct(std::move(terms));
    }
    unsafe_add(and_pop_excl);
  }

  void encode_stack_lifo_order(const PerAddressMap& per_address_map)
  {
    smt::UnsafeTerm and_stack(smt::literal<smt::Bool>(true));
    for (const PerAddressMap::value_type& pair : per_address_map)
    {
      const EventKinds& a = pair.second;
      for (const EventIter push_iter : a.pushes)
      {
        const Event& push = *push_iter;

        for (const EventIter push_prime_iter : a.pushes)
        {
          const Event& push_prime = *push_prime_iter;
          const smt::Bool pushes_order(
            time(push).happens_before(time(push_prime)));

          for (const EventIter pop_iter : a.pops)
          {
            const Event& pop = *pop_iter;
            const smt::Bool pf_bool(flow_bool(s_pf_prefix, push, pop));

            smt::UnsafeTerm or_pp(smt::literal<smt::Bool>(false));
            for (const EventIter pop_prime_iter : a.pops)
            {
              const Event& pop_prime = *pop_prime_iter;
              const smt::Bool pf_prime_bool(
                flow_bool(s_pf_prefix, push_prime, pop_prime)),
                pops_order(time(pop_prime).happens_before(time(pop)));

              // build pf!pop' = push' for some pop'
              or_pp = or_pp or pf_prime_bool;

              // if pf!pop = push and pf!pop' = push' and
              // t!push < t!push', then t!pop' < t!pop.
              and_stack = and_stack and
                smt::implies(
                  pf_bool and pf_prime_bool and pushes_order,
                  pops_order);
            }

            // if t!push < t!push' < t!pop and pf!pop = push and
            // guard(push'), then there exists a pop' such that
            // pf!pop' = push' (and t!pop' < t!pop by "pop-from").
            and_stack = and_stack and
              smt::implies(
                pf_bool and push_prime.guard and pushes_order and
                time(push_prime).happens_before(time(pop)), or_pp);
          }
        }
      }
    }
    unsafe_add(and_stack);
  }

  // Encode partial order model of stack abstract data type (ADT)
  void encode_stack_api(const Tracer& tracer)
  {
    const PerAddressMap& per_address_map = tracer.per_address_map();
    encode_pop_from(per_address_map);
    encode_pop_from_injectivity(per_address_map);
    encode_stack_lifo_order(per_address_map);
  }

  /*
   * Synchronization between threads (e.g. BEGIN/THREAD_END_EVENT) relies
   * on the fact that time(const Event&) builds an SMT variable whose
   * name is uniquely determined by the event's identifier.
   */
  void encode_thread_order(const PerThreadMap& per_thread_map)
  {
    smt::Bool thread_order(smt::literal<smt::Bool>(true));
    for (const PerThreadMap::value_type& pair : per_thread_map)
    {
      const EventIterList& events = pair.second;
      if (events.size() < 2)
        continue;

      EventIterList::const_iterator events_iter = events.cbegin();
      EventIter e_iter = *events_iter++;
      while (events_iter != events.cend())
      {
        thread_order = thread_order and
          time(*e_iter).happens_before(time(**events_iter));

        e_iter = *events_iter;
        events_iter++;
      }
    }
    unsafe_add(thread_order);
  }

public:
  Encoder()
#ifdef __BV_TIME__
  : m_solver(smt::QF_AUFBV_LOGIC),
#else
  : m_solver(smt::QF_AUFLIA_LOGIC),
#endif
    m_time_map(),
    m_epoch(smt::literal<TimeSort>(0)) {}

  smt::CVC4Solver& solver()
  {
    return m_solver;
  }

  void add(Rvalue<bool>&& c)
  {
    unsafe_add(c.term);
  }

  void encode(const Tracer& tracer)
  {
    encode_thread_order(tracer.per_thread_map());
    encode_memory_concurrency(tracer);
    encode_stack_api(tracer);
  }
};

}

#endif
