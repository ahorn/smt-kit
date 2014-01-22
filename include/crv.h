// Copyright 2013-2014, Alex Horn. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

#ifndef __CRV_H_
#define __CRV_H_

#include <smt>
#include <set>
#include <unordered_map>
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
  THREAD_BEGIN_EVENT = 0,
  THREAD_END_EVENT   = 1,
  BARRIER_EVENT,
  READ_EVENT         = 7,
  WRITE_EVENT,
  POP_EVENT,
  PUSH_EVENT,
  LOAD_EVENT,
  STORE_EVENT,
  RECV_EVENT,
  SEND_EVENT,
};

/// Positive unless event is_sync()
typedef unsigned int Address;
typedef unsigned int EventIdentifier;

/// Positive if and only if thread is joinable
typedef unsigned ThreadIdentifier;

class Event
{
public:
  const EventKind kind;
  const EventIdentifier event_id;
  const ThreadIdentifier thread_id;
  const Address address;
  const smt::Bool guard;
  const smt::UnsafeTerm term;
  const smt::UnsafeTerm offset_term;

  Event(Event&& other)
  : kind(other.kind),
    event_id(other.event_id),
    thread_id(other.thread_id),
    address(other.address),
    guard(std::move(other.guard)),
    term(std::move(other.term)),
    offset_term(std::move(other.offset_term)) {}

  Event(
    const EventKind kind_arg,
    const EventIdentifier event_id_arg,
    const ThreadIdentifier thread_id_arg,
    const Address address_arg,
    const smt::Bool guard_arg,
    const smt::UnsafeTerm& term_arg,
    const smt::UnsafeTerm& offset_term_arg)
  : kind(kind_arg),
    event_id(event_id_arg),
    thread_id(thread_id_arg),
    address(address_arg),
    guard(guard_arg),
    term(term_arg),
    offset_term(offset_term_arg)
  {
    assert(!guard.is_null());
    assert(is_sync() || !term.is_null());
    assert(is_sync() || 0 < address);
  }

  bool is_barrier() const { return kind == BARRIER_EVENT; }
  bool is_read() const { return kind == READ_EVENT; }
  bool is_write() const { return kind == WRITE_EVENT; }
  bool is_pop() const { return kind == POP_EVENT; }
  bool is_push() const { return kind == PUSH_EVENT; }
  bool is_recv() const { return kind == RECV_EVENT; }
  bool is_send() const { return kind == SEND_EVENT; }
  bool is_thread_begin() const { return kind == THREAD_BEGIN_EVENT; }
  bool is_thread_end() const { return kind == THREAD_END_EVENT; }
  bool is_sync() const { return kind < READ_EVENT; }
};

typedef std::list<Event> Events;
typedef Events::const_iterator EventIter;

}

namespace std
{
  template<>
  class hash<crv::EventIter>
  {
  public:
    size_t operator()(const crv::EventIter& e_iter) const
    {
      return e_iter->event_id;
    }
  };

  template<>
  class hash<std::pair<crv::EventIter, crv::EventIter>>
  {
  public:
    size_t operator()(const std::pair<crv::EventIter, crv::EventIter>& p) const
    {
      constexpr crv::EventIdentifier max_event_id =
        numeric_limits<crv::EventIdentifier>::max();

      static_assert(max_event_id * 2 < numeric_limits<size_t>::max(),
        "size_t must be at least twice as large as crv::EventIdentifier");

      return p.first->event_id * max_event_id + p.second->event_id;
    }
  };
}

namespace crv
{

typedef std::vector<EventIter> EventIters;

class EventKinds
{
private:
  EventIters m_reads;
  EventIters m_writes;
  EventIters m_pops;
  EventIters m_pushes;
  EventIters m_loads;
  EventIters m_stores;
  EventIters m_recvs;
  EventIters m_sends;

public:
  EventKinds()
  : m_reads(),
    m_writes(),
    m_pops(),
    m_pushes(),
    m_loads(),
    m_stores(),
    m_recvs(),
    m_sends() {}

  // See member function template specializations
  template<EventKind kind>
  void push_back(const EventIter e_iter) { /* skip */ }

  const EventIters& reads()  const { return m_reads;  }
  const EventIters& writes() const { return m_writes; }
  const EventIters& pops()   const { return m_pops;   }
  const EventIters& pushes() const { return m_pushes; }
  const EventIters& loads()  const { return m_loads;  }
  const EventIters& stores() const { return m_stores; }
  const EventIters& recvs()  const { return m_recvs;  }
  const EventIters& sends()  const { return m_sends;  }
};

template<> inline
void EventKinds::push_back<READ_EVENT>(const EventIter e_iter)
{
  m_reads.push_back(e_iter);
}

template<> inline
void EventKinds::push_back<WRITE_EVENT>(const EventIter e_iter)
{
  m_writes.push_back(e_iter);
}

template<> inline
void EventKinds::push_back<POP_EVENT>(const EventIter e_iter)
{
  m_pops.push_back(e_iter);
}

template<> inline
void EventKinds::push_back<PUSH_EVENT>(const EventIter e_iter)
{
  m_pushes.push_back(e_iter);
}

template<> inline
void EventKinds::push_back<LOAD_EVENT>(const EventIter e_iter)
{
  m_loads.push_back(e_iter);
}

template<> inline
void EventKinds::push_back<STORE_EVENT>(const EventIter e_iter)
{
  m_stores.push_back(e_iter);
}

template<> inline
void EventKinds::push_back<RECV_EVENT>(const EventIter e_iter)
{
  m_recvs.push_back(e_iter);
}

template<> inline
void EventKinds::push_back<SEND_EVENT>(const EventIter e_iter)
{
  m_sends.push_back(e_iter);
}

typedef std::unordered_map<Address, EventKinds> PerAddressMap;
typedef std::unordered_map<ThreadIdentifier, EventIters> PerThreadMap;
typedef std::unordered_map<EventIter, EventIters> PerEventMap;

/// Control flow decision along symbolic path
struct Flip
{
  bool direction;
  bool is_flip;

  Flip(bool direction)
  : direction(direction),
    is_flip(false) {}
};

typedef std::list<Flip> Flips;
typedef std::list<Flip>::const_iterator FlipIter;
typedef std::list<smt::Bool> Bools;

template<typename T> class External;
template<typename T> class Internal;

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
  Events m_events;

  // Index event list by various keys
  PerAddressMap m_per_address_map;
  PerThreadMap m_per_thread_map;

  // always nonempty
  std::stack<ThreadIdentifier> m_thread_id_stack;

  // never null
  smt::Bool m_guard;

  unsigned long long m_flip_cnt;
  Flips m_flips;
  FlipIter m_flip_iter;
  Bools m_assertions;
  Bools m_errors;

  Address m_next_address;

  // Generated barrier identifiers irrespective of threads
  std::list<EventIdentifier> m_barrier_list;

  // Per thread most recently used barrier
  std::unordered_map<ThreadIdentifier,
    std::list<EventIdentifier>::const_iterator> m_barrier_map;

  template<typename T>
  typename Smt<T>::Sort make_value_symbol()
  {
    assert(m_event_id_cnt < std::numeric_limits<EventIdentifier>::max());
    return smt::any<typename Smt<T>::Sort>(s_value_prefix +
      std::to_string(m_event_id_cnt++));
  }

  template<EventKind kind>
  void append_event(
    const EventIdentifier event_id,
    const Address address,
    const smt::UnsafeTerm& term,
    const smt::UnsafeTerm& offset_term = smt::UnsafeTerm())
  {
    const ThreadIdentifier thread_id(current_thread_id());
    m_events.push_back(Event(kind, event_id, thread_id,
      address, guard(), term, offset_term));

    const EventIter e_iter(--m_events.cend());
    m_per_address_map[e_iter->address].push_back<kind>(e_iter);
    m_per_thread_map[thread_id].push_back(e_iter);
  }

  void push_next_thread_id()
  {
    assert(0 < m_thread_id_cnt);
    assert(m_thread_id_cnt < std::numeric_limits<ThreadIdentifier>::max());
    m_thread_id_stack.push(m_thread_id_cnt++);
  }

public:
  Tracer()
  : m_event_id_cnt(0),
    m_thread_id_cnt(1),
    m_events(),
    m_per_address_map(),
    m_per_thread_map(),
    m_thread_id_stack(),
    m_guard(smt::literal<smt::Bool>(true)),
    m_flip_cnt(0),
    m_flips(),
    m_flip_iter(m_flips.cbegin()),
    m_assertions(),
    m_errors(),
    m_next_address(1),
    m_barrier_list(),
    m_barrier_map()
  {
    m_thread_id_stack.push(m_thread_id_cnt++);
  }

  ThreadIdentifier current_thread_id() const
  {
    assert(m_thread_id_stack.top() < m_thread_id_cnt);
    return m_thread_id_stack.top();
  }

  const smt::Bool& guard() const
  {
    assert(!m_guard.is_null());
    return m_guard;
  }

  const Events& events() const
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

  void reset_event_identifiers()
  {
    m_event_id_cnt = 0;
  }

  void reset_events()
  {
    m_events.clear();
    m_per_address_map.clear();
    m_per_thread_map.clear();

    while (!m_thread_id_stack.empty())
    {
      m_thread_id_stack.pop();
    }
    m_thread_id_cnt = 1;
    push_next_thread_id();
  }

  void reset_guard(const smt::Bool guard = smt::literal<smt::Bool>(true))
  {
    m_guard = guard;
  }

  void reset_flips()
  {
    m_flip_cnt = 0;
    m_flips.clear();
    m_flip_iter = m_flips.cbegin();
  }

  void reset_assertions()
  {
    m_assertions.clear();
  }

  void reset_errors()
  {
    m_errors.clear();
  }

  void reset_address()
  {
    m_next_address = 1;
  }

  void reset_barrier()
  {
    m_barrier_list.clear();
    m_barrier_map.clear();
  }

  void reset()
  {
    reset_event_identifiers();
    reset_events();
    reset_guard();
    reset_flips();
    reset_assertions();
    reset_errors();
    reset_address();
    reset_barrier();
  }

  /// Synchronization point between threads of execution
  void barrier()
  {
    const ThreadIdentifier thread_id(current_thread_id());
    if (m_barrier_map.find(thread_id) == m_barrier_map.cend())
    {
      if (m_barrier_list.empty())
        m_barrier_list.push_back(append_barrier_event());
      else
        append_barrier_event(*m_barrier_list.cbegin());

      m_barrier_map[thread_id] = m_barrier_list.cbegin();
    }
    else
    {
      // caution: branches rely on mutable reference!
      std::list<EventIdentifier>::const_iterator& citer =
        m_barrier_map.at(thread_id);
      assert(citer != m_barrier_list.cend());
      if (citer == --m_barrier_list.cend())
      {
        m_barrier_list.push_back(append_barrier_event());
        citer++;
      }
      else
      {
        citer++;
        append_barrier_event(*citer);
      }
    }
  }

  /// Depth-first search strategy

  /// \return is there more to explore?
  bool flip()
  {
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

    reset_events();
    reset_guard();
    reset_assertions();
    reset_errors();
    reset_address();
    reset_barrier();
    assert(0 < m_flip_cnt);
    assert(!m_flips.empty());

    return true;
  }

  unsigned long long flip_cnt() const
  {
    return m_flip_cnt;
  }

  Flips& flips()
  {
    return m_flips;
  }

  /// Encode as conjunction
  const Bools& assertions() const
  {
    return m_assertions;
  }

  /// Encode as disjunction 
  const Bools& errors() const
  {
    return m_errors;
  }

  void add_assertion(Internal<bool>&&);
  void add_error(Internal<bool>&&);

  Address next_address()
  {
    assert(m_next_address < std::numeric_limits<Address>::max());
    return m_next_address++;
  }

  bool append_guard(const Internal<bool>&, bool direction = true);

  /// Returns parent thread identifier
  ThreadIdentifier append_thread_begin_event()
  {
    const EventIdentifier event_id(m_event_id_cnt++);
    append_event<THREAD_BEGIN_EVENT>(
      event_id, 0, smt::UnsafeTerm());

    ThreadIdentifier parent_thread_id(current_thread_id());
    push_next_thread_id();

    append_event<THREAD_BEGIN_EVENT>(
      event_id, 0, smt::UnsafeTerm());
    return parent_thread_id;
  }

  /// Returns child thread identifier
  ThreadIdentifier append_thread_end_event()
  {
    append_event<THREAD_END_EVENT>(
      m_event_id_cnt++, 0, smt::UnsafeTerm());

    ThreadIdentifier child_thread_id(current_thread_id());
    m_thread_id_stack.pop();
    return child_thread_id;
  }

  EventIdentifier append_barrier_event()
  {
    const EventIdentifier event_id(m_event_id_cnt++);
    append_barrier_event(event_id);
    return event_id;
  }

  void append_barrier_event(const EventIdentifier event_id)
  {
    append_event<BARRIER_EVENT>(event_id, 0, smt::UnsafeTerm());
  }

  void append_join_event(const ThreadIdentifier thread_id)
  {
    const EventIter e_iter = m_per_thread_map.at(thread_id).back();
    assert(e_iter->thread_id != current_thread_id());

    append_event<THREAD_END_EVENT>(
      e_iter->event_id, 0, smt::UnsafeTerm());
  }

  /// Creates a new term for the read event
  template<typename T>
  typename Smt<T>::Sort append_read_event(const External<T>&);

  /// Creates a new term for the write event
  template<typename T>
  void append_nondet_write_event(const External<T>&);

  /// Uses external's term for the new write event
  template<typename T>
  void append_write_event(const External<T>&);

  /// Creates a new term for the pop event
  template<typename T>
  typename Smt<T>::Sort append_pop_event(const External<T>&);

  /// Uses external's term for the new push event
  template<typename T>
  void append_push_event(const External<T>&);

  /// Uses external's offset term for new load event
  template<typename T>
  typename Smt<T>::Sort append_load_event(const External<T>&);

  /// Uses external's offset term for new store event
  template<typename T>
  void append_store_event(const External<T>&);

  template<typename T>
  typename Smt<T>::Sort append_recv_event(const External<T>&);

  template<typename T>
  void append_send_event(const External<T>&);
};

// Global for symbolic execution
extern Tracer& tracer();

namespace internal
{
  /// Evaluate built-in arithmetic and boolean expressions

  /// Uses constexpr perfect forwarding since C++14
  template<smt::Opcode opcode> class Eval;

  #define EVAL_UNARY_ONLY(op, opcode)                              \
    template<>                                                     \
    struct Eval<opcode>                                            \
    {                                                              \
      template<typename U>                                         \
      static inline auto eval(U&& u)                               \
      -> decltype(op std::forward<U>(u))                           \
      { return op std::forward<U>(u); }                            \
                                                                   \
      template<typename U>                                         \
      static constexpr auto const_eval(U&& u)                      \
      -> decltype(op std::forward<U>(u))                           \
      { return op std::forward<U>(u); }                            \
    };

  #define EVAL_BINARY_ONLY(op, opcode)                             \
    template<>                                                     \
    struct Eval<opcode>                                            \
    {                                                              \
      template<typename U, typename V>                             \
      static inline auto eval(U&& u, V&& v)                        \
      -> decltype(std::forward<U>(u) op std::forward<V>(v))        \
      { return std::forward<U>(u) op std::forward<V>(v); }         \
                                                                   \
      template<typename U, typename V>                             \
      static constexpr auto const_eval(U&& u, V&& v)               \
      -> decltype(std::forward<U>(u) op std::forward<V>(v))        \
      { return std::forward<U>(u) op std::forward<V>(v); }         \
    };

  #define EVAL_UNARY_AND_BINARY(op, opcode)                        \
    template<>                                                     \
    struct Eval<opcode>                                            \
    {                                                              \
      template<typename U>                                         \
      static inline auto eval(U&& u)                               \
      -> decltype(op std::forward<U>(u))                           \
      { return op std::forward<U>(u); }                            \
                                                                   \
      template<typename U>                                         \
      static constexpr auto const_eval(U&& u)                      \
      -> decltype(op std::forward<U>(u))                           \
      { return op std::forward<U>(u); }                            \
                                                                   \
      template<typename U, typename V>                             \
      static inline auto eval(U&& u, V&& v)                        \
      -> decltype(std::forward<U>(u) op std::forward<V>(v))        \
      { return std::forward<U>(u) op std::forward<V>(v); }         \
                                                                   \
      template<typename U, typename V>                             \
      static constexpr auto const_eval(U&& u, V&& v)               \
      -> decltype(std::forward<U>(u) op std::forward<V>(v))        \
      { return std::forward<U>(u) op std::forward<V>(v); }         \
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

// Returns a new SMT term that can be set equal to another term
template<typename T>
typename Smt<T>::Sort append_input_event(const External<T>& external)
{
  if (external.offset_term.is_null())
    return tracer().append_read_event(external);
  else
    return tracer().append_load_event(external);
}

template<typename T>
class Internal
{
public:
  typename Smt<T>::Sort term;

  Internal(const Internal& other)
  : term(other.term) {}

  Internal(Internal&& other)
  : term(std::move(other.term)) {}

  explicit Internal(typename Smt<T>::Sort&& term_arg)
  : term(std::move(term_arg)) {}

  Internal(T v)
  : term(smt::literal<typename Smt<T>::Sort>(v)) {}

  Internal(const External<T>& other)
  : term()
  {
    term = append_input_event(other);
  }

  Internal& operator=(Internal<T>&& other)
  {
    term = std::move(other.term);
    return *this;
  }

  Internal& operator=(const Internal& other)
  {
    term = other.term;
    return *this;
  }
};

template<typename T> class __External;

template<typename T>
class External
{
public:
  const Address address;
  typename Smt<T>::Sort term;
  const Smt<size_t>::Sort offset_term;
  typedef typename std::remove_extent<T>::type Range;

private:
  void append_output_event()
  {
    assert(!term.is_null());
    if (offset_term.is_null())
      tracer().append_write_event(*this);
    else
      tracer().append_store_event(*this);
  }

protected:
  External(
    const Address address_arg,
    const Smt<size_t>::Sort& offset_term_arg)
  : address(address_arg),
    term(),
    offset_term(offset_term_arg) {}

public:
  External()
  : address(tracer().next_address()),
    term(),
    offset_term()
  {
    tracer().append_nondet_write_event(*this);
  }

  External(T v)
  : address(tracer().next_address()),
    term(smt::literal<typename Smt<T>::Sort>(v)),
    offset_term()
  {
    tracer().append_write_event(*this);
  }

  External(Internal<T>&& other)
  : address(tracer().next_address()),
    term(std::move(other.term)),
    offset_term()
  {
    tracer().append_write_event(*this);
  }

  /*
   * Careful: optimizations with copy elision (e.g. RVO)
   * break the side effects of this copy constructor.
   */
  External(const External& other)
  : address(tracer().next_address()),
    term(),
    offset_term()
  {
    term = append_input_event(other);
    tracer().append_write_event(*this);
  }

  virtual ~External() {}

  External& operator=(T v)
  {
    term = smt::literal<typename Smt<T>::Sort>(v);
    append_output_event();
    return *this;
  }

  External& operator=(const Internal<T>& other)
  {
    term = other.term;
    append_output_event();
    return *this;
  }

  External& operator=(Internal<T>&& other)
  {
    term = std::move(other.term);
    append_output_event();
    return *this;
  }

  External& operator=(const External& other)
  {
    term = append_input_event(other);
    append_output_event();
    return *this;
  }

  template<typename U = T, class Enable =
    typename std::enable_if<std::is_array<U>::value>::type>
  __External<Range> operator[](const Internal<size_t>& offset);
};

// Work around copy elision of External(const External&)
template<typename T>
class __External : public External<T>
{
public:
  __External(
    const Address address_arg,
    const Smt<size_t>::Sort& offset_term_arg)
  : External<T>(address_arg, offset_term_arg) {}

  External<T>& operator=(T v)
  {
    return External<T>::operator=(v);
  }

  External<T>& operator=(const Internal<T>& other)
  {
    return External<T>::operator=(other);
  }

  External<T>& operator=(Internal<T>&& other)
  {
    return External<T>::operator=(std::move(other));
  }

  External<T>& operator=(const External<T>& other)
  {
    return External<T>::operator=(other);
  }
};

template<typename T>
template<typename U, class Enable>
__External<typename External<T>::Range>
External<T>::operator[](const Internal<size_t>& offset)
{
  tracer().next_address();
  return __External<Range>(address, offset.term);
}

template<typename T>
typename Smt<T>::Sort Tracer::append_read_event(const External<T>& external)
{
  assert(external.offset_term.is_null());

  const EventIdentifier event_id(m_event_id_cnt);
  typename Smt<T>::Sort term(make_value_symbol<T>());
  // TODO: conversion to result type if necessary (e.g. smt::Bv<T>)
  append_event<READ_EVENT>(
    event_id, external.address, term);

  return term;
}

template<typename T>
void Tracer::append_nondet_write_event(const External<T>& external)
{
  assert(external.term.is_null());
  assert(external.offset_term.is_null());

  // since evaluation order of arguments is undefined ...
  const EventIdentifier event_id(m_event_id_cnt);
  append_event<WRITE_EVENT>(
    event_id, external.address, make_value_symbol<T>());
}

template<typename T>
void Tracer::append_write_event(const External<T>& external)
{
  assert(!external.term.is_null());
  assert(external.offset_term.is_null());

  append_event<WRITE_EVENT>(
    m_event_id_cnt++, external.address, external.term);
}

template<typename T>
typename Smt<T>::Sort Tracer::append_pop_event(const External<T>& stack)
{
  assert(stack.offset_term.is_null());

  const EventIdentifier event_id(m_event_id_cnt);
  typename Smt<T>::Sort term(make_value_symbol<T>());
  // TODO: conversion to result type if necessary (e.g. smt::Bv<T>)
  append_event<POP_EVENT>(event_id, stack.address, term);

  return term;
}

template<typename T>
void Tracer::append_push_event(const External<T>& stack)
{
  assert(!stack.term.is_null());
  assert(stack.offset_term.is_null());

  append_event<PUSH_EVENT>(m_event_id_cnt++, stack.address, stack.term);
}

template<typename T>
typename Smt<T>::Sort Tracer::append_load_event(const External<T>& external)
{
  assert(!external.offset_term.is_null());

  const EventIdentifier event_id(m_event_id_cnt);
  typename Smt<T>::Sort term(make_value_symbol<T>());
  // TODO: conversion to result type if necessary (e.g. smt::Bv<T>)
  append_event<LOAD_EVENT>(
    event_id, external.address, term, external.offset_term);

  return term;
}

template<typename T>
void Tracer::append_store_event(const External<T>& external)
{
  assert(!external.term.is_null());
  assert(!external.offset_term.is_null());

  append_event<STORE_EVENT>(
    m_event_id_cnt++, external.address, external.term, external.offset_term);
}

template<typename T>
typename Smt<T>::Sort Tracer::append_recv_event(const External<T>& channel)
{
  assert(channel.offset_term.is_null());

  const EventIdentifier event_id(m_event_id_cnt);
  typename Smt<T>::Sort term(make_value_symbol<T>());
  // TODO: conversion to result type if necessary (e.g. smt::Bv<T>)
  append_event<RECV_EVENT>(event_id, channel.address, term);

  return term;
}

template<typename T>
void Tracer::append_send_event(const External<T>& channel)
{
  assert(!channel.term.is_null());
  assert(channel.offset_term.is_null());

  append_event<SEND_EVENT>(m_event_id_cnt++, channel.address, channel.term);
}

}

#define CRV_BUILTIN_UNARY_OP(op, opcode)                                        \
  template<typename T>                                                          \
  inline auto operator op(const crv::Internal<T>& arg)                          \
  -> crv::Internal<typename crv::internal::Return<smt::opcode, T>::Type>        \
  {                                                                             \
    typedef typename crv::internal::Return<smt::opcode, T>::Type ReturnType;    \
    return crv::Internal<ReturnType>(op arg.term);                              \
  }                                                                             \
                                                                                \
  template<typename T>                                                          \
  inline auto operator op(crv::Internal<T>&& arg)                               \
  -> crv::Internal<typename crv::internal::Return<smt::opcode, T>::Type>        \
  {                                                                             \
    typedef typename crv::internal::Return<smt::opcode, T>::Type ReturnType;    \
    return crv::Internal<ReturnType>(op std::move(arg.term));                   \
  }                                                                             \
                                                                                \
  template<typename T>                                                          \
  inline auto operator op(const crv::External<T>& arg)                          \
  -> crv::Internal<typename crv::internal::Return<smt::opcode, T>::Type>        \
  {                                                                             \
    crv::Internal<T> arg_internal(crv::append_input_event(arg));                \
    return op std::move(arg_internal);                                          \
  }                                                                             \

CRV_BUILTIN_UNARY_OP(-, SUB)
CRV_BUILTIN_UNARY_OP(!, LNOT)

#ifdef __BIT_PRECISION__
CRV_BUILTIN_UNARY_OP(~, NOT)
#endif

#define CRV_BUILTIN_BINARY_OP(op, opcode)                                       \
  template<typename U, typename V>                                              \
  inline auto operator op(                                                      \
    const crv::Internal<U>& larg,                                               \
    const crv::Internal<V>& rarg)                                               \
  -> crv::Internal<typename crv::internal::Return<smt::opcode, U, V>::Type>     \
  {                                                                             \
    typedef typename crv::internal::Return<smt::opcode, U, V>::Type ReturnType; \
    return crv::Internal<ReturnType>(larg.term op rarg.term);                   \
  }                                                                             \
                                                                                \
  template<typename U, typename V>                                              \
  inline auto operator op(                                                      \
    const crv::Internal<U>& larg,                                               \
    crv::Internal<V>&& rarg)                                                    \
  -> crv::Internal<typename crv::internal::Return<smt::opcode, U, V>::Type>     \
  {                                                                             \
    typedef typename crv::internal::Return<smt::opcode, U, V>::Type ReturnType; \
    return crv::Internal<ReturnType>(larg.term op std::move(rarg.term));        \
  }                                                                             \
                                                                                \
  template<typename U, typename V>                                              \
  inline auto operator op(                                                      \
    crv::Internal<U>&& larg,                                                    \
    const crv::Internal<V>& rarg)                                               \
  -> crv::Internal<typename crv::internal::Return<smt::opcode, U, V>::Type>     \
  {                                                                             \
    typedef typename crv::internal::Return<smt::opcode, U, V>::Type ReturnType; \
    return crv::Internal<ReturnType>(std::move(larg.term) op rarg.term);        \
  }                                                                             \
                                                                                \
  template<typename U, typename V>                                              \
  inline auto operator op(                                                      \
    crv::Internal<U>&& larg,                                                    \
    crv::Internal<V>&& rarg)                                                    \
  -> crv::Internal<typename crv::internal::Return<smt::opcode, U, V>::Type>     \
  {                                                                             \
    typedef typename crv::internal::Return<smt::opcode, U, V>::Type ReturnType; \
    return crv::Internal<ReturnType>(                                           \
      std::move(larg.term) op std::move(rarg.term));                            \
  }                                                                             \
                                                                                \
  template<typename U, typename V,                                              \
    class Enable = typename std::enable_if<std::is_arithmetic<V>::value>::type> \
  inline auto operator op(                                                      \
    const crv::Internal<U>& larg,                                               \
    V literal)                                                                  \
  -> crv::Internal<typename crv::internal::Return<smt::opcode, U, V>::Type>     \
  {                                                                             \
    typedef typename crv::internal::Return<smt::opcode, U, V>::Type ReturnType; \
    return crv::Internal<ReturnType>(larg.term op literal);                     \
  }                                                                             \
                                                                                \
  template<typename U, typename V,                                              \
    class Enable = typename std::enable_if<std::is_arithmetic<V>::value>::type> \
  inline auto operator op(                                                      \
    crv::Internal<U>&& larg,                                                    \
    V literal)                                                                  \
  -> crv::Internal<typename crv::internal::Return<smt::opcode, U, V>::Type>     \
  {                                                                             \
    typedef typename crv::internal::Return<smt::opcode, U, V>::Type ReturnType; \
    return crv::Internal<ReturnType>(std::move(larg.term) op literal);          \
  }                                                                             \
                                                                                \
  template<typename U, typename V,                                              \
    class Enable = typename std::enable_if<std::is_arithmetic<U>::value>::type> \
  inline auto operator op(                                                      \
    U literal,                                                                  \
    const crv::Internal<V>& rarg)                                               \
  -> crv::Internal<typename crv::internal::Return<smt::opcode, U, V>::Type>     \
  {                                                                             \
    typedef typename crv::internal::Return<smt::opcode, U, V>::Type ReturnType; \
    return crv::Internal<ReturnType>(literal op rarg.term);                     \
  }                                                                             \
                                                                                \
  template<typename U, typename V,                                              \
    class Enable = typename std::enable_if<std::is_arithmetic<U>::value>::type> \
  inline auto operator op(                                                      \
    U literal,                                                                  \
    crv::Internal<V>&& rarg)                                                    \
  -> crv::Internal<typename crv::internal::Return<smt::opcode, U, V>::Type>     \
  {                                                                             \
    typedef typename crv::internal::Return<smt::opcode, U, V>::Type ReturnType; \
    return crv::Internal<ReturnType>(literal op std::move(rarg.term));          \
  }                                                                             \
                                                                                \
  template<typename U, typename V>                                              \
  inline auto operator op(                                                      \
  const crv::External<U>& larg,                                                 \
  const crv::Internal<V>& rarg)                                                 \
  -> crv::Internal<typename crv::internal::Return<smt::opcode, U, V>::Type>     \
  {                                                                             \
    crv::Internal<U> larg_internal(crv::append_input_event(larg));              \
    return std::move(larg_internal) op rarg;                                    \
  }                                                                             \
                                                                                \
  template<typename U, typename V>                                              \
  inline auto operator op(                                                      \
  const crv::External<U>& larg,                                                 \
  crv::Internal<V>&& rarg)                                                      \
  -> crv::Internal<typename crv::internal::Return<smt::opcode, U, V>::Type>     \
  {                                                                             \
    crv::Internal<U> larg_internal(crv::append_input_event(larg));              \
    return std::move(larg_internal) op std::move(rarg);                         \
  }                                                                             \
                                                                                \
  template<typename U, typename V>                                              \
  inline auto operator op(                                                      \
    const crv::Internal<U>& larg,                                               \
    const crv::External<V>& rarg)                                               \
  -> crv::Internal<typename crv::internal::Return<smt::opcode, U, V>::Type>     \
  {                                                                             \
    crv::Internal<U> rarg_internal(crv::append_input_event(rarg));              \
    return larg op std::move(rarg_internal);                                    \
  }                                                                             \
                                                                                \
  template<typename U, typename V>                                              \
  inline auto operator op(                                                      \
    crv::Internal<U>&& larg,                                                    \
    const crv::External<V>& rarg)                                               \
  -> crv::Internal<typename crv::internal::Return<smt::opcode, U, V>::Type>     \
  {                                                                             \
    crv::Internal<V> rarg_internal(crv::append_input_event(rarg));              \
    return std::move(larg) op std::move(rarg_internal);                         \
  }                                                                             \
                                                                                \
  template<typename U, typename V>                                              \
  inline auto operator op(                                                      \
    const crv::External<U>& larg,                                               \
    const crv::External<V>& rarg)                                               \
  -> crv::Internal<typename crv::internal::Return<smt::opcode, U, V>::Type>     \
  {                                                                             \
    crv::Internal<U> larg_internal(crv::append_input_event(larg));              \
    crv::Internal<V> rarg_internal(crv::append_input_event(rarg));              \
    return std::move(larg_internal) op std::move(rarg_internal);                \
  }                                                                             \
                                                                                \
  template<typename U, typename V,                                              \
    class Enable = typename std::enable_if<std::is_arithmetic<V>::value>::type> \
  inline auto operator op(                                                      \
    const crv::External<U>& larg,                                               \
    V literal)                                                                  \
  -> crv::Internal<typename crv::internal::Return<smt::opcode, U, V>::Type>     \
  {                                                                             \
    crv::Internal<U> larg_internal(crv::append_input_event(larg));              \
    typedef typename crv::internal::Return<smt::opcode, U, V>::Type ReturnType; \
    return crv::Internal<ReturnType>(std::move(larg_internal.term) op literal); \
  }                                                                             \
                                                                                \
  template<typename U, typename V,                                              \
    class Enable = typename std::enable_if<std::is_arithmetic<U>::value>::type> \
  inline auto operator op(                                                      \
    U literal,                                                                  \
    const crv::External<V>& rarg)                                               \
  -> crv::Internal<typename crv::internal::Return<smt::opcode, U, V>::Type>     \
  {                                                                             \
    crv::Internal<V> rarg_internal(crv::append_input_event(rarg));              \
    typedef typename crv::internal::Return<smt::opcode, U, V>::Type ReturnType; \
    return crv::Internal<ReturnType>(literal op std::move(rarg_internal.term)); \
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
  static const std::string s_ldf_prefix;

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
  std::unordered_map<EventIdentifier, Time> m_time_map;
  const Time m_epoch;

  /// Uses e's identifier to build a numerical SMT variable
  const Time& time(const Event& e)
  {
    if (m_time_map.find(e.event_id) == m_time_map.cend())
    {
      Time time(smt::any<TimeSort>(prefix_event_id(s_time_prefix, e)));
      m_solver.add(m_epoch.happens_before(time));
      m_time_map.insert(std::make_pair(e.event_id, time));
    }

    return m_time_map.at(e.event_id);
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
      for (const EventIter r_iter : a.reads())
      {
        const Event& r = *r_iter;

        smt::UnsafeTerm or_rf(smt::literal<smt::Bool>(false));
        for (const EventIter w_iter : a.writes())
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
      for (const EventIter r_iter : a.reads())
      {
        const Event& r = *r_iter;

        for (const EventIter w_iter : a.writes())
        {
          const Event& w = *w_iter;

          for (const EventIter w_prime_iter : a.writes())
          {
            if (w_iter == w_prime_iter)
              continue;

            const Event& w_prime = *w_prime_iter;
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
      if (a.writes().size() < 2)
        continue;

      smt::UnsafeTerms terms;
      terms.reserve(a.writes().size());
      for (const EventIter w_iter : a.writes())
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
      for (const EventIter pop_iter : a.pops())
      {
        const Event& pop = *pop_iter;

        smt::UnsafeTerm or_pf(smt::literal<smt::Bool>(false));
        for (const EventIter push_iter : a.pushes())
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
      if (a.pops().size() < 2)
        continue;

      smt::Terms<TimeSort> terms(a.pops().size());
      for (const EventIter pop_iter : a.pops())
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
      for (const EventIter push_iter : a.pushes())
      {
        const Event& push = *push_iter;

        for (const EventIter push_prime_iter : a.pushes())
        {
          const Event& push_prime = *push_prime_iter;
          const smt::Bool pushes_order(
            time(push).happens_before(time(push_prime)));

          for (const EventIter pop_iter : a.pops())
          {
            const Event& pop = *pop_iter;
            const smt::Bool pf_bool(flow_bool(s_pf_prefix, push, pop));
            const smt::Bool push_prime_pop_order(
              time(push_prime).happens_before(time(pop)));

            smt::UnsafeTerm or_pp(smt::literal<smt::Bool>(false));
            for (const EventIter pop_prime_iter : a.pops())
            {
              const Event& pop_prime = *pop_prime_iter;
              const smt::Bool pf_prime_bool(
                flow_bool(s_pf_prefix, push_prime, pop_prime)),
                pops_order(time(pop_prime).happens_before(time(pop)));

              // build pf!pop' = push' for some pop'
              or_pp = or_pp or pf_prime_bool;

              // if pf!pop = push and pf!pop' = push' and
              // t!push < t!push' and t!push' < t!pop,
              // then t!pop' < t!pop.
              and_stack = and_stack and smt::implies(
                pf_bool and pf_prime_bool and pushes_order and
                push_prime_pop_order, pops_order);
            }

            // if t!push < t!push' < t!pop and pf!pop = push and
            // guard(push'), then there exists a pop' such that
            // pf!pop' = push' (and t!pop' < t!pop by "pop-from").
            and_stack = and_stack and
              smt::implies(
                pf_bool and push_prime.guard and pushes_order and
                push_prime_pop_order, or_pp);
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

  // Similar to "read-from" axiom except that offsets must be equal and
  // loads from initial array return zero
  void encode_load_from(const PerAddressMap& per_address_map)
  {
    smt::UnsafeTerm and_ldf(smt::literal<smt::Bool>(true));
    for (const PerAddressMap::value_type& pair : per_address_map)
    {
      const EventKinds& a = pair.second;
      for (const EventIter ld_iter : a.loads())
      {
        const Event& ld = *ld_iter;
        const Time& ld_time = time(ld);

        smt::UnsafeTerm and_lds(smt::literal<smt::Bool>(true));
        smt::UnsafeTerm or_ldf(smt::literal<smt::Bool>(false));
        for (const EventIter s_iter : a.stores())
        {
          const Event& s = *s_iter;

          const smt::Bool sld_order(time(s).happens_before(ld_time));
          const smt::Bool ldf_bool(flow_bool(s_ldf_prefix, s, ld));
          const smt::UnsafeTerm sld_equality(s.term == ld.term);

          // for every store s, if ld and s access the same array
          // offset, then t!ld < t!s (i.e. ld must happen before s).
          and_lds = and_lds and
            smt::implies(/* if */ ld.offset_term == s.offset_term,
                         /* then */ ld_time.happens_before(time(s)));

          or_ldf = ldf_bool or or_ldf;

          and_ldf = and_ldf and
            smt::implies(
              /* if */ ldf_bool,
              /* then */ sld_order and s.guard and
                sld_equality and s.offset_term == ld.offset_term);
        }

        /* initial array elements are zero */
        smt::UnsafeTerm ld_zero(smt::literal(ld.term.sort(), 0));
        and_ldf = and_ldf and ld.guard and smt::implies(
          /* if */ not or_ldf,
          /* then */ and_lds and ld.term == std::move(ld_zero));
      }
    }
    unsafe_add(and_ldf);
  }

  // Similar to "from-read" axiom except that offsets must be equal
  void encode_from_load(const PerAddressMap& per_address_map)
  {
    smt::UnsafeTerm and_fld(smt::literal<smt::Bool>(true));
    for (const PerAddressMap::value_type& pair : per_address_map)
    {
      const EventKinds& a = pair.second;
      for (const EventIter ld_iter : a.loads())
      {
        const Event& ld = *ld_iter;

        for (const EventIter s_iter : a.stores())
        {
          const Event& s = *s_iter;

          for (const EventIter s_prime_iter : a.stores())
          {
            if (s_iter == s_prime_iter)
              continue;

            const Event& s_prime = *s_prime_iter;
            const smt::Bool ldf_bool(flow_bool(s_ldf_prefix, s, ld));
            and_fld = and_fld and s.guard and
              smt::implies(
                /* if */ ldf_bool and time(s).happens_before(time(s_prime)) and
                         s.offset_term == s_prime.offset_term,
                /* then */ time(ld).happens_before(time(s_prime)));
          }
        }
      }
    }
    unsafe_add(and_fld);
  }

  // Serialize every store regardless of array offset
  void encode_store_serialization(const PerAddressMap& per_address_map)
  {
    smt::UnsafeTerm and_ss(smt::literal<smt::Bool>(true));
    for (const PerAddressMap::value_type& pair : per_address_map)
    {
      const EventKinds& a = pair.second;
      if (a.stores().size() < 2)
        continue;

      smt::UnsafeTerms terms;
      terms.reserve(a.stores().size());
      for (const EventIter s_iter : a.stores())
      {
        const Event& s = *s_iter;
        terms.push_back(time(s).term());
      }

      and_ss = and_ss and smt::distinct(std::move(terms));
    }
    unsafe_add(and_ss);
  }

  void encode_array_api(const Tracer& tracer)
  {
    const PerAddressMap& per_address_map = tracer.per_address_map();
    encode_load_from(per_address_map);
    encode_from_load(per_address_map);
    encode_store_serialization(per_address_map);
  }

public:
  static PerEventMap build_predecessors_map(
    const PerThreadMap& per_thread_map)
  {
    // TODO: implement communication-select feature
    bool is_communication_select(false);
    PerEventMap predecessors_map;
    for (const PerThreadMap::value_type& pair : per_thread_map)
    {
      // ignore main thread
      if (pair.first == 1)
        continue;

      const EventIters& events = pair.second;
      assert(!events.empty());

      EventIters::const_reverse_iterator criter(events.crbegin());
      assert(criter != events.crend());

      EventIter e_iter(*criter);
      assert(e_iter->is_thread_end());

      EventIter e_prime_iter(e_iter);
      for (criter++; criter != events.crend(); criter++)
      {
        const EventKind e_kind((*criter)->kind);
        if (e_kind != RECV_EVENT && e_kind != SEND_EVENT)
          continue;

        e_prime_iter = *criter;
        EventIters& predecessors = predecessors_map[e_iter];
        if (!is_communication_select)
        {
          e_iter = e_prime_iter;
          for (const EventIter p_iter : predecessors)
          {
            predecessors_map[p_iter].push_back(e_iter);
          }
        }
        predecessors.push_back(e_prime_iter); 
      }

      // at least one event in every thread has no predecessors
      assert(e_prime_iter->is_recv() || e_prime_iter->is_send() ||
        e_prime_iter->is_thread_end());
      predecessors_map[e_prime_iter];
    }
    return predecessors_map;
  }

  /// Maps recv/send events on same channel but in different threads
  typedef std::unordered_map<std::pair<EventIter, EventIter>,
    smt::Bool> MatchableMap;

  static MatchableMap build_matchable_map(
    const PerAddressMap& per_address_map)
  {
    const std::string match_prefix("match!{");
    MatchableMap matchable_map;
    for (const PerAddressMap::value_type& pair : per_address_map)
    {
      const EventKinds& a = pair.second;
      for (const EventIter r_iter : a.recvs())
      {
        for (const EventIter s_iter : a.sends())
        {
          if (r_iter->thread_id == s_iter->thread_id)
            continue;

          std::string match_symbol(match_prefix +
            std::to_string(r_iter->event_id) + "," +
            std::to_string(s_iter->event_id) + "}");

          matchable_map[std::make_pair(r_iter, s_iter)] =
            smt::any<smt::Bool>(std::move(match_symbol));
        }
      }
    }
    return matchable_map;
  }

private:
  static smt::Bool communication_preds(
    const PerAddressMap& per_address_map,
    const MatchableMap& matchable_map,
    const EventIters& predecessors)
  {
    smt::Bool and_match(smt::literal<smt::Bool>(true));
    for (const EventIter e_iter : predecessors)
    {
      assert(e_iter->is_recv() || e_iter->is_send());

      const EventKinds& a = per_address_map.at(e_iter->address);
      const EventIters& matchables = e_iter->is_recv() ?
        a.sends() : a.recvs();

      smt::Bool or_match(smt::literal<smt::Bool>(false));
      for (const EventIter e_prime_iter : matchables)
      {
        if (e_iter->thread_id == e_prime_iter->thread_id)
          continue;

        const MatchableMap::key_type match_pair(
          e_iter->is_recv() ?
            std::make_pair(e_iter, e_prime_iter)
          : std::make_pair(e_prime_iter, e_iter));

        or_match = or_match or matchable_map.at(match_pair);
      }

      and_match = and_match and or_match;
    }
    return and_match;
  }

  static smt::Bool communication_excl(
    const PerAddressMap& per_address_map,
    const MatchableMap& matchable_map,
    const EventIter r_iter,
    const EventIter s_iter)
  {
    assert(r_iter->is_recv());
    assert(s_iter->is_send());
    assert(r_iter->thread_id != s_iter->thread_id);

    const EventKinds& r_a = per_address_map.at(r_iter->address);
    const EventKinds& s_a = per_address_map.at(s_iter->address);

    smt::Bool or_match(smt::literal<smt::Bool>(false));
    for (const EventIter e_iter : r_a.sends())
    {
      if (r_iter->thread_id == e_iter->thread_id || e_iter == s_iter)
        continue;

      or_match = or_match or
        matchable_map.at(std::make_pair(r_iter, e_iter));
    }
    for (const EventIter e_iter : s_a.recvs())
    {
      if (s_iter->thread_id == e_iter->thread_id || e_iter == r_iter)
        continue;

      or_match = or_match or
        matchable_map.at(std::make_pair(e_iter, s_iter));
    }
    return not or_match;
  }

  void encode_communication_concurrency(const Tracer& tracer, bool check_deadlocks)
  {
    const PerAddressMap& per_address_map = tracer.per_address_map();
    const PerThreadMap& per_thread_map = tracer.per_thread_map();

    auto matchable_map(build_matchable_map(per_address_map));
    auto predecessors_map(build_predecessors_map(per_thread_map));

    Bools inits;
    smt::UnsafeTerm ext_match(smt::literal<smt::Bool>(true));
    for (const PerAddressMap::value_type& pair : per_address_map)
    {
      const EventKinds& a = pair.second;
      for (const EventIter r_iter : a.recvs())
      {
        const Time& r_time = time(*r_iter);
        for (const EventIter s_iter : a.sends())
        {
          if (r_iter->thread_id == s_iter->thread_id)
            continue;

          const Event& r = *r_iter;
          const Event& s = *s_iter;
          const smt::Bool& match_bool =
            matchable_map.at(std::make_pair(r_iter, s_iter));

          smt::UnsafeTerm rs_value(smt::implies(
            /* if */ match_bool,
            /* then */ r.term == s.term));

          smt::UnsafeTerm rs_ext(match_bool ==
            (communication_preds(per_address_map, matchable_map,
               predecessors_map.at(r_iter)) and
             communication_preds(per_address_map, matchable_map,
               predecessors_map.at(s_iter)) and
             communication_excl(per_address_map, matchable_map,
               r_iter, s_iter) and r.guard and s.guard));

          ext_match = ext_match and rs_ext and rs_value and
            (match_bool == r_time.simultaneous(time(s)));

          if (predecessors_map.at(r_iter).empty() &&
              predecessors_map.at(s_iter).empty())
            inits.push_back(match_bool);
        }
      }
    }

    if (check_deadlocks)
    {
      const std::string finalizer_prefix("finalizer!");
      smt::Bool finalizers(smt::literal<smt::Bool>(true));
      for (const PerThreadMap::value_type& pair : per_thread_map)
      {
        // ignore main thread
        if (pair.first == 1)
          continue;

        const EventIter e_iter(pair.second.back());
        assert(e_iter->is_thread_end());

        smt::Bool finalizer_bool(smt::any<smt::Bool>(
          finalizer_prefix + std::to_string(e_iter->event_id)));
        finalizers = finalizers and finalizer_bool;
        ext_match = ext_match and
          (finalizer_bool == communication_preds(per_address_map,
             matchable_map, predecessors_map.at(e_iter)));
      }
      unsafe_add(not finalizers);
    }

    unsafe_add(ext_match);

    if (!inits.empty())
    {
      smt::Bool init_match(smt::literal<smt::Bool>(false));
      for (const smt::Bool init : inits)
      {
        init_match = init_match or init;
      }
      unsafe_add(init_match);
    }
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
      const EventIters& events = pair.second;
      if (events.size() < 2)
        continue;

      EventIters::const_iterator events_iter = events.cbegin();
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

  void encode_errors(const Bools& errors)
  {
    if (errors.empty())
      return;

    smt::Bool or_error(smt::literal<smt::Bool>(false));
    for (const smt::Bool& error : errors)
    {
      or_error = or_error or error;
    }
    unsafe_add(or_error);
  }

  void encode(const Tracer& tracer, bool check_deadlock)
  {
    unsafe_add(tracer.guard());
    for (const smt::Bool& assertion : tracer.assertions())
    {
      unsafe_add(assertion);
    }

    encode_thread_order(tracer.per_thread_map());
    encode_memory_concurrency(tracer);
    encode_communication_concurrency(tracer, check_deadlock);
    encode_stack_api(tracer);
    encode_array_api(tracer);
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

  /// Checks only whether there is a communication deadlock

  /// No errors are encoded
  smt::CheckResult check_deadlock(const Tracer& tracer)
  {
    m_solver.push();
    encode(tracer, true);
    const smt::CheckResult result = m_solver.check();
    m_solver.pop();
    return result;
  }

  /// Check for any program safety violations (i.e. bugs)

  /// Use SAT/SMT solver to check the satisfiability of the
  /// disjunction of errors() and conjunction of assertions()
  ///
  /// If there is a communication deadlock, receive events are
  /// permitted to take on nondeterministic values possibly
  /// leading to false alarms.
  ///
  /// pre: not errors().empty()
  smt::CheckResult check(const Tracer& tracer)
  {
    assert(!tracer.errors().empty());

    m_solver.push();
    encode(tracer, false);
    encode_errors(tracer.errors());
    const smt::CheckResult result = m_solver.check();
    m_solver.pop();
    return result;
  }

  // Check satisfiability of given condition and conjunction of
  // assertions(). Note: errors() are always ignored.
  //
  // If there is a communication deadlock, receive events are
  // permitted to take on nondeterministic values possibly
  // leading to false alarms.
  smt::CheckResult check(
    Internal<bool>&& condition,
    const Tracer& tracer)
  {
    m_solver.push();
    unsafe_add(std::move(condition.term));
    encode(tracer, false);
    const smt::CheckResult result = m_solver.check();
    m_solver.pop();
    return result;
  }
};

/// Symbolic thread using partial order encoding
class Thread
{
private:
  const smt::Bool m_guard;
  ThreadIdentifier m_parent_thread_id;
  ThreadIdentifier m_thread_id;

public:
  /// Symbolically spawn `f(args...)` as a new thread of execution

  /// \param f non-member function to be executed as a new symbolic thread
  /// \param args arguments \ref std::forward "forwarded" to `f`
  ///
  /// The return value of `f` is always ignored.
  template<typename Function, typename... Args>
  Thread(Function&& f, Args&&... args)
  : m_guard(tracer().guard()),
    m_parent_thread_id(0),
    m_thread_id(0)
  {
    tracer().reset_guard();
    m_parent_thread_id = tracer().append_thread_begin_event();
    f(args...);
    m_thread_id = tracer().append_thread_end_event();
    tracer().reset_guard(m_guard);
  }

  bool joinable() const
  {
    return 0 < m_thread_id;
  }

  void join()
  {
    assert(joinable());
    tracer().append_join_event(m_thread_id);
    m_thread_id = 0;
  }
};

namespace ThisThread
{
  ThreadIdentifier thread_id();
}

/// Symbolic spinlock

/// The Mutex class symbolically encodes a spinlock that protects shared data
/// from being simultaneously accessed by multiple threads.
class Mutex {
private:
  ThreadIdentifier m_lock_thread_id;
  External<ThreadIdentifier> m_thread_id;

public:
  Mutex() :
  m_lock_thread_id(/* no thread */ 0),
  m_thread_id(/* no thread */ 0) {}

  /// Acquire lock
  void lock() {
    m_lock_thread_id = ThisThread::thread_id();
    m_thread_id = m_lock_thread_id;
  }

  /// Release lock

  /// \pre: ThisThread is the same as the one that called lock()
  void unlock()
  {
    // TODO: ensure that lock() and unlock() are in preserved program order
    assert(m_lock_thread_id == ThisThread::thread_id());
    tracer().add_assertion(m_thread_id == m_lock_thread_id);
  }
};

/// CSP-style communication
template<typename T>
class Channel
{
private:
  External<T> m_channel;

public:
  void send(T v)
  {
    send(Internal<T>(v));
  }

  void send(const Internal<T>& payload)
  {
    m_channel.term = payload.term;
    tracer().append_send_event(m_channel);
  }

  void send(const External<T>& payload)
  {
    m_channel.term = append_input_event(payload);
    tracer().append_send_event(m_channel);
  }

  Internal<T> recv() const
  {
    return Internal<T>(tracer().append_recv_event(m_channel));
  }
};

template<typename T>
class Stack
{
private:
  External<T> m_stack;

public:
  void push(T v)
  {
    push(Internal<T>(v));
  }

  void push(const Internal<T>& internal)
  {
    m_stack.term = internal.term;
    tracer().append_push_event(m_stack);
  }

  void push(const External<T>& external)
  {
    m_stack.term = append_input_event(external);
    tracer().append_push_event(m_stack);
  }

  Internal<T> pop()
  {
    return Internal<T>(tracer().append_pop_event(m_stack));
  }
};

}

#endif
