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
#include <iterator>
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
  CHANNEL_RECV_EVENT,
  CHANNEL_SEND_EVENT,
  MESSAGE_RECV_EVENT,
  MESSAGE_SEND_EVENT,
};

/// Positive unless event is_sync()

/// An address must not be exposed to users of APIs modelled with partial orders
typedef unsigned int Address;

/// Unique identifier of an instruction in a loop-free (i.e. unrolled) program
typedef unsigned int EventIdentifier;

/// Positive if and only if thread is joinable
typedef unsigned ThreadIdentifier;

/// Unique number for each basic block when in multi-path mode
typedef unsigned BlockIdentifier;

/// Number of thread-local nested if-then-else blocks
typedef unsigned ScopeLevel;

class Event
{
public:
  const EventKind kind;
  const EventIdentifier event_id;
  const ThreadIdentifier thread_id;
  const BlockIdentifier block_id;
  const ScopeLevel scope_level;
  const Address address;
  const smt::Bool guard;
  const smt::UnsafeTerm term;
  const smt::UnsafeTerm offset_term;

  Event(const Event&) = delete;

  Event(
    const EventKind kind_arg,
    const EventIdentifier event_id_arg,
    const ThreadIdentifier thread_id_arg,
    const BlockIdentifier block_id_arg,
    const ScopeLevel scope_level_arg,
    const Address address_arg,
    const smt::Bool guard_arg,
    const smt::UnsafeTerm& term_arg,
    const smt::UnsafeTerm& offset_term_arg)
  : kind(kind_arg),
    event_id(event_id_arg),
    thread_id(thread_id_arg),
    block_id(block_id_arg),
    scope_level(scope_level_arg),
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
  bool is_channel_recv() const { return kind == CHANNEL_RECV_EVENT; }
  bool is_channel_send() const { return kind == CHANNEL_SEND_EVENT; }
  bool is_message_recv() const { return kind == MESSAGE_RECV_EVENT; }
  bool is_message_send() const { return kind == MESSAGE_SEND_EVENT; }
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
  EventIters m_channel_recvs;
  EventIters m_channel_sends;
  EventIters m_message_recvs;
  EventIters m_message_sends;

public:
  EventKinds()
  : m_reads(),
    m_writes(),
    m_pops(),
    m_pushes(),
    m_loads(),
    m_stores(),
    m_channel_recvs(),
    m_channel_sends(),
    m_message_recvs(),
    m_message_sends() {}

  // See member function template specializations
  template<EventKind kind>
  void push_back(const EventIter e_iter) { /* skip */ }

  const EventIters& reads()  const { return m_reads;  }
  const EventIters& writes() const { return m_writes; }
  const EventIters& pops()   const { return m_pops;   }
  const EventIters& pushes() const { return m_pushes; }
  const EventIters& loads()  const { return m_loads;  }
  const EventIters& stores() const { return m_stores; }

  const EventIters& channel_recvs()  const { return m_channel_recvs; }
  const EventIters& channel_sends()  const { return m_channel_sends; }

  const EventIters& message_recvs()  const { return m_message_recvs; }
  const EventIters& message_sends()  const { return m_message_sends; }
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
void EventKinds::push_back<CHANNEL_RECV_EVENT>(const EventIter e_iter)
{
  m_channel_recvs.push_back(e_iter);
}

template<> inline
void EventKinds::push_back<CHANNEL_SEND_EVENT>(const EventIter e_iter)
{
  m_channel_sends.push_back(e_iter);
}

template<> inline
void EventKinds::push_back<MESSAGE_RECV_EVENT>(const EventIter e_iter)
{
  m_message_recvs.push_back(e_iter);
}

template<> inline
void EventKinds::push_back<MESSAGE_SEND_EVENT>(const EventIter e_iter)
{
  m_message_sends.push_back(e_iter);
}

typedef std::unordered_map<EventIter, EventIters> PerEventMap;
typedef std::unordered_map<Address, EventKinds> PerAddressIndex;
typedef std::unordered_map<ThreadIdentifier, EventKinds> PerThreadIndex;
typedef std::unordered_map<ThreadIdentifier, EventIters> PerThreadMap;
typedef std::unordered_map<EventIter, EventIter> EventMap;

/// Control flow decision along symbolic path
struct Flip
{
  bool direction;
  bool is_flip;

  Flip(const Flip&) = delete;

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
    /* else */ smt::Real>::type Sort;
};

/// Nesting of branches within a single thread

/// Facilitate symbolic multi-path analysis where both
/// branches of control-flow statements are encoded

// TODO: Support Internal<T> inside scopes
// TODO: Think about Tracer::decide_flip()
struct ThreadLocalScope
{
  /// never null
  smt::Bool guard;

  /// null if and only if level is zero
  smt::Bool guard_prime;

  /// starting at zero
  const ScopeLevel level;

  ThreadLocalScope(const ThreadLocalScope&) = delete;

  /// outermost scope when a thread starts
  ThreadLocalScope(const smt::Bool& guard_arg)
  : guard(guard_arg),
    guard_prime(),
    level(0)
  {
    assert(!guard.is_null());
  }

  ThreadLocalScope(
    const smt::Bool& guard_arg,
    const smt::Bool& guard_prime_arg,
    const ScopeLevel level_arg)
  : guard(guard_arg),
    guard_prime(guard_prime_arg),
    level(level_arg)
  {
    assert(!guard.is_null());
    assert(!guard_prime_arg.is_null());
    assert(0 < level);
  }
};

class Tracer
{
public:
  // 2^(N-1)-1 where N is the number of bits in Address
  static constexpr Address s_max_reserved_address =
    std::numeric_limits<Address>::max() / 2;

private:
  static const std::string s_value_prefix;

  EventIdentifier m_event_id_cnt;
  ThreadIdentifier m_thread_id_cnt;
  BlockIdentifier m_block_id_cnt;
  Events m_events;

  // Index event list by various keys
  PerAddressIndex m_per_address_index;
  PerThreadIndex m_per_thread_index;
  PerThreadMap m_per_thread_map;

  // always nonempty
  std::stack<ThreadIdentifier> m_thread_id_stack;
  std::stack<ThreadLocalScope> m_scope_stack;

  // never null
  smt::Bool m_guard;

  unsigned long long m_flip_cnt;
  Flips m_flips;
  FlipIter m_flip_iter;
  Bools m_assertions;
  Bools m_errors;

  Address m_next_reserved_address;

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
    assert(!m_scope_stack.empty());

    const ThreadIdentifier thread_id(current_thread_id());
    m_events.emplace_back(kind, event_id, thread_id, m_block_id_cnt,
      m_scope_stack.top().level, address, guard(), term, offset_term);

    const EventIter e_iter(std::prev(m_events.cend()));
    m_per_address_index[e_iter->address].push_back<kind>(e_iter);
    m_per_thread_index[thread_id].push_back<kind>(e_iter);
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
    m_block_id_cnt(0),
    m_events(),
    m_per_address_index(),
    m_per_thread_index(),
    m_per_thread_map(),
    m_thread_id_stack(),
    m_scope_stack(),
    m_guard(smt::literal<smt::Bool>(true)),
    m_flip_cnt(0),
    m_flips(),
    m_flip_iter(m_flips.cbegin()),
    m_assertions(),
    m_errors(),
    m_next_reserved_address(1),
    m_barrier_list(),
    m_barrier_map()
  {
    m_thread_id_stack.push(m_thread_id_cnt++);
    m_scope_stack.emplace(m_guard);
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

  const PerAddressIndex& per_address_index() const
  {
    return m_per_address_index;
  }

  const PerThreadIndex& per_thread_index() const
  {
    return m_per_thread_index;
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
    m_per_address_index.clear();
    m_per_thread_index.clear();
    m_per_thread_map.clear();

    while (!m_thread_id_stack.empty())
    {
      m_thread_id_stack.pop();
    }
    m_thread_id_cnt = 1;
    push_next_thread_id();

    m_block_id_cnt = 0;
    while (!m_scope_stack.empty())
    {
      m_scope_stack.pop();
    }
    m_guard = smt::literal<smt::Bool>(true);
    m_scope_stack.emplace(m_guard);
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
    m_next_reserved_address = 1;
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

      m_barrier_map.insert(
        std::make_pair(thread_id, m_barrier_list.cbegin()));
    }
    else
    {
      // caution: branches rely on mutable reference!
      std::list<EventIdentifier>::const_iterator& citer =
        m_barrier_map.at(thread_id);
      assert(citer != m_barrier_list.cend());
      if (citer == std::prev(m_barrier_list.cend()))
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

  /// Encoded as conjunction
  const Bools& assertions() const
  {
    return m_assertions;
  }

  /// Encoded as disjunction 
  const Bools& errors() const
  {
    return m_errors;
  }

  /// Add Boolean term of argument to assertions()

  /// This is similar to entering "if (condition) { ... }"
  /// except that no further flips are required.
  void add_assertion(Internal<bool>&&);

  /// Add conjunction of guard() and given Boolean term to errors()
  void add_error(Internal<bool>&&);

  Address next_reserved_address()
  {
    assert(m_next_reserved_address < s_max_reserved_address);
    return m_next_reserved_address++;
  }

  /// Decide which control flow direction to follow

  /// The second direction argument is only a suggestion that is ignored when
  /// the first condition argument is_literal()
  bool decide_flip(const Internal<bool>&, bool direction = true);

  /// Returns parent thread identifier
  ThreadIdentifier append_thread_begin_event()
  {
    const EventIdentifier event_id(m_event_id_cnt++);
    append_event<THREAD_BEGIN_EVENT>(
      event_id, 0, smt::UnsafeTerm());

    ThreadIdentifier parent_thread_id(current_thread_id());
    push_next_thread_id();

    m_guard = smt::literal<smt::Bool>(true);
    m_scope_stack.emplace(m_guard);

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

    assert(m_scope_stack.top().level == 0);
    m_scope_stack.pop();
    const ThreadLocalScope& parent_scope = m_scope_stack.top();
    if (parent_scope.guard_prime.is_null())
      m_guard = parent_scope.guard;
    else
      m_guard = parent_scope.guard and parent_scope.guard_prime;

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

  /// Incoming channel communication
  template<typename T>
  typename Smt<T>::Sort append_channel_recv_event(const Address);

  /// Outgoing channel communication
  void append_channel_send_event(const Address, const smt::UnsafeTerm&);

  /// Incoming message
  template<typename T>
  typename Smt<T>::Sort append_message_recv_event(const Address);

  /// Outgoing message
  void append_message_send_event(const Address, const smt::UnsafeTerm&);

  // Symbolic multi-path analysis
  void scope_then(const Internal<bool>& guard);
  void scope_else();
  void scope_end();
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

namespace simplifier
{
  /// Functor that applies a binary operation to an SMT term and literal
  template<class T>
  class AbstractOp
  {
  protected:
    AbstractOp() {}

    // no polymorphic deletes
    ~AbstractOp() {}

  public:
    AbstractOp(const AbstractOp&) = delete;

    typedef typename Smt<T>::Sort Term;

    virtual smt::Opcode opcode() const = 0;
    virtual Term fuse(const Term& u, const T& v) const = 0;
    virtual Term fuse(const Term& u, T&& v) const = 0;
    virtual Term fuse(Term&& u, const T& v) const = 0;
    virtual Term fuse(Term&& u, T&& v) const = 0;

    virtual bool is_group() const = 0;
    virtual T inverse(const T v) const = 0;

    /// same as Eval<opcode>::eval(u, inverse(v))
    virtual T right_cancel(const T u, const T v) const = 0;
  };

  template<typename T>
  struct IsUnsignedIntegral :
    std::integral_constant<bool,
      std::is_integral<T>::value and
      std::is_unsigned<T>::value>
  {};

  template<smt::Opcode opcode, class T>
  struct CommutativeGroupOp
  {
    static constexpr bool is_group() { return false; }
    static T inverse(const T u) { assert(is_group()); }

    /// same as Eval<opcode>::eval(u, inverse(v))
    static T right_cancel(const T u, const T v) { assert(is_group()); }
  };

  template<class T>
  struct CommutativeGroupOp<smt::ADD, T>
  {
    static constexpr bool is_group()
    {
      return IsUnsignedIntegral<T>::value;
    }

    static T inverse(const T v)
    {
      assert(is_group());
      return -v;
    }

    static T right_cancel(const T u, const T v)
    {
      assert(is_group());
      return u - v;
    }
  };

  /// Singleton class, use sole static member function
  template<smt::Opcode _opcode, class T>
  class Op : public AbstractOp<T>
  {
  private:
    // default base constructors are automatically called
    Op() {}

  public:
    using typename AbstractOp<T>::Term;

    static const Op* op_ptr()
    {
      static Op s_op;
      static const Op* const s_op_ptr = &s_op;
      return s_op_ptr;
    }

    smt::Opcode opcode() const override
    {
      return _opcode;
    }

    Term fuse(Term&& u, T&& v) const override
    {
      return internal::Eval<_opcode>::eval(std::move(u), std::move(v));
    }

    Term fuse(Term&& u, const T& v) const override
    {
      return internal::Eval<_opcode>::eval(std::move(u), v);
    }

    Term fuse(const Term& u, const T& v) const override
    {
      return internal::Eval<_opcode>::eval(u, v);
    }

    Term fuse(const Term& u, T&& v) const override
    {
      return internal::Eval<_opcode>::eval(u, std::move(v));
    }

    bool is_group() const override
    {
      return CommutativeGroupOp<_opcode, T>::is_group();
    }

    T inverse(const T v) const override
    {
      return CommutativeGroupOp<_opcode, T>::inverse(v);
    }

    /// same as Eval<opcode>::eval(u, inverse(v))
    T right_cancel(const T u, const T v) const override
    {
      assert(internal::Eval<_opcode>::eval(
        CommutativeGroupOp<_opcode, T>::right_cancel(u, v), v) == u);

      return CommutativeGroupOp<_opcode, T>::right_cancel(u, v);
    }
  };
}

// Uses lazy SMT terms for fast constant propagation in commutative monoids

// Call the static member function Internal<T>::term(const Internal<T>&)
// to get simplified SMT term
template<typename T>
class Internal
{
private:
  // lazy unless m_op == nullptr
  typename Smt<T>::Sort m_term;

  // Used in either of two ways:
  //
  // 1) if m_term.is_null() (thus m_op == nullptr), it represents a literal
  // 2) if not m_term.is_null() and m_op != nullptr, it is the intermediate
  //    result of propagating constants in a commutative monoid structure
  //    where the operator corresponds to m_op->opcode()
  //
  // Otherwise, it is undefined.
  T m_v;

  // Statically allocated, do not delete!
  //
  // invariant: m_term.is_null() implies m_op == nullptr
  const simplifier::AbstractOp<T>* m_op;

  explicit Internal(
    const typename Smt<T>::Sort& term,
    const T v,
    const simplifier::AbstractOp<T>* const op)
  : m_term(term),
    m_v(v),
    m_op(op)
  {
    assert(!m_term.is_null() || m_op == nullptr);
  }

  explicit Internal(
    typename Smt<T>::Sort&& term,
    const T v,
    const simplifier::AbstractOp<T>* const op)
  : m_term(std::move(term)),
    m_v(v),
    m_op(op)
  {
    assert(!m_term.is_null() || m_op == nullptr);
  }

public:
  Internal(const Internal& other)
  : m_term(other.m_term),
    m_v(other.m_v),
    m_op(other.m_op)
  {
    assert(!m_term.is_null() || m_op == nullptr);
  }

  Internal(Internal&& other)
  : m_term(std::move(other.m_term)),
    m_v(std::move(other.m_v)),
    m_op(other.m_op)
  {
    assert(!m_term.is_null() || m_op == nullptr);
  }

  explicit Internal(typename Smt<T>::Sort&& term)
  : m_term(std::move(term)),
    m_v(),
    m_op(nullptr)
  {
    assert(!m_term.is_null());
  }

  Internal(T v)
  : m_term(nullptr),
    m_v(v),
    m_op(nullptr) {}

  Internal(const External<T>& other)
  : m_term(nullptr),
    m_v(),
    m_op(nullptr)
  {
    m_term = append_input_event(other);
    assert(!m_term.is_null());
  }

  bool is_literal() const
  {
    return m_term.is_null();
  }

  bool is_lazy() const
  {
    return m_op != nullptr;
  }

  // \pre: is_literal()
  T literal() const
  {
    assert(is_literal());
    assert(m_op == nullptr);

    return m_v;
  }

  // \pre: is_lazy()
  smt::Opcode opcode() const
  {
    assert(is_lazy());
    return m_op->opcode();
  }

  bool is_lazy_group() const
  {
    return is_lazy() && m_op->is_group();
  }

  const simplifier::AbstractOp<T>& op() const
  {
    assert(is_lazy());
    return *m_op;
  }

  Internal& operator=(Internal&& other)
  {
    m_term = std::move(other.m_term);
    m_v = std::move(other.m_v);
    m_op = other.m_op;
    assert(!m_term.is_null() || m_op == nullptr);
    return *this;
  }

  Internal& operator=(const Internal& other)
  {
    m_term = other.m_term;
    m_v = other.m_v;
    m_op = other.m_op;
    assert(!m_term.is_null() || m_op == nullptr);
    return *this;
  }

  /// \pre: not is_literal()
  template<smt::Opcode opcode>
  static Internal make_lazy(const Internal& arg, const T literal)
  {
    assert(!arg.is_literal());
    return Internal(term(arg), literal, simplifier::Op<opcode, T>::op_ptr());
  }

  /// \pre: not is_literal()
  template<smt::Opcode opcode>
  static Internal make_lazy(Internal&& arg, const T literal)
  {
    assert(!arg.is_literal());
    return Internal(term(std::move(arg)), literal, simplifier::Op<opcode, T>::op_ptr());
  }

  /// Propagate constants in commutative monoids

  /// \pre: arg.is_literal() or arg.is_lazy()
  template<smt::Opcode opcode>
  static Internal propagate(const Internal& arg, const T literal)
  {
    // check that arg.m_v is defined
    assert(arg.is_literal() || arg.is_lazy());

    const simplifier::AbstractOp<T>* const op =
      arg.is_literal() ? nullptr : simplifier::Op<opcode, T>::op_ptr();
    return Internal(arg.m_term, internal::Eval<opcode>::eval(arg.m_v, literal), op);
  }

  /// Propagate constants in commutative monoids

  /// \pre: arg.is_literal() or arg.is_lazy()
  template<smt::Opcode opcode>
  static Internal propagate(Internal&& arg, const T literal)
  {
    // check that arg.m_v is defined
    assert(arg.is_literal() || arg.is_lazy());

    const simplifier::AbstractOp<T>* const op =
      arg.is_literal() ? nullptr : simplifier::Op<opcode, T>::op_ptr();
    return Internal(std::move(arg.m_term),
      internal::Eval<opcode>::eval(std::move(arg.m_v), literal), op);
  }

  /// Folds constant expressions over commutative monoid operators
  static typename Smt<T>::Sort term(const Internal& arg)
  {
    if (arg.m_term.is_null())
      return smt::literal<typename Smt<T>::Sort>(arg.m_v);

    if (arg.m_op == nullptr)
      return arg.m_term;

    // lazy term
    return arg.m_op->fuse(arg.m_term, arg.m_v);
  }

  /// Folds constant expressions over commutative monoid operators
  static typename Smt<T>::Sort term(Internal&& arg)
  {
    if (arg.m_term.is_null())
      return smt::literal<typename Smt<T>::Sort>(arg.m_v);

    if (arg.m_op == nullptr)
      return std::move(arg.m_term);

    // lazy term
    return arg.m_op->fuse(std::move(arg.m_term), std::move(arg.m_v));
  }
};

namespace simplifier
{
  template<smt::Opcode opcode, typename T>
  struct IsCommutativeMonoid :
    std::integral_constant<bool,
      std::is_integral<T>::value and
      smt::ADD <= opcode and opcode <= smt::LOR>
  {};

  /// Constant propagation in commutative monoids
  struct Lazy
  {
    template<smt::Opcode opcode, typename T, typename Enable =
      typename std::enable_if<IsCommutativeMonoid<opcode, T>::value>::type>
    static Internal<T> apply(const Internal<T>& arg, const T literal)
    {
      if ((!arg.is_lazy() || arg.opcode() != opcode) && !arg.is_literal())
        return Internal<T>::template make_lazy<opcode>(arg, literal);
      else
        return Internal<T>::template propagate<opcode>(arg, literal);
    }

    template<smt::Opcode opcode, typename T, typename Enable =
      typename std::enable_if<IsCommutativeMonoid<opcode, T>::value>::type>
    static Internal<T> apply(Internal<T>&& arg, const T literal)
    {
      if ((!arg.is_lazy() || arg.opcode() != opcode) && !arg.is_literal())
        return Internal<T>::template make_lazy<opcode>(std::move(arg), literal);
      else
        return Internal<T>::template propagate<opcode>(std::move(arg), literal);
    }

    template<smt::Opcode opcode, typename T, typename Enable =
      typename std::enable_if<IsCommutativeMonoid<opcode, T>::value>::type>
    static Internal<T> apply(const T literal, const Internal<T>& arg)
    {
      // by commutativity, Eval::eval(x,y) == Eval::eval(y,x)
      return apply<opcode>(arg, literal);
    }

    template<smt::Opcode opcode, typename T, typename Enable =
      typename std::enable_if<IsCommutativeMonoid<opcode, T>::value>::type>
    static Internal<T> apply(const T literal, Internal<T>&& arg)
    {
      // by commutativity, Eval::eval(x,y) == Eval::eval(y,x)
      return apply<opcode>(std::move(arg), literal);
    }
  };

  // No constant propagation but literal simplifications
  struct Eager
  {
    template<smt::Opcode opcode, typename T, typename U, typename V>
    static Internal<T> apply(const Internal<U>& u, const V literal)
    {
      if (u.is_literal())
        return Internal<T>(internal::Eval<opcode>::eval(u.literal(), literal));
      else
        return Internal<T>(internal::Eval<opcode>::eval(
          Internal<U>::term(u), literal));
    }

    template<smt::Opcode opcode, typename T, typename U, typename V>
    static Internal<T> apply(Internal<U>&& u, const V literal)
    {
      if (u.is_literal())
        return Internal<T>(internal::Eval<opcode>::eval(u.literal(), literal));
      else
        return Internal<T>(internal::Eval<opcode>::eval(
          Internal<U>::term(std::move(u)), literal));
    }

    template<smt::Opcode opcode, typename T, typename U, typename V>
    static Internal<T> apply(const U literal, const Internal<V>& v)
    {
      if (v.is_literal())
        return Internal<T>(internal::Eval<opcode>::eval(literal, v.literal()));
      else
        return Internal<T>(internal::Eval<opcode>::eval(
          literal, Internal<V>::term(v)));
    }

    template<smt::Opcode opcode, typename T, typename U, typename V>
    static Internal<T> apply(const U literal, Internal<V>&& v)
    {
      if (v.is_literal())
        return Internal<T>(internal::Eval<opcode>::eval(literal, v.literal()));
      else
        return Internal<T>(internal::Eval<opcode>::eval(
          literal, Internal<V>::term(std::move(v))));
    }
  };

  template<smt::Opcode opcode, typename T, typename U, typename V>
  static Internal<T> apply(const Internal<U>& u, const Internal<V>& v)
  {
    return Internal<T>(internal::Eval<opcode>::eval(
      Internal<U>::term(u), Internal<V>::term(v)));
  }

  template<smt::Opcode opcode, typename T, typename U, typename V>
  static Internal<T> apply(const Internal<U>& u, Internal<V>&& v)
  {
    return Internal<T>(internal::Eval<opcode>::eval(
      Internal<U>::term(u), Internal<V>::term(std::move(v))));
  }

  template<smt::Opcode opcode, typename T, typename U, typename V>
  static Internal<T> apply(Internal<U>&& u, const Internal<V>& v)
  {
    return Internal<T>(internal::Eval<opcode>::eval(
      Internal<U>::term(std::move(u)), Internal<V>::term(v)));
  }

  template<smt::Opcode opcode, typename T, typename U, typename V>
  static Internal<T> apply(Internal<U>&& u, Internal<V>&& v)
  {
    return Internal<T>(internal::Eval<opcode>::eval(
      Internal<U>::term(std::move(u)), Internal<V>::term(std::move(v))));
  }

  template<smt::Opcode opcode, typename T, typename U, typename V>
  static Internal<T> apply(const Internal<U>& u, const V literal)
  {
    return std::conditional<
      /* if */ std::is_same<T, U>::value and
               std::is_same<U, V>::value and
               IsCommutativeMonoid<opcode, T>::value,
      /* then */ Lazy,
      /* else */ Eager>::type::template apply<opcode, T>(u, literal);
  }

  template<smt::Opcode opcode, typename T, typename U, typename V>
  static Internal<T> apply(Internal<U>&& u, const V literal)
  {
    return std::conditional<
      /* if */ std::is_same<T, U>::value and
               std::is_same<U, V>::value and
               IsCommutativeMonoid<opcode, T>::value,
      /* then */ Lazy,
      /* else */ Eager>::type::template apply<opcode, T>(std::move(u), literal);
  }

  template<smt::Opcode opcode, typename T, typename U, typename V>
  static Internal<T> apply(const U literal, const Internal<V>& v)
  {
    return std::conditional<
      /* if */ std::is_same<T, U>::value and
               std::is_same<U, V>::value and
               IsCommutativeMonoid<opcode, T>::value,
      /* then */ Lazy,
      /* else */ Eager>::type::template apply<opcode, T>(literal, v);
  }

  template<smt::Opcode opcode, typename T, typename U, typename V>
  static Internal<T> apply(const U literal, Internal<V>&& v)
  {
    return std::conditional<
      /* if */ std::is_same<T, U>::value and
               std::is_same<U, V>::value and
               IsCommutativeMonoid<opcode, T>::value,
      /* then */ Lazy,
      /* else */ Eager>::type::template apply<opcode, T>(literal, std::move(v));
  }
}

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
  : address(tracer().next_reserved_address()),
    term(),
    offset_term()
  {
    tracer().append_nondet_write_event(*this);
  }

  External(T v)
  : address(tracer().next_reserved_address()),
    term(smt::literal<typename Smt<T>::Sort>(v)),
    offset_term()
  {
    tracer().append_write_event(*this);
  }

  External(Internal<T>&& other)
  : address(tracer().next_reserved_address()),
    term(Internal<T>::term(std::move(other))),
    offset_term()
  {
    tracer().append_write_event(*this);
  }

  /*
   * Careful: optimizations with copy elision (e.g. RVO)
   * break the side effects of this copy constructor.
   */
  External(const External& other)
  : address(tracer().next_reserved_address()),
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
    term = Internal<T>::term(other);
    append_output_event();
    return *this;
  }

  External& operator=(Internal<T>&& other)
  {
    term = Internal<T>::term(std::move(other));
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
  tracer().next_reserved_address();
  return __External<Range>(address, Internal<size_t>::term(offset));
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
typename Smt<T>::Sort Tracer::append_channel_recv_event(const Address address)
{
  const EventIdentifier event_id(m_event_id_cnt);
  typename Smt<T>::Sort term(make_value_symbol<T>());
  // TODO: conversion to result type if necessary (e.g. smt::Bv<T>)
  append_event<CHANNEL_RECV_EVENT>(event_id, address, term);

  return term;
}

template<typename T>
typename Smt<T>::Sort Tracer::append_message_recv_event(const Address address)
{
  const EventIdentifier event_id(m_event_id_cnt);
  typename Smt<T>::Sort term(make_value_symbol<T>());
  // TODO: conversion to result type if necessary (e.g. smt::Bv<T>)
  append_event<MESSAGE_RECV_EVENT>(event_id, address, term);

  return term;
}

}

#define CRV_BUILTIN_UNARY_OP(op, opcode)                                        \
  template<typename T>                                                          \
  inline auto operator op(const crv::Internal<T>& arg)                          \
  -> crv::Internal<typename crv::internal::Return<smt::opcode, T>::Type>        \
  {                                                                             \
    typedef typename crv::internal::Return<smt::opcode, T>::Type ReturnType;    \
    return crv::Internal<ReturnType>(op crv::Internal<T>::term(arg));           \
  }                                                                             \
                                                                                \
  template<typename T>                                                          \
  inline auto operator op(crv::Internal<T>&& arg)                               \
  -> crv::Internal<typename crv::internal::Return<smt::opcode, T>::Type>        \
  {                                                                             \
    typedef typename crv::internal::Return<smt::opcode, T>::Type ReturnType;    \
    return crv::Internal<ReturnType>(op crv::Internal<T>::term(std::move(arg)));\
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
    const crv::Internal<U>& u,                                                  \
    const crv::Internal<V>& v)                                                  \
  -> crv::Internal<typename crv::internal::Return<smt::opcode, U, V>::Type>     \
  {                                                                             \
    typedef typename crv::internal::Return<smt::opcode, U, V>::Type ReturnType; \
    return crv::simplifier::apply<smt::opcode, ReturnType>(u, v);               \
  }                                                                             \
                                                                                \
  template<typename U, typename V>                                              \
  inline auto operator op(                                                      \
    const crv::Internal<U>& u,                                                  \
    crv::Internal<V>&& v)                                                       \
  -> crv::Internal<typename crv::internal::Return<smt::opcode, U, V>::Type>     \
  {                                                                             \
    typedef typename crv::internal::Return<smt::opcode, U, V>::Type ReturnType; \
    return crv::simplifier::apply<smt::opcode, ReturnType>(u, std::move(v));    \
  }                                                                             \
                                                                                \
  template<typename U, typename V>                                              \
  inline auto operator op(                                                      \
    crv::Internal<U>&& u,                                                       \
    const crv::Internal<V>& v)                                                  \
  -> crv::Internal<typename crv::internal::Return<smt::opcode, U, V>::Type>     \
  {                                                                             \
    typedef typename crv::internal::Return<smt::opcode, U, V>::Type ReturnType; \
    return crv::simplifier::apply<smt::opcode, ReturnType>(std::move(u), v);    \
  }                                                                             \
                                                                                \
  template<typename U, typename V>                                              \
  inline auto operator op(                                                      \
    crv::Internal<U>&& u,                                                       \
    crv::Internal<V>&& v)                                                       \
  -> crv::Internal<typename crv::internal::Return<smt::opcode, U, V>::Type>     \
  {                                                                             \
    typedef typename crv::internal::Return<smt::opcode, U, V>::Type ReturnType; \
    return crv::simplifier::apply<smt::opcode, ReturnType>(                     \
      std::move(u), std::move(v));                                              \
  }                                                                             \
                                                                                \
  template<typename U, typename V,                                              \
    class Enable = typename std::enable_if<std::is_arithmetic<V>::value>::type> \
  inline auto operator op(                                                      \
    const crv::Internal<U>& u,                                                  \
    V literal)                                                                  \
  -> crv::Internal<typename crv::internal::Return<smt::opcode, U, V>::Type>     \
  {                                                                             \
    typedef typename crv::internal::Return<smt::opcode, U, V>::Type ReturnType; \
    return crv::simplifier::apply<smt::opcode, ReturnType>(u, literal);         \
  }                                                                             \
                                                                                \
  template<typename U, typename V,                                              \
    class Enable = typename std::enable_if<std::is_arithmetic<V>::value>::type> \
  inline auto operator op(                                                      \
    crv::Internal<U>&& u,                                                       \
    V literal)                                                                  \
  -> crv::Internal<typename crv::internal::Return<smt::opcode, U, V>::Type>     \
  {                                                                             \
    typedef typename crv::internal::Return<smt::opcode, U, V>::Type ReturnType; \
    return crv::simplifier::apply<smt::opcode, ReturnType>(                     \
      std::move(u), literal);                                                   \
  }                                                                             \
                                                                                \
  template<typename U, typename V,                                              \
    class Enable = typename std::enable_if<std::is_arithmetic<U>::value>::type> \
  inline auto operator op(                                                      \
    U literal,                                                                  \
    const crv::Internal<V>& v)                                                  \
  -> crv::Internal<typename crv::internal::Return<smt::opcode, U, V>::Type>     \
  {                                                                             \
    typedef typename crv::internal::Return<smt::opcode, U, V>::Type ReturnType; \
    return crv::simplifier::apply<smt::opcode, ReturnType>(literal, v);         \
  }                                                                             \
                                                                                \
  template<typename U, typename V,                                              \
    class Enable = typename std::enable_if<std::is_arithmetic<U>::value>::type> \
  inline auto operator op(                                                      \
    U literal,                                                                  \
    crv::Internal<V>&& v)                                                       \
  -> crv::Internal<typename crv::internal::Return<smt::opcode, U, V>::Type>     \
  {                                                                             \
    typedef typename crv::internal::Return<smt::opcode, U, V>::Type ReturnType; \
    return crv::simplifier::apply<smt::opcode, ReturnType>(                     \
      literal, std::move(v));                                                   \
  }                                                                             \
                                                                                \
  template<typename U, typename V>                                              \
  inline auto operator op(                                                      \
  const crv::External<U>& u,                                                    \
  const crv::Internal<V>& v)                                                    \
  -> crv::Internal<typename crv::internal::Return<smt::opcode, U, V>::Type>     \
  {                                                                             \
    crv::Internal<U> u_internal(crv::append_input_event(u));                    \
    return std::move(u_internal) op v;                                          \
  }                                                                             \
                                                                                \
  template<typename U, typename V>                                              \
  inline auto operator op(                                                      \
  const crv::External<U>& u,                                                    \
  crv::Internal<V>&& v)                                                         \
  -> crv::Internal<typename crv::internal::Return<smt::opcode, U, V>::Type>     \
  {                                                                             \
    crv::Internal<U> u_internal(crv::append_input_event(u));                    \
    return std::move(u_internal) op std::move(v);                               \
  }                                                                             \
                                                                                \
  template<typename U, typename V>                                              \
  inline auto operator op(                                                      \
    const crv::Internal<U>& u,                                                  \
    const crv::External<V>& v)                                                  \
  -> crv::Internal<typename crv::internal::Return<smt::opcode, U, V>::Type>     \
  {                                                                             \
    crv::Internal<U> v_internal(crv::append_input_event(v));                    \
    return u op std::move(v_internal);                                          \
  }                                                                             \
                                                                                \
  template<typename U, typename V>                                              \
  inline auto operator op(                                                      \
    crv::Internal<U>&& u,                                                       \
    const crv::External<V>& v)                                                  \
  -> crv::Internal<typename crv::internal::Return<smt::opcode, U, V>::Type>     \
  {                                                                             \
    crv::Internal<V> v_internal(crv::append_input_event(v));                    \
    return std::move(u) op std::move(v_internal);                               \
  }                                                                             \
                                                                                \
  template<typename U, typename V>                                              \
  inline auto operator op(                                                      \
    const crv::External<U>& u,                                                  \
    const crv::External<V>& v)                                                  \
  -> crv::Internal<typename crv::internal::Return<smt::opcode, U, V>::Type>     \
  {                                                                             \
    crv::Internal<U> u_internal(crv::append_input_event(u));                    \
    crv::Internal<V> v_internal(crv::append_input_event(v));                    \
    return std::move(u_internal) op std::move(v_internal);                      \
  }                                                                             \
                                                                                \
  template<typename U, typename V,                                              \
    class Enable = typename std::enable_if<std::is_arithmetic<V>::value>::type> \
  inline auto operator op(                                                      \
    const crv::External<U>& u,                                                  \
    V literal)                                                                  \
  -> crv::Internal<typename crv::internal::Return<smt::opcode, U, V>::Type>     \
  {                                                                             \
    typedef typename crv::internal::Return<smt::opcode, U, V>::Type ReturnType; \
    return crv::Internal<ReturnType>(crv::append_input_event(u) op literal);    \
  }                                                                             \
                                                                                \
  template<typename U, typename V,                                              \
    class Enable = typename std::enable_if<std::is_arithmetic<U>::value>::type> \
  inline auto operator op(                                                      \
    U literal,                                                                  \
    const crv::External<V>& v)                                                  \
  -> crv::Internal<typename crv::internal::Return<smt::opcode, U, V>::Type>     \
  {                                                                             \
    typedef typename crv::internal::Return<smt::opcode, U, V>::Type ReturnType; \
    return crv::Internal<ReturnType>(literal op crv::append_input_event(v));    \
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

template<typename T,
  class Enable = typename std::enable_if<std::is_arithmetic<T>::value>::type>
inline Internal<T>& post_increment(Internal<T>& arg)
{
  arg = simplifier::apply<smt::ADD, T>(arg, 1);
  return arg;
}

template<typename T,
  class Enable = typename std::enable_if<std::is_arithmetic<T>::value>::type>
inline External<T>& post_increment(External<T>& arg)
{
  Internal<T> arg_internal(append_input_event(arg));
  arg = simplifier::apply<smt::ADD, T>(std::move(arg_internal), 1);
  return arg;
}

#ifdef __BV_TIME__
typedef smt::Bv<unsigned short> TimeSort;
#else
typedef smt::Real TimeSort;
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

#define _SUP_READ_FROM_ 1
class Encoder
{
public:
  static constexpr Address s_max_channel_address =
    Tracer::s_max_reserved_address;
  static constexpr Address s_wildcard_address =
    std::numeric_limits<Address>::max();

private:
  static const std::string s_time_prefix;
#ifdef _SUP_READ_FROM_
  static const std::string s_sup_time_prefix;
#endif

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

  smt::Z3Solver m_solver;
  std::unordered_map<EventIdentifier, Time> m_time_map;

#ifdef _SUP_READ_FROM_
  std::unordered_map<EventIdentifier, Time> m_sup_time_map;
#endif

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

#ifdef _SUP_READ_FROM_

  /// Uses a read event's identifier to build a numerical SMT variable
  const Time& sup_time(const Event& e)
  {
    assert(e.is_read());

    if (m_sup_time_map.find(e.event_id) == m_sup_time_map.cend())
    {
      Time time(smt::any<TimeSort>(prefix_event_id(s_sup_time_prefix, e)));
      m_solver.add(m_epoch.happens_before(time));
      m_sup_time_map.insert(std::make_pair(e.event_id, time));
    }

    return m_sup_time_map.at(e.event_id);
  }

  // Unpublished quadratic-size encoding
  void encode_read_from(const PerAddressIndex& per_address_index)
  {
    smt::UnsafeTerm and_rf(smt::literal<smt::Bool>(true));
    for (const PerAddressIndex::value_type& pair : per_address_index)
    {
      const EventKinds& a = pair.second;
      for (const EventIter r_iter : a.reads())
      {
        const Event& r = *r_iter;
        const Time& r_time = time(r);
        const Time& r_sup_time = sup_time(r);

        smt::UnsafeTerm or_rf(smt::literal<smt::Bool>(false));
        for (const EventIter w_iter : a.writes())
        {
          const Event& w = *w_iter;

          const smt::Bool wr_order(time(w).simultaneous_or_happens_before(r_time));
          const smt::Bool wr_sup(r_sup_time.simultaneous(time(w)));
          const smt::Bool rf_bool(flow_bool(s_rf_prefix, w, r));
          const smt::UnsafeTerm wr_equality(w.term == r.term);

          or_rf = rf_bool or or_rf;
          and_rf = and_rf and
            smt::implies(
            /* if */ rf_bool,
            /* then */ r.guard and w.guard and
                       wr_order and wr_equality and wr_sup) and
            smt::implies(
            /* if */ wr_order and w.guard,
            /* then */ time(w).simultaneous_or_happens_before(r_sup_time));
        }
        and_rf = and_rf and smt::implies(r.guard, or_rf);
      }
    }
    unsafe_add(and_rf);
  }

#else

  // CAV'13 cubic-size encoding
  void encode_read_from(const PerAddressIndex& per_address_index)
  {
    smt::UnsafeTerm and_rf(smt::literal<smt::Bool>(true));
    for (const PerAddressIndex::value_type& pair : per_address_index)
    {
      const EventKinds& a = pair.second;
      for (const EventIter r_iter : a.reads())
      {
        const Event& r = *r_iter;
        const Time& r_time = time(r);

        smt::UnsafeTerm or_rf(smt::literal<smt::Bool>(false));
        for (const EventIter w_iter : a.writes())
        {
          const Event& w = *w_iter;

          const smt::Bool wr_order(time(w).happens_before(r_time));
          const smt::Bool rf_bool(flow_bool(s_rf_prefix, w, r));
          const smt::UnsafeTerm wr_equality(w.term == r.term);

          or_rf = rf_bool or or_rf;
          and_rf = and_rf and
            smt::implies(
              /* if */ rf_bool,
              /* then */ r.guard and w.guard and
                         wr_order and wr_equality);
        }
        and_rf = and_rf and smt::implies(r.guard, or_rf);
      }
    }
    unsafe_add(and_rf);
  }

  // CAV'13 cubic-size encoding
  void encode_from_read(const PerAddressIndex& per_address_index)
  {
    smt::UnsafeTerm and_fr(smt::literal<smt::Bool>(true));
    for (const PerAddressIndex::value_type& pair : per_address_index)
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
            const Time& w_prime_time = time(w_prime);
            const smt::Bool rf_bool(flow_bool(s_rf_prefix, w, r));
            and_fr = and_fr and smt::implies(
              rf_bool and w_prime.guard and
              time(w).happens_before(w_prime_time),
              time(r).happens_before(w_prime_time));
          }
        }
      }
    }
    unsafe_add(and_fr);
  }

#endif

  void encode_write_serialization(const PerAddressIndex& per_address_index)
  {
    smt::UnsafeTerm and_ws(smt::literal<smt::Bool>(true));
    for (const PerAddressIndex::value_type& pair : per_address_index)
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
    const PerAddressIndex& per_address_index = tracer.per_address_index();
    encode_read_from(per_address_index);
#ifndef _SUP_READ_FROM_
    encode_from_read(per_address_index);
#endif
    encode_write_serialization(per_address_index);
  }

  void encode_pop_from(const PerAddressIndex& per_address_index)
  {
    smt::UnsafeTerm and_pf(smt::literal<smt::Bool>(true));
    for (const PerAddressIndex::value_type& pair : per_address_index)
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
                         pop.guard and push.guard and
                         push.term == pop.term);
        }
        and_pf = and_pf and or_pf;
      }
    }
    unsafe_add(and_pf);
  }

  // Make sure "pop-from" is like an injective function
  void encode_pop_from_injectivity(const PerAddressIndex& per_address_index)
  {
    smt::UnsafeTerm and_pop_excl(smt::literal<smt::Bool>(true));
    for (const PerAddressIndex::value_type& pair : per_address_index)
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

  void encode_stack_lifo_order(const PerAddressIndex& per_address_index)
  {
    smt::UnsafeTerm and_stack(smt::literal<smt::Bool>(true));
    for (const PerAddressIndex::value_type& pair : per_address_index)
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
    const PerAddressIndex& per_address_index = tracer.per_address_index();
    encode_pop_from(per_address_index);
    encode_pop_from_injectivity(per_address_index);
    encode_stack_lifo_order(per_address_index);
  }

  // Similar to "read-from" axiom except that offsets must be equal and
  // loads from initial array return zero
  void encode_load_from(const PerAddressIndex& per_address_index)
  {
    smt::UnsafeTerm and_ldf(smt::literal<smt::Bool>(true));
    for (const PerAddressIndex::value_type& pair : per_address_index)
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

          // part of the initial zero array axiom:
          // for every store s, if ld and s access the same array
          // offset, then t!ld < t!s (i.e. ld must happen before s).
          and_lds = and_lds and
            smt::implies(/* if */ ld.offset_term == s.offset_term,
                         /* then */ ld_time.happens_before(time(s)));

          or_ldf = ldf_bool or or_ldf;

          and_ldf = and_ldf and
            smt::implies(
              /* if */ ldf_bool,
              /* then */ s.guard and ld.guard and sld_order and
                         sld_equality and s.offset_term == ld.offset_term);
        }

        /* initial array elements are zero */
        smt::UnsafeTerm ld_zero(smt::literal(ld.term.sort(), 0));
        and_ldf = and_ldf and smt::implies(
          /* if */ not or_ldf,
          /* then */ ld.guard and and_lds and
                     ld.term == std::move(ld_zero));
      }
    }
    unsafe_add(and_ldf);
  }

  // Similar to "from-read" axiom except that offsets must be equal
  void encode_from_load(const PerAddressIndex& per_address_index)
  {
    smt::UnsafeTerm and_fld(smt::literal<smt::Bool>(true));
    for (const PerAddressIndex::value_type& pair : per_address_index)
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
            and_fld = and_fld and
              smt::implies(
                /* if */ ldf_bool and time(s).happens_before(time(s_prime)) and
                         s.offset_term == s_prime.offset_term and s_prime.guard,
                /* then */ time(ld).happens_before(time(s_prime)));
          }
        }
      }
    }
    unsafe_add(and_fld);
  }

  // Serialize every store regardless of array offset
  void encode_store_serialization(const PerAddressIndex& per_address_index)
  {
    smt::UnsafeTerm and_ss(smt::literal<smt::Bool>(true));
    for (const PerAddressIndex::value_type& pair : per_address_index)
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
    const PerAddressIndex& per_address_index = tracer.per_address_index();
    encode_load_from(per_address_index);
    encode_from_load(per_address_index);
    encode_store_serialization(per_address_index);
  }

  static bool is_any_event(const EventIter e_iter)
  {
    return true;
  }

  static bool is_communication_event(const EventIter e_iter)
  {
    // note: immediate_dominator_map() already allows THREAD_END_EVENT
    const EventKind e_kind(e_iter->kind);
    return CHANNEL_RECV_EVENT <= e_kind && e_kind <= MESSAGE_SEND_EVENT;
  }

public:
  template<typename UnaryPredicate>
  static EventMap immediate_dominator_map(const Tracer&, UnaryPredicate);

  static EventMap immediate_dominator_map(const Tracer& tracer)
  {
    return Encoder::immediate_dominator_map(tracer, is_any_event);
  }

  static EventMap communication_immediate_dominator_map(const Tracer& tracer)
  {
    return Encoder::immediate_dominator_map(tracer, is_communication_event);
  }

  /// matchable recv/send events in different threads
  typedef std::unordered_map<std::pair<EventIter, EventIter>,
    smt::Bool> MatchBoolMap;

  static ThreadIdentifier dest_thread_id(const EventIter e_iter)
  {
    assert(e_iter->address != s_wildcard_address);
    assert(e_iter->is_message_recv() ^ e_iter->is_message_send());

    const ThreadIdentifier thread_id = e_iter->address - s_max_channel_address;
    assert(thread_id != e_iter->thread_id);
    return thread_id;
  }

  // check that a given receive event and is allowed to match a send event
  static void match_check(const EventIter r_iter, const EventIter s_iter)
  {
    const Event& r = *r_iter;
    const Event& s = *s_iter;
    assert(r.is_channel_recv() ^ r.is_message_recv());
    assert(s.is_channel_send() ^ s.is_message_send());
    assert(s.is_channel_send() == r.is_channel_recv());
    assert(s.is_message_send() == r.is_message_recv());
    assert(r.thread_id != s.thread_id);
    assert(r.address != s_wildcard_address || r.is_message_recv());
    assert(!r.is_message_recv() || s_max_channel_address < r.address);
    assert(!s.is_message_send() || s_max_channel_address < r.address);
    assert(!s.is_message_send() || s.address != s_wildcard_address);
    assert(!s.is_message_send() || r.address == s_wildcard_address ||
      (dest_thread_id(s_iter) == r.thread_id &&
       dest_thread_id(r_iter) == s.thread_id));
  }

  static std::string match_symbol(const EventIter r_iter, const EventIter s_iter)
  {
    static const std::string match_prefix("match!{");
    match_check(r_iter, s_iter);

    return match_prefix +
      std::to_string(r_iter->event_id) + "," +
      std::to_string(s_iter->event_id) + "}";
  }

  // Build potential match set (i.e. matchables) and match variable cache
  static void build_matchables(
    const Tracer& tracer,
    PerEventMap& per_event_map,
    MatchBoolMap& match_bool_map)
  {
    const PerAddressIndex& per_address_index = tracer.per_address_index();
    for (const PerAddressIndex::value_type& pair : per_address_index)
    {
      const EventKinds& a = pair.second;

      // every channel event must have a (possibly empty) matchbles set
      {
        if (a.channel_recvs().empty())
          for (const EventIter s_iter : a.channel_sends())
            per_event_map[s_iter];
        else if (a.channel_sends().empty())
          for (const EventIter r_iter : a.channel_recvs())
            per_event_map[r_iter];
      }
          
      for (const EventIter r_iter : a.channel_recvs())
      {
        for (const EventIter s_iter : a.channel_sends())
        {
          if (r_iter->thread_id == s_iter->thread_id)
            continue;

          match_bool_map.emplace(std::make_pair(r_iter, s_iter),
            smt::any<smt::Bool>(match_symbol(r_iter, s_iter)));

          per_event_map[r_iter].push_back(s_iter);
          per_event_map[s_iter].push_back(r_iter);
        }
      }
    }

    const Events& events = tracer.events();
    const PerThreadIndex& per_thread_index = tracer.per_thread_index();
    for (EventIter e_iter = events.cbegin();
         e_iter != events.cend();
         e_iter++)
    {
      if (e_iter->is_message_recv())
      {
        // every message receive event has a (possibly empty) matchables set
        per_event_map[e_iter];

        if (e_iter->address == s_wildcard_address)
        {
          for (EventIter s_iter = events.cbegin();
               s_iter != events.cend();
               s_iter++)
          {
            if (s_iter->is_message_send() &&
                e_iter->thread_id != s_iter->thread_id)
            {
              match_bool_map.emplace(std::make_pair(e_iter, s_iter),
                smt::any<smt::Bool>(match_symbol(e_iter, s_iter)));

              per_event_map[e_iter].push_back(s_iter);
              per_event_map[s_iter].push_back(e_iter);
            }
          }
        }
        else
        {
          const EventIters& message_sends = per_thread_index.at(
            dest_thread_id(e_iter)).message_sends();
          for (const EventIter s_iter : message_sends)
          {
            if (dest_thread_id(s_iter) != e_iter->thread_id)
              continue;

            match_bool_map.emplace(std::make_pair(e_iter, s_iter),
              smt::any<smt::Bool>(match_symbol(e_iter, s_iter)));

            per_event_map[e_iter].push_back(s_iter);
            per_event_map[s_iter].push_back(e_iter);
          }
        }
      }
      else if (e_iter->is_message_send())
      {
        // every message send event has a (possibly empty) matchables set
        per_event_map[e_iter];

        const EventIters& message_recvs = per_thread_index.at(
          dest_thread_id(e_iter)).message_recvs();

        for (const EventIter r_iter : message_recvs)
        {
            if (r_iter->address != s_wildcard_address &&
                dest_thread_id(r_iter) != e_iter->thread_id)
              continue;

            match_bool_map.emplace(std::make_pair(r_iter, e_iter),
              smt::any<smt::Bool>(match_symbol(r_iter, e_iter)));

            per_event_map[e_iter].push_back(r_iter);
            per_event_map[r_iter].push_back(e_iter);
        }
      }
    }
  }

private:
  // Encode potential match set of channel or message passing event
  static smt::Bool communication_match_disjunction(
    const PerEventMap& per_event_map,
    const MatchBoolMap& match_bool_map,
    const EventIter e_iter)
  {
    assert(is_communication_event(e_iter));

    smt::Bool or_match(smt::literal<smt::Bool>(false));
    const EventIters& matchables = per_event_map.at(e_iter);
    if (e_iter->is_channel_recv() || e_iter->is_message_recv())
      for (const EventIter s_iter : matchables)
      {
        assert(s_iter->is_channel_send() || s_iter->is_message_send());
        or_match = or_match or match_bool_map.at(
          std::make_pair(e_iter, s_iter));
      }
    else
      for (const EventIter r_iter : matchables)
      {
        assert(r_iter->is_channel_recv() || r_iter->is_message_recv());
        or_match = or_match or match_bool_map.at(
          std::make_pair(r_iter, e_iter));
      }

    return or_match;
  }

  static smt::Bool communication_match_conjunction(
    const PerEventMap& per_event_map,
    const MatchBoolMap& match_bool_map,
    const EventIters e_iters)
  {
    smt::Bool and_match(smt::literal<smt::Bool>(true));
    for (const EventIter e_iter : e_iters)
      and_match = and_match and communication_match_disjunction(
        per_event_map, match_bool_map, e_iter);

    return and_match;
  }

  static smt::Bool communication_excl(
    const PerEventMap& per_event_map,
    const MatchBoolMap& match_bool_map,
    const EventIter r_iter,
    const EventIter s_iter)
  {
    match_check(r_iter, s_iter);

    smt::Bool or_match(smt::literal<smt::Bool>(false));
    for (const EventIter e_iter : per_event_map.at(r_iter))
    {
      if (e_iter == s_iter)
        continue;

      assert(e_iter->is_channel_send() || e_iter->is_message_send());
      or_match = or_match or match_bool_map.at(
        std::make_pair(r_iter, e_iter));
    }
    for (const EventIter e_iter : per_event_map.at(s_iter))
    {
      if (e_iter == r_iter)
        continue;

      assert(e_iter->is_channel_recv() || e_iter->is_message_recv());
      or_match = or_match or match_bool_map.at(
        std::make_pair(e_iter, s_iter));
    }
    return not or_match;
  }

  void encode_communication_concurrency(const Tracer& tracer, bool check_deadlocks)
  {
    PerEventMap per_event_map;
    MatchBoolMap match_bool_map;
    build_matchables(tracer, per_event_map, match_bool_map);

    auto cidom_map(Encoder::communication_immediate_dominator_map(tracer));

    Bools inits;
    smt::UnsafeTerm ext_match(smt::literal<smt::Bool>(true));
    for (const MatchBoolMap::value_type& triple : match_bool_map)
    {
      const MatchBoolMap::key_type& key = triple.first;
      const EventIter r_iter = key.first;
      const EventIter s_iter = key.second;
      match_check(r_iter, s_iter);

      const Event& r = *r_iter;
      const Event& s = *s_iter;
      const smt::Bool& match_bool = triple.second;

      smt::UnsafeTerm rs_value(smt::implies(
        /* if */ match_bool,
        /* then */ r.term == s.term));

      EventIters cidoms;
      if (cidom_map.find(r_iter) != cidom_map.cend())
        cidoms.push_back(cidom_map.at(r_iter));

      if (cidom_map.find(s_iter) != cidom_map.cend())
        cidoms.push_back(cidom_map.at(s_iter));

      smt::UnsafeTerm rs_ext(match_bool ==
        (communication_match_conjunction(per_event_map,
           match_bool_map, cidoms) and
         communication_excl(per_event_map,
           match_bool_map, r_iter, s_iter) and
         r.guard and s.guard));

      ext_match = ext_match and rs_ext and rs_value and
        (match_bool == time(r).simultaneous(time(s)));

      if (cidom_map.find(r_iter) == cidom_map.cend() &&
          cidom_map.find(r_iter) == cidom_map.cend())
        inits.push_back(match_bool);
    }

    if (check_deadlocks)
    {
      const std::string finalizer_prefix("finalizer!");
      smt::Bool finalizers(smt::literal<smt::Bool>(true));
      for (const PerThreadMap::value_type& pair : tracer.per_thread_map())
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
          (finalizer_bool == communication_match_disjunction(
             per_event_map, match_bool_map, cidom_map.at(e_iter)));
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
  : m_solver(smt::QF_LRA_LOGIC),
#endif
    m_time_map(),
#ifdef _SUP_READ_FROM_
    m_sup_time_map(),
#endif
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
    unsafe_add(tracer.guard() and Internal<bool>::term(std::move(condition)));
    encode(tracer, false);
    const smt::CheckResult result = m_solver.check();
    m_solver.pop();
    return result;
  }
};

template<typename UnaryPredicate>
EventMap Encoder::immediate_dominator_map(const Tracer& tracer,
  UnaryPredicate predicate)
{
  EventMap map;
  const PerThreadMap& per_thread_map = tracer.per_thread_map();

  EventIters::const_reverse_iterator criter;
  std::vector<EventIter> worklist;
  EventIter e_iter, e_prime_iter;
  ScopeLevel scope_level;

  for (const PerThreadMap::value_type& pair : per_thread_map)
  {
    const EventIters& events = pair.second;

    if (events.size() < 2)
      continue;

    assert(worklist.empty());
    worklist.reserve(events.size());

    criter = events.crbegin();
    e_iter = *criter++;

    // unless we're looking at the main thread, THREAD_END_EVENT
    // is always in the returned map regardless of predicate
    assert(pair.first == 1 || e_iter->is_thread_end());

    for (; criter != events.crend(); criter++)
    {
      e_prime_iter = *criter;
      if (!predicate(e_prime_iter))
        continue;

      scope_level = e_prime_iter->scope_level;

      if (scope_level > e_iter->scope_level)
      {
        // save event for later
        worklist.push_back(e_iter);
      }
      else if (scope_level == e_iter->scope_level)
      {
        // TODO: support Tracer::decide_flip() inside scopes
        if (e_iter->block_id == e_prime_iter->block_id)
        {
          // both events are in the same branch, i.e. e_prime_iter
          // is the direct predecessor of e_iter in the unrolled CFG
          map.emplace(e_iter, e_prime_iter);
        }
        else
        {
          // crossing over to another branch or even a different
          // "if-then-else" block, e.g. if (*) { a } if (*) { b }
          worklist.push_back(e_iter);
        }
      }
      else
      {
        // note: scope level may have decreased by more than one,
        // e.g. if (*) { if (*) { a } }
        while (!worklist.empty() &&
          scope_level <= worklist.back()->scope_level)
        {
          map.emplace(worklist.back(), e_prime_iter);
          worklist.pop_back();
        }

        // process first event in "then" branch
        map.emplace(e_iter, e_prime_iter);
      }

      e_iter = e_prime_iter;
    }
  }
  return map;
}

/// Symbolic thread using partial order encoding
class Thread
{
private:
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
  : m_parent_thread_id(0),
    m_thread_id(0)
  {
    m_parent_thread_id = tracer().append_thread_begin_event();
    f(args...);
    m_thread_id = tracer().append_thread_end_event();
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

/// Go-style concurrency

/// A Channel<T> object is like a channel in the Go language without
/// the concept of higher-order channels (i.e. channels of channels).
template<typename T>
class Channel
{
private:
  const Address m_address;

public:
  Channel()
  : m_address(tracer().next_reserved_address())
  {
    assert(m_address < Encoder::s_max_channel_address);
  }

  void send(T v)
  {
    send(Internal<T>(v));
  }

  void send(const Internal<T>& data)
  {
    tracer().append_channel_send_event(m_address, Internal<T>::term(data));
  }

  void send(const External<T>& data)
  {
    smt::UnsafeTerm term = append_input_event(data);
    tracer().append_channel_send_event(m_address, std::move(term));
  }

  Internal<T> recv()
  {
    return Internal<T>(tracer().append_channel_recv_event<T>(m_address));
  }
};

/// MPI-style concurrency

/// The static member function of Message are intended to
/// model synchronous MPI calls.
class Message
{
private:
  static Address to_address(const ThreadIdentifier thread_id)
  {
    // disallow main thread
    assert(1 < thread_id);

    // detect overflows
    assert(thread_id < Encoder::s_max_channel_address);

    return Encoder::s_max_channel_address + thread_id;
  }

  Message() {}

public:
  template<typename T>
  static void send(const ThreadIdentifier thread_id, T v)
  {
    send(thread_id, Internal<T>(v));
  }

  template<typename T>
  static void send(const ThreadIdentifier thread_id,
    const Internal<T>& data)
  {
    tracer().append_message_send_event(to_address(thread_id), Internal<T>::term(data));
  }

  template<typename T>
  static void send(const ThreadIdentifier thread_id,
    const External<T>& data)
  {
    smt::UnsafeTerm term = append_input_event(data);
    tracer().append_message_send_event(
      to_address(thread_id), std::move(term));
  }

  template<typename T>
  static Internal<T> recv(const ThreadIdentifier thread_id)
  {
    return Internal<T>(tracer().append_message_recv_event<T>(
      to_address(thread_id)));
  }

  // MPI's synchronous 'wildcard receive'
  template<typename T>
  static Internal<T> recv_any()
  {
    return Internal<T>(tracer().append_message_recv_event<T>(
      Encoder::s_wildcard_address));
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
    m_stack.term = Internal<T>::term(internal);
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
