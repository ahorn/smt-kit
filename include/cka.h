// Copyright 2014, Alex Horn. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

#ifndef _CKA_H_
#define _CKA_H_

#include <smt>
#include <list>
#include <vector>
#include <limits>
#include <utility>
#include <cassert>

#define _CKA_OPTIMIZE_

#ifdef _CKA_DEBUG_
#include <iostream>
#endif

namespace cka
{

typedef unsigned Label;
typedef unsigned Event;
typedef unsigned Length;

/// Finite partial string
class PartialString
{
public:
  typedef std::list<const Event> Events;
  typedef std::pair<const Event, const Event> EventPair;
  typedef std::list<const EventPair> EventPairs;
  typedef std::vector<Label> LabelFunction;

private:
  // Is an event either a maximal or minimal element in a partial order?
  static constexpr bool IS_EXTREMAL_EVENT = false;

  typedef std::vector<bool> EventSet;

  // function from Event to Label
  LabelFunction m_label_function;

  // transitive reduction of an irreflexive, transitive and asymmetric relation
  EventPairs m_strict_partial_order;

  // number of events in partial string
  Length m_length;

  //  pairs of events that happen concurrently, encode `(e,e')` and `(e',e)`
  EventPairs m_incomparables;

  // initially, all events are deemed to be extremals
  EventSet m_minimals, m_maximals;

  /// Empty partial string

  /// \post: `length()` is zero
  PartialString()
  : m_label_function{},
    m_strict_partial_order{},
    m_length{0},
    m_incomparables{},
    m_minimals{},
    m_maximals{} {}

  friend PartialString operator|(const PartialString&, const PartialString&);
  friend PartialString operator,(const PartialString&, const PartialString&);

  /// Coproduct (i.e. disjoint union) of `x` and `y`

  /// \post: `length() == x.length() + y.length()`
  ///
  /// \remark: call `recompute_extremals()` afterwards
  PartialString(const PartialString& x, const PartialString& y)
  : m_label_function{x.m_label_function},
    m_strict_partial_order{x.m_strict_partial_order},
    m_length{x.length() + y.length()},
    m_incomparables{x.m_incomparables},
    m_minimals(m_length),
    m_maximals(m_length)
  {
    // point-wise union with labelling function of `y`
    m_label_function.reserve(m_length);
    for (Label label : y.m_label_function)
      m_label_function.push_back(label);

    // inequality check relies on integral type promotion
    assert(m_label_function.size() <= std::numeric_limits<Length>::max());
    assert(m_length == m_label_function.size());

    // compute new identifiers for events in `y`
    const Length offset{x.length()};

    // union with strict partial order constraints of `y`
    for (const EventPair& pair : y.m_strict_partial_order)
      m_strict_partial_order.emplace_back(offset + pair.first, offset + pair.second);

    // incomparables in `y` stay incomparable in the coproduct of `x` and `y`
    for (const EventPair& pair : y.m_incomparables)
      m_incomparables.emplace_back(offset + pair.first, offset + pair.second);
  }

  /// Update `m_maximals` and `m_minmals` according to `m_strict_partial_order`

  /// This procedure is idempotent, calling it twice without any intermittent
  /// updates to `m_strict_partial_order` has no side effects.
  ///
  /// \post: for every `e < length()`, `is_maximal(e)` iff `e` is maximal
  /// \post: for every `e < length()`, `is_minimal(e)` iff `e` is minimal
  void recompute_extremals()
  {
    for (const PartialString::EventPair& pair : m_strict_partial_order)
      m_maximals[pair.first] = m_minimals[pair.second] = not IS_EXTREMAL_EVENT;
  }

public:
  /// Unique empty partial string
  static PartialString& empty()
  {
    static PartialString s_empty;
    return s_empty;
  }

  /// A new partial string with a single event labelled by `label`

  /// \post: `length() == 1`
  PartialString(const Label label)
  : m_label_function{label},
    m_strict_partial_order{},
    m_length{1},
    m_incomparables{},
    m_minimals(1),
    m_maximals(1)
  {
    recompute_extremals();
  }

  Length length() const noexcept
  {
    return m_length;
  }

  const LabelFunction& label_function() const noexcept
  {
    return m_label_function;
  }

  /// Transitive reduction of a strict partial order
  const EventPairs& strict_partial_order() const noexcept
  {
    return m_strict_partial_order;
  }

  /// Events that are neither less than nor greater than
  /// some other event in `strict_partial_order()`
  const EventPairs& incomparables() const noexcept
  {
    return m_incomparables;
  }

  /// Get events that do not have an event below them

  /// \warning recomputes the set of minimals on each call
  Events minimals() const
  {
    Events events;
    for (Event e = 0; e < m_length; ++e)
      if (is_minimal(e))
        events.push_back(e);

    return events;
  }

  /// Get events that do not have an event above them

  /// \warning recomputes the set of maximals on each call
  Events maximals() const
  {
    Events events;
    for (Event e = 0; e < m_length; ++e)
      if (is_maximal(e))
        events.push_back(e);

    return events;
  }

  /// Is `e` a minimal element in `strict_partial_order()`?

  /// \pre: `e` is an event in the partial string
  bool is_minimal(Event e) const
  {
    assert(e < m_length);
    return m_minimals[e] == IS_EXTREMAL_EVENT;
  }

  /// Is `e` a maximal element in `strict_partial_order()`?

  /// \pre: `e` is an event in the partial string
  bool is_maximal(Event e) const
  {
    assert(e < m_length);
    return m_maximals[e] == IS_EXTREMAL_EVENT;
  }
};

/// Concurrent composition of two partial strings

/// All events between `x` and `y` happen concurrently.
PartialString operator|(const PartialString&, const PartialString&);

/// Strongly sequential composition of two partial strings

/// All events in `x` happen before those in `y`.
PartialString operator,(const PartialString&, const PartialString&);

/// Downward-closed set of finite partial strings
class Program
{
private:
  typedef std::vector<PartialString> PartialStrings;
  PartialStrings m_partial_strings;

  friend Program operator|(const Program&, const Program&);
  friend Program operator,(const Program&, const Program&);
  friend Program operator+(const Program&, const Program&);

  Program(PartialStrings&& partial_strings)
  : m_partial_strings{std::move(partial_strings)} {}

public:
  /// A single partial string whose only event is labelled by `label`
  Program(const Label label)
  : m_partial_strings{}
  {
    m_partial_strings.emplace_back(label);
  }

  /// Finite set of finite partial strings
  const PartialStrings& partial_strings() const noexcept
  {
    return m_partial_strings;
  }

  /// Cardinality of `partial_strings()`
  PartialStrings::size_type size() const noexcept
  {
    return m_partial_strings.size();
  }
};

/// Concurrent composition of two programs
Program operator|(const Program&, const Program&);

/// Strongly sequential composition of two programs
Program operator,(const Program&, const Program&);

/// Nondeterministic choice between two programs
Program operator+(const Program&, const Program&);

/// Utility class for `Program`s
struct Programs
{
  Programs() = delete;

  /// Length of shortest partial strings in `X`

  /// \pre: 0 < X.size()
  static Length min_length(const Program& X)
  {
    assert(0U < X.size());

    Length len{std::numeric_limits<Length>::max()};
    for (const PartialString& x : X.partial_strings())
      if (x.length() < len)
        len = x.length();

    return len;
  }

  /// Length of longest partial strings in `X`

  /// \pre: 0 < X.size()
  static Length max_length(const Program& X)
  {
    assert(0U < X.size());

    Length len{0};
    for (const PartialString& x : X.partial_strings())
      if (len < x.length())
        len = x.length();

    return len;
  }
};

/// Human-readable representation of a partial string operator
typedef char Opchar;

/// Least fixed point of a `Program`

/// \pre: `opchar` is either ',' or '|'
template<Opchar opchar>
class LfpProgram
{
private:
  static_assert(opchar == ',' or opchar == '|', "opchar must be \',\' or \'|\'");

  template<Opchar c> friend LfpProgram<c> lfp(const Program&);

  Program m_P;

  LfpProgram(const Program& P)
  : m_P(P) {}

public:
  const Program& P() const noexcept
  {
    return m_P;
  }
};

/// Utility class for program operators
template<Opchar opchar>
struct Eval
{
  static Program bowtie(const Program&, const Program&);
};

/// Template specialization for concurrent program composition
template<>
struct Eval<'|'>
{
  static Program bowtie(const Program& X, const Program& Y)
  {
    return {(X | Y)};
  }
};

/// Template specialization for strongly sequential program composition
template<>
struct Eval<','>
{
  static Program bowtie(const Program& X, const Program& Y)
  {
    return {(X , Y)};
  }
};

template<Opchar opchar>
LfpProgram<opchar> lfp(const Program& P)
{
  return {P};
}

/// Iterate over each `event` and its `label` in a partial string `p`
#define for_each_label(p, event, label)                                 \
  Event event{0};                                                       \
  Label label;                                                          \
  PartialString::LabelFunction::const_iterator                          \
    citer{(p).label_function().cbegin()},                               \
    cend{(p).label_function().cend()};                                  \
  for (label = *citer; citer != cend; ++citer, ++event, label = *citer) \

/// Symbolic decision procedure for certain CKA language containment problems
class Refinement
{
private:
  typedef smt::Int EventSort;
  typedef smt::Int LabelSort;

  typedef smt::Func<EventSort, EventSort> EventFuncSort;
  typedef smt::Func<EventSort, LabelSort> LabelFuncSort;

  // Binary predicate to symbolically encode strict partial order
  typedef smt::Func<EventSort, EventSort, smt::Bool> OrderPredSort;

  typedef smt::Decl<EventFuncSort> EventFunc;
  typedef smt::Decl<LabelFuncSort> LabelFunc;
  typedef smt::Decl<OrderPredSort> OrderPred;

  // Other SMT solvers include smt::CVC4Solver and smt::MsatSolver
  smt::Z3Solver m_solver;

  // The goal is to check that `m_event_func` is a monotonic bijective morphism
  EventFunc m_event_func;

  // The range of `m_event_func` must respect the labelling and ordering of `x`
  LabelFunc m_label_func_x;
  OrderPred m_order_pred_x;

  // Statistics
  unsigned m_number_of_solver_calls;
  unsigned m_number_of_checks;

  smt::Bool order(const OrderPred& order_pred, Event e_a, Event e_b)
  {
    EventSort e_a_literal{smt::literal<EventSort>(e_a)};
    EventSort e_b_literal{smt::literal<EventSort>(e_b)};
    return smt::apply(order_pred, std::move(e_a_literal), std::move(e_b_literal));
  }

  void encode_label(const LabelFunc& label_func_p, const PartialString& p)
  {
    if (p.length() == 0)
      return;

    smt::Bools equalities(p.length());
    for_each_label(p, event, label)
      equalities.push_back(smt::apply(label_func_p, event) == label);

    m_solver.add(smt::conjunction(std::move(equalities)));
  }

  void encode_strict_partial_order(const OrderPred& order_pred_p, const PartialString& p)
  {
    // in the worst case, encoding is cubic in the number of events in `p`
    const Length len{p.length()};
    smt::Bools partial_order(len * len * len);

    // transitive reduction of `p`
    for (const PartialString::EventPair& pair : p.strict_partial_order())
      partial_order.push_back(order(order_pred_p, pair.first, pair.second));

    // irreflexivity
    for (Event e{0}; e < len; ++e)
      partial_order.push_back(not order(order_pred_p, e, e));

    // asymmetry
    smt::Bool order_a_b;
    {
      smt::Bool order_b_a;
      for (Event e_a{0}; e_a < len; ++e_a)
        for (Event e_b{e_a + 1U}; e_b < len; ++e_b)
        {
          order_a_b = order(order_pred_p, e_a, e_b);
          order_b_a = order(order_pred_p, e_b, e_a);

          partial_order.push_back(smt::implies(order_a_b, not order_b_a));
        }
    }

    // transitivity
    smt::Bool order_b_c, order_a_c;
    for (Event e_a{0}; e_a < len; ++e_a)
      for (Event e_b{e_a + 1U}; e_b < len; ++e_b)
        for (Event e_c{e_b + 1U}; e_c < len; ++e_c)
        {
          order_a_b = order(order_pred_p, e_a, e_b);
          order_b_c = order(order_pred_p, e_b, e_c);
          order_a_c = order(order_pred_p, e_a, e_c);

          partial_order.push_back(smt::implies(order_a_b and order_b_c, order_a_c));
        }

    // incomparable events
    for (const PartialString::EventPair& pair : p.incomparables())
    {
      partial_order.push_back(not order(order_pred_p, pair.first, pair.second));
      partial_order.push_back(not order(order_pred_p, pair.second, pair.first));
    }

    m_solver.add(smt::conjunction(std::move(partial_order)));
  }

  void encode_monotonic_bijective_morphism(const PartialString& x, const PartialString& y)
  {
    // strict monotonicity from y to x
    if (not y.strict_partial_order().empty())
    {
      EventSort e_first, e_second;
      smt::Bools partial_order;

      // It suffices to only check strict monotonicity for the transitive reduction of
      // the strict partial ordering of `y` because `m_order_pred_x` is transitive.
      for (const PartialString::EventPair& y_pair : y.strict_partial_order())
      {
        e_first = smt::apply(m_event_func, y_pair.first);
        e_second = smt::apply(m_event_func, y_pair.second);

        partial_order.push_back(smt::apply(m_order_pred_x, e_first, e_second));
      }

      assert(not partial_order.empty());
      m_solver.add(smt::conjunction(partial_order));
    }

    if (const Length len{y.length()})
    {
      // bijective
      {
        const Event last_event{len - 1U};
        assert(0U < len);
        assert(x.length() == len);

        EventSort e_x;
        smt::Terms<EventSort> codomain_injective(last_event);
        smt::Bools codomain_surjective(last_event * 2U);
        for (Event e_y = 0; e_y < len; ++e_y)
        {
          e_x = smt::apply(m_event_func, e_y);
          codomain_injective.push_back(e_x);

          codomain_surjective.push_back(0U <= e_x);
          codomain_surjective.push_back(e_x <= last_event);
        }

        m_solver.add(smt::conjunction(std::move(codomain_surjective)));
        m_solver.add(smt::distinct(std::move(codomain_injective)));
      }

      // label-preserving
      {
        LabelSort label_x;
        for_each_label(y, event, label_y)
        {
          label_x = smt::apply(m_label_func_x, smt::apply(m_event_func, event));
          m_solver.add(label_x == label_y);
        }
      }
    }
  }

public:
  Refinement()
  : m_solver(smt::QF_UFLIA_LOGIC),
    m_event_func{"event"},
    m_label_func_x{"label_x"},
    m_order_pred_x{"order_x"},
    m_number_of_solver_calls{0},
    m_number_of_checks{0} {}

  unsigned number_of_solver_calls() const
  {
    return m_number_of_solver_calls;
  }

  void reset_number_of_solver_calls()
  {
    m_number_of_solver_calls = 0;
  }

  unsigned number_of_checks() const
  {
    return m_number_of_checks;
  }

  void reset_number_of_checks()
  {
    m_number_of_checks = 0;
  }

  /// Does `x` refine `y`?
  bool check(const PartialString& x, const PartialString& y)
  {
    ++m_number_of_checks;

    if (x.length() != y.length())
      return false;

#ifdef _CKA_OPTIMIZE_
    if (x.strict_partial_order().size() < y.strict_partial_order().size())
      return false;
#endif

    encode_label(m_label_func_x, x);
    encode_strict_partial_order(m_order_pred_x, x);
    encode_monotonic_bijective_morphism(x, y);

    ++m_number_of_solver_calls;
    smt::CheckResult r{m_solver.check()};

#ifdef _CKA_DEBUG_
    std::cout << "Solver: " << m_solver.solver() << std::endl;
    if (r == smt::sat)
      std::cout << "Model: " << m_solver.solver().get_model() << std::endl;
#endif

    m_solver.reset();

    // Does there exist a strictly monotonic bijective
    // label-preserving function from y to x?
    return r == smt::sat;
  }

  bool check(const Program& X, const Program& Y)
  {
    bool is_refine;
    for (const PartialString& x : X.partial_strings())
    {
      is_refine = false;
      for (const PartialString& y : Y.partial_strings())
        if (check(x, y))
        {
          is_refine = true;
          break;
        }

      if (not is_refine)
        return false;
    }

    return true;
  }

  template<Opchar opchar>
  bool check(const LfpProgram<opchar>& lfpX, const LfpProgram<opchar>& lfpY)
  {
    const Program& X = lfpX.P();
    const Program& Y = lfpY.P();
    const unsigned j = Programs::max_length(X) / Programs::min_length(Y);

    Program K = Y;
    for (unsigned k{0}; k <= j; ++k, K = Eval<opchar>::bowtie(K, Y))
      if (check(X, K))
        return true;

    return false;
  }
};

/// Does `x` refine `y`?
bool operator<=(const PartialString&, const PartialString&);

/// Does `X` refine `Y`?
bool operator<=(const Program&, const Program&);

/// Does the first least fixed point refine the second least fixed point?
template<Opchar opchar>
bool operator<=(const LfpProgram<opchar>& lfpX, const LfpProgram<opchar>& lfpY)
{
  static Refinement s_refinement;
  return s_refinement.check(lfpX, lfpY);
}

}

#endif
