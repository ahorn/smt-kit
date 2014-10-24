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
#include <algorithm>

#ifdef _CKA_DEBUG_
#include <iostream>
#endif

namespace cka
{

typedef unsigned Label;
typedef unsigned Event;
typedef unsigned Length;

/// Treated as a list of `const Event`
typedef std::list<Event> Events;

/// Finite partial string
class PartialString
{
public:
  /// Treated as a pair of `const Event`
  typedef std::pair<Event, Event> EventPair;

  /// Treated as a `const EventPair`
  typedef std::list<EventPair> EventPairs;

  /// A map from `Event` to `Label`
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

  // smallest and largest label, undefined whenever `m_length` is zero
  Label m_min_label, m_max_label;

  // size of vector is fixed to `m_max_label + 1`
  std::vector<unsigned> m_number_of_events_with_label;

  /// Empty partial string

  /// \post: `length()` is zero
  PartialString()
  : m_label_function{},
    m_strict_partial_order{},
    m_length{0},
    m_incomparables{},
    m_minimals{},
    m_maximals{},
    m_min_label{0},
    m_max_label{0},
    m_number_of_events_with_label{} {}

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
    m_maximals(m_length),
    m_min_label{std::min(x.min_label(), y.min_label())},
    m_max_label{std::max(x.max_label(), y.max_label())},
    m_number_of_events_with_label{x.m_number_of_events_with_label}
  {
    // Is `m_min_label` currently undefined?
    if (x.length() == 0) m_min_label = y.min_label();
    if (y.length() == 0) m_min_label = x.min_label();

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

    // vector is never resized, assumes labels are dense and sufficiently small
    m_number_of_events_with_label.resize(m_max_label + 1U);

    unsigned i{0};
    for (unsigned j : y.m_number_of_events_with_label)
      m_number_of_events_with_label[i++] += j;
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
    m_maximals(1),
    m_min_label{label},
    m_max_label{label},
    m_number_of_events_with_label{}
  {
    recompute_extremals();

    m_number_of_events_with_label.resize(label + 1U);
    m_number_of_events_with_label[label] = 1U;
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

  /// Smallest label

  /// \warning undefined whenever `length()` is zero
  Label min_label() const noexcept
  {
    return m_min_label;
  }

  /// Largest label

  /// \warning undefined whenever `length()` is zero
  Label max_label() const noexcept
  {
    return m_max_label;
  }

  unsigned number_of_events_with_label(Label label) const noexcept
  {
    if (m_number_of_events_with_label.size() <= label)
      return 0;

    return m_number_of_events_with_label[label];
  }

  /// Checks equality of two partial strings, not their isomorphism!
  friend bool operator==(const PartialString& x, const PartialString& y)
  {
    return x.m_label_function == y.m_label_function and
      x.m_strict_partial_order == y.m_strict_partial_order and
      x.m_length == y.m_length and
      x.m_incomparables == y.m_incomparables and
      x.m_minimals == y.m_minimals and
      x.m_maximals == y.m_maximals;
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
  static Program& zero()
  {
    static Program s_zero{PartialStrings()};
    return s_zero;
  }

  /// A single partial string whose only event is labelled by `label`
  Program(const Label label)
  : m_partial_strings{}
  {
    m_partial_strings.emplace_back(label);
  }

  /// Convert a partial string to a program
  Program(const PartialString& x)
  : m_partial_strings{x} {}

  /// Moves a partial string into a new program
  Program(PartialString&& x)
  : m_partial_strings{std::move(x)} {}

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

/// Utility class for partial string and program operators
template<Opchar opchar>
struct Eval
{
  /// Compose two partial strings
  static PartialString bowtie(const PartialString&, const PartialString&);

  /// Compose two finite programs
  static Program bowtie(const Program&, const Program&);
};

/// Template specialization for concurrent program composition
template<>
struct Eval<'|'>
{
  static PartialString bowtie(const PartialString& x, const PartialString& y)
  {
    return {(x | y)};
  }

  static Program bowtie(const Program& X, const Program& Y)
  {
    return {(X | Y)};
  }
};

/// Template specialization for strongly sequential program composition
template<>
struct Eval<','>
{
  static PartialString bowtie(const PartialString& x, const PartialString& y)
  {
    return {(x , y)};
  }

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

namespace internal
{
  /// Raise `base` to the power of `exp`, i.e. `base^exp`
  unsigned uint_pow(unsigned base, unsigned exp);

  /// A nonstandard single-pass input iterator for constant partial strings

  /// \warning at most one `PartialStringIterator` object for a `Program`
  ///   must be instantiated at a given time
  ///
  /// \remark we do not implement a more standard iterator such as
  ///   `std::iterator<std::input_iterator_tag, const PartialString>`
  ///   because this would require copies of possibly long vectors
  ///
  /// \see LazyProgram<opchar>
  template<Opchar opchar>
  class PartialStringIterator
  {
  private:
    const Program* m_program_ptr;
    std::vector<unsigned>& m_vector;

  public:
    PartialStringIterator(
      const Program* program_ptr,
      std::vector<unsigned>& vector)
    : m_program_ptr{program_ptr},
      m_vector(vector) {}

    bool has_next_partial_string() const noexcept
    {
      return m_program_ptr != nullptr and not m_vector.empty();
    }

    void reset()
    {
      std::fill(m_vector.begin(), m_vector.end(), 0);
    }

    /// \pre: `has_next_partial_string()`
    PartialString next_partial_string()
    {
      assert(has_next_partial_string());

      PartialString p{PartialString::empty()};
      for (unsigned i : m_vector)
      {
        assert(i < m_program_ptr->size());

        // compose `p` with `i`th partial string in `*m_program_ptr`
        p = Eval<opchar>::bowtie(p, m_program_ptr->partial_strings().at(i));
      }

      // detect whether another partial string can be generated
      bool is_end = true;

      // similar to a ripple-carry adder that computes
      // `m_vector + 1` modulus `m_program_ptr->size()`
      for (unsigned& i : m_vector)
      {
        ++i;

        // Need to carry over to next index?
        if (m_program_ptr->size() == i)
        {
          i = 0;
        }
        else
        {
          is_end = false;

          break;
        }
      }

      if (is_end)
        m_program_ptr = nullptr;

      // good compilers will use RVO
      return p;
    }
  };

  /// Defer the computation of program compositions, strictly internal

  /// Asymptotically, the `n`-repeated composition of `Program` requires
  /// exponential space in `n`. The purpose of `LazyProgram` is to reduce
  /// this to an asymptotic linear space requirement.
  template<Opchar opchar>
  class LazyProgram
  {
  private:
    // iteratively compose `*m_program_ptr` under `opchar`
    const Program* m_program_ptr;

    // array of indexes into `m_program_ptr->partial_strings()`
    std::vector<unsigned> m_vector;

  public:
    LazyProgram(const Program& program_ref)
    : m_program_ptr{&program_ref},
      m_vector{0}
    {
      assert(m_vector.size() == 1);
      assert(m_vector[0] == 0);
    }

    const Program& P() const noexcept
    {
      return *m_program_ptr;
    }

    /// Program size grows exponentially with every call to `extend()`
    unsigned size() const noexcept
    {
      return uint_pow(m_program_ptr->size(), m_vector.size());
    }

    /// Conceptually computes `Eval<opchar>::bowtie(*this, P())`
    void extend()
    {
      static constexpr unsigned zero = 0;

      std::fill(m_vector.begin(), m_vector.end(), zero);
      m_vector.push_back(zero);
    }

    /// \warning cheap but at most one iterator can be used at a given time

    /// The iterator is in the same state the previous owner left it in.
    /// \see also PartialStringIterator<opchar>::reset()
    PartialStringIterator<opchar> partial_string_iterator() noexcept
    {
      return {m_program_ptr, m_vector};
    }
  };
}

/// Iterate over each `event` and its `label` in a partial string `p`
#define for_each_label(p, event, label)                                 \
  Event event{0};                                                       \
  Label label;                                                          \
  PartialString::LabelFunction::const_iterator                          \
    citer{(p).label_function().cbegin()},                               \
    cend{(p).label_function().cend()};                                  \
  for (label = *citer; citer != cend; ++citer, ++event, label = *citer) \

namespace internal
{
  /// Iterative algorithm to check the refinement of two elementary programs

  /// This template class implements an iterative algorithm that repeatably calls
  /// `PartialStringChecker::check(const PartialString&, const PartialString&)`
  /// for each pair of partial strings in two elementary programs.
  ///
  /// If `Program::partial_strings()` are sorted, we can sometimes exit
  /// the innermost loop quicker. But we found this not to make a big
  /// difference on random sets.
  template<class PartialStringChecker>
  class ProgramChecker
  {
  private:
    template<Opchar opchar>
    bool lazy_check(const Program& X, internal::LazyProgram<opchar>& Y)
    {
      bool is_refine;
      for (const PartialString& x : X.partial_strings())
      {
        internal::PartialStringIterator<opchar> iter{Y.partial_string_iterator()};
        is_refine = false;
        while (iter.has_next_partial_string())
        {
          PartialString y{iter.next_partial_string()};

          if (static_cast<PartialStringChecker*>(this)->check(x, y))
          {
            // relinquish ownership
            iter.reset();

            is_refine = true;
            break;
          }
        }

        if (not is_refine)
          return false;
      }

      return true;
    }

  public:
    bool check(const Program& X, const Program& Y)
    {
      bool is_refine;
      for (const PartialString& x : X.partial_strings())
      {
        is_refine = false;
        for (const PartialString& y : Y.partial_strings())
          if (static_cast<PartialStringChecker*>(this)->check(x, y))
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

/// \warning if programs are composed eagerly, you're likely to run out of memory!
#ifdef _CKA_EAGER_
      Program K{Y};
      for (unsigned k{0}; k <= j; ++k, K = Eval<opchar>::bowtie(K, Y))
        if (ProgramChecker::check(X, K))
#else
      internal::LazyProgram<opchar> K{Y};
      for (unsigned k{0}; k <= j; ++k, K.extend())
        if (ProgramChecker::lazy_check(X, K))
#endif
          return true;

      return false;
    }
  };
}

namespace memory
{
  class Refinement;
}

namespace internal
{
  /// A conservative refinement check for two partial strings
  class Refinement
  {
  private:
    // Statistics
    unsigned m_number_of_shortcuts;

  protected:
    Refinement() : m_number_of_shortcuts{0} {}

    /// Returns true whenever `x` does not refine `y`, and false if unknown
    bool shortcut(const PartialString& x, const PartialString& y)
    {
      if (x.length() != y.length() or
          x.min_label() != y.min_label() or
          x.max_label() != y.max_label())
      {
        ++m_number_of_shortcuts;
        return true;
      }

      return false;
    }

    /// Returns true whenever `x` does not refine `y`, and false if unknown

    /// This approximation is more precise than `shortcut` but may be therefore slower.
    bool more_precise_shortcut(const PartialString& x, const PartialString& y)
    {
      if (shortcut(x, y))
        return true;

      for (Label label{x.min_label()}; label <= x.min_label(); ++label)
        if (x.number_of_events_with_label(label) != y.number_of_events_with_label(label))
        {
          ++m_number_of_shortcuts;
          return true;
        }

      return false;
    }

  public:
    void reset_number_of_shortcuts()
    {
      m_number_of_shortcuts = 0;
    }

    unsigned number_of_shortcuts() const
    {
      return m_number_of_shortcuts;
    }
  };
}

/// SMT sort for events
typedef smt::Int EventSort;

/// Symbolic partial order base model

/// This model uses partial orders to describe the computation of concurrent
/// programs. Other models have been developed that rely only on relations.
/// The underpinning principles of our symbolic implementation of relations
/// would, however, remain the same.
class PartialOrderModel
{
private:
  // Binary predicate to symbolically encode strict partial order
  typedef smt::Func<EventSort, EventSort, smt::Bool> OrderPredSort;
  typedef smt::Decl<OrderPredSort> OrderPred;

  OrderPred m_order_pred;

public:
  PartialOrderModel()
  : m_order_pred{"order_x"} {}

  /// \internal binary predicate to enforce the ordering between events

  /// \see order(Event, Event)
  const OrderPred& order_pred() const
  {
    return m_order_pred;
  }

  /// Adds the symbolic ordering constraint that `a` enables `b`
  smt::Bool order(Event a, Event b) const
  {
    EventSort a_literal{smt::literal<EventSort>(a)};
    EventSort b_literal{smt::literal<EventSort>(b)};
    return smt::apply(m_order_pred, std::move(a_literal), std::move(b_literal));
  }

  /// Symbolically encodes an irreflexive, transitive and asymmetric relation

  /// Returns `true` if `conjuncts` is unsatisfiable, `false` if unknown
  bool strict_partial_order(const PartialString& p, smt::Bools& conjuncts)
  {
    // in the worst case, encoding is cubic in the number of events in `p`
    const Length len{p.length()};
    conjuncts.reserve(conjuncts.size() + (len * len * len));

    // transitive reduction of `p`
    for (const PartialString::EventPair& pair : p.strict_partial_order())
      conjuncts.push_back(order(pair.first, pair.second));

    // irreflexivity
    for (Event e{0}; e < len; ++e)
      conjuncts.push_back(not order(e, e));

    // asymmetry
    smt::Bool order_a_b;
    {
      smt::Bool order_b_a;
      for (Event e_a{0}; e_a < len; ++e_a)
        for (Event e_b{e_a + 1U}; e_b < len; ++e_b)
        {
          order_a_b = order(e_a, e_b);
          order_b_a = order(e_b, e_a);

          conjuncts.push_back(smt::implies(order_a_b, not order_b_a));
        }
    }

    // transitivity
    smt::Bool order_b_c, order_a_c;
    for (Event e_a{0}; e_a < len; ++e_a)
      for (Event e_b{0}; e_b < len; ++e_b)
        for (Event e_c{0}; e_c < len; ++e_c)
        {
          order_a_b = order(e_a, e_b);
          order_b_c = order(e_b, e_c);
          order_a_c = order(e_a, e_c);

          conjuncts.push_back(smt::implies(order_a_b and order_b_c, order_a_c));
        }

    return false;
  }

  /// Symbolically encode the incomparable events in `p`

  /// Returns `true` if `conjuncts` is unsatisfiable, `false` if unknown
  bool incomparables(const PartialString& p, smt::Bools& conjuncts)
  {
    conjuncts.reserve(conjuncts.size() + (2U * p.incomparables().size()));
    for (const PartialString::EventPair& pair : p.incomparables())
    {
      conjuncts.push_back(not order(pair.first, pair.second));
      conjuncts.push_back(not order(pair.second, pair.first));
    }

    return false;
  }
};

namespace internal
{
  /// RAII
  class ResetSolver
  {
  private:
    smt::Solver& m_solver_ref;
  public:
    ResetSolver(smt::Solver& solver) : m_solver_ref(solver) {}
    ~ResetSolver() { m_solver_ref.reset(); }
  };
}

/// Symbolic decision procedure for certain CKA language containment problems
class Refinement
: public internal::ProgramChecker<Refinement>,
  public internal::Refinement
{
private:
  friend class memory::Refinement;

  typedef smt::Int LabelSort;
  typedef smt::Func<EventSort, EventSort> EventFuncSort;
  typedef smt::Func<EventSort, LabelSort> LabelFuncSort;

  typedef smt::Decl<EventFuncSort> EventFunc;
  typedef smt::Decl<LabelFuncSort> LabelFunc;

  // Other SMT solvers include smt::CVC4Solver and smt::MsatSolver
  smt::Z3Solver m_solver;

  // The goal is to check that `m_event_func` is a monotonic bijective morphism
  EventFunc m_event_func;

  // The range of `m_event_func` must respect the labelling and ordering of `x`
  LabelFunc m_label_func_x;

  // The core of the encoding
  PartialOrderModel m_po_model;

  // Statistics
  unsigned m_number_of_solver_calls;
  unsigned m_number_of_checks;

  void encode_label(const LabelFunc& label_func_p, const PartialString& p)
  {
    if (p.length() == 0)
      return;

    smt::Bools equalities(p.length());
    for_each_label(p, event, label)
      equalities.push_back(smt::apply(label_func_p, event) == label);

    m_solver.add(smt::conjunction(std::move(equalities)));
  }

  void encode_monotonic_bijective_morphism(const PartialString& x, const PartialString& y)
  {
    // strict monotonicity from y to x
    if (not y.strict_partial_order().empty())
    {
      EventSort e_first, e_second;
      smt::Bools partial_order;

      // It suffices to check the strict monotonicity of the
      // transitive reduction of the strict partial ordering
      // of `y` because `model.order_pred()` is transitive.
      for (const PartialString::EventPair& y_pair : y.strict_partial_order())
      {
        e_first = smt::apply(m_event_func, y_pair.first);
        e_second = smt::apply(m_event_func, y_pair.second);

        partial_order.push_back(smt::apply(m_po_model.order_pred(), e_first, e_second));
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
  using internal::ProgramChecker<Refinement>::check;

  Refinement()
  : m_solver(smt::QF_UFLIA_LOGIC),
    m_event_func{"event"},
    m_label_func_x{"label_x"},
    m_po_model{},
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

    if (internal::Refinement::shortcut(x, y))
      return false;

    smt::Bools conjuncts;
    internal::ResetSolver reset_solver{m_solver};

    if (m_po_model.strict_partial_order(x, conjuncts))
      return false;

    if (m_po_model.incomparables(x, conjuncts))
      return false;

    if (!conjuncts.empty())
      m_solver.add(smt::conjunction(conjuncts));

    encode_label(m_label_func_x, x);
    encode_monotonic_bijective_morphism(x, y);

    ++m_number_of_solver_calls;
    smt::CheckResult r{m_solver.check()};

#ifdef _CKA_DEBUG_
    std::cout << "Solver: " << m_solver.solver() << std::endl;
    if (r == smt::sat)
      std::cout << "Model: " << m_solver.solver().get_model() << std::endl;
#endif

    // Does there exist a strictly monotonic bijective
    // label-preserving function from y to x?
    return r == smt::sat;
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

namespace memory
{

/// At least 16-bit address of a memory location
typedef unsigned short Address;

/// Treated as an 8-bit value written to memory
typedef unsigned char Byte;

/// Returns an even non-negative number

/// A non-synchronization store instruction
Label none_store_label(Address a, Byte b = 0);

/// Returns an odd positive number

/// A non-synchronization load instruction
///
/// Stores with a higher address will result in greater labels.
/// That is, `none_store_label` is monotonic; equivalently,
///
///   for all addresses a and a', if a is less than a', then
///   `none_store_label(a, b) < none_store_label(a, b')`
///   where b and b' are arbitrary bytes.
Label none_load_label(Address);

/// Returns an even non-negative number

/// C++14-style release store of an atomic byte `b` (default zero)
/// to a memory location identified by address `a`.
///
/// Stores with a higher address will result in greater labels.
/// That is, `release_store_label` is monotonic; equivalently,
///
///   for all addresses a and a', if a is less than a', then
///   `release_store_label(a, b) < release_store_label(a, b')`
///   where b and b' are arbitrary bytes.
Label release_store_label(Address a, Byte b = 0);

/// Returns an odd positive number

/// C++14-style acquire load instruction of an atomic integral value.
Label acquire_load_label(Address);

/// Returns an acquire load label that assumes `b` was read
Label assume_acquire_eq_label(Address a, Byte b);

/// Returns an acquire load label that assumes anything but `b` was read
Label assume_acquire_neq_label(Address a, Byte b);

/// Is label a non-synchronization store instruction?
bool is_none_store(Label);

/// Is label a non-synchronization load instruction?
bool is_none_load(Label);

/// Is label a C++14-style release store on an atomic integral type?
bool is_release_store(Label);

/// Is label a C++14-style acquire load on an atomic integral type?
bool is_acquire_load(Label);

bool is_store(Label);
bool is_load(Label);

/// Is label a load that assumes a certain byte was read?
bool is_assume(Label);
bool is_assume_acquire_eq(Label);
bool is_assume_acquire_neq(Label);

/// The byte written or expected by `op`

/// \pre: `is_store(op)` or `is_assume(op)`
Byte byte(Label op);

/// The memory address read or written by a load or store

/// \pre: `is_store(op)` or `is_load(op)`
Address address(Label op);

/// Is same memory accessed by `store` and `load`?

/// \pre: `is_release_store(store)` and `is_acquire_load(load)`
bool is_shared(Label store, Label load);

/// Is same memory accessed by a `store` and `load` event?

/// \pre: `store` and `load` are events in `x`
/// \pre: `is_release_store(x.label_function().at(store))`
/// \pre: `is_acquire_load(x.label_function().at(load))`
bool is_shared(const PartialString& x, Event store, Event load);

/// Maps a memory address to a list of events, sorted in ascending order

/// \remark we assume that memory addresses are dense
typedef std::vector<Events> PerAddressMap;

namespace internal
{
  struct Filter
  {
    Filter() = delete;

    /// Extracts stores and loads from `x`

    /// \pre: for all events `e`, if `store_predicate(e)` then `is_store(e)`
    /// \pre: for all events `e`, if `load_predicate(e)` then `is_load(e)`
    template<class Predicate>
    static Address store_load_filter(
      const PartialString& x,
      PerAddressMap& store_map,
      PerAddressMap& load_map,
      Predicate store_predicate,
      Predicate load_predicate)
    {
      // see monotonicity of store labels
      // and assumptions on memory addresses
      const Address max_address{memory::address(x.max_label())};

      Label label;
      Address address;

      store_map.resize(max_address + 1U);
      load_map.resize(max_address + 1U);

      for (Event e{0}; e < x.length(); ++e)
      {
        label = x.label_function().at(e);
        address = memory::address(label);

        assert(address < store_map.size());
        assert(address < load_map.size());

        if (store_predicate(label))
        {
          assert(is_store(label));
          store_map[address].emplace_back(e);
        }

        if (load_predicate(label))
        {
          assert(is_load(label));
          load_map[address].emplace_back(e);
        }
      }

      assert(store_map.size() == max_address + 1U);
      assert(load_map.size() == max_address + 1U);

      return max_address;
    }
  };
}

/// A partial order model of C++14-style release-acquire semantics
class ReleaseAcquireModel
{
private:
  const PartialOrderModel& m_po_model;

public:
  ReleaseAcquireModel(const PartialOrderModel& po_model)
  : m_po_model(po_model) {}

  /// Symbolically encodes a form of release-acquire semantics

  /// Returns `true` if `conjuncts` is unsatisfiable, `false` if unknown
  template<class Order>
  bool release_acquire(const Order& order, const PartialString& x,
    smt::Bools& conjuncts)
  {
    static const char* const s_rf_prefix = "rf!";

    Address address;
    smt::Bool rf_bool;
    EventSort rf_event;
    Label label, store_label;
    PerAddressMap store_map, load_map;

    const Address max_address{internal::Filter::store_load_filter(
      x, store_map, load_map, is_release_store, is_acquire_load)};

    // some read-from pair:
    //
    // for every load e, there exists a store e' to the
    // same memory address such that e' happens-before e
    smt::Bools some_rf;

    // for all memory addresses, the "some read-from" axiom
    // must hold, i.e. conjunction of "some_rf" predicates
    smt::Bools all_rf;

    // read-from relation:
    //
    // for all loads e and stores e', if e and e' access the
    // same memory and e reads-from e', then e' happens-before e
    smt::Bools order_rf;

    // modification order:
    //
    // atomic stores on the same memory address are totally ordered
    smt::Bools mo;

    // from-read relation (optional if we don't check written values):
    //
    // for all stores s and s' and loads l such that all three
    // access the same memory location, if l reads-from s and
    // s happens-before s', then l happens-before s'.
    smt::Bools order_fr;

    for (address = 0; address <= max_address; ++address)
    {
      const Events& stores = store_map[address];
      const Events& loads = load_map[address];

      for (Event load : loads)
      {
        label = x.label_function().at(load);
        rf_event = smt::any<EventSort>(s_rf_prefix, load);

        for (Event store_a : stores)
        {
          store_label = x.label_function().at(store_a);

          assert(is_release_store(store_label));
          assert(is_shared(x, store_a, load));

          if ((is_assume_acquire_eq(label) and byte(store_label) != byte(label)) or
                (is_assume_acquire_neq(label) and byte(store_label) == byte(label)))
            continue;

          rf_bool = store_a == rf_event;
          some_rf.push_back(rf_bool);
          order_rf.push_back(smt::implies(rf_bool,
            order.order(store_a, load)));

          for (Event store_b : stores)
            if (store_a != store_b)
            {
              order_fr.push_back(smt::implies(
                rf_bool and order.order(store_a, store_b),
                order.order(load, store_b)));
            }
        }

        if (some_rf.empty())
          return true;

        all_rf.push_back(smt::disjunction(some_rf));
        some_rf.clear();
      }

      for (Event store_a : stores)
        for (Event store_b : stores)
          if (store_a < store_b)
          {
            mo.push_back(order.order(store_a, store_b));
            mo.push_back(order.order(store_b, store_a));
          }

    } // end of address iteration

    if (!all_rf.empty())
      conjuncts.push_back(smt::conjunction(all_rf));

    if (!order_rf.empty())
      conjuncts.push_back(smt::conjunction(order_rf));

    if (!mo.empty())
      conjuncts.push_back(smt::disjunction(mo));

    if (!order_fr.empty())
      conjuncts.push_back(smt::conjunction(order_fr));

    return false;
  }
};

/// Checks refinement of two concurrent shared memory programs

/// Memory addresses are assumed to be consecutive, starting at zero.
class Refinement
: public cka::internal::ProgramChecker<Refinement>,
  public cka::internal::Refinement
{
private:
  friend class ReleaseAcquireModel;

  /// Increase precision of the generic partial string refinement checker
  cka::Refinement m_refinement;
  ReleaseAcquireModel m_rel_acq_model;

  /// Encode happens-before relation with monotonic bijective morphism

  /// \remark not the same as `PartialOrderModel::order`, the difference
  ///   is that we first map the events with `m_refinement.m_event_func`
  smt::Bool order(Event a, Event b) const
  {
    EventSort e_a{smt::apply(m_refinement.m_event_func, a)};
    EventSort e_b{smt::apply(m_refinement.m_event_func, b)};

    return smt::apply(m_refinement.m_po_model.order_pred(), e_a, e_b);
  }

public:
  using cka::internal::ProgramChecker<Refinement>::check;

  Refinement()
  : m_refinement{},
    m_rel_acq_model(m_refinement.m_po_model) {}

  /// Does `x` refine `y` when `y` satisfies the memory axioms?
  bool check(const cka::PartialString& x, const PartialString& y)
  {
    if (cka::internal::Refinement::shortcut(x, y))
      return false;

    smt::Bools conjuncts;

    if (m_rel_acq_model.release_acquire(*this, y, conjuncts))
      return false;

    if (!conjuncts.empty())
      m_refinement.m_solver.add(smt::conjunction(conjuncts));

    return m_refinement.check(x, y);
  }
};

/// Symbolic data race detector
class DataRaceDetector
{
private:
  /// Maps a memory address to a list of events, sorted in ascending order

  /// \remark we assume that memory addresses are dense
  typedef std::vector<Events> PerAddressMap;

  // Other SMT solvers include smt::CVC4Solver and smt::MsatSolver
  smt::Z3Solver m_solver;

  // The core of the encoding
  PartialOrderModel m_po_model;

  // Memory axioms
  friend class ReleaseAcquireModel;
  ReleaseAcquireModel m_rel_acq_model;

public:
  DataRaceDetector()
  : m_solver{smt::QF_UFLIA_LOGIC},
    m_po_model{},
    m_rel_acq_model{m_po_model} {}

  /// Is there a data race in `x`?
  bool is_racy(const PartialString& x)
  {
    cka::internal::ResetSolver reset_solver{m_solver};

    smt::Bools conjuncts;
    if (m_po_model.strict_partial_order(x, conjuncts))
      return false;

    if (m_rel_acq_model.release_acquire(m_po_model, x, conjuncts))
      return false;

    if (!conjuncts.empty())
      m_solver.add(smt::conjunction(conjuncts));

    Address address;
    PerAddressMap store_map, load_map;

    const Address max_address{internal::Filter::store_load_filter(
      x, store_map, load_map, is_none_store, is_none_load)};

    if (store_map.empty() or load_map.empty())
      return false;

    smt::Bools dr;
    dr.reserve(x.length() * x.length());

    for (address = 0; address <= max_address; ++address)
    {
      const Events& stores = store_map[address];
      const Events& loads = load_map[address];

      if (stores.empty() and loads.empty())
        continue;

      for (Event store : stores)
      {
        for (Event load : loads)
          dr.push_back(not (m_po_model.order(store, load) or
            m_po_model.order(load, store)));

        for (Event store_b : stores)
          if (store < store_b)
            dr.push_back(not (m_po_model.order(store_b, store) or
              m_po_model.order(store, store_b)));
      }
    }

    if (dr.empty())
      return false;

    m_solver.add(smt::disjunction(dr));

    smt::CheckResult r{m_solver.check()};

#ifdef _CKA_DEBUG_
    std::cout << "Solver: " << m_solver.solver() << std::endl;
    if (r == smt::sat)
      std::cout << "Model: " << m_solver.solver().get_model() << std::endl;
#endif

    // Does there exist a data race in `x`?
    return r == smt::sat;
  }
};

}

}

#endif
