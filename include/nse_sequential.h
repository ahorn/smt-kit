// Copyright 2014, Alex Horn. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

#ifndef __NSE_SEQUENTIAL_H_
#define __NSE_SEQUENTIAL_H_

#include <smt>
#include <list>
#include <vector>
#include <string>
#include <limits>
#include <cassert>
#include <type_traits>

namespace crv
{

#define _BV_THEORY_ 1

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

// Use smt::Bv<T> for bit-precision
template<typename T>
struct Smt
{
  typedef typename std::conditional<
    /* if */ std::is_same<bool, T>::value,
    /* then */ smt::Bool,
    /* else */
#ifdef _BV_THEORY_
  smt::Bv<T>
#else
  smt::Int
#endif
  >::type Sort;
};

template<class T>
struct Smt<T[]>
{
  typedef smt::Array<typename Smt<size_t>::Sort, typename Smt<T>::Sort> Sort;
};

template<class T, size_t N>
struct Smt<T[N]>
{
  typedef smt::Array<typename Smt<size_t>::Sort, typename Smt<T>::Sort> Sort;
};

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

namespace internal
{
  /// Symbolic inputs
  class Inputs
  {
  private:
    static constexpr char s_prefix[] = "x!";

    typedef unsigned long long Counter;
    static Counter s_counter;

  public:
    Inputs() = delete;

    static void reset()
    {
      s_counter = 0;
    }

    template<typename T>
    static typename Smt<T>::Sort make_symbol()
    {
      assert(s_counter < std::numeric_limits<Counter>::max());
      return smt::any<typename Smt<T>::Sort>(s_prefix, ++s_counter);
    }
  };
}

template<typename T> class External;

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

  // Returns statically allocated memory if is_literal is false; otherwise, null
  template<smt::Opcode opcode>
  static inline const simplifier::AbstractOp<T>* op_ptr(const bool is_literal)
  {
    // The following equivalent form does not generally perform better:
    //
    // return reinterpret_cast<const simplifier::AbstractOp<T>* const>(
    //    reinterpret_cast<uintptr_t>(simplifier::Op<opcode, T>::op_ptr()) &
    //      (static_cast<uintptr_t>(is_literal) - 1U));
    return is_literal ? nullptr : simplifier::Op<opcode, T>::op_ptr();
  }

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

protected:
  const typename Smt<T>::Sort& term() const
  {
    return m_term;
  }

public:
  // nondeterministic value
  Internal()
  : m_term(internal::Inputs::make_symbol<T>()),
    m_v(),
    m_op(nullptr)
  {
    assert(!m_term.is_null());
  }

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

#ifdef _BV_THEORY_
  template<typename U>
  explicit Internal(smt::Bv<U>&& term)
  : m_term(smt::bv_cast<T>(std::move(term))),
    m_v(),
    m_op(nullptr)
  {
    assert(!m_term.is_null());
  }
#endif

  Internal(T v)
  : m_term(),
    m_v(v),
    m_op(nullptr) {}

  // see External<T> definition
  Internal(const External<T>&);

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

    // recall m_op invariant
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

    return Internal(arg.m_term, internal::Eval<opcode>::eval(arg.m_v, literal),
      Internal<T>::op_ptr<opcode>(arg.is_literal()));
  }

  /// Propagate constants in commutative monoids

  /// \pre: arg.is_literal() or arg.is_lazy()
  template<smt::Opcode opcode>
  static Internal propagate(Internal&& arg, const T literal)
  {
    // check that arg.m_v is defined
    assert(arg.is_literal() || arg.is_lazy());

    return Internal(std::move(arg.m_term), internal::Eval<opcode>::eval(
      std::move(arg.m_v), literal), Internal<T>::op_ptr<opcode>(arg.is_literal()));
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

  template<typename S>
  static typename Smt<T>::Sort term(const Internal<S>& arg)
  {
#ifdef _BV_THEORY_
    return smt::bv_cast<T>(Internal<S>::term(arg));
#else
    // assume no cast required
    return Internal<S>::term(arg);
#endif
  }

  template<typename S>
  static typename Smt<T>::Sort term(Internal<S>&& arg)
  {
#ifdef _BV_THEORY_
    return smt::bv_cast<T>(Internal<S>::term(std::move(arg)));
#else
    // assume no cast required
    return Internal<S>::term(std::move(arg));
#endif
  }

  template<typename S>
  static Internal<T> cast(const Internal<S>& source)
  {
    return Internal<T>(term<S>(source));
  }

  static Internal cast(const Internal& source)
  {
    return source;
  }

  static Internal cast(Internal&& source)
  {
    return std::move(source);
  }
};

template<typename T, typename U> class _Internal;

// McCarthy array with constant propagation
template<typename T>
class Internal<T[]>
{
public:
  typedef size_t Size;
  typedef typename Smt<Size>::Sort DomainSort;
  typedef typename Smt<T>::Sort RangeSort;
  typedef smt::Array<DomainSort, RangeSort> Sort;

  // Used for simplifications
  typedef std::vector<Internal<T>> Vector;

private:
  typedef typename Vector::size_type VectorSize;

  // we want to detect overflows
  static_assert(std::is_unsigned<VectorSize>::value, "VectorSize must be unsigned");

  // if m_vector is nonempty, then m_term.is_null()
  // Once !m_term.is_null(), it stays this way.
  Sort m_term;
  Vector m_vector;

  template<typename _T>
  friend void make_any(Internal<_T[]>& arg);

  // reset variable to be nondeterministic
  void clear()
  {
    m_term = Sort();
    m_vector.clear();
  }

public:
  Internal() : m_term(), m_vector() {}

  template<typename U>
  _Internal<T, Size> operator[](const Internal<U>& offset);

  _Internal<T, Size> operator[](Size offset)
  {
    return operator[](Internal<Size>(offset));
  }
};

// McCarthy array with constant propagation and explicit size
template<typename T, size_t N>
class Internal<T[N]>
{
private:
  typedef size_t Size;
  typedef Internal<T[]> Forward;
  Forward m_forward;

  template<typename _T, size_t _N>
  friend void make_any(Internal<_T[_N]>& arg);

public:
  Internal() : m_forward() {}

  template<typename U>
  _Internal<T, Size> operator[](const Internal<U>& offset)
  {
    if (offset.is_literal())
      assert(offset.literal() < N);

    return m_forward[offset];
  }

  _Internal<T, Size> operator[](Size offset)
  {
    return m_forward[offset];
  }
};

// Temporary returned by Internal<T[]>::operator[](const Internal<U>&)
template<typename T, typename U>
class _Internal : public Internal<T>
{
public:
  typedef Internal<T[]> InternalArray;

private:
  // !m_term_ref.is_null() if and only if s_empty is referenced by m_vector_ref
  static typename InternalArray::Vector s_empty;

  typename InternalArray::Sort& m_term_ref;
  typename InternalArray::Vector& m_vector_ref;
  const Internal<U> m_offset;

  template<typename V>
  friend _Internal<T, U> Internal<T[]>::operator[](const Internal<V>&);

  // McCarthy array without simplifications
  _Internal(
    typename InternalArray::Sort& term_ref,
    const Internal<U>& offset)
  : Internal<T>(smt::select(term_ref, Internal<U>::term(offset))),
    m_term_ref(term_ref),
    m_vector_ref(s_empty),
    m_offset(offset)
  {
    assert(!term_ref.is_null());
    assert(!Internal<T>::term().is_null());

    // we don't simplify any longer
    assert(m_vector_ref.empty());
  }

  // Constant propagation

  // \pre: offset_literal < vector_ref.size()
  _Internal(
    typename InternalArray::Sort& term_ref,
    typename InternalArray::Vector& vector_ref,
    const U literal_offset)
  : Internal<T>(vector_ref.at(literal_offset)),
    m_term_ref(term_ref),
    m_vector_ref(vector_ref),
    m_offset(literal_offset)
  {
    assert(term_ref.is_null());
    assert(!m_vector_ref.empty());
    assert(m_offset.is_literal());
    assert(m_offset.literal() == literal_offset);
  }

  void store(typename InternalArray::RangeSort&& term)
  {
    m_term_ref = smt::store(m_term_ref, Internal<U>::term(m_offset), term);
  }

  bool is_simplified() const
  {
    return &m_vector_ref != &s_empty;
  }

public:
  _Internal(_Internal&& other)
  : m_term_ref(other.m_term_ref),
    m_vector_ref(other.m_vector_ref),
    m_offset(std::move(other.m_offset))
  {}

  Internal<T>& operator=(T v)
  {
    if (is_simplified())
      m_vector_ref.at(m_offset.literal()) = v;
    else
      store(smt::literal<typename InternalArray::RangeSort>(v));

    return *this;
  }

  Internal<T>& operator=(const Internal<T>& other)
  {
    if (is_simplified())
      m_vector_ref.at(m_offset.literal()) = other;
    else
      store(Internal<T>::term(other));

    return *this;
  }

  Internal<T>& operator=(Internal<T>&& other)
  {
    if (is_simplified())
      m_vector_ref.at(m_offset.literal()) = std::move(other);
    else
      store(Internal<T>::term(std::move(other)));

    return *this;
  }

  Internal<T>& operator=(_Internal<T, U>&& other)
  {
    return operator=(std::move(static_cast<Internal<T>>(other)));
  }
};

template<typename T, typename U>
typename Internal<T[]>::Vector _Internal<T, U>::s_empty;

template<typename T>
template<typename U>
_Internal<T, size_t> Internal<T[]>::operator[](const Internal<U>& offset)
{
  if (m_term.is_null())
  {
    if (offset.is_literal())
    {
      const U offset_literal = offset.literal();

      if (offset_literal >= m_vector.size())
      {
        VectorSize new_size = static_cast<VectorSize>(offset_literal) + 1;

        // overflow?
        assert(new_size != 0);

        // fill in nondeterministic array elements by
        // using Internal<T> default constructor
        m_vector.resize(new_size);
      }

      assert(offset_literal < m_vector.size());
      return _Internal<T, Size>(m_term, m_vector, offset_literal);
    }
    else
    {
      // initialize nondeterministic array
      m_term = internal::Inputs::make_symbol<T[]>();

      // before freeing m_vector, we symbolically represent it in m_term
      for (typename Vector::size_type i = 0; i < m_vector.size(); ++i)
        m_term = smt::store(m_term, smt::literal<DomainSort>(i),
          Internal<T>::term(m_vector[i]));

      // free memory
      m_vector.clear();
      m_vector.shrink_to_fit();
    }
  }

  assert(!m_term.is_null());
  assert(m_vector.empty());

  return _Internal<T, Size>(m_term, Internal<Size>::cast(offset));
}

namespace simplifier
{
  template<smt::Opcode opcode, typename T>
  struct IsCommutativeMonoid :
    std::integral_constant<bool,
      std::is_integral<T>::value and
      smt::ADD <= opcode and opcode <= smt::LOR>
  {};

  template<smt::Opcode opcode, typename T>
  struct AlgebraicProperty
  {
    static bool is_annihilator(T literal) { return false; }
  };

  template<>
  struct AlgebraicProperty<smt::LAND, bool>
  {
    static bool is_annihilator(bool literal) { return !literal; }
  };

  template<>
  struct AlgebraicProperty<smt::LOR, bool>
  {
    static bool is_annihilator(bool literal) { return literal; }
  };

  /// Constant propagation in commutative monoids
  struct Lazy
  {
    template<smt::Opcode opcode, typename T, typename Enable =
      typename std::enable_if<IsCommutativeMonoid<opcode, T>::value>::type>
    static Internal<T> apply(const Internal<T>& arg, const T literal)
    {
      if (AlgebraicProperty<opcode, T>::is_annihilator(literal))
        return Internal<T>(literal);
      else if ((!arg.is_lazy() || arg.opcode() != opcode) && !arg.is_literal())
        return Internal<T>::template make_lazy<opcode>(arg, literal);
      else
        return Internal<T>::template propagate<opcode>(arg, literal);
    }

    template<smt::Opcode opcode, typename T, typename Enable =
      typename std::enable_if<IsCommutativeMonoid<opcode, T>::value>::type>
    static Internal<T> apply(Internal<T>&& arg, const T literal)
    {
      if (AlgebraicProperty<opcode, T>::is_annihilator(literal))
        return Internal<T>(literal);
      else if ((!arg.is_lazy() || arg.opcode() != opcode) && !arg.is_literal())
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
    template<smt::Opcode opcode, typename T, typename S>
    static Internal<T> apply(const Internal<S>& u, const S literal)
    {
      if (u.is_literal())
        return Internal<T>(internal::Eval<opcode>::eval(u.literal(), literal));
      else
        return Internal<T>(internal::Eval<opcode>::eval(
          Internal<S>::term(u), literal));
    }

    template<smt::Opcode opcode, typename T, typename S>
    static Internal<T> apply(Internal<S>&& u, const S literal)
    {
      if (u.is_literal())
        return Internal<T>(internal::Eval<opcode>::eval(u.literal(), literal));
      else
        return Internal<T>(internal::Eval<opcode>::eval(
          Internal<S>::term(std::move(u)), literal));
    }

    template<smt::Opcode opcode, typename T, typename S>
    static Internal<T> apply(const S literal, const Internal<S>& v)
    {
      if (v.is_literal())
        return Internal<T>(internal::Eval<opcode>::eval(literal, v.literal()));
      else
        return Internal<T>(internal::Eval<opcode>::eval(
          literal, Internal<S>::term(v)));
    }

    template<smt::Opcode opcode, typename T, typename S>
    static Internal<T> apply(const S literal, Internal<S>&& v)
    {
      if (v.is_literal())
        return Internal<T>(internal::Eval<opcode>::eval(literal, v.literal()));
      else
        return Internal<T>(internal::Eval<opcode>::eval(
          literal, Internal<S>::term(std::move(v))));
    }
  };

  template<smt::Opcode opcode, typename T, typename S>
  static Internal<T> apply(const Internal<S>& u, const S literal)
  {
    return std::conditional<
      /* if */ std::is_same<T, S>::value and
               IsCommutativeMonoid<opcode, T>::value,
      /* then */ Lazy,
      /* else */ Eager>::type::template apply<opcode, T>(u, literal);
  }

  template<smt::Opcode opcode, typename T, typename S>
  static Internal<T> apply(Internal<S>&& u, const S literal)
  {
    return std::conditional<
      /* if */ std::is_same<T, S>::value and
               IsCommutativeMonoid<opcode, T>::value,
      /* then */ Lazy,
      /* else */ Eager>::type::template apply<opcode, T>(std::move(u), literal);
  }

  template<smt::Opcode opcode, typename T, typename S>
  static Internal<T> apply(const S literal, const Internal<S>& v)
  {
    return std::conditional<
      /* if */ std::is_same<T, S>::value and
               IsCommutativeMonoid<opcode, T>::value,
      /* then */ Lazy,
      /* else */ Eager>::type::template apply<opcode, T>(literal, v);
  }

  template<smt::Opcode opcode, typename T, typename S>
  static Internal<T> apply(const S literal, Internal<S>&& v)
  {
    return std::conditional<
      /* if */ std::is_same<T, S>::value and
               IsCommutativeMonoid<opcode, T>::value,
      /* then */ Lazy,
      /* else */ Eager>::type::template apply<opcode, T>(literal, std::move(v));
  }

  template<smt::Opcode opcode, typename T, typename S>
  static Internal<T> apply(const Internal<S>& u, const Internal<S>& v)
  {
    if (u.is_literal())
      return apply<opcode, T, S>(u.literal(), v);
    else if (v.is_literal())
      return apply<opcode, T, S>(u, v.literal());
    else
      return Internal<T>(internal::Eval<opcode>::eval(
        Internal<S>::term(u), Internal<S>::term(v)));
  }

  template<smt::Opcode opcode, typename T, typename S>
  static Internal<T> apply(const Internal<S>& u, Internal<S>&& v)
  {
    if (u.is_literal())
      return apply<opcode, T, S>(u.literal(), std::move(v));
    else if (v.is_literal())
      return apply<opcode, T, S>(u, v.literal());
    else
      return Internal<T>(internal::Eval<opcode>::eval(
        Internal<S>::term(u), Internal<S>::term(std::move(v))));
  }

  template<smt::Opcode opcode, typename T, typename S>
  static Internal<T> apply(Internal<S>&& u, const Internal<S>& v)
  {
    if (u.is_literal())
      return apply<opcode, T, S>(u.literal(), v);
    else if (v.is_literal())
      return apply<opcode, T, S>(std::move(u), v.literal());
    else
      return Internal<T>(internal::Eval<opcode>::eval(
        Internal<S>::term(std::move(u)), Internal<S>::term(v)));
  }

  template<smt::Opcode opcode, typename T, typename S>
  static Internal<T> apply(Internal<S>&& u, Internal<S>&& v)
  {
    if (u.is_literal())
      return apply<opcode, T, S>(u.literal(), std::move(v));
    else if (v.is_literal())
      return apply<opcode, T, S>(std::move(u), v.literal());
    else
      return Internal<T>(internal::Eval<opcode>::eval(
        Internal<S>::term(std::move(u)), Internal<S>::term(std::move(v))));
  }
}

} // end library namespace

#define NSE_UNARY_OP(op, opcode)                                                \
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

NSE_UNARY_OP(-, SUB)
NSE_UNARY_OP(!, LNOT)

#ifdef _BV_THEORY_
NSE_UNARY_OP(~, NOT)
#endif

#define NSE_BINARY_OP(op, opcode)                                               \
  template<typename U, typename V>                                              \
  inline auto operator op(                                                      \
    const crv::Internal<U>& u,                                                  \
    const crv::Internal<V>& v)                                                  \
  -> crv::Internal<typename crv::internal::Return<smt::opcode, U, V>::Type>     \
  {                                                                             \
    typedef typename std::common_type<U, V>::type CommonType;                   \
    typedef typename crv::internal::Return<smt::opcode, U, V>::Type ReturnType; \
    return crv::simplifier::apply<smt::opcode, ReturnType>(                     \
      crv::Internal<CommonType>::cast(u),                                       \
      crv::Internal<CommonType>::cast(v));                                      \
  }                                                                             \
                                                                                \
  template<typename U, typename V>                                              \
  inline auto operator op(                                                      \
    const crv::Internal<U>& u,                                                  \
    crv::Internal<V>&& v)                                                       \
  -> crv::Internal<typename crv::internal::Return<smt::opcode, U, V>::Type>     \
  {                                                                             \
    typedef typename std::common_type<U, V>::type CommonType;                   \
    typedef typename crv::internal::Return<smt::opcode, U, V>::Type ReturnType; \
    return crv::simplifier::apply<smt::opcode, ReturnType>(                     \
      crv::Internal<CommonType>::cast(u),                                       \
      crv::Internal<CommonType>::cast(std::move(v)));                           \
  }                                                                             \
                                                                                \
  template<typename U, typename V>                                              \
  inline auto operator op(                                                      \
    crv::Internal<U>&& u,                                                       \
    const crv::Internal<V>& v)                                                  \
  -> crv::Internal<typename crv::internal::Return<smt::opcode, U, V>::Type>     \
  {                                                                             \
    typedef typename std::common_type<U, V>::type CommonType;                   \
    typedef typename crv::internal::Return<smt::opcode, U, V>::Type ReturnType; \
    return crv::simplifier::apply<smt::opcode, ReturnType>(                     \
      crv::Internal<CommonType>::cast(std::move(u)),                            \
      crv::Internal<CommonType>::cast(v));                                      \
  }                                                                             \
                                                                                \
  template<typename U, typename V>                                              \
  inline auto operator op(                                                      \
    crv::Internal<U>&& u,                                                       \
    crv::Internal<V>&& v)                                                       \
  -> crv::Internal<typename crv::internal::Return<smt::opcode, U, V>::Type>     \
  {                                                                             \
    typedef typename std::common_type<U, V>::type CommonType;                   \
    typedef typename crv::internal::Return<smt::opcode, U, V>::Type ReturnType; \
    return crv::simplifier::apply<smt::opcode, ReturnType>(                     \
      crv::Internal<CommonType>::cast(std::move(u)),                            \
      crv::Internal<CommonType>::cast(std::move(v)));                           \
  }                                                                             \
                                                                                \
  template<typename U, typename V,                                              \
    class Enable = typename std::enable_if<std::is_arithmetic<V>::value>::type> \
  inline auto operator op(                                                      \
    const crv::Internal<U>& u,                                                  \
    V literal)                                                                  \
  -> crv::Internal<typename crv::internal::Return<smt::opcode, U, V>::Type>     \
  {                                                                             \
    typedef typename std::common_type<U, V>::type CommonType;                   \
    typedef typename crv::internal::Return<smt::opcode, U, V>::Type ReturnType; \
    return crv::simplifier::apply<smt::opcode, ReturnType>(                     \
      crv::Internal<CommonType>::cast(u),                                       \
      static_cast<CommonType>(literal));                                        \
  }                                                                             \
                                                                                \
  template<typename U, typename V,                                              \
    class Enable = typename std::enable_if<std::is_arithmetic<V>::value>::type> \
  inline auto operator op(                                                      \
    crv::Internal<U>&& u,                                                       \
    V literal)                                                                  \
  -> crv::Internal<typename crv::internal::Return<smt::opcode, U, V>::Type>     \
  {                                                                             \
    typedef typename std::common_type<U, V>::type CommonType;                   \
    typedef typename crv::internal::Return<smt::opcode, U, V>::Type ReturnType; \
    return crv::simplifier::apply<smt::opcode, ReturnType>(                     \
      crv::Internal<CommonType>::cast(std::move(u)),                            \
      static_cast<CommonType>(literal));                                        \
  }                                                                             \
                                                                                \
  template<typename U, typename V,                                              \
    class Enable = typename std::enable_if<std::is_arithmetic<U>::value>::type> \
  inline auto operator op(                                                      \
    U literal,                                                                  \
    const crv::Internal<V>& v)                                                  \
  -> crv::Internal<typename crv::internal::Return<smt::opcode, U, V>::Type>     \
  {                                                                             \
    typedef typename std::common_type<U, V>::type CommonType;                   \
    typedef typename crv::internal::Return<smt::opcode, U, V>::Type ReturnType; \
    return crv::simplifier::apply<smt::opcode, ReturnType>(                     \
      static_cast<CommonType>(literal),                                         \
      crv::Internal<CommonType>::cast(v));                                      \
  }                                                                             \
                                                                                \
  template<typename U, typename V,                                              \
    class Enable = typename std::enable_if<std::is_arithmetic<U>::value>::type> \
  inline auto operator op(                                                      \
    U literal,                                                                  \
    crv::Internal<V>&& v)                                                       \
  -> crv::Internal<typename crv::internal::Return<smt::opcode, U, V>::Type>     \
  {                                                                             \
    typedef typename std::common_type<U, V>::type CommonType;                   \
    typedef typename crv::internal::Return<smt::opcode, U, V>::Type ReturnType; \
    return crv::simplifier::apply<smt::opcode, ReturnType>(                     \
      static_cast<CommonType>(literal),                                         \
      crv::Internal<CommonType>::cast(std::move(v)));                           \
  }                                                                             \

NSE_BINARY_OP(-, SUB)
NSE_BINARY_OP(+, ADD)
NSE_BINARY_OP(*, MUL)
NSE_BINARY_OP(/, QUO)
NSE_BINARY_OP(%, REM)
NSE_BINARY_OP(<, LSS)
NSE_BINARY_OP(>, GTR)
NSE_BINARY_OP(!=, NEQ)
NSE_BINARY_OP(<=, LEQ)
NSE_BINARY_OP(>=, GEQ)
NSE_BINARY_OP(==, EQL)
NSE_BINARY_OP(&&, LAND)
NSE_BINARY_OP(||, LOR)

#ifdef _BV_THEORY_
NSE_BINARY_OP(&, AND)
NSE_BINARY_OP(|, OR)
NSE_BINARY_OP(^, XOR)
#endif

namespace crv
{

// \internal works also with External<T>(Internal<T>&&) constructor
template<typename T>
Internal<T> any()
{
  return Internal<T>(internal::Inputs::make_symbol<T>());
}

template<typename T> void make_any(Internal<T>& arg) { arg = any<T>(); }

/// Make an array nondeterministic (i.e. symbolic)
template<typename T> void make_any(Internal<T[]>& arg) { arg.clear(); }

/// Make a fixed-size array nondeterministic (i.e. symbolic)
template<typename T, size_t N>
void make_any(Internal<T[N]>& arg)
{
  make_any(arg.m_forward);
}

template<typename T,
  class Enable = typename std::enable_if<std::is_arithmetic<T>::value>::type>
inline Internal<T>& post_increment(Internal<T>& arg)
{
  arg = simplifier::apply<smt::ADD, T>(arg, static_cast<T>(1));
  return arg;
}

/// Control flow decision along symbolic path
struct Flip
{
  bool direction;

  /// freezing means that we won't try the other direction
  bool is_frozen;

  ~Flip() noexcept
  {}

  Flip(const bool direction_arg, const bool is_frozen_arg) noexcept
  : direction(direction_arg),
    is_frozen(is_frozen_arg) {}
};

/// Iterators into Flips are not stable
typedef std::vector<Flip> Flips;

// Explore execution paths in a program using depth-first search
class Dfs
{
private:
  typedef Flips::size_type FlipIndex;

  unsigned long long m_path_cnt;
  Flips m_flips;
  FlipIndex m_flip_index;

public:
  Dfs()
  : m_path_cnt(0),
    m_flips(),
    m_flip_index(0) {}

  void reset()
  {
    m_path_cnt = 0;
    m_flips.clear();
    m_flip_index = 0;
  }

  unsigned long long path_cnt() const
  {
    return m_path_cnt;
  }

  const Flips& flips() const
  {
    return m_flips;
  }

  Flips& flips()
  {
    return m_flips;
  }

  /// Depth-first search strategy

  /// \return is there more to explore?
  bool find_next_path(bool enable_counter = true)
  {
    m_flip_index = 0;

    while (!m_flips.empty() && m_flips.back().is_frozen)
    {
      m_flips.pop_back();
    }

    if (m_flips.empty())
      return false;

    Flip& flip = m_flips.back();
    flip.direction = !flip.direction;
    flip.is_frozen = true;

    if (enable_counter)
    {
      m_path_cnt++;

      // overflow?
      assert(0 != m_path_cnt);
    }

    assert(!m_flips.empty());

    return true;
  }

  bool has_next() const
  {
    return m_flip_index < m_flips.size();
  }

  void append_flip(const bool direction = false, const bool is_frozen = false)
  {
    m_flips.emplace_back(direction, is_frozen);

    assert(m_flips.back().direction == direction);
    assert(m_flips.back().is_frozen == is_frozen);

    ++m_flip_index;
  }

  /// \pre: has_next()

  /// \return direction of current_flip()
  bool next()
  {
    assert(has_next());

    // increment index after returning flip at m_flip_index
    return m_flips[m_flip_index++].direction;
  }

  /// \pre: has_next()
  const Flip& current_flip() const
  {
    assert(has_next());

    return m_flips[m_flip_index];
  }
};

/// Avoids Z3 performance issues
#define _NSE_ENABLE_GUARDS_ 1

/// Depth-first search checker for sequential code
class SequentialDfsChecker
{
public:
  typedef std::chrono::milliseconds ElapsedTime;

  struct Stats
  {
    // time it has taken so far to explore new branches
    ElapsedTime branch_time;

    // time it has taken so far to restore earlier explored states
    ElapsedTime replay_time;

    // number of branch(c) calls
    unsigned long long branch_cnt;

    // number of branch(c) calls where c is a literal
    unsigned long long branch_literal_cnt;
  };

private:
  typedef smt::NonReentrantTimer<ElapsedTime> Timer;

  smt::Z3Solver m_solver;

#ifdef _NSE_ENABLE_GUARDS_
  smt::Bools m_guards;
#endif
  smt::Bools m_errors;
  bool m_is_feasible;
  Dfs m_dfs;
  Stats m_stats;

  smt::ManualTimer<ElapsedTime> m_replay_manual_timer;

  void add_guard(smt::Bool&& g)
  {
    assert(!g.is_null());
#ifdef _NSE_ENABLE_GUARDS_
    m_guards.push_back(std::move(g));
#else
    m_solver.add(std::move(g));
#endif
  }

  smt::CheckResult check(const smt::Bool& condition)
  {
    smt::TemporaryAssertions t(m_solver);

#ifdef _NSE_ENABLE_GUARDS_
    if (!m_guards.empty())
      m_solver.add(smt::conjunction(m_guards));
#endif

    m_solver.add(condition);

    return m_solver.check();
  }

  /// \pre: not m_is_feasible
  bool branch(smt::Bool&& g_term, const bool direction_hint)
  {
    assert(m_is_feasible);

    if (m_dfs.has_next())
    {
      const bool direction = m_dfs.next();
      if (direction)
        add_guard(std::move(g_term));
      else
        add_guard(not std::move(g_term));

      return direction;
    }

    if (m_replay_manual_timer.is_active())
      m_replay_manual_timer.stop();

    Timer timer(m_stats.branch_time);

    if (direction_hint)
      goto THEN_BRANCH;
    else
      goto ELSE_BRANCH;

  THEN_BRANCH:
    if (smt::unsat != check(g_term))
    {
      add_guard(std::move(g_term));
      m_dfs.append_flip(true, !direction_hint);
      return true;
    }

    // neither THEN_BRANCH nor ELSE_BRANCH is feasible
    if (!direction_hint)
      goto NO_BRANCH;

  // fall through THEN_BRANCH to try ELSE_BRANCH
  ELSE_BRANCH:
    if (smt::unsat != check(not g_term))
    {
      add_guard(not std::move(g_term));
      m_dfs.append_flip(false, direction_hint);
      return false;
    }

    if (!direction_hint)
      // try the other branch
      goto THEN_BRANCH;

  NO_BRANCH:
    // both THEN_BRANCH and ELSE_BRANCH are infeasible
    m_is_feasible = false;

    // favour "else" branch, hoping for shorter infeasible path
    return false;
  }

protected:
  void reset_dfs()
  {
    m_is_feasible = true;
    m_dfs.reset();
  }

  void reset_errors()
  {
    m_errors.clear();
  }

#ifdef _NSE_ENABLE_GUARDS_
  void reset_guards()
  {
    m_guards.clear();
  }
#endif

  void reset_solver()
  {
    m_solver.reset();
  }

  void reset_stats()
  {
    m_stats.replay_time = m_stats.branch_time = ElapsedTime::zero();
    m_stats.branch_cnt = m_stats.branch_literal_cnt = 0;

    if (m_replay_manual_timer.is_active())
      m_replay_manual_timer.stop();
  }

public:

  SequentialDfsChecker()
#ifdef _BV_THEORY_
  : m_solver(smt::QF_ABV_LOGIC),
#else
  : m_solver(smt::QF_AUFLIRA_LOGIC),
#endif
#ifdef _NSE_ENABLE_GUARDS_
    m_guards(),
#endif
    m_errors(),
    m_is_feasible(true),
    m_dfs(),
    m_stats{},
    m_replay_manual_timer(m_stats.replay_time)
  {
    reset_stats();
  }

  void reset()
  {
    reset_dfs();
#ifdef _NSE_ENABLE_GUARDS_
    reset_guards();
#endif
    reset_errors();
    reset_solver();
    reset_stats();
    internal::Inputs::reset();
  }

  /// interpret as logical disjunction, or false if empty()
  const smt::Bools& errors() const
  {
    return m_errors;
  }

  void add_error(Internal<bool>&& error)
  {
    if (error.is_literal())
      assert(!m_is_feasible || (!error.literal() &&
        "Found bug without calling decision procedure"));
    else
      m_errors.push_back(Internal<bool>::term(std::move(error)));
  }

  const smt::Solver& solver() const
  {
    return m_solver;
  }

  const Stats& stats() const
  {
    return m_stats;
  }

  unsigned long long path_cnt() const
  {
    unsigned long long path_cnt = m_dfs.path_cnt() + 1;

    // overflow?
    assert(path_cnt != 0);
    return path_cnt;
  }

  void add_assertion(Internal<bool>&& g)
  {
    add_guard(Internal<bool>::term(std::move(g)));
  }

  /// Follow a feasible control flow direction, i.e. prunes infeasible branches

  /// The second direction argument is only a suggestion that may be ignored.
  bool branch(const Internal<bool>&, const bool direction_hint = false);

  /// Follow a feasible control flow direction, i.e. prunes infeasible branches

  /// The second direction argument is only a suggestion that may be ignored.
  bool branch(Internal<bool>&&, const bool direction_hint = false);

  /// Follow both control flow directions regardless of their feasibility
  bool force_branch(const Internal<bool>& g)
  {
    if (g.is_literal())
      return g.literal();

    bool direction = false;
    if (m_dfs.has_next())
    {
      direction = m_dfs.next();
    }
    else
    {
      if (m_replay_manual_timer.is_active())
        m_replay_manual_timer.stop();

      m_dfs.append_flip(direction);
    }

    smt::Bool g_term = Internal<bool>::term(g);
    if (direction)
      add_guard(std::move(g_term));
    else
      add_guard(not std::move(g_term));

    return direction;
  }

  /// Follow both control flow directions regardless of their feasibility
  bool force_branch(Internal<bool>&& g)
  {
    if (g.is_literal())
      return g.literal();

    bool direction = false;
    if (m_dfs.has_next())
    {
      direction = m_dfs.next();
    }
    else
    {
      if (m_replay_manual_timer.is_active())
        m_replay_manual_timer.stop();

      m_dfs.append_flip(direction);
    }

    smt::Bool g_term = Internal<bool>::term(std::move(g));
    if (direction)
      add_guard(std::move(g_term));
    else
      add_guard(not std::move(g_term));

    return direction;
  }

  /// Use DFS to find an unexplored path, if any

  /// \return is there another path to explore?
  bool find_next_path()
  {
    m_is_feasible = true;

    const bool found_path = m_dfs.find_next_path();
    if (found_path)
    {
      // always reset solver regardless whether we invoke
      // the incremental solving interface or not
      reset_solver();
#ifdef _NSE_ENABLE_GUARDS_
      reset_guards();
#endif
      reset_errors();

      // in case all branches could be resolved
      // with constant propagation and there is
      // no SequentialDfsChecker::check() call
      if (m_replay_manual_timer.is_active())
         m_replay_manual_timer.stop();

      m_replay_manual_timer.start();
    }

    return found_path;
  }

  /// Check for any sequential program safety violations (i.e. bugs)

  /// If errors() is empty, then return unsat; otherwise, invoke
  /// SAT/SMT solver to check the satisfiability of the disjunction
  /// of errors() plus the conjunction of guards and assertions.
  smt::CheckResult check()
  {
    // in case all branches could be resolved
    // with constant propagation
    if (m_replay_manual_timer.is_active())
       m_replay_manual_timer.stop();

    if (m_errors.empty())
      return smt::unsat;

#ifdef _NSE_ENABLE_GUARDS_
    if (!m_guards.empty())
      m_solver.add(smt::conjunction(m_guards));
#endif

    m_solver.add(smt::disjunction(m_errors));
    return m_solver.check();
  }
};

/// Symbolic execution of only feasible paths in a depth-first search manner
extern SequentialDfsChecker& sequential_dfs_checker();

class Checker
{
protected:
  smt::Bools m_assertions;
  smt::Bools m_errors;
  smt::Bools m_guards;

  void reset_assertions()
  {
    m_assertions.clear();
  }

  void reset_errors()
  {
    m_errors.clear();
  }

  void reset_guards()
  {
    m_guards.clear();
  }

  // no polymorphic deletes
  ~Checker() {}

  Checker()
  : m_assertions(),
    m_errors(),
    m_guards() {}

  void reset()
  {
    reset_assertions();
    reset_errors();
    reset_guards();
  }

  /// Create an array that only contains the given guard
  void set_guards(const smt::Bool& guard)
  {
    m_guards.clear();
    m_guards.push_back(guard);
  }

public:
  /// Add Boolean term of argument to assertions()

  /// This is similar to evaluating the condition in an
  /// if-statement except that no further flips are required.
  void add_assertion(Internal<bool>&&);

  /// Add conjunction of guards() and given Boolean term to errors()
  void add_error(Internal<bool>&&);

  void add_guard(smt::Bool&& g)
  {
    assert(!g.is_null());
    m_guards.push_back(std::move(g));
  }

  void add_guard(const smt::Bool& g)
  {
    assert(!g.is_null());
    m_guards.push_back(g);
  }

  /// interpret as logical conjunction, or true if empty()
  const smt::Bools& assertions() const
  {
    return m_assertions;
  }

  /// interpret as logical disjunction, or false if empty()
  const smt::Bools& errors() const
  {
    return m_errors;
  }

  const smt::Bools& guards() const
  {
    return m_guards;
  }
};


/// Non-chronological symbolic execution
class BacktrackDfsChecker : public Checker
{
public:
  typedef std::chrono::milliseconds ElapsedTime;

  struct Stats
  {
    // time it has taken so far to explore new branches
    ElapsedTime branch_time;

    // time it has taken so far to restore earlier explored states
    ElapsedTime replay_time;

    // number of branch(c) calls
    unsigned long long branch_cnt;

    // number of branch(c) calls where c is a literal
    unsigned long long branch_literal_cnt;
  };

private:
  typedef smt::NonReentrantTimer<ElapsedTime> Timer;

  smt::Z3Solver m_solver;
  Dfs m_dfs;
  Stats m_stats;

  // use m_found_path whenever m_allow_backtrack_check is false
  bool m_allow_backtrack_check;
  bool m_found_path;

  // a singleton vector because we aim to find the latest guard that
  // causes the conjunction of path conditions to be unsatisfiable
  smt::Bools m_unsat_core;

  smt::ManualTimer<ElapsedTime> m_replay_manual_timer;

  /// Checks satisfiability of assertions and guards (if any)

  /// Sets m_allow_backtrack_check to false if path condition is unsatisfiable.
  /// If m_allow_backtrack_check is false, m_found_path is set to the return
  /// value of m_dfs.find_next_path() and this function must not be called
  /// until symbolic execution has followed the path given by m_dfs.flips().
  ///
  /// The procedure always adds Check::assertions() to m_solver regardless
  //// whether there are guards or not.
  ///
  /// \pre: m_allow_backtrack_check is true
  void backtrack_check()
  {
    assert(m_allow_backtrack_check);

    // objects invariants
    assert(m_unsat_core.size() == 1);
    assert(Checker::guards().size() == m_dfs.flips().size());

    // procedure contract
    if (!Checker::assertions().empty())
      m_solver.add(smt::conjunction(Checker::assertions()));

    // okay, we're done
    if (Checker::guards().empty())
      return;

    std::pair<smt::CheckResult, smt::Bools::SizeType> r;
    smt::Bool flip_guard;
    uintptr_t flip_guard_addr;

REPEAT_BACKTRACK_CHECK: // until we've found a path or checked all
    r = m_solver.check_assumptions(Checker::guards(), m_unsat_core);

    // there isn't an unsat core
    if (r.second == 0)
      return;

    // we'll be working with unsat cores
    assert(r.first == smt::unsat);

    // procedure isn't idempotent so set flag
    m_allow_backtrack_check = false;

    // address of guard that is the most conservative possible
    // reason why the path condition is unsatisfiable
    flip_guard_addr = m_unsat_core.back().addr();

    // find out how many flips can be ignored (i.e. popped) by Dfs
    // since they were made after flip_guard_addr; the loop modifies
    // Checker::m_guards because we'll check their feasibility and
    // this vector will be cleared by find_next_path() anyway.
    while (flip_guard_addr != Checker::m_guards.back().addr())
    {
      Checker::m_guards.pop_back();
      m_dfs.flips().pop_back();

      // loop invariants
      assert(!Checker::m_guards.empty());
      assert(Checker::m_guards.size() == m_dfs.flips().size());
    }

    // after this call it may not be the case anymore that
    // Checker::m_guards.size() == m_dfs.flips().size()
    m_found_path = m_dfs.find_next_path(false);
    assert(m_dfs.flips().size() <= Checker::m_guards.size());

    // okay, we're done
    if (!m_found_path)
      return;

    // shrink guards if necessary and flip last one
    Checker::m_guards.resize(m_dfs.flips().size());

    // since Checker::m_guards is empty if and only if
    // m_found_path is true, the assertion holds
    assert(!Checker::m_guards.empty());

    flip_guard = Checker::m_guards.back();
    Checker::m_guards.pop_back();
    Checker::m_guards.push_back(not flip_guard);
    goto REPEAT_BACKTRACK_CHECK;
  }

protected:
  void reset_dfs()
  {
    m_dfs.reset();
  }

  void reset_solver()
  {
    m_solver.reset();
  }

  void reset_stats()
  {
    m_stats.replay_time = m_stats.branch_time = ElapsedTime::zero();
    m_stats.branch_cnt = m_stats.branch_literal_cnt = 0;

    if (m_replay_manual_timer.is_active())
      m_replay_manual_timer.stop();
  }

  void reset_unsat_core()
  {
    // do not reset m_found_path!
    m_allow_backtrack_check = true;
    m_unsat_core.resize(1);
  }

public:

  BacktrackDfsChecker()
  : Checker(),
#ifdef _BV_THEORY_
    m_solver(smt::QF_ABV_LOGIC),
#else
    m_solver(smt::QF_AUFLIRA_LOGIC),
#endif
    m_dfs(),
    m_stats{},
    m_allow_backtrack_check(true),
    m_found_path(true),
    m_unsat_core(),
    m_replay_manual_timer(m_stats.replay_time)
  {
    reset_stats();
    reset_unsat_core();
  }

  void reset()
  {
    reset_dfs();
    reset_solver();
    reset_stats();
    reset_unsat_core();

    Checker::reset();
    internal::Inputs::reset();
  }

  const smt::Solver& solver() const
  {
    return m_solver;
  }

  const Stats& stats() const
  {
    return m_stats;
  }

  unsigned long long path_cnt() const
  {
    unsigned long long path_cnt = m_dfs.path_cnt() + 1;

    // overflow?
    assert(path_cnt != 0);
    return path_cnt;
  }

  bool force_branch(const Internal<bool>& g)
  {
    return branch(g);
  }

  /// Follow both control flow directions regardless of their feasibility
  bool branch(const Internal<bool>& g)
  {
    if (g.is_literal())
      return g.literal();

    bool direction = false;
    if (m_dfs.has_next())
    {
      assert(m_allow_backtrack_check);
      direction = m_dfs.next();
    }
    else
    {
      if (m_replay_manual_timer.is_active())
        m_replay_manual_timer.stop();

      if (!m_allow_backtrack_check)
        return false;

      m_dfs.append_flip(direction);
    }

    smt::Bool g_term = Internal<bool>::term(g);
    if (direction)
      Checker::add_guard(g_term);
    else
      Checker::add_guard(not g_term);

    return direction;
  }

  bool force_branch(Internal<bool>&& g)
  {
    return branch(std::move(g));
  }

  /// Follow both control flow directions regardless of their feasibility
  bool branch(Internal<bool>&& g)
  {
    if (g.is_literal())
      return g.literal();

    bool direction = false;
    if (m_dfs.has_next())
    {
      assert(m_allow_backtrack_check);
      direction = m_dfs.next();
    }
    else
    {
      if (m_replay_manual_timer.is_active())
        m_replay_manual_timer.stop();

      if (!m_allow_backtrack_check)
        return false;

      m_dfs.append_flip(direction);
    }

    smt::Bool g_term = Internal<bool>::term(std::move(g));
    if (direction)
      Checker::add_guard(std::move(g_term));
    else
      Checker::add_guard(not std::move(g_term));

    return direction;
  }

  /// Use DFS with backtracking to find an unexplored path, if any

  /// \return is there another path to explore?
  bool find_next_path()
  {
    if (m_allow_backtrack_check)
    {
      backtrack_check();

      if (m_allow_backtrack_check)
        m_found_path = m_dfs.find_next_path();
    }

    if (m_found_path)
    {
      reset_solver();   // since we don't use incremental solving
      Checker::reset(); // do not reset m_dfs etc.

      if (m_replay_manual_timer.is_active())
         m_replay_manual_timer.stop();

      m_replay_manual_timer.start();
    }

    // doesn't reset m_found_path
    reset_unsat_core();
    return m_found_path;
  }

  /// Check for any sequential program safety violations (i.e. bugs)

  /// Invoke SAT/SMT solver to check the satisfiability of the disjunction of
  /// errors() conjoined with the conjunction of guards() and assertions() (if any)
  ///
  /// pre: not Checker::errors().empty()
  smt::CheckResult check()
  {
    assert(!Checker::errors().empty());

    if (!m_allow_backtrack_check)
      return smt::unsat;

    // avoid redundant satisfiability checks
    backtrack_check();
    if (!m_allow_backtrack_check)
      return smt::unsat;

    m_solver.add(smt::disjunction(Checker::errors()));
    return m_solver.check();
  }
};

/// Non-chronological symbolic execution
extern BacktrackDfsChecker& backtrack_dfs_checker();

}

#endif
