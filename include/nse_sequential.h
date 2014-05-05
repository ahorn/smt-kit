// Copyright 2014, Alex Horn. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

#ifndef __NSE_SEQUENTIAL_H_
#define __NSE_SEQUENTIAL_H_

#include <smt>
#include <list>
#include <vector>
#include <string>
#include <cassert>
#include <type_traits>

namespace crv
{

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
    static const std::string s_prefix;

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
      return smt::any<typename Smt<T>::Sort>(s_prefix + std::to_string(s_counter++));
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
  : m_term(nullptr),
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

  Flip(const Flip&) = delete;

  Flip(const bool direction_arg, const bool is_frozen_arg)
  : direction(direction_arg),
    is_frozen(is_frozen_arg) {}
};

typedef std::list<Flip> Flips;
typedef std::list<Flip>::iterator FlipIter;

// Explore execution paths in a program using depth-first search
class Dfs
{
private:
  unsigned long long m_path_cnt;
  Flips m_flips;
  FlipIter m_flip_iter;

public:
  Dfs()
  : m_path_cnt(0),
    m_flips(),
    m_flip_iter(m_flips.begin()) {}

  void reset()
  {
    m_path_cnt = 0;
    m_flips.clear();
    m_flip_iter = m_flips.begin();
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
  bool find_next_path()
  {
    m_flip_iter = m_flips.begin();

    while (!m_flips.empty() && m_flips.back().is_frozen)
    {
      m_flips.pop_back();
    }

    if (m_flips.empty())
      return false;

    Flip& flip = m_flips.back();
    flip.direction = !flip.direction;
    flip.is_frozen = true;
    m_path_cnt++;

    assert(0 < m_path_cnt);
    assert(!m_flips.empty());

    return true;
  }

  bool has_next() const
  {
    return m_flip_iter != m_flips.end();
  }

  void append_flip(const bool direction = false, const bool is_frozen = false)
  {
    m_flips.emplace_back(direction, is_frozen);

    assert(m_flips.back().direction == direction);
    assert(m_flips.back().is_frozen == is_frozen);
  }

  /// \pre: has_next()

  /// \return direction of current_flip()
  bool next()
  {
    assert(has_next());

    // increment after returning m_flip_iter->direction
    return (m_flip_iter++)->direction;
  }

  /// \pre: has_next()
  const Flip& current_flip() const
  {
    assert(has_next());

    return *m_flip_iter;
  }
};

typedef std::list<smt::Bool> Bools;

class Checker
{
private:
  smt::Bool m_assertions;
  smt::Bool m_errors;

  // never null
  smt::Bool m_guard;

  void reset_assertions()
  {
    m_assertions = smt::Bool();
  }

  void reset_errors()
  {
    m_errors = smt::Bool();
  }

  void reset_guard()
  {
    m_guard = smt::literal<smt::Bool>(true);
  }

protected:
  // no polymorphic deletes
  ~Checker() {}

  Checker()
  : m_assertions(),
    m_errors(),
    m_guard(smt::literal<smt::Bool>(true)) {}

  void reset()
  {
    reset_assertions();
    reset_errors();
    reset_guard();
  }

  void set_guard(const smt::Bool& guard)
  {
    m_guard = guard;
  }

public:
  /// Add Boolean term of argument to assertions()

  /// This is similar to evaluating the condition in an
  /// if-statement except that no further flips are required.
  void add_assertion(Internal<bool>&&);

  /// Add conjunction of guard() and given Boolean term to errors()
  void add_error(Internal<bool>&&);

  void add_guard(smt::Bool&& g)
  {
    assert(!g.is_null());
    m_guard = m_guard and std::move(g);
  }

  void add_guard(const smt::Bool& g)
  {
    assert(!g.is_null());
    m_guard = m_guard and g;
  }

  /// is_null() or logical conjunction
  const smt::Bool& assertions() const
  {
    return m_assertions;
  }

  /// is_null() or logical disjunction
  const smt::Bool& errors() const
  {
    return m_errors;
  }

  const smt::Bool& guard() const
  {
    assert(!m_guard.is_null());
    return m_guard;
  }
};

/// Depth-first search checker for sequential code
class SequentialDfsChecker : public Checker
{
private:
  smt::Z3Solver m_solver;
  bool m_is_feasible;
  Dfs m_dfs;

  smt::CheckResult check(const smt::Bool& condition)
  {
    m_solver.push();
    m_solver.add(condition);
    const smt::CheckResult r = m_solver.check();
    m_solver.pop();
    return r;
  }

protected:
  void reset_dfs()
  {
    m_is_feasible = true;
    m_dfs.reset();
  }

  void reset_solver()
  {
    m_solver.reset();
  }

public:

  SequentialDfsChecker()
  : Checker(),
#ifdef _BV_THEORY_
    m_solver(smt::QF_ABV_LOGIC),
#else
    m_solver(smt::QF_AUFLIRA_LOGIC),
#endif
    m_is_feasible(true),
    m_dfs() {}

  void reset()
  {
    reset_dfs();
    reset_solver();

    Checker::reset();
    internal::Inputs::reset();
  }

  /// Follow a feasible control flow direction, i.e. prunes infeasible branches

  /// The second direction argument is only a suggestion that may be ignored.
  bool branch(const Internal<bool>&, const bool direction_hint = false);

  /// Use DFS to find an unexplored path, if any

  /// \return is there another path to explore?
  bool find_next_path()
  {
    m_is_feasible = true;

    const bool found_path = m_dfs.find_next_path();
    if (found_path)
      Checker::reset(); // do not reset m_dfs etc.

    return found_path;
  }

  /// Check for any sequential program safety violations (i.e. bugs)

  /// Use SAT/SMT solver to check the satisfiability of the
  /// disjunction of errors() and guard() conjoined with
  /// the conjunction of assertions() (if any)
  ///
  /// pre: not Checker::errors().is_null()
  smt::CheckResult check()
  {
    assert(!Checker::errors().is_null());

    m_solver.push();

    if (!Checker::assertions().is_null())
      m_solver.add(Checker::assertions());

    m_solver.add(Checker::errors());
    m_solver.add(Checker::guard());

    const smt::CheckResult result = m_solver.check();
    m_solver.pop();
    return result;
  }
};

/// Symbolic execution of only feasible paths in a depth-first search manner
extern SequentialDfsChecker& sequential_dfs_checker();

}

#endif
