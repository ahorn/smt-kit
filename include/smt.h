// Copyright 2013, Alex Horn. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

#ifndef __SMT_H_
#define __SMT_H_

#include <tuple>
#include <array>
#include <vector>
#include <string>
#include <memory>
#include <cassert>
#include <stdexcept>
#include <type_traits>

namespace smt
{

enum Opcode : unsigned char
{
  LNOT, // !
  NOT,  // ~
  SUB,  // -
  AND,  // &
  OR,   // |
  XOR,  // ^
  LAND, // &&
  LOR,  // ||
  IMP,  // logical implication
  EQL,  // ==
  ADD,  // +
  MUL,  // *
  QUO,  // /
  REM,  // %
  LSS,  // <
  GTR,  // >
  NEQ,  // !=
  LEQ,  // <=
  GEQ   // >=
};

#define SMT_SORT(name) \
namespace sort         \
{                      \
  struct name          \
  {                    \
    name() = delete;   \
  };                   \
}                      \

SMT_SORT(Bool)
SMT_SORT(Int)
SMT_SORT(Real)

namespace sort
{
  template<typename Domain, typename Range>
  struct Array
  {
    Array() = delete;
  };

  template<typename... T>
  struct Func
  {
    // last tuple element
    typedef typename std::tuple_element<sizeof...(T) - 1,
      std::tuple<T...>>::type Range;

    Func() = delete;
  };
}

// Contingencies that a caller of the API must always consider
enum Error : unsigned {
  // No error, OK equals zero
  OK = 0,

  // Unexpected operator encountered
  OPCODE_ERROR,

  // Unsupported SMT-LIB feature
  UNSUPPORT_ERROR
};

enum CheckResult 
{
  unsat,
  sat,
  unknown
};

enum ExprKind : unsigned
{
  LITERAL_EXPR_KIND,
  UNARY_EXPR_KIND,
  BINARY_EXPR_KIND,
  NARY_EXPR_KIND,
  CONST_ARRAY_EXPR_KIND,
  ARRAY_SELECT_EXPR_KIND,
  ARRAY_STORE_EXPR_KIND,
  CONSTANT_EXPR_KIND,
  FUNC_APP_EXPR_KIND,
};

class Sort {
private:
  const bool m_is_bool;
  const bool m_is_int;
  const bool m_is_real;
  const bool m_is_bv;
  const bool m_is_signed;
  const size_t m_bv_size;
  const bool m_is_array;
  const bool m_is_func;
  const bool m_is_tuple;
  const Sort* const * m_sorts;
  const size_t m_sorts_size;

  constexpr unsigned check_sorts_index(size_t index)
  {
    return index >= m_sorts_size ?
      throw std::out_of_range("check_sorts_index fails") : index;
  }

public:
  constexpr Sort(
    bool is_bool,
    bool is_int,
    bool is_real,
    bool is_bv,
    bool is_signed,
    size_t bv_size)
  : m_is_bool(is_bool),
    m_is_int(is_int),
    m_is_real(is_real),
    m_is_bv(is_bv),
    m_is_signed(is_signed),
    m_bv_size(bv_size),
    m_is_array(false),
    m_is_func(false),
    m_is_tuple(false),
    m_sorts{ nullptr },
    m_sorts_size(0) {}

  template<size_t N>
  constexpr Sort(
    bool is_func,
    bool is_array,
    bool is_tuple,
    const Sort* const (&sorts)[N])
  : m_is_bool(false),
    m_is_int(false),
    m_is_real(false),
    m_is_bv(false),
    m_is_signed(false),
    m_bv_size(0),
    m_is_func(is_func),
    m_is_array(is_array),
    m_is_tuple(is_tuple),
    m_sorts{sorts},
    m_sorts_size(N) {}

  Sort(const Sort&) = delete;

  constexpr Sort(Sort&& other)
  : m_is_bool(other.m_is_bool),
    m_is_int(other.m_is_int),
    m_is_real(other.m_is_real),
    m_is_bv(other.m_is_bv),
    m_is_signed(other.m_is_signed),
    m_bv_size(other.m_bv_size),
    m_is_func(other.m_is_func),
    m_is_array(other.m_is_array),
    m_is_tuple(other.m_is_tuple),
    m_sorts(std::move(other.m_sorts)),
    m_sorts_size(other.m_sorts_size) {}

  constexpr bool is_bool()   const { return m_is_bool;   }
  constexpr bool is_int()    const { return m_is_int;    }
  constexpr bool is_real()   const { return m_is_real;   }
  constexpr bool is_bv()     const { return m_is_bv;     }
  constexpr bool is_signed() const { return m_is_signed; }
  constexpr size_t bv_size() const { return m_bv_size;   }

  constexpr bool is_func()   const { return m_is_func;   }
  constexpr bool is_array()  const { return m_is_array;  }

  constexpr const Sort& sorts(size_t index) const
  {
    return check_sorts_index(index), *m_sorts[index];
  }

  constexpr size_t sorts_size() const { return m_sorts_size; }

  bool operator==(const Sort& other) const
  {
    // Most often we expect to encounter statically allocated sorts.
    return this == &other ? true :
      m_is_bool    == other.m_is_bool   &&
      m_is_int     == other.m_is_int    &&
      m_is_real    == other.m_is_real   &&
      m_is_bv      == other.m_is_bv     &&
      m_is_signed  == other.m_is_signed &&
      m_bv_size    == other.m_bv_size   &&
      m_is_func    == other.m_is_func   &&
      m_is_array   == other.m_is_array  &&
      m_is_tuple   == other.m_is_tuple  &&
      m_sorts      == other.m_sorts     &&
      m_sorts_size == other.m_sorts_size;
  }
};

namespace internal {
  template<typename T>
  struct __Bv
  {
    static constexpr size_t bv_size()
    {
      return 8 * sizeof(T);
    }

    static constexpr Sort s_sort = Sort(
      false, false, false,
      std::is_integral<T>::value, std::is_signed<T>::value, bv_size());
  };

  template<typename T>
  constexpr Sort __Bv<T>::s_sort;

  template<typename T>
  struct __Math
  {
    static constexpr Sort s_sort = Sort(
      std::is_same<T, sort::Bool>::value,
      std::is_same<T, sort::Int>::value,
      std::is_same<T, sort::Real>::value,
      false, false, 0);
  };

  template<typename T>
  constexpr Sort __Math<T>::s_sort;

  template<typename T>
  struct __SortSwitch
  {
    typedef __Bv<T> Type;
  };

  template<>
  struct __SortSwitch<sort::Int>
  {
    typedef __Math<sort::Int> Type;
  };

  template<>
  struct __SortSwitch<sort::Bool>
  {
    typedef __Math<sort::Bool> Type;
  };

  template<>
  struct __SortSwitch<sort::Real>
  {
    typedef __Math<sort::Real> Type;
  };

  /* Array sort */
  template<typename Domain, typename Range>
  struct __SortSwitch<sort::Array<Domain, Range>>
  {
    typedef __Math<sort::Array<Domain, Range>> Type;
  };

  template<typename Domain, typename Range>
  struct __Math<sort::Array<Domain, Range>>
  {
    static constexpr const Sort* const s_sorts[2] = {
      &__SortSwitch<Domain>::Type::s_sort,
      &__SortSwitch<Range>::Type::s_sort };

    static constexpr Sort s_sort = Sort(false, true, false, s_sorts);
  };

  template<typename Domain, typename Range>
  constexpr const Sort* const __Math<sort::Array<Domain, Range>>::s_sorts[2];

  template<typename Domain, typename Range>
  constexpr Sort __Math<sort::Array<Domain, Range>>::s_sort;

  /* Function sort */
  template<typename... T>
  struct __SortSwitch<sort::Func<T...>>
  {
    typedef __Math<sort::Func<T...>> Type;
  };

  template<size_t N, const Sort* const... sorts>
  struct __SortArray
  {
  };

  template<typename... T>
  struct __FuncSort
  {
  };

  // Function sort: base case
  template<size_t N, const Sort* const... sorts>
  struct __FuncSort<__SortArray<N, sorts...>>
  {
    static constexpr const Sort* const s_sorts[N] = {sorts...};
    static constexpr const Sort* const (&result())[N]
    {
      return s_sorts;
    }
  };

  template<typename T, typename... U, size_t N, const Sort* const... sorts>
  struct __FuncSort<__SortArray<N, sorts...>, T, U...>
  {
    // Function sort: prepend sort for T and then recurse on U...
    typedef __FuncSort<__SortArray<N, sorts...,
      &__SortSwitch<T>::Type::s_sort>, U...> Build;

    static constexpr const Sort* const (&result())[N]
    {
      return Build::result();
    }
  };

  // Function sort: allocate memory for sort array at compile-time
  template<size_t N, const Sort* const... sorts>
  constexpr const Sort* const __FuncSort<__SortArray<N, sorts...>>::s_sorts[N];

  // Function sort: T is first function argument, U are additional ones
  template<typename T, typename... U>
  struct __Math<sort::Func<T, U...>>
  {
    static constexpr size_t N = sizeof...(U) + 1;
    static constexpr Sort s_sort = Sort(true, false, false,
      __FuncSort<__SortArray<N, &__SortSwitch<T>::Type::s_sort>, U...>::result());
  };

  template<typename T, typename... U>
  constexpr Sort __Math<sort::Func<T, U...>>::s_sort;

  // Return statically allocated type information about T
  template<typename T>
  static constexpr const Sort& sort()
  {
    return __SortSwitch<T>::Type::s_sort;
  }
};

// Return dynamically allocated sort, use at own risk
const Sort& bv_sort(bool is_signed, size_t size);

class UnsafeDecl
{
private:
  const std::string m_symbol;
  const Sort& m_sort;

public:
  // Allocate sort statically!
  UnsafeDecl(
    const std::string& symbol,
    const Sort& sort)
  : m_symbol(symbol),
    m_sort(sort) {}

  // Allocate sort statically!
  UnsafeDecl(
    std::string&& symbol,
    const Sort& sort)
  : m_symbol(std::move(symbol)),
    m_sort(sort) {}

  UnsafeDecl(const UnsafeDecl& other)
  : m_symbol(other.m_symbol),
    m_sort(other.m_sort) {}

  UnsafeDecl(UnsafeDecl&& other)
  : m_symbol(std::move(other.m_symbol)),
    m_sort(other.m_sort) {}

  virtual ~UnsafeDecl() {}

  const std::string& symbol() const
  {
    return m_symbol;
  }

  const Sort& sort() const
  {
    return m_sort;
  }

  bool operator==(const UnsafeDecl& other) const
  {
    if (this == &other) {
      return true;
    }

    return m_symbol == other.m_symbol and &m_sort == &other.m_sort;
  }
};

template<typename T>
class Decl : public UnsafeDecl 
{
public:
  Decl(const std::string& symbol)
  : UnsafeDecl(symbol, internal::sort<T>()) {}

  Decl(std::string&& symbol)
  : UnsafeDecl(std::move(symbol), internal::sort<T>()) {}

  Decl(const Decl& other)
  : UnsafeDecl(other) {}

  Decl(Decl&& other)
  : UnsafeDecl(std::move(other)) {}
};

class UnsafeExpr;
typedef std::shared_ptr<const UnsafeExpr> UnsafeExprPtr;
typedef std::vector<UnsafeExprPtr> UnsafeExprPtrs;

template<typename T>
class Expr;

template<typename T>
using ExprPtr = std::shared_ptr<const Expr<T>>;

class Solver
{
#define SMT_ENCODE_BUILTIN_LITERAL(type)    \
private:                                    \
  virtual Error __encode_literal(           \
    const Sort& sort,                       \
    type literal)                           \
  {                                         \
    return UNSUPPORT_ERROR;                 \
  }                                         \
                                            \
public:                                     \
  Error encode_literal(                     \
    const Sort& sort,                       \
    type literal)                           \
  {                                         \
    return __encode_literal(sort, literal); \
  }                                         \

SMT_ENCODE_BUILTIN_LITERAL(bool)
SMT_ENCODE_BUILTIN_LITERAL(char)
SMT_ENCODE_BUILTIN_LITERAL(signed char)
SMT_ENCODE_BUILTIN_LITERAL(unsigned char)
SMT_ENCODE_BUILTIN_LITERAL(wchar_t)
SMT_ENCODE_BUILTIN_LITERAL(char16_t)
SMT_ENCODE_BUILTIN_LITERAL(char32_t)
SMT_ENCODE_BUILTIN_LITERAL(short)
SMT_ENCODE_BUILTIN_LITERAL(unsigned short)
SMT_ENCODE_BUILTIN_LITERAL(int)
SMT_ENCODE_BUILTIN_LITERAL(unsigned int)
SMT_ENCODE_BUILTIN_LITERAL(long)
SMT_ENCODE_BUILTIN_LITERAL(unsigned long)
SMT_ENCODE_BUILTIN_LITERAL(long long)
SMT_ENCODE_BUILTIN_LITERAL(unsigned long long)

private:
  virtual Error __encode_constant(
    const UnsafeDecl& decl) = 0;

  virtual Error __encode_func_app(
    const UnsafeDecl& func_decl,
    const size_t arity,
    const UnsafeExprPtr* const arg_ptrs) = 0;

  virtual Error __encode_const_array(
    const Sort& sort,
    UnsafeExprPtr init_ptr) = 0;

  virtual Error __encode_array_select(
    UnsafeExprPtr array_ptr,
    UnsafeExprPtr index_ptr) = 0;

  virtual Error __encode_array_store(
    UnsafeExprPtr array_ptr,
    UnsafeExprPtr index_ptr,
    UnsafeExprPtr value_ptr) = 0;

  virtual Error __encode_unary(
    Opcode opcode,
    const Sort& sort,
    UnsafeExprPtr expr_ptr) = 0;

  virtual Error __encode_binary(
    Opcode opcode,
    const Sort& sort,
    UnsafeExprPtr lptr,
    UnsafeExprPtr rptr) = 0;

  virtual Error __encode_nary(
    Opcode opcode,
    const Sort& sort,
    const UnsafeExprPtrs& ptrs) = 0;

  virtual void __reset() = 0;
  virtual void __push() = 0;
  virtual void __pop() = 0;
  virtual Error __add(ExprPtr<sort::Bool> condition) = 0;
  virtual Error __unsafe_add(UnsafeExprPtr condition) = 0;
  virtual CheckResult __check() = 0;

public:
  Error encode_constant(
    const UnsafeDecl& decl);

  Error encode_func_app(
    const UnsafeDecl& func_decl,
    const size_t arity,
    const UnsafeExprPtr* const arg_ptrs);

  Error encode_const_array(
    const Sort& sort,
    UnsafeExprPtr init_ptr);

  Error encode_array_select(
    UnsafeExprPtr array_ptr,
    UnsafeExprPtr index_ptr);

  Error encode_array_store(
    UnsafeExprPtr array_ptr,
    UnsafeExprPtr index_ptr,
    UnsafeExprPtr value_ptr);

  Error encode_unary(
    Opcode opcode,
    const Sort& sort,
    UnsafeExprPtr expr_ptr);

  Error encode_binary(
    Opcode opcode,
    const Sort& sort,
    UnsafeExprPtr lptr,
    UnsafeExprPtr rptr);

  Error encode_nary(
    Opcode opcode,
    const Sort& sort,
    const UnsafeExprPtrs& ptrs);

  void reset();

  void push();

  void pop();

  Error add(ExprPtr<sort::Bool> condition);
  Error unsafe_add(UnsafeExprPtr condition);

  CheckResult check();
};

class UnsafeExpr
{
private:
  const ExprKind m_expr_kind;
  const Sort& m_sort;

  virtual Error __encode(Solver&) const = 0;

protected:
  // Allocate sort statically!
  UnsafeExpr(ExprKind expr_kind, const Sort& sort)
  : m_expr_kind(expr_kind), m_sort(sort) {}

public:
  UnsafeExpr(const UnsafeExpr&) = delete;
  virtual ~UnsafeExpr() {}

  ExprKind expr_kind() const
  {
    return m_expr_kind;
  }

  const Sort& sort() const
  {
    return m_sort;
  }

  Error encode(Solver& solver) const
  {
    return __encode(solver);
  }
};

template<typename T>
class Expr : public virtual UnsafeExpr
{
protected:
  Expr(ExprKind expr_kind)
  : UnsafeExpr(expr_kind, internal::sort<T>()) {}
};

namespace internal
{
  template<typename T>
  struct IsPrimitive :
    std::integral_constant<bool,
      std::is_integral<T>::value
      or std::is_same<sort::Bool, T>::value
      or std::is_same<sort::Int, T>::value
      or std::is_same<sort::Real, T>::value>
  {};
}

template<typename T>
class UnsafeLiteralExpr : public virtual UnsafeExpr
{
private:
  const T m_literal;

  virtual Error __encode(Solver& solver) const override
  {
    return solver.encode_literal(UnsafeExpr::sort(), m_literal);
  }

public:
  // Allocate sort statically!
  UnsafeLiteralExpr(const Sort& sort, T literal)
  : UnsafeExpr(LITERAL_EXPR_KIND, sort),
    m_literal(literal) {}

  const T literal() const
  {
    return m_literal;
  }
};

template<typename T, typename U = T,
  typename Enable = typename std::enable_if<internal::IsPrimitive<T>::value>::type>
class LiteralExpr : public UnsafeLiteralExpr<U>, public Expr<T>
{
public:
  using UnsafeLiteralExpr<U>::literal;

  LiteralExpr(U literal)
  : UnsafeExpr(LITERAL_EXPR_KIND, internal::sort<T>()),
    UnsafeLiteralExpr<U>(internal::sort<T>(), literal),
    Expr<T>(LITERAL_EXPR_KIND) {}
};

class UnsafeConstantExpr : public virtual UnsafeExpr
{
private:
  const UnsafeDecl m_decl;

  virtual Error __encode(Solver& solver) const override
  {
    return solver.encode_constant(m_decl);
  }

public:
  UnsafeConstantExpr(const UnsafeDecl& decl)
  : UnsafeExpr(CONSTANT_EXPR_KIND, decl.sort()),
    m_decl(decl) {}
};

template<typename T>
class ConstantExpr : public UnsafeConstantExpr, public Expr<T>
{
private:
  const Decl<T> m_decl;

public:
  ConstantExpr(const Decl<T>& decl)
  : UnsafeExpr(CONSTANT_EXPR_KIND, internal::sort<T>()),
    UnsafeConstantExpr(decl),
    Expr<T>(CONSTANT_EXPR_KIND),
    m_decl(decl) {}

  const Decl<T>& decl() const
  {
    return m_decl;
  }
};

namespace internal
{
  template<typename... T>
  struct ExprPtrFold;

  template<typename T>
  struct ExprPtrFold<T>
  {
    typedef std::tuple<ExprPtr<T>> Type;
  };

  template<typename T, typename... U>
  struct ExprPtrFold<T, U...>
  {
    typedef decltype(std::tuple_cat(std::make_tuple(std::declval<ExprPtr<T>>()),
      std::declval<typename ExprPtrFold<U...>::Type>())) Type;
  };

  template<typename... T>
  struct ExprPtrFoldExceptLast;

  template<typename T, typename U>
  struct ExprPtrFoldExceptLast<T, U>
  {
    typedef std::tuple<ExprPtr<T>> Type;
  };

  template<typename T, typename... U>
  struct ExprPtrFoldExceptLast<T, U...>
  {
    typedef decltype(std::tuple_cat(std::make_tuple(std::declval<ExprPtr<T>>()),
      std::declval<typename ExprPtrFoldExceptLast<U...>::Type>())) Type;
  };

  template<size_t... seqs>
  struct __Sequence
  {
    using next = __Sequence<seqs..., sizeof...(seqs)>;
  };

  template<size_t N>
  struct __BuildSequence
  {
    using type = typename __BuildSequence<N - 1>::type::next;
  };

  template<>
  struct __BuildSequence<0>
  {
    using type = __Sequence<>;
  };

  template<typename Result, typename Tuple, size_t... seqs>
  std::array<Result, std::tuple_size<Tuple>::value>
    __to_array(const Tuple& tuple, __Sequence<seqs...>)
  {
    return {{ std::get<seqs>(tuple)... }};
  }

  template<typename Result, typename Tuple>
  std::array<Result, std::tuple_size<Tuple>::value> to_array(const Tuple& tuple)
  {
    constexpr size_t N = std::tuple_size<Tuple>::value;
    return __to_array<Result, Tuple>(tuple, typename __BuildSequence<N>::type());
  }
}

template<size_t arity>
class UnsafeFuncAppExpr : public virtual UnsafeExpr
{
private:
  const UnsafeDecl m_func_decl;
  const std::array<UnsafeExprPtr, arity> m_arg_ptrs;

  virtual Error __encode(Solver& solver) const override
  {
    return solver.encode_func_app(m_func_decl, arity, m_arg_ptrs.data());
  }

public:
  UnsafeFuncAppExpr(
    UnsafeDecl func_decl,
    std::array<UnsafeExprPtr, arity>&& arg_ptrs)
  : UnsafeExpr(FUNC_APP_EXPR_KIND, func_decl.sort().sorts(arity)),
    m_func_decl(func_decl),
    m_arg_ptrs(std::move(arg_ptrs)) {}
};

template<typename... T>
class FuncAppExpr
: public UnsafeFuncAppExpr<std::tuple_size<
    typename internal::ExprPtrFoldExceptLast<T...>::Type>::value>,
  public Expr<typename sort::Func<T...>::Range>
{
public:
  typedef typename internal::ExprPtrFoldExceptLast<T...>::Type DomainPtrs;

private:
  const Decl<sort::Func<T...>> m_func_decl;
  const DomainPtrs m_arg_ptrs;

public:
  FuncAppExpr(
    Decl<sort::Func<T...>> func_decl,
    DomainPtrs arg_ptrs)
  : UnsafeExpr(FUNC_APP_EXPR_KIND,
      internal::sort<typename sort::Func<T...>::Range>()),
    UnsafeFuncAppExpr<std::tuple_size<typename
        internal::ExprPtrFoldExceptLast<T...>::Type>::value>(
      func_decl,
      internal::to_array<UnsafeExprPtr, DomainPtrs>(arg_ptrs)),
    Expr<typename sort::Func<T...>::Range>(FUNC_APP_EXPR_KIND),
    m_func_decl(func_decl),
    m_arg_ptrs(arg_ptrs) {}

  const Decl<sort::Func<T...>>& func_decl() const
  {
    return m_func_decl;
  }

  const DomainPtrs& arg_ptrs() const
  {
    return m_arg_ptrs;
  }
};

template<typename T>
inline UnsafeExprPtr literal(const Sort& sort, const T literal)
{
  return UnsafeExprPtr(new UnsafeLiteralExpr<T>(sort, literal));
}

template<typename T, typename U,
  typename Enable = typename std::enable_if<std::is_integral<U>::value>::type>
inline ExprPtr<T> literal(const U literal)
{
  return ExprPtr<T>(new LiteralExpr<T, U>(literal));
}

UnsafeExprPtr constant(const UnsafeDecl& decl);

template<typename T>
ExprPtr<T> constant(const Decl<T>& decl)
{
  return ExprPtr<T>(new ConstantExpr<T>(decl));
}

template<typename T>
ExprPtr<T> constant(Decl<T>&& decl)
{
  return ExprPtr<T>(new ConstantExpr<T>(std::move(decl)));
}

UnsafeExprPtr apply(UnsafeDecl func_decl, UnsafeExprPtr arg_ptr);

UnsafeExprPtr apply(
  UnsafeDecl func_decl,
  UnsafeExprPtr larg_ptr,
  UnsafeExprPtr rarg_ptr);

// unary function application
template<typename Domain, typename Range, typename T,
  typename Enable = typename std::enable_if<std::is_integral<T>::value>::type>
ExprPtr<Range> apply(
  Decl<sort::Func<Domain, Range>> func_decl,
  const T arg)
{
  return apply(func_decl, literal<Domain, T>(arg));
}

// unary function application
template<typename Domain, typename Range>
ExprPtr<Range> apply(
  Decl<sort::Func<Domain, Range>> func_decl,
  ExprPtr<Domain> arg_ptr)
{
  return apply(func_decl, std::make_tuple(arg_ptr));
}

// binary function application
template<typename T, typename U, typename Range>
ExprPtr<Range> apply(
  Decl<sort::Func<T, U, Range>> func_decl,
  ExprPtr<T> larg_ptr,
  ExprPtr<U> rarg_ptr)
{
  return apply(func_decl, std::make_tuple(larg_ptr, rarg_ptr));
}

// nary function application
template<typename... T>
ExprPtr<typename sort::Func<T...>::Range> apply(
  Decl<sort::Func<T...>> func_decl,
  typename FuncAppExpr<T...>::DomainPtrs arg_ptrs)
{
  return ExprPtr<typename sort::Func<T...>::Range>(
    new FuncAppExpr<T...>(func_decl, arg_ptrs));
}

template<typename T>
ExprPtr<T> any(const std::string& symbol)
{
  return constant(Decl<T>(symbol));
}

template<typename T>
ExprPtr<T> any(std::string&& symbol)
{
  return constant(Decl<T>(std::move(symbol)));
}

class UnsafeUnaryExpr : public virtual UnsafeExpr
{
private:
  const Opcode m_opcode;
  const UnsafeExprPtr m_operand_ptr;

  virtual Error __encode(Solver& solver) const override
  {
    return solver.encode_unary(m_opcode, UnsafeExpr::sort(), m_operand_ptr);
  }

public:
  // Allocate sort statically!
  UnsafeUnaryExpr(
    const Sort& sort,
    Opcode opcode,
    UnsafeExprPtr operand_ptr)
  : UnsafeExpr(UNARY_EXPR_KIND, sort),
    m_opcode(opcode),
    m_operand_ptr(operand_ptr)
  {
    assert(m_operand_ptr.get() != nullptr);
  }
};

template<Opcode opcode, typename T, typename U = T>
class UnaryExpr : public UnsafeUnaryExpr, public Expr<U>
{
private:
  const ExprPtr<T> m_operand_ptr;

public:
  UnaryExpr(ExprPtr<T> operand_ptr)
  : UnsafeExpr(UNARY_EXPR_KIND, internal::sort<U>()),
    UnsafeUnaryExpr(internal::sort<U>(), opcode, operand_ptr),
    Expr<U>(UNARY_EXPR_KIND),
    m_operand_ptr(operand_ptr) {}

  ExprPtr<T> operand_ptr() const
  {
    return m_operand_ptr;
  }
};

class UnsafeBinaryExpr : public virtual UnsafeExpr
{
private:
  const Opcode m_opcode;
  const UnsafeExprPtr m_loperand_ptr;
  const UnsafeExprPtr m_roperand_ptr;

  virtual Error __encode(Solver& solver) const override
  {
    return solver.encode_binary(m_opcode, UnsafeExpr::sort(),
      m_loperand_ptr, m_roperand_ptr);
  }

public:
  // Allocate sort statically!
  UnsafeBinaryExpr(
    const Sort& sort,
    Opcode opcode,
    UnsafeExprPtr loperand_ptr,
    UnsafeExprPtr roperand_ptr)
  : UnsafeExpr(BINARY_EXPR_KIND, sort),
    m_opcode(opcode),
    m_loperand_ptr(loperand_ptr),
    m_roperand_ptr(roperand_ptr)
  {
    assert(m_loperand_ptr.get() != nullptr);
    assert(m_roperand_ptr.get() != nullptr);
  }
};

template<Opcode opcode, typename T, typename U = T>
class BinaryExpr : public UnsafeBinaryExpr, public Expr<U>
{
private:
  const ExprPtr<T> m_loperand_ptr;
  const ExprPtr<T> m_roperand_ptr;

public:
  BinaryExpr(ExprPtr<T> loperand_ptr, ExprPtr<T> roperand_ptr)
  : UnsafeExpr(BINARY_EXPR_KIND, internal::sort<U>()),
    UnsafeBinaryExpr(internal::sort<U>(), opcode, loperand_ptr, roperand_ptr),
    Expr<U>(BINARY_EXPR_KIND),
    m_loperand_ptr(loperand_ptr),
    m_roperand_ptr(roperand_ptr) {}

  ExprPtr<T> loperand_ptr() const
  {
    return m_loperand_ptr;
  }

  ExprPtr<T> roperand_ptr() const
  {
    return m_roperand_ptr;
  }
};

template<typename T>
class ExprPtrs
{
private:
  template<Opcode opcode, typename U, typename V>
  friend class NaryExpr;

  UnsafeExprPtrs m_ptrs;

public:
  ExprPtrs(size_t count)
  : m_ptrs()
  {
    m_ptrs.reserve(count);
  }

  ExprPtrs(ExprPtrs&& other)
  : m_ptrs(std::move(other.m_ptrs)) {}

  void push_back(ExprPtr<T> ptr)
  {
    m_ptrs.push_back(ptr);
  }

  size_t size() const
  {
    return m_ptrs.size();
  }

  ExprPtr<T> at(size_t pos) const
  {
    return std::dynamic_pointer_cast<const Expr<T>>(m_ptrs.at(pos));
  }
};

class UnsafeNaryExpr : public virtual UnsafeExpr
{
private:
  const Opcode m_opcode;
  const UnsafeExprPtrs m_operand_ptrs;

  virtual Error __encode(Solver& solver) const override
  {
    return solver.encode_nary(m_opcode, UnsafeExpr::sort(),
      m_operand_ptrs);
  }

protected:
  const UnsafeExprPtrs& operand_ptrs() const
  {
    return m_operand_ptrs;
  }

public:
  // Sort must be statically allocated and
  // there must be at least one operand.
  UnsafeNaryExpr(
    const Sort& sort,
    Opcode opcode,
    UnsafeExprPtrs&& ptrs)
  : UnsafeExpr(NARY_EXPR_KIND, sort),
    m_opcode(opcode),
    m_operand_ptrs(std::move(ptrs))
  {
    assert(!m_operand_ptrs.empty());
  }

  // Sort must be statically allocated and
  // there must be at least one operand.
  UnsafeNaryExpr(
    const Sort& sort,
    Opcode opcode,
    const UnsafeExprPtrs& ptrs)
  : UnsafeExpr(NARY_EXPR_KIND, sort),
    m_opcode(opcode),
    m_operand_ptrs(ptrs)
  {
    assert(!m_operand_ptrs.empty());
  }
};

template<Opcode opcode, typename T, typename U = T>
class NaryExpr : public UnsafeNaryExpr, public Expr<U>
{
public:
  // There must be at least one operand.
  NaryExpr(ExprPtrs<T>&& operand_ptrs)
  : UnsafeExpr(NARY_EXPR_KIND, internal::sort<U>()),
    UnsafeNaryExpr(internal::sort<U>(), opcode,
      std::move(operand_ptrs.m_ptrs)),
    Expr<U>(NARY_EXPR_KIND) {}

  // There must be at least one operand.
  NaryExpr(const ExprPtrs<T>& operand_ptrs)
  : UnsafeExpr(NARY_EXPR_KIND, internal::sort<U>()),
    UnsafeNaryExpr(internal::sort<U>(), opcode, operand_ptrs.m_ptrs),
    Expr<U>(NARY_EXPR_KIND) {}

  size_t size() const
  {
    return UnsafeNaryExpr::operand_ptrs().size();
  }

  ExprPtr<T> operand_ptr(size_t pos) const
  {
    return std::dynamic_pointer_cast<const Expr<T>>(
      UnsafeNaryExpr::operand_ptrs().at(pos));
  }
};

UnsafeExprPtr distinct(UnsafeExprPtrs&& ptrs);

template<typename T>
ExprPtr<sort::Bool> distinct(ExprPtrs<T>&& ptrs)
{
  return ExprPtr<sort::Bool>(new NaryExpr<NEQ, T, sort::Bool>(
    std::move(ptrs)));
}

class UnsafeConstArrayExpr : public virtual UnsafeExpr
{
private:
  const UnsafeExprPtr m_init_ptr;

  virtual Error __encode(Solver& solver) const override
  {
    return solver.encode_const_array(UnsafeExpr::sort(), m_init_ptr);
  }

public:
  // Allocate sort statically!
  UnsafeConstArrayExpr(const Sort& sort, UnsafeExprPtr init_ptr)
  : UnsafeExpr(CONST_ARRAY_EXPR_KIND, sort),
    m_init_ptr(init_ptr)
  {
    assert(m_init_ptr.get() != nullptr);
  }
};

template<typename Domain, typename Range>
class ConstArrayExpr
: public UnsafeConstArrayExpr, public Expr<sort::Array<Domain, Range>>
{
private:
  const ExprPtr<Range> m_init_ptr;

public:
  ConstArrayExpr(ExprPtr<Range> init_ptr)
  : UnsafeExpr(CONST_ARRAY_EXPR_KIND,
      internal::sort<sort::Array<Domain, Range>>()),
    UnsafeConstArrayExpr(internal::sort<sort::Array<Domain, Range>>(), init_ptr),
    Expr<sort::Array<Domain, Range>>(CONST_ARRAY_EXPR_KIND),
    m_init_ptr(init_ptr) {}

  ExprPtr<Range> init_ptr() const
  {
    return m_init_ptr;
  }
};

class UnsafeArraySelectExpr : public virtual UnsafeExpr
{
private:
  const UnsafeExprPtr m_array_ptr;
  const UnsafeExprPtr m_index_ptr;

  virtual Error __encode(Solver& solver) const override
  {
    return solver.encode_array_select(m_array_ptr, m_index_ptr);
  }

public:
  UnsafeArraySelectExpr(
    UnsafeExprPtr array_ptr,
    UnsafeExprPtr index_ptr)
  : UnsafeExpr(ARRAY_SELECT_EXPR_KIND, array_ptr->sort().sorts(1)),
    m_array_ptr(array_ptr),
    m_index_ptr(index_ptr)
  {
    assert(m_array_ptr.get() != nullptr);
    assert(m_index_ptr.get() != nullptr);
  }
};

template<typename Domain, typename Range>
class ArraySelectExpr : public UnsafeArraySelectExpr, public Expr<Range>
{
private:
  const ExprPtr<sort::Array<Domain, Range>> m_array_ptr;
  const ExprPtr<Domain> m_index_ptr;

public:
  ArraySelectExpr(
    ExprPtr<sort::Array<Domain, Range>> array_ptr,
    ExprPtr<Domain> index_ptr)
  : UnsafeExpr(ARRAY_SELECT_EXPR_KIND, internal::sort<Range>()),
    UnsafeArraySelectExpr(array_ptr, index_ptr),
    Expr<Range>(ARRAY_SELECT_EXPR_KIND),
    m_array_ptr(array_ptr),
    m_index_ptr(index_ptr) {}

  ExprPtr<sort::Array<Domain, Range>> array_ptr() const
  {
    return m_array_ptr;
  }

  ExprPtr<Domain> index_ptr() const
  {
    return m_index_ptr;
  }
};

class UnsafeArrayStoreExpr : public virtual UnsafeExpr
{
private:
  const UnsafeExprPtr m_array_ptr;
  const UnsafeExprPtr m_index_ptr;
  const UnsafeExprPtr m_value_ptr;

  virtual Error __encode(Solver& solver) const override
  {
    return solver.encode_array_store(m_array_ptr, m_index_ptr, m_value_ptr);
  }

public:
  // Allocate sort statically!
  UnsafeArrayStoreExpr(
    UnsafeExprPtr array_ptr,
    UnsafeExprPtr index_ptr,
    UnsafeExprPtr value_ptr)
  : UnsafeExpr(ARRAY_STORE_EXPR_KIND, array_ptr->sort()),
    m_array_ptr(array_ptr),
    m_index_ptr(index_ptr),
    m_value_ptr(value_ptr)
  {
    assert(m_array_ptr.get() != nullptr);
    assert(m_index_ptr.get() != nullptr);
    assert(m_value_ptr.get() != nullptr);
  }
};

template<typename Domain, typename Range>
class ArrayStoreExpr
: public UnsafeArrayStoreExpr, public Expr<sort::Array<Domain, Range>>
{
private:
  const ExprPtr<sort::Array<Domain, Range>> m_array_ptr;
  const ExprPtr<Domain> m_index_ptr;
  const ExprPtr<Range> m_value_ptr;

public:
  ArrayStoreExpr(
    ExprPtr<sort::Array<Domain, Range>> array_ptr,
    ExprPtr<Domain> index_ptr,
    ExprPtr<Range> value_ptr)
  : UnsafeExpr(ARRAY_STORE_EXPR_KIND,
      internal::sort<sort::Array<Domain, Range>>()),
    UnsafeArrayStoreExpr(
      array_ptr,
      index_ptr,
      value_ptr),
    Expr<sort::Array<Domain, Range>>(ARRAY_STORE_EXPR_KIND),
    m_array_ptr(array_ptr),
    m_index_ptr(index_ptr),
    m_value_ptr(value_ptr) {}

  ExprPtr<sort::Array<Domain, Range>> array_ptr() const
  {
    return m_array_ptr;
  }

  ExprPtr<Domain> index_ptr() const
  {
    return m_index_ptr;
  }

  ExprPtr<Range> value_ptr() const
  {
    return m_value_ptr;
  }
};

UnsafeExprPtr select(UnsafeExprPtr array_ptr, UnsafeExprPtr index_ptr);

template<typename Domain, typename Range>
ExprPtr<Range> select(
  ExprPtr<sort::Array<Domain, Range>> array_ptr,
  ExprPtr<Domain> index_ptr)
{
  return ExprPtr<Range>(
    new ArraySelectExpr<Domain, Range>(array_ptr, index_ptr));
}

UnsafeExprPtr store(
  UnsafeExprPtr array_ptr,
  UnsafeExprPtr index_ptr,
  UnsafeExprPtr value_ptr);

template<typename Domain, typename Range>
ExprPtr<sort::Array<Domain, Range>> store(
  ExprPtr<sort::Array<Domain, Range>> array_ptr,
  ExprPtr<Domain> index_ptr,
  ExprPtr<Range> value_ptr)
{
  return ExprPtr<sort::Array<Domain, Range>>(
    new ArrayStoreExpr<Domain, Range>(array_ptr, index_ptr, value_ptr));
}

UnsafeExprPtr implies(UnsafeExprPtr lptr, UnsafeExprPtr rptr);
ExprPtr<sort::Bool> implies(ExprPtr<sort::Bool> lptr, ExprPtr<sort::Bool> rptr);

template<Opcode opcode, typename T>
struct Identity;

template<>
struct Identity<LAND, sort::Bool>
{
  static ExprPtr<sort::Bool> expr_ptr;
};

}

#define SMT_BUILTIN_UNARY_OP(op, opcode)                                       \
  template<typename T>                                                         \
  inline smt::ExprPtr<T> operator op(smt::ExprPtr<T> ptr)                      \
  {                                                                            \
    return smt::ExprPtr<T>(new smt::UnaryExpr<smt::opcode, T>(ptr));           \
  }                                                                            \

#define SMT_BUILTIN_BINARY_OP(op, opcode)                                      \
  template<typename T>                                                         \
  inline smt::ExprPtr<T> operator op(smt::ExprPtr<T> lptr,                     \
    smt::ExprPtr<T> rptr)                                                      \
  {                                                                            \
    return smt::ExprPtr<T>(new smt::BinaryExpr<smt::opcode, T>(lptr, rptr));   \
  }                                                                            \
  template<typename T, typename U>                                             \
  inline smt::ExprPtr<T> operator op(smt::ExprPtr<T> lptr, const U rarg)       \
  {                                                                            \
    return lptr op smt::literal<T, U>(rarg);                                   \
  }                                                                            \
  template<typename T, typename U>                                             \
  inline smt::ExprPtr<T> operator op(const U larg, smt::ExprPtr<T> rptr)\
  {                                                                            \
    return smt::literal<T, U>(larg) op rptr;                                   \
  }                                                                            \

#define SMT_BUILTIN_BINARY_REL(op, opcode)                                     \
  template<typename T>                                                         \
  inline smt::ExprPtr<smt::sort::Bool> operator op(smt::ExprPtr<T> lptr,       \
    smt::ExprPtr<T> rptr)                                                      \
  {                                                                            \
    return smt::ExprPtr<smt::sort::Bool>(                                      \
      new smt::BinaryExpr<smt::opcode, T, smt::sort::Bool>(lptr, rptr));       \
  }                                                                            \
  template<typename T, typename U>                                             \
  inline smt::ExprPtr<smt::sort::Bool> operator op(smt::ExprPtr<T> lptr,\
    const U rarg)                                                              \
  {                                                                            \
    return lptr op smt::literal<T, U>(rarg);                                   \
  }                                                                            \
  template<typename T, typename U>                                             \
  inline smt::ExprPtr<smt::sort::Bool> operator op(const U larg,               \
    smt::ExprPtr<T> rptr)                                                      \
  {                                                                            \
    return smt::literal<T, U>(larg) op rptr;                                   \
  }                                                                            \

SMT_BUILTIN_UNARY_OP(-, SUB)

SMT_BUILTIN_BINARY_OP(-, SUB)
SMT_BUILTIN_BINARY_OP(+, ADD)
SMT_BUILTIN_BINARY_OP(*, MUL)
SMT_BUILTIN_BINARY_OP(/, QUO)
SMT_BUILTIN_BINARY_OP(%, REM)

SMT_BUILTIN_BINARY_REL(<, LSS)
SMT_BUILTIN_BINARY_REL(>, GTR)
SMT_BUILTIN_BINARY_REL(!=, NEQ)
SMT_BUILTIN_BINARY_REL(<=, LEQ)
SMT_BUILTIN_BINARY_REL(>=, GEQ)
SMT_BUILTIN_BINARY_REL(==, EQL)

#define SMT_BUILTIN_BV_UNARY_OP(op, opcode)                                    \
  template<typename T>                                                         \
  inline smt::ExprPtr<T> operator op(smt::ExprPtr<T> ptr)                      \
  {                                                                            \
    return smt::ExprPtr<T>(new smt::UnaryExpr<smt::opcode, T>(ptr));           \
  }                                                                            \

#define SMT_BUILTIN_BV_BINARY_OP(op, opcode)                                   \
  template<typename T>                                                         \
  inline smt::ExprPtr<T> operator op(smt::ExprPtr<T> lptr,                     \
    smt::ExprPtr<T> rptr)                                                      \
  {                                                                            \
    return smt::ExprPtr<T>(new smt::BinaryExpr<smt::opcode, T>(lptr, rptr));   \
  }                                                                            \
  template<typename T>                                                         \
  inline smt::ExprPtr<T> operator op(smt::ExprPtr<T> lptr, const T rarg)       \
  {                                                                            \
    return lptr op smt::literal<T>(rarg);                                      \
  }                                                                            \
  template<typename T>                                                         \
  inline smt::ExprPtr<T> operator op(const T larg, smt::ExprPtr<T> rptr)       \
  {                                                                            \
    return smt::literal<T>(larg) op rptr;                                      \
  }                                                                            \

SMT_BUILTIN_BV_UNARY_OP(~, NOT)

SMT_BUILTIN_BV_BINARY_OP(&, AND)
SMT_BUILTIN_BV_BINARY_OP(|, OR)
SMT_BUILTIN_BV_BINARY_OP(^, XOR)

#define SMT_BUILTIN_BOOL_UNARY_OP(op, opcode)                                  \
  inline smt::ExprPtr<smt::sort::Bool> operator op(                            \
    smt::ExprPtr<smt::sort::Bool> ptr)                                         \
  {                                                                            \
    return smt::ExprPtr<smt::sort::Bool>(                                      \
      new smt::UnaryExpr<smt::opcode, smt::sort::Bool>(ptr));                  \
  }                                                                            \

#define SMT_BUILTIN_BOOL_BINARY_OP(op, opcode)                                 \
  inline smt::ExprPtr<smt::sort::Bool> operator op(                            \
    smt::ExprPtr<smt::sort::Bool> lptr, smt::ExprPtr<smt::sort::Bool> rptr)    \
  {                                                                            \
    return smt::ExprPtr<smt::sort::Bool>(                                      \
      new smt::BinaryExpr<smt::opcode, smt::sort::Bool>(lptr, rptr));          \
  }                                                                            \
  inline smt::ExprPtr<smt::sort::Bool> operator op(                            \
    smt::ExprPtr<smt::sort::Bool> lptr, const bool rarg)                       \
  {                                                                            \
    return lptr op smt::literal<smt::sort::Bool>(rarg);                        \
  }                                                                            \
  inline smt::ExprPtr<smt::sort::Bool> operator op(const bool larg,            \
    smt::ExprPtr<smt::sort::Bool> rptr)                                        \
  {                                                                            \
    return smt::literal<smt::sort::Bool>(larg) op rptr;                        \
  }                                                                            \

SMT_BUILTIN_BOOL_UNARY_OP(!, LNOT)

SMT_BUILTIN_BOOL_BINARY_OP(&&, LAND)
SMT_BUILTIN_BOOL_BINARY_OP(||, LOR)
SMT_BUILTIN_BOOL_BINARY_OP(==, EQL)
SMT_BUILTIN_BOOL_BINARY_OP(!=, NEQ)

#define SMT_UNSAFE_UNARY_OP(op, opcode)                                        \
  inline smt::UnsafeExprPtr operator op(smt::UnsafeExprPtr ptr)                \
  {                                                                            \
    return smt::UnsafeExprPtr(                                                 \
      new smt::UnsafeUnaryExpr(ptr->sort(), smt::opcode, ptr));                \
  }                                                                            \

#define SMT_UNSAFE_BINARY_OP(op, opcode)                                       \
  inline smt::UnsafeExprPtr operator op(smt::UnsafeExprPtr lptr,               \
    smt::UnsafeExprPtr rptr)                                                   \
  {                                                                            \
    return smt::UnsafeExprPtr(new smt::UnsafeBinaryExpr(                       \
      lptr->sort(), smt::opcode, lptr, rptr));                                 \
  }                                                                            \

#define SMT_UNSAFE_BINARY_REL(op, opcode)                                      \
  inline smt::UnsafeExprPtr operator op(smt::UnsafeExprPtr lptr,               \
    smt::UnsafeExprPtr rptr)                                                   \
  {                                                                            \
    return smt::UnsafeExprPtr(new smt::UnsafeBinaryExpr(                       \
      smt::internal::sort<smt::sort::Bool>(), smt::opcode, lptr, rptr));       \
  }                                                                            \

SMT_UNSAFE_UNARY_OP(-, SUB)
SMT_UNSAFE_UNARY_OP(~, NOT)
SMT_UNSAFE_UNARY_OP(!, LNOT)

SMT_UNSAFE_BINARY_OP(&&, LAND)
SMT_UNSAFE_BINARY_OP(||, LOR)

SMT_UNSAFE_BINARY_OP(-, SUB)
SMT_UNSAFE_BINARY_OP(+, ADD)
SMT_UNSAFE_BINARY_OP(*, MUL)
SMT_UNSAFE_BINARY_OP(/, QUO)
SMT_UNSAFE_BINARY_OP(%, REM)

SMT_UNSAFE_BINARY_OP(&, AND)
SMT_UNSAFE_BINARY_OP(|, OR)
SMT_UNSAFE_BINARY_OP(^, XOR)

SMT_UNSAFE_BINARY_REL(<, LSS)
SMT_UNSAFE_BINARY_REL(>, GTR)
SMT_UNSAFE_BINARY_REL(!=, NEQ)
SMT_UNSAFE_BINARY_REL(<=, LEQ)
SMT_UNSAFE_BINARY_REL(>=, GEQ)
SMT_UNSAFE_BINARY_REL(==, EQL)

#endif
