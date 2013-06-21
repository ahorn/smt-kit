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
#include <cstdint>
#include <cassert>
#include <stdexcept>
#include <type_traits>

namespace smt
{

/// Standard acronyms of logic declarations in SMT-LIB 2.0

/// \see_also http://smtlib.cs.uiowa.edu/logics.html
enum Logic : unsigned
{
  /// Closed formulas built over arbitrary expansions of the Ints and ArraysEx
  /// signatures with free sort and function symbols, but with the following 
  /// restrictions:
  /// - all terms of sort Int are linear, that is, have no occurrences of the
  ///  function symbols *, /, div, mod, and abs
  /// - all array terms have sort (Array Int Int).
  ///
  /// This logic extends QF_AUFLIA by allowing quantifiers.
  AUFLIA_LOGIC,

  /// Closed formulas built over arbitrary expansions of the Reals_Ints and
  /// ArraysEx signatures with free sort and function symbols, but with the
  /// following restrictions:
  /// - all terms of sort Int are linear, that is, have no occurrences of the
  ///   function symbols *, /, div, mod, and abs
  /// - all terms of sort Real are linear, that is, have no occurrences of the
  ///  function symbols * and /
  /// - all array terms have sort 
  ///  (Array Int Real) or 
  ///  (Array Int (Array Int Real)).
  AUFLIRA_LOGIC,

  /// Closed formulas built over arbitrary expansions of the Reals_Ints and
  /// ArraysEx signatures with free sort and function symbols.
  AUFNIRA_LOGIC,

  /// Closed formulas built over arbitrary expansions of the Reals signature
  /// with free constant symbols, but containing only linear atoms, that is, 
  /// atoms with no occurrences of the function symbols * and /
  LRA_LOGIC,

  /// Closed quantifier-free formulas built over the Fixed_Size_BitVectors and
  /// ArraysEx signatures, with the restriction that all array terms have sort of
  /// the form (Array (_ BitVec i) (_ BitVec j)) for some i, j > 0.
  QF_ABV_LOGIC,

  /// Closed quantifier-free formulas built over an arbitrary expansion of the
  /// Fixed_Size_BitVectors and ArraysEx signatures with free sort and function
  /// symbols, but with the restriction that all array terms have sort of the 
  /// form (Array (_ BitVec i) (_ BitVec j)) for some i, j > 0.
  QF_AUFBV_LOGIC,

  /// Closed quantifier-free formulas built over arbitrary expansions of
  /// the Fixed_Size_BitVectors signature with free sort and function symbols.
  QF_UFBV_LOGIC,

  /// Closed quantifier-free formulas built over arbitrary expansions of the
  /// Ints and ArraysEx signatures with free sort and function symbols, but
  /// with the following restrictions:
  /// - all terms of sort Int are linear, that is, have no occurrences of the
  ///  function symbols *, /, div, mod, and abs
  /// - all array terms have sort (Array Int Int).
  QF_AUFLIA_LOGIC,

  /// Closed quantifier-free formulas built over an arbitrary expansion of
  /// the ArraysEx signature with free sort and constant symbols.
  QF_AX_LOGIC,

  /// Closed quantifier-free formulas built over an arbitrary expansion of the
  /// Fixed_Size_BitVectors signature with free constant symbols over the sorts
  /// (_ BitVec m) for 0 < m.  Formulas in ite terms must satisfy the same
  /// restriction as well, with the exception that they need not be closed 
  /// (because they may be in the scope of a let binder).
  QF_BV_LOGIC,

  /// Closed quantifier-free formulas with atoms of the form:
  /// - q
  /// - (op (- x y) n),
  /// - (op (- x y) (- n)), or
  /// - (op x y)
  /// where
  ///  - q is a variable or free constant symbol of sort Bool,
  ///  - op is <, <=, >, >=, =, or distinct,
  ///  - x, y are free constant symbols of sort Int, 
  ///  - n is a numeral. 
  QF_IDL_LOGIC,

  /// Closed quantifier-free formulas with atoms of the form:
  /// - p
  /// - (op (- x y) c),
  /// - (op x y),
  /// - (op (- (+ x ... x) (+ y ... y)) c) with n > 1 occurrences of x and of y,
  /// where
  ///  - p is a variable or free constant symbol of sort Bool,
  ///  - c is an expression of the form m or (- m) for some numeral m,
  ///  - op is <, <=, >, >=, =, or distinct,
  ///  - x, y are free constant symbols of sort Real. 
  QF_RDL_LOGIC,

  /// Closed quantifier-free formulas built over an arbitrary expansion of the
  /// Ints signature with free constant symbols, but whose terms of sort Int 
  /// are all linear, that is, have no occurrences of the function symbols
  /// *, /, div, mod, and abs
  QF_LIA_LOGIC,

  /// Closed quantifier-free formulas built over arbitrary expansions of 
  /// the Reals signature with free constant symbols, but containing only
  /// linear atoms, that is, atoms with no occurrences of the function
  /// symbols * and /
  QF_LRA_LOGIC,

  /// Closed quantifier-free formulas built over an arbitrary expansion of the
  /// Ints signature with free constant symbols.
  QF_NIA_LOGIC,

  /// Closed quantifier-free formulas built over arbitrary expansions of 
  /// the Reals signature with free constant symbols.
  QF_NRA_LOGIC,

  /// Closed quantifier-free formulas built over an arbitrary expansion of
  /// the Core signature with free sort and function symbols.
  QF_UF_LOGIC,

  /// Closed quantifier-free formulas built over an arbitrary expansion with 
  /// free sort and function symbols of the signature consisting of 
  /// - all the sort and function symbols of Core and
  /// - the following symbols of Int:
  ///
  ///   :sorts ((Int 0))
  ///  :funs ((NUMERAL Int) 
  ///         (- Int Int Int)
  ///         (+ Int Int Int) 
  ///         (<= Int Int Bool)
  ///         (< Int Int Bool)
  ///         (>= Int Int Bool)
  ///         (> Int Int Bool)
  ///        )
  ///
  /// Additionally, for every term of the form (op t1 t2) with op in {+, -}, 
  /// at least one of t1 and t2 is a numeral.
  QF_UFIDL_LOGIC,

  /// Closed quantifier-free formulas built over arbitrary expansions of the
  /// Ints signatures with free sort and function symbols, but with the 
  /// following restrictions:
  /// - all terms of sort Int are linear, that is, have no occurrences of the
  ///   function symbols *, /, div, mod, and abs
  QF_UFLIA_LOGIC,

  /// Closed quantifier-free formulas built over arbitrary expansions of the 
  /// Reals signature with free sort and function symbols, but containing 
  /// only linear atoms, that is, atoms with no occurrences of the function
  /// symbols * and /
  QF_UFLRA_LOGIC,

  /// Closed quantifier-free formulas built over arbitrary expansions of 
  /// the Reals signature with free sort and function symbols.
  QF_UFNRA_LOGIC,

  /// Closed formulas built over arbitrary expansions of the Reals signature 
  /// with free sort and function symbols, but containing only linear atoms, 
  /// that is, atoms with no occurrences of the function symbols * and /
  UFLRA_LOGIC,

  /// Closed formulas built over an arbitrary expansion of the Ints signature
  /// with free sort and function symbols.
  UFNIA_LOGIC,
};

struct Logics
{
  // index must be a logic acronym enum value
  static constexpr const char* const acronyms[] =
  {
    "AUFLIA",
    "AUFLIRA",
    "AUFNIRA",
    "LRA",
    "QF_ABV",
    "QF_AUFBV",
    "QF_UFBV",
    "QF_AUFLIA",
    "QF_AX",
    "QF_BV",
    "QF_IDL",
    "QF_RDL",
    "QF_LIA",
    "QF_LRA",
    "QF_NIA",
    "QF_NRA",
    "QF_UF",
    "QF_UFIDL",
    "QF_UFLIA",
    "QF_UFLRA",
    "QF_UFNRA",
    "UFLRA",
    "UFNIA"
  };

  Logics() = delete;
};

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

// Contingencies that an implementation of the API must always consider
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
    m_sorts(other.m_sorts),
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
  // Allocate sort statically and use globally unique symbol names!
  UnsafeDecl(
    const std::string& symbol,
    const Sort& sort)
  : m_symbol(symbol),
    m_sort(sort) {}

  // Allocate sort statically and use globally unique symbol names!
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
  // Use globally unique symbol names!
  Decl(const std::string& symbol)
  : UnsafeDecl(symbol, internal::sort<T>()) {}

  // Use globally unique symbol names!
  Decl(std::string&& symbol)
  : UnsafeDecl(std::move(symbol), internal::sort<T>()) {}

  Decl(const Decl& other)
  : UnsafeDecl(other) {}

  Decl(Decl&& other)
  : UnsafeDecl(std::move(other)) {}
};

class UnsafeTerm;
typedef std::vector<UnsafeTerm> UnsafeTerms;

template<typename T>
class Term;

class Solver
{
public:
  struct Stats
  {
    unsigned constants;
    unsigned func_apps;
    unsigned array_selects;
    unsigned array_stores;
    unsigned unary_ops;
    unsigned binary_ops;
    unsigned nary_ops;
    unsigned equalities;
    unsigned disequalities;
    unsigned inequalities;
    unsigned implications;
    unsigned conjunctions;
    unsigned disjunctions;
  };

private:
  Stats m_stats;

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
    const UnsafeTerm* const args) = 0;

  virtual Error __encode_const_array(
    const Sort& sort,
    const UnsafeTerm& init) = 0;

  virtual Error __encode_array_select(
    const UnsafeTerm& array,
    const UnsafeTerm& index) = 0;

  virtual Error __encode_array_store(
    const UnsafeTerm& array,
    const UnsafeTerm& index,
    const UnsafeTerm& value) = 0;

  virtual Error __encode_unary(
    Opcode opcode,
    const Sort& sort,
    const UnsafeTerm& arg) = 0;

  virtual Error __encode_binary(
    Opcode opcode,
    const Sort& sort,
    const UnsafeTerm& larg,
    const UnsafeTerm& rarg) = 0;

  virtual Error __encode_nary(
    Opcode opcode,
    const Sort& sort,
    const UnsafeTerms& args) = 0;

  virtual void __reset() = 0;
  virtual void __push() = 0;
  virtual void __pop() = 0;
  virtual Error __add(const Term<sort::Bool>& condition) = 0;
  virtual Error __unsafe_add(const UnsafeTerm& condition) = 0;
  virtual CheckResult __check() = 0;

protected:
  // Subclasses must have a constructor with a Logic enum value as argument
  Solver()
  : m_stats{0} {}

public:
  Error encode_constant(
    const UnsafeDecl& decl);

  Error encode_func_app(
    const UnsafeDecl& func_decl,
    const size_t arity,
    const UnsafeTerm* const args);

  Error encode_const_array(
    const Sort& sort,
    const UnsafeTerm& init);

  Error encode_array_select(
    const UnsafeTerm& array,
    const UnsafeTerm& index);

  Error encode_array_store(
    const UnsafeTerm& array,
    const UnsafeTerm& index,
    const UnsafeTerm& value);

  Error encode_unary(
    Opcode opcode,
    const Sort& sort,
    const UnsafeTerm& arg);

  Error encode_binary(
    Opcode opcode,
    const Sort& sort,
    const UnsafeTerm& larg,
    const UnsafeTerm& rarg);

  Error encode_nary(
    Opcode opcode,
    const Sort& sort,
    const UnsafeTerms& args);

  // Generic SMT formula statistics
  const Stats& stats()
  {
    return m_stats;
  }

  void reset();

  void push();

  void pop();

  void add(const Term<sort::Bool>& condition);
  void unsafe_add(const UnsafeTerm& condition);

  CheckResult check();

  virtual ~Solver() {}
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

/// shared but potentially not well-sorted SMT expression

/// All arithmetic and bit vector operators are overloaded.
class UnsafeTerm
{
private:
  std::shared_ptr<const UnsafeExpr> m_ptr;

public:
  UnsafeTerm()
  : m_ptr(nullptr) {}

  UnsafeTerm(const UnsafeExpr* ptr)
  : m_ptr(ptr) {}

  UnsafeTerm(std::shared_ptr<const UnsafeExpr>&& ptr)
  : m_ptr(std::move(ptr)) {}

  template<typename T>
  UnsafeTerm(const std::shared_ptr<const Expr<T>>& ptr)
  : m_ptr(ptr) {}

  UnsafeTerm(const UnsafeTerm& other)
  : m_ptr(other.m_ptr) {}

  UnsafeTerm(UnsafeTerm&& other)
  : m_ptr(std::move(other.m_ptr)) {}

  UnsafeTerm& operator=(const UnsafeTerm& other) 
  {
    m_ptr = other.m_ptr;
    return *this;
  }

  template<typename T>
  explicit operator Term<T>() const
  {
    return Term<T>(std::dynamic_pointer_cast<const Expr<T>>(m_ptr));
  }

  bool is_null() const
  {
    return m_ptr.get() == nullptr;
  }

  /// memory address of underlying SMT expression
  uintptr_t addr() const
  {
    return reinterpret_cast<uintptr_t>(m_ptr.get());
  }

  /// \pre !is_null()
  const UnsafeExpr& ref() const
  {
    assert(!is_null());
    return *m_ptr;
  }

  /// \pre !is_null()
  ExprKind expr_kind() const
  {
    assert(!is_null());
    return m_ptr->expr_kind();
  }

  /// \pre !is_null()
  const Sort& sort() const
  {
    assert(!is_null());
    return m_ptr->sort();
  }

  /// \internal \pre !is_null()
  Error encode(Solver& solver) const
  {
    assert(!is_null());
    return m_ptr->encode(solver);
  }
};

/// shared and well-sorted SMT expression 

/// Supported built-in operators depends on the type T.
template<typename T>
class Term
{
private:
  std::shared_ptr<const Expr<T>> m_ptr;

public:
  Term()
  : m_ptr(nullptr) {}

  Term(const Expr<T>* ptr)
  : m_ptr(ptr) {}

  Term(std::shared_ptr<const Expr<T>>&& ptr)
  : m_ptr(std::move(ptr)) {}

  Term(const Term& other)
  : m_ptr(other.m_ptr) {}

  Term(Term&& other)
  : m_ptr(std::move(other.m_ptr)) {}

  Term& operator=(const Term& other) 
  {
    m_ptr = other.m_ptr;
    return *this;
  }

  operator UnsafeTerm() const
  {
    return UnsafeTerm(m_ptr);
  }

  bool is_null() const
  {
    return m_ptr.get() == nullptr;
  }

  /// memory address of underlying SMT expression
  uintptr_t addr() const
  {
    return reinterpret_cast<uintptr_t>(m_ptr.get());
  }

  /// \pre !is_null()
  const Expr<T>& ref() const
  {
    assert(!is_null());
    return *m_ptr;
  }

  /// \pre !is_null()
  ExprKind expr_kind() const
  {
    assert(!is_null());
    return m_ptr->expr_kind();
  }

  /// \pre !is_null()
  const Sort& sort() const
  {
    assert(!is_null());
    return m_ptr->sort();
  }
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
  struct TermFold;

  template<typename T>
  struct TermFold<T>
  {
    typedef std::tuple<Term<T>> Type;
  };

  template<typename T, typename... U>
  struct TermFold<T, U...>
  {
    typedef decltype(std::tuple_cat(std::make_tuple(std::declval<Term<T>>()),
      std::declval<typename TermFold<U...>::Type>())) Type;
  };

  template<typename... T>
  struct TermFoldExceptLast;

  template<typename T, typename U>
  struct TermFoldExceptLast<T, U>
  {
    typedef std::tuple<Term<T>> Type;
  };

  template<typename T, typename... U>
  struct TermFoldExceptLast<T, U...>
  {
    typedef decltype(std::tuple_cat(std::make_tuple(std::declval<Term<T>>()),
      std::declval<typename TermFoldExceptLast<U...>::Type>())) Type;
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
  const std::array<UnsafeTerm, arity> m_args;

  virtual Error __encode(Solver& solver) const override
  {
    return solver.encode_func_app(m_func_decl, arity, m_args.data());
  }

public:
  UnsafeFuncAppExpr(
    UnsafeDecl func_decl,
    std::array<UnsafeTerm, arity>&& args)
  : UnsafeExpr(FUNC_APP_EXPR_KIND, func_decl.sort().sorts(arity)),
    m_func_decl(func_decl),
    m_args(std::move(args)) {}
};

template<typename... T>
class FuncAppExpr
: public UnsafeFuncAppExpr<std::tuple_size<
    typename internal::TermFoldExceptLast<T...>::Type>::value>,
  public Expr<typename sort::Func<T...>::Range>
{
public:
  typedef typename internal::TermFoldExceptLast<T...>::Type Args;

private:
  const Decl<sort::Func<T...>> m_func_decl;
  const Args m_args;

public:
  FuncAppExpr(
    Decl<sort::Func<T...>> func_decl,
    Args args)
  : UnsafeExpr(FUNC_APP_EXPR_KIND,
      internal::sort<typename sort::Func<T...>::Range>()),
    UnsafeFuncAppExpr<std::tuple_size<typename
        internal::TermFoldExceptLast<T...>::Type>::value>(
      func_decl,
      internal::to_array<UnsafeTerm, Args>(args)),
    Expr<typename sort::Func<T...>::Range>(FUNC_APP_EXPR_KIND),
    m_func_decl(func_decl),
    m_args(args) {}

  const Decl<sort::Func<T...>>& func_decl() const
  {
    return m_func_decl;
  }

  const Args& args() const
  {
    return m_args;
  }
};

template<typename T>
inline UnsafeTerm literal(const Sort& sort, const T literal)
{
  return UnsafeTerm(new UnsafeLiteralExpr<T>(sort, literal));
}

template<typename T, typename U,
  typename Enable = typename std::enable_if<std::is_integral<U>::value>::type>
inline Term<T> literal(const U literal)
{
  return Term<T>(new LiteralExpr<T, U>(literal));
}

UnsafeTerm constant(const UnsafeDecl& decl);

template<typename T>
Term<T> constant(const Decl<T>& decl)
{
  return Term<T>(new ConstantExpr<T>(decl));
}

template<typename T>
Term<T> constant(Decl<T>&& decl)
{
  return Term<T>(new ConstantExpr<T>(std::move(decl)));
}

UnsafeTerm apply(
  const UnsafeDecl& func_decl,
  const UnsafeTerm& arg);

UnsafeTerm apply(
  const UnsafeDecl& func_decl,
  const UnsafeTerm& larg,
  const UnsafeTerm& rarg);

// unary function application
template<typename Domain, typename Range, typename T,
  typename Enable = typename std::enable_if<std::is_integral<T>::value>::type>
Term<Range> apply(
  const Decl<sort::Func<Domain, Range>>& func_decl,
  const T arg)
{
  return apply(func_decl, literal<Domain, T>(arg));
}

// unary function application
template<typename Domain, typename Range>
Term<Range> apply(
  const Decl<sort::Func<Domain, Range>>& func_decl,
  const Term<Domain>& arg)
{
  return apply(func_decl, std::make_tuple(arg));
}

// binary function application
template<typename T, typename U, typename Range>
Term<Range> apply(
  const Decl<sort::Func<T, U, Range>>& func_decl,
  const Term<T>& larg,
  const Term<U>& rarg)
{
  return apply(func_decl, std::make_tuple(larg, rarg));
}

// nary function application
template<typename... T>
Term<typename sort::Func<T...>::Range> apply(
  const Decl<sort::Func<T...>>& func_decl,
  const typename FuncAppExpr<T...>::Args& args)
{
  return Term<typename sort::Func<T...>::Range>(
    new FuncAppExpr<T...>(func_decl, args));
}

// Use globally unique symbol names!
template<typename T>
Term<T> any(const std::string& symbol)
{
  return constant(Decl<T>(symbol));
}

// Use globally unique symbol names!
template<typename T>
Term<T> any(std::string&& symbol)
{
  return constant(Decl<T>(std::move(symbol)));
}

class UnsafeUnaryExpr : public virtual UnsafeExpr
{
private:
  const Opcode m_opcode;
  const UnsafeTerm m_operand;

  virtual Error __encode(Solver& solver) const override
  {
    return solver.encode_unary(m_opcode, UnsafeExpr::sort(), m_operand);
  }

public:
  // Allocate sort statically!
  UnsafeUnaryExpr(
    const Sort& sort,
    Opcode opcode,
    const UnsafeTerm& operand)
  : UnsafeExpr(UNARY_EXPR_KIND, sort),
    m_opcode(opcode),
    m_operand(operand)
  {
    assert(!m_operand.is_null());
  }
};

template<Opcode opcode, typename T, typename U = T>
class UnaryExpr : public UnsafeUnaryExpr, public Expr<U>
{
private:
  const Term<T> m_operand;

public:
  UnaryExpr(const Term<T>& operand)
  : UnsafeExpr(UNARY_EXPR_KIND, internal::sort<U>()),
    UnsafeUnaryExpr(internal::sort<U>(), opcode, operand),
    Expr<U>(UNARY_EXPR_KIND),
    m_operand(operand) {}

  const Term<T>& operand() const
  {
    return m_operand;
  }
};

class UnsafeBinaryExpr : public virtual UnsafeExpr
{
private:
  const Opcode m_opcode;
  const UnsafeTerm m_loperand;
  const UnsafeTerm m_roperand;

  virtual Error __encode(Solver& solver) const override
  {
    return solver.encode_binary(m_opcode, UnsafeExpr::sort(),
      m_loperand, m_roperand);
  }

public:
  // Allocate sort statically!
  UnsafeBinaryExpr(
    const Sort& sort,
    Opcode opcode,
    const UnsafeTerm& loperand,
    const UnsafeTerm& roperand)
  : UnsafeExpr(BINARY_EXPR_KIND, sort),
    m_opcode(opcode),
    m_loperand(loperand),
    m_roperand(roperand)
  {
    assert(!m_loperand.is_null());
    assert(!m_roperand.is_null());
  }
};

template<Opcode opcode, typename T, typename U = T>
class BinaryExpr : public UnsafeBinaryExpr, public Expr<U>
{
private:
  const Term<T> m_loperand;
  const Term<T> m_roperand;

public:
  BinaryExpr(
    const Term<T>& loperand,
    const Term<T>& roperand)
  : UnsafeExpr(BINARY_EXPR_KIND, internal::sort<U>()),
    UnsafeBinaryExpr(internal::sort<U>(), opcode, loperand, roperand),
    Expr<U>(BINARY_EXPR_KIND),
    m_loperand(loperand),
    m_roperand(roperand) {}

  const Term<T>& loperand() const
  {
    return m_loperand;
  }

  const Term<T>& roperand() const
  {
    return m_roperand;
  }
};

template<typename T>
class Terms
{
private:
  template<Opcode opcode, typename U, typename V>
  friend class NaryExpr;

  UnsafeTerms m_terms;

public:
  Terms(size_t count)
  : m_terms()
  {
    m_terms.reserve(count);
  }

  Terms(Terms&& other)
  : m_terms(std::move(other.m_terms)) {}

  void push_back(const Term<T>& term)
  {
    m_terms.push_back(term);
  }

  size_t size() const
  {
    return m_terms.size();
  }

  Term<T> at(size_t pos) const
  {
    return static_cast<const Term<T>>(m_terms.at(pos));
  }
};

class UnsafeNaryExpr : public virtual UnsafeExpr
{
private:
  const Opcode m_opcode;
  const UnsafeTerms m_operands;

  virtual Error __encode(Solver& solver) const override
  {
    return solver.encode_nary(m_opcode, UnsafeExpr::sort(),
      m_operands);
  }

protected:
  const UnsafeTerms& operands() const
  {
    return m_operands;
  }

public:
  // Sort must be statically allocated and
  // there must be at least one operand.
  UnsafeNaryExpr(
    const Sort& sort,
    Opcode opcode,
    UnsafeTerms&& operands)
  : UnsafeExpr(NARY_EXPR_KIND, sort),
    m_opcode(opcode),
    m_operands(std::move(operands))
  {
    assert(!m_operands.empty());
  }

  // Sort must be statically allocated and
  // there must be at least one operand.
  UnsafeNaryExpr(
    const Sort& sort,
    Opcode opcode,
    const UnsafeTerms& operands)
  : UnsafeExpr(NARY_EXPR_KIND, sort),
    m_opcode(opcode),
    m_operands(operands)
  {
    assert(!m_operands.empty());
  }
};

template<Opcode opcode, typename T, typename U = T>
class NaryExpr : public UnsafeNaryExpr, public Expr<U>
{
public:
  // There must be at least one operand.
  NaryExpr(Terms<T>&& operands)
  : UnsafeExpr(NARY_EXPR_KIND, internal::sort<U>()),
    UnsafeNaryExpr(internal::sort<U>(), opcode,
      std::move(operands.m_terms)),
    Expr<U>(NARY_EXPR_KIND) {}

  // There must be at least one operand.
  NaryExpr(const Terms<T>& operands)
  : UnsafeExpr(NARY_EXPR_KIND, internal::sort<U>()),
    UnsafeNaryExpr(internal::sort<U>(), opcode, operands.m_terms),
    Expr<U>(NARY_EXPR_KIND) {}

  size_t size() const
  {
    return UnsafeNaryExpr::operands().size();
  }

  Term<T> operand(size_t pos) const
  {
    return static_cast<const Term<T>>(UnsafeNaryExpr::operands().at(pos));
  }
};

UnsafeTerm distinct(UnsafeTerms&& terms);

template<typename T>
Term<sort::Bool> distinct(Terms<T>&& terms)
{
  return Term<sort::Bool>(new NaryExpr<NEQ, T, sort::Bool>(
    std::move(terms)));
}

class UnsafeConstArrayExpr : public virtual UnsafeExpr
{
private:
  const UnsafeTerm m_init;

  virtual Error __encode(Solver& solver) const override
  {
    return solver.encode_const_array(UnsafeExpr::sort(), m_init);
  }

public:
  // Allocate sort statically!
  UnsafeConstArrayExpr(const Sort& sort, const UnsafeTerm& init)
  : UnsafeExpr(CONST_ARRAY_EXPR_KIND, sort),
    m_init(init)
  {
    assert(!m_init.is_null());
  }
};

template<typename Domain, typename Range>
class ConstArrayExpr
: public UnsafeConstArrayExpr, public Expr<sort::Array<Domain, Range>>
{
private:
  const Term<Range> m_init;

public:
  ConstArrayExpr(const Term<Range>& init)
  : UnsafeExpr(CONST_ARRAY_EXPR_KIND,
      internal::sort<sort::Array<Domain, Range>>()),
    UnsafeConstArrayExpr(internal::sort<sort::Array<Domain, Range>>(), init),
    Expr<sort::Array<Domain, Range>>(CONST_ARRAY_EXPR_KIND),
    m_init(init) {}

  const Term<Range>& init() const
  {
    return m_init;
  }
};

class UnsafeArraySelectExpr : public virtual UnsafeExpr
{
private:
  const UnsafeTerm m_array;
  const UnsafeTerm m_index;

  virtual Error __encode(Solver& solver) const override
  {
    return solver.encode_array_select(m_array, m_index);
  }

public:
  UnsafeArraySelectExpr(
    const UnsafeTerm& array,
    const UnsafeTerm& index)
  : UnsafeExpr(ARRAY_SELECT_EXPR_KIND, array.sort().sorts(1)),
    m_array(array),
    m_index(index)
  {
    assert(!m_array.is_null());
    assert(!m_index.is_null());
  }
};

template<typename Domain, typename Range>
class ArraySelectExpr : public UnsafeArraySelectExpr, public Expr<Range>
{
private:
  const Term<sort::Array<Domain, Range>> m_array;
  const Term<Domain> m_index;

public:
  ArraySelectExpr(
    const Term<sort::Array<Domain, Range>>& array,
    const Term<Domain>& index)
  : UnsafeExpr(ARRAY_SELECT_EXPR_KIND, internal::sort<Range>()),
    UnsafeArraySelectExpr(array, index),
    Expr<Range>(ARRAY_SELECT_EXPR_KIND),
    m_array(array),
    m_index(index) {}

  const Term<sort::Array<Domain, Range>>& array() const
  {
    return m_array;
  }

  const Term<Domain>& index() const
  {
    return m_index;
  }
};

class UnsafeArrayStoreExpr : public virtual UnsafeExpr
{
private:
  const UnsafeTerm m_array;
  const UnsafeTerm m_index;
  const UnsafeTerm m_value;

  virtual Error __encode(Solver& solver) const override
  {
    return solver.encode_array_store(m_array, m_index, m_value);
  }

public:
  // Allocate sort statically!
  UnsafeArrayStoreExpr(
    const UnsafeTerm& array,
    const UnsafeTerm& index,
    const UnsafeTerm& value)
  : UnsafeExpr(ARRAY_STORE_EXPR_KIND, array.sort()),
    m_array(array),
    m_index(index),
    m_value(value)
  {
    assert(!m_array.is_null());
    assert(!m_index.is_null());
    assert(!m_value.is_null());
  }
};

template<typename Domain, typename Range>
class ArrayStoreExpr
: public UnsafeArrayStoreExpr, public Expr<sort::Array<Domain, Range>>
{
private:
  const Term<sort::Array<Domain, Range>> m_array;
  const Term<Domain> m_index;
  const Term<Range> m_value;

public:
  ArrayStoreExpr(
    const Term<sort::Array<Domain, Range>>& array,
    const Term<Domain>& index,
    const Term<Range>& value)
  : UnsafeExpr(ARRAY_STORE_EXPR_KIND,
      internal::sort<sort::Array<Domain, Range>>()),
    UnsafeArrayStoreExpr(
      array,
      index,
      value),
    Expr<sort::Array<Domain, Range>>(ARRAY_STORE_EXPR_KIND),
    m_array(array),
    m_index(index),
    m_value(value) {}

  const Term<sort::Array<Domain, Range>>& array() const
  {
    return m_array;
  }

  const Term<Domain>& index() const
  {
    return m_index;
  }

  const Term<Range>& value() const
  {
    return m_value;
  }
};

UnsafeTerm select(
  const UnsafeTerm& array,
  const UnsafeTerm& index);

template<typename Domain, typename Range>
Term<Range> select(
  const Term<sort::Array<Domain, Range>>& array,
  const Term<Domain>& index)
{
  return Term<Range>(
    new ArraySelectExpr<Domain, Range>(array, index));
}

UnsafeTerm store(
  const UnsafeTerm& array,
  const UnsafeTerm& index,
  const UnsafeTerm& value);

template<typename Domain, typename Range>
Term<sort::Array<Domain, Range>> store(
  const Term<sort::Array<Domain, Range>>& array,
  const Term<Domain>& index,
  const Term<Range>& value)
{
  return Term<sort::Array<Domain, Range>>(
    new ArrayStoreExpr<Domain, Range>(array, index, value));
}

UnsafeTerm implies(
  const UnsafeTerm& larg,
  const UnsafeTerm& rarg);

Term<sort::Bool> implies(
  const Term<sort::Bool>& larg,
  const Term<sort::Bool>& rarg);

template<Opcode opcode, typename T>
struct Identity;

template<>
struct Identity<LAND, sort::Bool>
{
  static Term<sort::Bool> term;
};

}

#define SMT_BUILTIN_UNARY_OP(op, opcode)                                       \
  template<typename T>                                                         \
  inline smt::Term<T> operator op(const smt::Term<T>& arg)                     \
  {                                                                            \
    return smt::Term<T>(new smt::UnaryExpr<smt::opcode, T>(arg));              \
  }                                                                            \

#define SMT_BUILTIN_BINARY_OP(op, opcode)                                      \
  template<typename T>                                                         \
  inline smt::Term<T> operator op(const smt::Term<T>& larg,                    \
    const smt::Term<T>& rarg)                                                  \
  {                                                                            \
    return smt::Term<T>(new smt::BinaryExpr<smt::opcode, T>(larg, rarg));      \
  }                                                                            \
  template<typename T, typename U>                                             \
  inline smt::Term<T> operator op(const smt::Term<T>& larg, const U rscalar)   \
  {                                                                            \
    return larg op smt::literal<T, U>(rscalar);                                \
  }                                                                            \
  template<typename T, typename U>                                             \
  inline smt::Term<T> operator op(const U lscalar, const smt::Term<T>& rarg)   \
  {                                                                            \
    return smt::literal<T, U>(lscalar) op rarg;                                \
  }                                                                            \

#define SMT_BUILTIN_BINARY_REL(op, opcode)                                     \
  template<typename T>                                                         \
  inline smt::Term<smt::sort::Bool> operator op(                               \
    const smt::Term<T>& larg, const smt::Term<T>& rarg)                        \
  {                                                                            \
    return smt::Term<smt::sort::Bool>(                                         \
      new smt::BinaryExpr<smt::opcode, T, smt::sort::Bool>(larg, rarg));       \
  }                                                                            \
  template<typename T, typename U>                                             \
  inline smt::Term<smt::sort::Bool> operator op(                               \
    const smt::Term<T>& larg, const U rscalar)                                 \
  {                                                                            \
    return larg op smt::literal<T, U>(rscalar);                                \
  }                                                                            \
  template<typename T, typename U>                                             \
  inline smt::Term<smt::sort::Bool> operator op(const U lscalar,               \
    const smt::Term<T>& rarg)                                                  \
  {                                                                            \
    return smt::literal<T, U>(lscalar) op rarg;                                \
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
  inline smt::Term<T> operator op(const smt::Term<T>& arg)                     \
  {                                                                            \
    return smt::Term<T>(new smt::UnaryExpr<smt::opcode, T>(arg));              \
  }                                                                            \

#define SMT_BUILTIN_BV_BINARY_OP(op, opcode)                                   \
  template<typename T>                                                         \
  inline smt::Term<T> operator op(const smt::Term<T>& larg,                    \
    const smt::Term<T>& rarg)                                                  \
  {                                                                            \
    return smt::Term<T>(new smt::BinaryExpr<smt::opcode, T>(larg, rarg));      \
  }                                                                            \
  template<typename T>                                                         \
  inline smt::Term<T> operator op(const smt::Term<T>& larg, const T rscalar)   \
  {                                                                            \
    return larg op smt::literal<T>(rscalar);                                   \
  }                                                                            \
  template<typename T>                                                         \
  inline smt::Term<T> operator op(const T lscalar, const smt::Term<T>& rarg)   \
  {                                                                            \
    return smt::literal<T>(lscalar) op rarg;                                   \
  }                                                                            \

SMT_BUILTIN_BV_UNARY_OP(~, NOT)

SMT_BUILTIN_BV_BINARY_OP(&, AND)
SMT_BUILTIN_BV_BINARY_OP(|, OR)
SMT_BUILTIN_BV_BINARY_OP(^, XOR)

#define SMT_BUILTIN_BOOL_UNARY_OP(op, opcode)                                  \
  inline smt::Term<smt::sort::Bool> operator op(                               \
    const smt::Term<smt::sort::Bool>& arg)                                     \
  {                                                                            \
    return smt::Term<smt::sort::Bool>(                                         \
      new smt::UnaryExpr<smt::opcode, smt::sort::Bool>(arg));                  \
  }                                                                            \

#define SMT_BUILTIN_BOOL_BINARY_OP(op, opcode)                                 \
  inline smt::Term<smt::sort::Bool> operator op(                               \
    const smt::Term<smt::sort::Bool>& larg,                                    \
    const smt::Term<smt::sort::Bool>& rarg)                                    \
  {                                                                            \
    return smt::Term<smt::sort::Bool>(                                         \
      new smt::BinaryExpr<smt::opcode, smt::sort::Bool>(larg, rarg));          \
  }                                                                            \
  inline smt::Term<smt::sort::Bool> operator op(                               \
    const smt::Term<smt::sort::Bool>& larg, const bool rscalar)                \
  {                                                                            \
    return larg op smt::literal<smt::sort::Bool>(rscalar);                     \
  }                                                                            \
  inline smt::Term<smt::sort::Bool> operator op(const bool lscalar,            \
    const smt::Term<smt::sort::Bool>& rarg)                                    \
  {                                                                            \
    return smt::literal<smt::sort::Bool>(lscalar) op rarg;                     \
  }                                                                            \

SMT_BUILTIN_BOOL_UNARY_OP(!, LNOT)

SMT_BUILTIN_BOOL_BINARY_OP(&&, LAND)
SMT_BUILTIN_BOOL_BINARY_OP(||, LOR)
SMT_BUILTIN_BOOL_BINARY_OP(==, EQL)
SMT_BUILTIN_BOOL_BINARY_OP(!=, NEQ)

#define SMT_UNSAFE_UNARY_OP(op, opcode)                                        \
  inline smt::UnsafeTerm operator op(const smt::UnsafeTerm& arg)               \
  {                                                                            \
    return smt::UnsafeTerm(                                                    \
      new smt::UnsafeUnaryExpr(arg.sort(), smt::opcode, arg));                 \
  }                                                                            \

#define SMT_UNSAFE_BINARY_OP(op, opcode)                                       \
  inline smt::UnsafeTerm operator op(const smt::UnsafeTerm& larg,              \
    const smt::UnsafeTerm& rarg)                                               \
  {                                                                            \
    return smt::UnsafeTerm(new smt::UnsafeBinaryExpr(                          \
      larg.sort(), smt::opcode, larg, rarg));                                  \
  }                                                                            \
  template<typename T, typename Enable =                                       \
    typename std::enable_if<std::is_integral<T>::value>::type>                 \
  inline smt::UnsafeTerm operator op(const T lscalar,                          \
    const smt::UnsafeTerm& rarg)                                               \
  {                                                                            \
    return smt::UnsafeTerm(new smt::UnsafeBinaryExpr(                          \
      rarg.sort(), smt::opcode, literal(rarg.sort(), lscalar), rarg));         \
  }                                                                            \
  template<typename T, typename Enable =                                       \
    typename std::enable_if<std::is_integral<T>::value>::type>                 \
  inline smt::UnsafeTerm operator op(                                          \
    const smt::UnsafeTerm& larg, const T rscalar)                              \
  {                                                                            \
    return smt::UnsafeTerm(new smt::UnsafeBinaryExpr(                          \
      larg.sort(), smt::opcode, larg, literal(larg.sort(), rscalar)));         \
  }                                                                            \

#define SMT_UNSAFE_BINARY_REL(op, opcode)                                      \
  inline smt::UnsafeTerm operator op(const smt::UnsafeTerm& larg,              \
    const smt::UnsafeTerm& rarg)                                               \
  {                                                                            \
    return smt::UnsafeTerm(new smt::UnsafeBinaryExpr(                          \
      smt::internal::sort<smt::sort::Bool>(), smt::opcode, larg, rarg));       \
  }                                                                            \
  template<typename T, typename Enable =                                       \
    typename std::enable_if<std::is_integral<T>::value>::type>                 \
  inline smt::UnsafeTerm operator op(const T lscalar,                          \
    const smt::UnsafeTerm& rarg)                                               \
  {                                                                            \
    return smt::UnsafeTerm(new smt::UnsafeBinaryExpr(                          \
      smt::internal::sort<smt::sort::Bool>(), smt::opcode,                     \
        literal(rarg.sort(), lscalar), rarg));                                 \
  }                                                                            \
  template<typename T, typename Enable =                                       \
    typename std::enable_if<std::is_integral<T>::value>::type>                 \
  inline smt::UnsafeTerm operator op(                                          \
    const smt::UnsafeTerm& larg, const T rscalar)                              \
  {                                                                            \
    return smt::UnsafeTerm(new smt::UnsafeBinaryExpr(                          \
      smt::internal::sort<smt::sort::Bool>(), smt::opcode, larg,               \
        literal(larg.sort(), rscalar)));                                       \
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
