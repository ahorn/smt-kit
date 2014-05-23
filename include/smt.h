// Copyright 2013-2014, Alex Horn. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

#ifndef __SMT_H_
#define __SMT_H_

#include <tuple>
#include <array>
#include <vector>
#include <unordered_set>
#include <unordered_map>
#include <chrono>
#include <string>
#include <memory>
#include <cstddef>
#include <cstdint>
#include <cassert>
#include <stdexcept>
#include <type_traits>

// Perfect sharing of syntactically equivalent expressions
#define ENABLE_HASH_CONS

namespace smt
{

/// Standard acronyms of logic declarations in SMT-LIB 2.0

/// \see_also http://smtlib.cs.uiowa.edu/logics.html
enum Logic : unsigned
{
  /// Linear Integer Arithmetic with Uninterpreted Functions and Arrays

  /// Summary: quantified formulas to be tested for satisfiability modulo a
  /// background theory combining linear integer arithmetic, uninterpreted
  /// function and predicate symbols, and extensional arrays.
  ///
  /// Closed formulas built over arbitrary expansions of the Ints and ArraysEx
  /// signatures with free sort and function symbols, but with the following 
  /// restrictions:
  /// - all terms of sort Int are linear, that is, have no occurrences of the
  ///  function symbols *, /, div, mod, and abs
  /// - all array terms have sort (Array Int Int).
  ///
  /// This logic extends QF_AUFLIA by allowing quantifiers.
  AUFLIA_LOGIC,

  /// Arrays, Uninterpreted Functions, and Linear Arithmetic

  /// Summary: quantifier formulas with arrays of reals indexed by integers
  /// (Array1), arrays of Array1 indexed by integers (Array2), and linear
  /// arithmetic over the integers and reals.
  ///
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

  /// Arrays, Uninterpreted Functions, and Nonlinear Arithmetic

  /// Summary: quantifier formulas with arrays of reals indexed by integers
  /// (Array1), arrays of Array1 indexed by integers (Array2), and
  /// nonlinear arithmetic over the integers and reals.
  ///
  /// Closed formulas built over arbitrary expansions of the Reals_Ints and
  /// ArraysEx signatures with free sort and function symbols.
  AUFNIRA_LOGIC,

  /// Linear Real Arithmetic

  /// Closed formulas built over arbitrary expansions of the Reals signature
  /// with free constant symbols, but containing only linear atoms, that is, 
  /// atoms with no occurrences of the function symbols * and /
  LRA_LOGIC,

  /// Bit-vectors with Arrays

  /// Closed quantifier-free formulas built over the Fixed_Size_BitVectors and
  /// ArraysEx signatures, with the restriction that all array terms have sort of
  /// the form (Array (_ BitVec i) (_ BitVec j)) for some i, j > 0.
  QF_ABV_LOGIC,

  /// Bit-vectors with Arrays and Uninterpreted Functions

  /// Summary: quantifier-free formulas over bit vectors of fixed size, with
  /// arrays and uninterpreted functions and predicate symbols.
  /// 
  /// Closed quantifier-free formulas built over an arbitrary expansion of the
  /// Fixed_Size_BitVectors and ArraysEx signatures with free sort and function
  /// symbols, but with the restriction that all array terms have sort of the 
  /// form (Array (_ BitVec i) (_ BitVec j)) for some i, j > 0.
  QF_AUFBV_LOGIC,

  /// Uninterpreted Functions with bit vectors

  /// Closed quantifier-free formulas built over arbitrary expansions of
  /// the Fixed_Size_BitVectors signature with free sort and function symbols.
  QF_UFBV_LOGIC,

  /// Linear Integer and Real Arithmetic with Uninterpreted Functions and Arrays

  /// Not official (yet) but supported by at least CVC4 and Z3
  QF_AUFLIRA_LOGIC,

  /// Linear Integer Arithmetic with Uninterpreted Functions and Arrays

  /// Summary: quantifier-free formulas to be tested for satisfiability modulo
  /// a background theory combining linear integer arithmetic, uninterpreted
  /// function and predicate symbols, and extensional arrays.
  ///
  /// Closed quantifier-free formulas built over arbitrary expansions of the
  /// Ints and ArraysEx signatures with free sort and function symbols, but
  /// with the following restrictions:
  /// - all terms of sort Int are linear, that is, have no occurrences of the
  ///   function symbols *, /, div, mod, and abs
  /// - all array terms have sort (Array Int Int).
  QF_AUFLIA_LOGIC,

  /// Arrays with Extensionality

  /// Summary: quantifier-free formulas to be tested for satisfiability modulo
  /// a background theory of arrays which includes the extensionality axiom.
  ///
  /// Closed quantifier-free formulas built over an arbitrary expansion of
  /// the ArraysEx signature with free sort and constant symbols.
  QF_AX_LOGIC,

  /// Fixed-size Bit-vectors

  /// Summary:  quantifier-free formulas over bit vectors of fixed size.
  ///
  /// Closed quantifier-free formulas built over an arbitrary expansion of the
  /// Fixed_Size_BitVectors signature with free constant symbols over the sorts
  /// (_ BitVec m) for 0 < m.  Formulas in ite terms must satisfy the same
  /// restriction as well, with the exception that they need not be closed 
  /// (because they may be in the scope of a let binder).
  QF_BV_LOGIC,

  /// Integer Difference Logic

  /// Summary:  quantifier-free formulas to be tested for satisfiability modulo
  /// a background theory of integer arithmetic.  The syntax of atomic formulas
  /// is restricted to difference logic, i.e. x - y op c, where op is either
  /// equality or inequality and c is an integer constant.
  ///
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

  /// Real Difference Logic

  /// Summary: like QF_IDL, except that the background theory is real
  /// arithmetic.
  ///
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

  /// Linear Integer Arithmetic

  /// Summary: quantifier-free formulas to be tested for satisfiability modulo
  /// a background theory of integer arithmetic.  The syntax of atomic formulas
  /// is restricted to contain only linear terms.
  ///
  /// Closed quantifier-free formulas built over an arbitrary expansion of the
  /// Ints signature with free constant symbols, but whose terms of sort Int 
  /// are all linear, that is, have no occurrences of the function symbols
  /// *, /, div, mod, and abs
  QF_LIA_LOGIC,

  /// Linear Real Arithmetic

  /// Summary: like QF_LIA, except that the background theory is real
  /// arithmetic.
  ///
  /// Closed quantifier-free formulas built over arbitrary expansions of 
  /// the Reals signature with free constant symbols, but containing only
  /// linear atoms, that is, atoms with no occurrences of the function
  /// symbols * and /
  QF_LRA_LOGIC,

  /// Nonlinear Integer Arithmetic

  /// Summary: quantifier-free formulas to be tested for satisfiability modulo
  /// a background theory of integer arithmetic.  There is no restriction to
  /// linear terms.
  ///
  /// Closed quantifier-free formulas built over an arbitrary expansion of the
  /// Ints signature with free constant symbols.
  QF_NIA_LOGIC,

  /// Nonlinear Real Arithmetic

  /// Closed quantifier-free formulas built over arbitrary expansions of 
  /// the Reals signature with free constant symbols.
  QF_NRA_LOGIC,

  /// Uninterpreted Functions

  /// Summary:  quantifier-free formulas whose satisfiability is to be decided
  /// modulo the empty theory. Each formula may introduce its own uninterpreted
  /// function and predicate symbols.
  ///
  /// Closed quantifier-free formulas built over an arbitrary expansion of
  /// the Core signature with free sort and function symbols.
  QF_UF_LOGIC,

  /// Integer Difference Logic with Uninterpreted Functions

  /// Summary: a logic which is similar to QF_IDL, except that it also allows
  /// uninterpreted functions and predicates.
  ///
  /// Closed quantifier-free formulas built over an arbitrary expansion with 
  /// free sort and function symbols of the signature consisting of 
  /// - all the sort and function symbols of Core and
  /// - the following symbols of Int:
  ///
  ///   :sorts ((Int 0))
  ///   :funs ((NUMERAL Int) 
  ///          (- Int Int Int)
  ///          (+ Int Int Int) 
  ///          (<= Int Int Bool)
  ///          (< Int Int Bool)
  ///          (>= Int Int Bool)
  ///          (> Int Int Bool)
  ///         )
  ///
  /// Additionally, for every term of the form (op t1 t2) with op in {+, -}, 
  /// at least one of t1 and t2 is a numeral.
  QF_UFIDL_LOGIC,

  /// Linear Integer Arithmetic with Uninterpreted Functions

  /// Summary:  a logic which is similar to QF_LIA, except that it also allows
  /// uninterpreted functions and predicates.
  ///
  /// Closed quantifier-free formulas built over arbitrary expansions of the
  /// Ints signatures with free sort and function symbols, but with the 
  /// following restrictions:
  /// - all terms of sort Int are linear, that is, have no occurrences of the
  ///   function symbols *, /, div, mod, and abs
  QF_UFLIA_LOGIC,

  /// Linear Real Arithmetic with Uninterpreted Functions

  /// Summary: similar to QF_LRA, except that it also allows uninterpreted
  /// functions and predicates.
  ///
  /// Closed quantifier-free formulas built over arbitrary expansions of the 
  /// Reals signature with free sort and function symbols, but containing 
  /// only linear atoms, that is, atoms with no occurrences of the function
  /// symbols * and /
  QF_UFLRA_LOGIC,

  /// Nonlinear Real Arithmetic with Uninterpreted Functions

  /// Summary: similar to QF_NRA, except that it also allows uninterpreted
  /// functions and predicates.
  /// 
  /// Closed quantifier-free formulas built over arbitrary expansions of 
  /// the Reals signature with free sort and function symbols.
  QF_UFNRA_LOGIC,

  /// Linear Real Arithmetic with Uninterpreted Functions

  /// Summary:  similar to QF_LRA, except that it also allows uninterpreted
  /// functions and predicates.
  ///
  /// Closed formulas built over arbitrary expansions of the Reals signature 
  /// with free sort and function symbols, but containing only linear atoms, 
  /// that is, atoms with no occurrences of the function symbols * and /
  UFLRA_LOGIC,

  /// Uninterpreted Functions and Nonlinear Arithmetic

  /// Summary: quantifier formulas with uninterpreted functions and nonlinear
  /// integer arithmetic.
  ///
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
    "QF_AUFLIRA",
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
  ADD,  // +
  MUL,  // *
  AND,  // &
  OR,   // |
  XOR,  // ^
  LAND, // &&
  LOR,  // ||
  IMP,  // logical implication
  EQL,  // ==
  QUO,  // /
  REM,  // %
  LSS,  // <
  GTR,  // >
  NEQ,  // !=
  LEQ,  // <=
  GEQ   // >=
};

#define SMT_TERM_DECL(name) \
  class name;               \

SMT_TERM_DECL(Bool)
SMT_TERM_DECL(Int)
SMT_TERM_DECL(Real)

template<typename Domain, typename Range>
class Array;

template<typename... T>
class Func;

template<typename T, typename Enable>
class Bv;

/// Contingencies that an implementation of the API must always consider

/// An error is a value between 0 and 255. Any higher value is reserved
/// for solver implementation uses. Any of these internal values are
/// interpreted as errors if they leak the Solver interface.
enum Error : unsigned {
  // No error, OK equals zero
  OK = 0,

  // Virtual call incorrectly implemented
  OPCODE_ERROR,

  // Unsupported SMT-LIB feature
  UNSUPPORT_ERROR,

  /// Bitwise mask to clear any internal error flags
  ERROR_MASK = 0xFFU
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
  BV_ZERO_EXTEND_EXPR_KIND,
  BV_SIGN_EXTEND_EXPR_KIND,
  BV_EXTRACT_EXPR_KIND,
};

// courtesy of Daniel Kroening, see CPROVER source file util/irep.cpp
static inline size_t hash_rotl(const size_t value, const int shift)
{
  return (value << shift) | (value >> (sizeof(value)*8 - shift));
}

// courtesy of Daniel Kroening, see CPROVER source file util/irep.cpp
static inline size_t hash_combine(const size_t h1, const size_t h2)
{
  return hash_rotl(h1, 7)^h2;
}

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

  // courtesy of Daniel Kroening, see CPROVER source file util/irep.cpp
  static constexpr size_t hash_rotl(const size_t value, const int shift)
  {
    return (value << shift) | (value >> (sizeof(value)*8 - shift));
  }

  // courtesy of Daniel Kroening, see CPROVER source file util/irep.cpp
  static constexpr size_t hash_combine(const size_t h1, const size_t h2)
  {
    return hash_rotl(h1, 7)^h2;
  }

  // compute the combined hash value of sort.sorts(i) for all 0 <= i <= k
  static constexpr size_t hash(const size_t k, const Sort& sort)
  {
    return k == 0 ?
      sort.sorts(k).hash() : hash_combine(sort.sorts(k).hash(), hash(k - 1, sort));
  }

  // prefers short bit vector sorts
  constexpr size_t hash_flags() const
  {
    static_assert(1 <= sizeof(size_t), "size of size_t must be at least one byte");

    return (
      m_is_real   << 7 |
      m_is_array  << 6 |
      m_is_func   << 5 |
      m_is_tuple  << 4 |
      m_is_int    << 3 |
      m_is_bool   << 2 | // two since m_bv_size is zero exactly if m_is_bv is zero
      m_bv_size   << 2 |
      m_is_signed << 1 |
      m_is_bv     << 0 ) * 50331653;
  }

  constexpr unsigned check_sorts_index(size_t index) const
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

public:
  constexpr size_t hash() const
  {
    return m_sorts_size == 0 ?
      hash_flags() : hash_combine(hash_flags(), hash(m_sorts_size - 1, *this));
  }

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

  bool operator!=(const Sort& other) const
  {
    return !operator==(other);
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
      std::is_same<T, Bool>::value,
      std::is_same<T, Int>::value,
      std::is_same<T, Real>::value,
      false, false, 0);
  };

  template<typename T>
  constexpr Sort __Math<T>::s_sort;

  template<typename T>
  struct __SortSwitch
  {
    typedef __Bv<T> Type;
  };

  template<typename T>
  struct __SortSwitch<Bv<T, void>>
  {
    typedef __Bv<T> Type;
  };

  template<>
  struct __SortSwitch<Int>
  {
    typedef __Math<Int> Type;
  };

  template<>
  struct __SortSwitch<Bool>
  {
    typedef __Math<Bool> Type;
  };

  template<>
  struct __SortSwitch<Real>
  {
    typedef __Math<Real> Type;
  };

  /* Array sort */
  template<typename Domain, typename Range>
  struct __SortSwitch<Array<Domain, Range>>
  {
    typedef __Math<Array<Domain, Range>> Type;
  };

  template<typename Domain, typename Range>
  struct __Math<Array<Domain, Range>>
  {
    static constexpr const Sort* const s_sorts[2] = {
      &__SortSwitch<Domain>::Type::s_sort,
      &__SortSwitch<Range>::Type::s_sort };

    static constexpr Sort s_sort = Sort(false, true, false, s_sorts);
  };

  template<typename Domain, typename Range>
  constexpr const Sort* const __Math<Array<Domain, Range>>::s_sorts[2];

  template<typename Domain, typename Range>
  constexpr Sort __Math<Array<Domain, Range>>::s_sort;

  /* Function sort */
  template<typename... T>
  struct __SortSwitch<Func<T...>>
  {
    typedef __Math<Func<T...>> Type;
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
  struct __Math<Func<T, U...>>
  {
    static constexpr size_t N = sizeof...(U) + 1;
    static constexpr Sort s_sort = Sort(true, false, false,
      __FuncSort<__SortArray<N, &__SortSwitch<T>::Type::s_sort>, U...>::result());
  };

  template<typename T, typename... U>
  constexpr Sort __Math<Func<T, U...>>::s_sort;

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
  const char* const m_prefix;
  const unsigned m_counter;
  const Sort& m_sort;

  // constructed lazily by symbol()
  mutable std::string m_symbol;

public:
  /// Allocate sort statically, counter must be globally unique
  UnsafeDecl(
    const char* const prefix,
    const unsigned counter,
    const Sort& sort)
  : m_prefix(prefix),
    m_counter(counter),
    m_sort(sort),
    m_symbol() {}

  /// Allocate sort statically!

  /// \pre: name must be nonempty
  UnsafeDecl(
    std::string&& symbol_name,
    const Sort& sort)
  : m_prefix(),
    m_counter(0),
    m_sort(sort),
    m_symbol(std::move(symbol_name))
  {
    assert(!m_symbol.empty());
  }

  UnsafeDecl(const UnsafeDecl& other)
  : m_prefix(other.m_prefix),
    m_counter(other.m_counter),
    m_sort(other.m_sort),
    m_symbol(other.m_symbol) {}

  UnsafeDecl(UnsafeDecl&& other)
  : m_prefix(other.m_prefix),
    m_counter(other.m_counter),
    m_sort(other.m_sort),
    m_symbol(std::move(other.m_symbol)) {}

  virtual ~UnsafeDecl() {}

  const char* prefix() const
  {
    return m_prefix;
  }

  unsigned counter() const
  {
    return m_counter;
  }

  const std::string& symbol() const
  {
    if (m_symbol.empty())
    {
      if (m_counter != 0)
        m_symbol = m_prefix + std::to_string(m_counter);
      else
        m_symbol = m_prefix;
    }

    assert(!m_symbol.empty());
    return m_symbol;
  }

  const Sort& sort() const
  {
    return m_sort;
  }

  size_t hash() const
  {
    if (m_prefix == nullptr)
    {
      std::hash<std::string> string_hash;
      return hash_combine(m_sort.hash(), string_hash(m_symbol));
    }

    // see also http://planetmath.org/goodhashtableprimes
    constexpr size_t good_hash_table_prime = 12582917;
    return hash_combine(m_sort.hash(), m_counter * good_hash_table_prime);
  }

  bool operator==(const UnsafeDecl& other) const
  {
    if (this == &other)
      return true;

    if (m_prefix == nullptr)
      return other.m_prefix == nullptr &&
        m_symbol == other.m_symbol &&
        m_sort == other.m_sort;

    return m_prefix == other.m_prefix &&
      m_counter == other.m_counter &&
      m_sort == other.m_sort;
  }

  bool operator!=(const UnsafeDecl& other) const
  {
    return !operator==(other);
  }
};

template<typename T>
class Decl : public UnsafeDecl 
{
public:
  /// Counter must be globally unique

  /// Prefix won't be freed; so it is (preferably) statically allocated
  Decl(const char* const prefix, const unsigned counter)
  : UnsafeDecl(prefix, counter, internal::sort<T>()) {}

  /// Symbol name must be globally unique and nonempty
  Decl(std::string&& symbol_name)
  : UnsafeDecl(std::move(symbol_name), internal::sort<T>()) {}

  Decl(const Decl& other)
  : UnsafeDecl(other) {}
};

class SharedExpr;
typedef std::vector<SharedExpr> SharedExprs;

class Expr;

namespace internal
{
  /// Measure elapsed time within a scope (e.g. function body)

  /// Timers can be conveniently used to measure the time it takes to
  /// execute an entire function because return values are constructed
  /// before the local variables are destroyed.
  ///
  /// Implementations should make clear whether timers can be used
  /// in recursive functions or not.
  template<typename T, typename Clock=std::chrono::system_clock>
  class Timer
  {
  private:
    T& m_time_ref;

  protected:
    std::chrono::time_point<Clock> m_start;

    Timer(T& time_ref)
    : m_time_ref(time_ref),
      m_start(Clock::now()) {}

    Timer(T& time_ref, const std::chrono::time_point<Clock>& start)
    : m_time_ref(time_ref),
      m_start(start) {}

    void start() noexcept
    {
       m_start = Clock::now();
    }

    void stop() noexcept
    {
      auto stop = Clock::now();
      m_time_ref += std::chrono::duration_cast<T>(stop - m_start);
    }
  };
}

/// Timer that can be used inside recursive functions
template<typename T, typename Clock=std::chrono::system_clock>
class ReentrantTimer : public internal::Timer<T, Clock>
{
private:
  bool& m_is_active;

public:
  ReentrantTimer(T& time_ref, bool& is_active)
  : internal::Timer<T, Clock>(time_ref),
    m_is_active(is_active)
  {
    m_is_active = true;
  }

  ~ReentrantTimer()
  {
    if (m_is_active)
      internal::Timer<T, Clock>::stop();

    m_is_active = false;
  }
};

/// Timer that must not be used inside recursive functions
template<typename T, typename Clock=std::chrono::system_clock>
class NonReentrantTimer : public internal::Timer<T, Clock>
{
public:
  NonReentrantTimer(T& time_ref)
  : internal::Timer<T, Clock>(time_ref) {}

  ~NonReentrantTimer()
  {
    internal::Timer<T, Clock>::stop();
  }
};

/// Timer that must be explicitly started and stopped
template<typename T, typename Clock=std::chrono::system_clock>
class ManualTimer : public internal::Timer<T, Clock>
{
private:
  bool m_is_active;
public:
  /// Modifies time_ref argument on stop() calls
  ManualTimer(T& time_ref)
  : internal::Timer<T, Clock>(time_ref,
      std::chrono::time_point<Clock>::min()),
     m_is_active(false) {}

  /// Is stop watch on?
  bool is_active() const noexcept
  {
    return m_is_active;
  }

  /// Restarting an active timer is a programmer error.

  /// \pre: not is_active() then \post: is_active()
  void start() noexcept
  {
    assert(!m_is_active);
    m_is_active = true;
    internal::Timer<T, Clock>::start();
  }

  /// Adds the elapsed time to the time_ref constructor argument

  /// Stopping a nonactive timer is a programmer error.
  ///
  /// \pre: is_active() then \post: not is_active()
  void stop() noexcept
  {
    assert(m_is_active);

    internal::Timer<T, Clock>::stop();
    m_is_active = false;
  }
};

class Solver;

namespace internal
{
  /// Static dispatch to private virtual member functions in Solver
  template<Opcode opcode>
  struct EncodeDispatch
  {
    /// By default returns OPCODE_ERROR, an implementation error
    static Error encode_unary(
      Solver* const solver,
      const Expr* const expr,
      const SharedExpr& arg)
    {
      return OPCODE_ERROR;
    }

    /// By default returns OPCODE_ERROR, an implementation error
    static Error encode_binary(
      Solver* const solver,
      const Expr* const expr,
      const SharedExpr& larg,
      const SharedExpr& rarg)
    {
      return OPCODE_ERROR;
    }
  };
}

/// Abstract base class of an SMT/SAT solver

/// Memory management:
///
///   Let \c s be a Solver implementation and \c expr be an Expr.
///   When \c expr is deleted (i.e. its destructor is invoked),
///   \c s.notify_delete(expr) is called at which point every
///   Solver subclass should free any solver-specific memory
///   associated with \c expr without throwing an exception.
///
/// Optional features:
///
///   Subclasses are encouraged to provide pretty-printing and model
///   extraction functionality.
class Solver
{
public:
  typedef std::chrono::milliseconds ElapsedTime;

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

    /// Total time it has taken up to now to build expressions
    ElapsedTime encode_elapsed_time;

    /// Total time it has taken up to now to compute SAT or UNSAT
    ElapsedTime check_elapsed_time;
  };

private:
  typedef ReentrantTimer<ElapsedTime> ElapsedTimer;

  Stats m_stats;
  bool m_is_timer_on;

#define SMT_ENCODE_BUILTIN_LITERAL(type)                                       \
private:                                                                       \
  virtual Error __encode_literal(                                              \
    const Expr* const expr,                                                    \
    type literal)                                                              \
  {                                                                            \
    return UNSUPPORT_ERROR;                                                    \
  }                                                                            \
                                                                               \
public:                                                                        \
  Error encode_literal(                                                        \
    const Expr* const expr,                                                    \
    type literal)                                                              \
  {                                                                            \
    return __encode_literal(expr, literal);                                    \
  }                                                                            \

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
  template<Opcode opcode>
  friend class internal::EncodeDispatch;

  virtual Error __encode_constant(
    const Expr* const expr,
    const UnsafeDecl& decl) = 0;

  virtual Error __encode_func_app(
    const Expr* const expr,
    const UnsafeDecl& func_decl,
    const size_t arity,
    const SharedExpr* const args) = 0;

  virtual Error __encode_const_array(
    const Expr* const expr,
    const SharedExpr& init) = 0;

  virtual Error __encode_array_select(
    const Expr* const expr,
    const SharedExpr& array,
    const SharedExpr& index) = 0;

  virtual Error __encode_array_store(
    const Expr* const expr,
    const SharedExpr& array,
    const SharedExpr& index,
    const SharedExpr& value) = 0;

  virtual Error __encode_unary_lnot(
    const Expr* const expr,
    const SharedExpr& arg) = 0;

  virtual Error __encode_unary_not(
    const Expr* const expr,
    const SharedExpr& arg) = 0;

  virtual Error __encode_unary_sub(
    const Expr* const expr,
    const SharedExpr& arg) = 0;

  virtual Error __encode_binary_sub(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg) = 0;

  virtual Error __encode_binary_and(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg) = 0;

  virtual Error __encode_binary_or(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg) = 0;

  virtual Error __encode_binary_xor(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg) = 0;

  virtual Error __encode_binary_land(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg) = 0;

  virtual Error __encode_binary_lor(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg) = 0;

  virtual Error __encode_binary_imp(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg) = 0;

  virtual Error __encode_binary_eql(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg) = 0;

  virtual Error __encode_binary_add(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg) = 0;

  virtual Error __encode_binary_mul(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg) = 0;

  virtual Error __encode_binary_quo(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg) = 0;

  virtual Error __encode_binary_rem(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg) = 0;

  virtual Error __encode_binary_lss(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg) = 0;

  virtual Error __encode_binary_gtr(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg) = 0;

  virtual Error __encode_binary_neq(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg) = 0;

  virtual Error __encode_binary_leq(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg) = 0;

  virtual Error __encode_binary_geq(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg) = 0;

  virtual Error __encode_nary(
    const Expr* const expr,
    Opcode opcode,
    const SharedExprs& args) = 0;

  virtual Error __encode_bv_zero_extend(
    const Expr* const expr,
    const SharedExpr& bv,
    const unsigned ext) = 0;

  virtual Error __encode_bv_sign_extend(
    const Expr* const expr,
    const SharedExpr& bv,
    const unsigned ext) = 0;

  virtual Error __encode_bv_extract(
    const Expr* const expr,
    const SharedExpr& bv,
    const unsigned high,
    const unsigned low) = 0;

  virtual void __notify_delete(const Expr* const) = 0;

  virtual void __reset() = 0;
  virtual void __push() = 0;
  virtual void __pop() = 0;
  virtual Error __add(const Bool& condition) = 0;
  virtual Error __unsafe_add(const SharedExpr& condition) = 0;
  virtual CheckResult __check() = 0;

protected:
  /// Registers solver
  Solver();

  /// Registers solver
  Solver(Logic);

public:
  /// Unregisters solver
  virtual ~Solver();

  /// notifies solver that the given expression is being deleted

  /// Frees any solver-specific resources associated with \c expr
  void notify_delete(const Expr* const expr)
  {
    __notify_delete(expr);
  }

  Error encode_constant(
    const Expr* const expr,
    const UnsafeDecl& decl);

  Error encode_func_app(
    const Expr* const expr,
    const UnsafeDecl& func_decl,
    const size_t arity,
    const SharedExpr* const args);

  Error encode_const_array(
    const Expr* const expr,
    const SharedExpr& init);

  Error encode_array_select(
    const Expr* const expr,
    const SharedExpr& array,
    const SharedExpr& index);

  Error encode_array_store(
    const Expr* const expr,
    const SharedExpr& array,
    const SharedExpr& index,
    const SharedExpr& value);

  template<Opcode opcode>
  Error encode_unary(
    const Expr* const expr,
    const SharedExpr& arg);

  template<Opcode opcode>
  Error encode_binary(
    const Expr* const expr,
    const SharedExpr& larg,
    const SharedExpr& rarg);

  Error encode_nary(
    const Expr* const expr,
    Opcode opcode,
    const SharedExprs& args);

  Error encode_bv_zero_extend(
    const Expr* const expr,
    const SharedExpr& bv,
    const unsigned ext);

  Error encode_bv_sign_extend(
    const Expr* const expr,
    const SharedExpr& bv,
    const unsigned ext);

  Error encode_bv_extract(
    const Expr* const expr,
    const SharedExpr& bv,
    const unsigned high,
    const unsigned low);

  // Generic SMT formula statistics
  const Stats& stats() const
  {
    return m_stats;
  }

  void reset();

  void push();

  void pop();

  void add(const Bool& condition);
  void unsafe_add(const SharedExpr& condition);

  CheckResult check();
};

class Expr
{
#ifdef ENABLE_HASH_CONS
public:
  /// Hash value
  typedef size_t Hash;
#endif

private:
  friend class Solver;
  friend class SharedExpr;

  // allow Solver implementations to manage memory
  typedef std::unordered_set<uintptr_t> SolverPtrs;
  static SolverPtrs s_solver_ptrs;

  static void register_solver(Solver* s_ptr)
  {
    bool ok = std::get<1>(s_solver_ptrs.insert(reinterpret_cast<uintptr_t>(s_ptr)));
    assert(ok);
  }

  static void unregister_solver(Solver* s_ptr)
  {
    SolverPtrs::size_type count = s_solver_ptrs.erase(reinterpret_cast<uintptr_t>(s_ptr));
    assert(count == 1);
  }

  const ExprKind m_expr_kind;
  const Sort& m_sort;

#ifdef ENABLE_HASH_CONS
  const size_t m_hash;
#endif

  // modified by SharedExpr
  unsigned ref_counter;

  virtual Error __encode(Solver&) const = 0;

protected:
  // Allocate sort statically!
  Expr(
    ExprKind expr_kind,
    const Sort& sort)
  : m_expr_kind(expr_kind),
    m_sort(sort),
#ifdef ENABLE_HASH_CONS
    m_hash(0),
#endif
    ref_counter(0)
  {
    ++Expr::s_counter;
  }

#ifdef ENABLE_HASH_CONS
  // Allocate sort statically!
  Expr(
    ExprKind expr_kind,
    const Sort& sort,
    size_t hash)
  : m_expr_kind(expr_kind),
    m_sort(sort),
    m_hash(hash),
    ref_counter(0)
  {
    ++Expr::s_counter;
  }
#endif

public:
  static unsigned s_counter;

  Expr(const Expr&) = delete;

  virtual ~Expr()
  {
    --Expr::s_counter;

    assert(ref_counter == 0);

    for (uintptr_t s_ptr : s_solver_ptrs)
      reinterpret_cast<Solver*>(s_ptr)->notify_delete(this);
  }

  ExprKind expr_kind() const
  {
    return m_expr_kind;
  }

  const Sort& sort() const
  {
    return m_sort;
  }

#ifdef ENABLE_HASH_CONS
  /// \internal Weak hash value or zero if expression is not hash-consed

  /// If not zero, the hash value is only suitable among a group of
  /// expressions of the same kind
  Expr::Hash hash() const
  {
    return m_hash;
  }
#endif

  Error encode(Solver& solver) const
  {
    return __encode(solver);
  }
};

namespace internal
{
  template<typename T>
  class Term;
}

/// Shared but potentially not well-sorted SMT expression

/// All arithmetic and bit vector operators are overloaded.
class SharedExpr
{
private:
  Expr* m_ptr;

  void inc() const noexcept
  {
    if (m_ptr != nullptr)
      ++m_ptr->ref_counter;
  }

  void dec() const noexcept
  {
    assert(m_ptr == nullptr || 0 < m_ptr->ref_counter);

    if (m_ptr != nullptr && --m_ptr->ref_counter == 0)
      delete m_ptr;
  }

  // terms call SharedExpr(Expr* const) directly because they
  // must not have a constructor with argument SharedExpr;
  // otherwise, there will be overload ambiguity
  template<typename T>
  friend class internal::Term;

protected:
  // Subclasses must avoid exception safety
  // issues by not leaking the pointer
  SharedExpr(Expr* const ptr) noexcept
  : m_ptr(ptr)
  {
    assert(m_ptr != nullptr);

    inc();
  }

public:
  SharedExpr() noexcept
  : m_ptr(nullptr) {}

  SharedExpr(const SharedExpr& other) noexcept
  : m_ptr(other.m_ptr)
  {
    inc();
  }

  SharedExpr(SharedExpr&& other) noexcept
  : m_ptr(other.m_ptr)
  {
    // move semantics allow us to bypass inc()
    other.m_ptr = nullptr;
  }

  ~SharedExpr()
  {
    dec();
  }

  bool is_null() const noexcept
  {
    return m_ptr == nullptr;
  }

  /// memory address of underlying SMT expression
  uintptr_t addr() const noexcept
  {
    return reinterpret_cast<uintptr_t>(m_ptr);
  }

  SharedExpr& operator=(const SharedExpr& other) noexcept
  {
    other.inc();
    dec();
    m_ptr = other.m_ptr;

    return *this;
  }

  SharedExpr& operator=(SharedExpr&& other) noexcept
  {
    dec();
    m_ptr = other.m_ptr;

    // move semantics allow us to bypass inc()
    other.m_ptr = nullptr;

    return *this;
  }

  template<typename T>
  explicit operator T() const
  {
    return T(m_ptr);
  }

  /// \pre !is_null()
  const Expr& ref() const
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

#ifdef ENABLE_HASH_CONS
  /// \pre !is_null()
  Expr::Hash hash() const
  {
    assert(!is_null());
    return m_ptr->hash();
  }
#endif

  /// \internal \pre !is_null()
  Error encode(Solver& solver) const
  {
    assert(!is_null());
    return m_ptr->encode(solver);
  }
};

/// Temporaries only constructable via make_shared_expr(Args&&...)

/// This intermediate type avoids overload ambiguity and unwanted casts.
class MakeSharedExpr : public SharedExpr
{
private:
  // external linkage
  template<typename T, class... Args>
  friend MakeSharedExpr make_shared_expr(Args&&...);

protected:
  MakeSharedExpr(Expr* const ptr) noexcept
  : SharedExpr(ptr) {}

public:
  // maintainer note: always use RVO instead of copy or move!
  MakeSharedExpr() = delete;
  MakeSharedExpr(const MakeSharedExpr&) = delete;
  MakeSharedExpr(MakeSharedExpr&&) = delete;
};

#ifdef ENABLE_HASH_CONS
namespace internal
{
  /// Hash table that contains expressions of type T

  /// It is safe for an expression store to have static storage duration.
  template<typename T>
  class ExprStore
  {
  private:
    typedef std::unordered_multimap<Expr::Hash, T* const> Multimap;
    Multimap m_multimap;

  public:
    typedef typename Multimap::iterator Iterator;
    typedef typename Multimap::const_iterator ConstIterator;

    ExprStore()
    : m_multimap() {}

    // maintainer note: it is this destructor that makes
    // static storage duration of expression stores safe
    ~ExprStore()
    {
      for (typename Multimap::value_type& pair : m_multimap)
        pair.second->release_from_store();

      m_multimap.clear();
    }

    /// Return all expressions that have the given hash key
    ConstIterator find(const Expr::Hash hash) const
    {
      return m_multimap.find(hash);
    }

    ConstIterator cend() const
    {
      return m_multimap.cend();
    }

    /// Add expression T to store

    /// The newly added T expression removes itself from this
    /// expression store when T's destructor is called.
    template<class... Args>
    Iterator emplace(const Expr::Hash hash, Args&&... args)
    {
      return m_multimap.emplace(hash,
        new T(this, hash, std::forward<Args>(args)...));
    }

    void erase(const ConstIterator citer)
    {
      m_multimap.erase(citer);
    }
  };
}

/// Hash consing
template<typename T, class... Args>
MakeSharedExpr make_shared_expr(Args&&... args)
{
  // unique hash table for expressions of type T
  static internal::ExprStore<T> s_expr_multimap;

  const Expr::Hash hash = T::hash_args(args...);
  {
    typename internal::ExprStore<T>::ConstIterator citer =
      s_expr_multimap.find(hash);

    for (const typename internal::ExprStore<T>::ConstIterator
         cend = s_expr_multimap.cend();

         citer != cend;
         ++citer)
    {
      T* const expr_ptr = citer->second;
      if (expr_ptr->is_equal(args...))
        return {expr_ptr};
    }
  }

  typename internal::ExprStore<T>::Iterator iter =
    s_expr_multimap.emplace(hash, std::forward<Args>(args)...);

  return {iter->second};
}

#else
/// No hash consing
template<typename T, class... Args>
MakeSharedExpr make_shared_expr(Args&&... args)
{
  // use RVO instead of copy or move constructor
  return {new T(std::forward<Args>(args)...)};
}
#endif

namespace internal
{
  template<>
  struct EncodeDispatch<LNOT>
  {
    static Error encode_unary(
      Solver* const solver,
      const Expr* const expr,
      const SharedExpr& arg)
    {
      return solver->__encode_unary_lnot(expr, arg);
    }

    static Error encode_binary(
      Solver* const solver,
      const Expr* const expr,
      const SharedExpr& larg,
      const SharedExpr& rarg)
    {
      return OPCODE_ERROR;
    }
  };

  template<>
  struct EncodeDispatch<NOT>
  {
    static Error encode_unary(
      Solver* const solver,
      const Expr* const expr,
      const SharedExpr& arg)
    {
      return solver->__encode_unary_not(expr, arg);
    }

    static Error encode_binary(
      Solver* const solver,
      const Expr* const expr,
      const SharedExpr& larg,
      const SharedExpr& rarg)
    {
      return OPCODE_ERROR;
    }
  };

  template<>
  struct EncodeDispatch<SUB>
  {
    static Error encode_unary(
      Solver* const solver,
      const Expr* const expr,
      const SharedExpr& arg)
    {
      return solver->__encode_unary_sub(expr, arg);
    }

    static Error encode_binary(
      Solver* const solver,
      const Expr* const expr,
      const SharedExpr& larg,
      const SharedExpr& rarg)
    {
      return solver->__encode_binary_sub(expr, larg, rarg);
    }
  };

  template<>
  struct EncodeDispatch<AND>
  {
    static Error encode_unary(
      Solver* const solver,
      const Expr* const expr,
      const SharedExpr& arg)
    {
      return OPCODE_ERROR;
    }

    static Error encode_binary(
      Solver* const solver,
      const Expr* const expr,
      const SharedExpr& larg,
      const SharedExpr& rarg)
    {
      return solver->__encode_binary_and(expr, larg, rarg);
    }
  };

  template<>
  struct EncodeDispatch<OR>
  {
    static Error encode_unary(
      Solver* const solver,
      const Expr* const expr,
      const SharedExpr& arg)
    {
      return OPCODE_ERROR;
    }

    static Error encode_binary(
      Solver* const solver,
      const Expr* const expr,
      const SharedExpr& larg,
      const SharedExpr& rarg)
    {
      return solver->__encode_binary_or(expr, larg, rarg);
    }
  };

  template<>
  struct EncodeDispatch<XOR>
  {
    static Error encode_unary(
      Solver* const solver,
      const Expr* const expr,
      const SharedExpr& arg)
    {
      return OPCODE_ERROR;
    }

    static Error encode_binary(
      Solver* const solver,
      const Expr* const expr,
      const SharedExpr& larg,
      const SharedExpr& rarg)
    {
      return solver->__encode_binary_xor(expr, larg, rarg);
    }
  };

  template<>
  struct EncodeDispatch<LAND>
  {
    static Error encode_unary(
      Solver* const solver,
      const Expr* const expr,
      const SharedExpr& arg)
    {
      return OPCODE_ERROR;
    }

    static Error encode_binary(
      Solver* const solver,
      const Expr* const expr,
      const SharedExpr& larg,
      const SharedExpr& rarg)
    {
      solver->m_stats.conjunctions++;
      return solver->__encode_binary_land(expr, larg, rarg);
    }
  };

  template<>
  struct EncodeDispatch<LOR>
  {
    static Error encode_unary(
      Solver* const solver,
      const Expr* const expr,
      const SharedExpr& arg)
    {
      return OPCODE_ERROR;
    }

    static Error encode_binary(
      Solver* const solver,
      const Expr* const expr,
      const SharedExpr& larg,
      const SharedExpr& rarg)
    {
      solver->m_stats.disjunctions++;
      return solver->__encode_binary_lor(expr, larg, rarg);
    }
  };

  template<>
  struct EncodeDispatch<IMP>
  {
    static Error encode_unary(
      Solver* const solver,
      const Expr* const expr,
      const SharedExpr& arg)
    {
      return OPCODE_ERROR;
    }

    static Error encode_binary(
      Solver* const solver,
      const Expr* const expr,
      const SharedExpr& larg,
      const SharedExpr& rarg)
    {
      solver->m_stats.implications++;
      return solver->__encode_binary_imp(expr, larg, rarg);
    }
  };

  template<>
  struct EncodeDispatch<EQL>
  {
    static Error encode_unary(
      Solver* const solver,
      const Expr* const expr,
      const SharedExpr& arg)
    {
      return OPCODE_ERROR;
    }

    static Error encode_binary(
      Solver* const solver,
      const Expr* const expr,
      const SharedExpr& larg,
      const SharedExpr& rarg)
    {
      solver->m_stats.equalities++;
      return solver->__encode_binary_eql(expr, larg, rarg);
    }
  };

  template<>
  struct EncodeDispatch<ADD>
  {
    static Error encode_unary(
      Solver* const solver,
      const Expr* const expr,
      const SharedExpr& arg)
    {
      return OPCODE_ERROR;
    }

    static Error encode_binary(
      Solver* const solver,
      const Expr* const expr,
      const SharedExpr& larg,
      const SharedExpr& rarg)
    {
      return solver->__encode_binary_add(expr, larg, rarg);
    }
  };

  template<>
  struct EncodeDispatch<MUL>
  {
    static Error encode_unary(
      Solver* const solver,
      const Expr* const expr,
      const SharedExpr& arg)
    {
      return OPCODE_ERROR;
    }

    static Error encode_binary(
      Solver* const solver,
      const Expr* const expr,
      const SharedExpr& larg,
      const SharedExpr& rarg)
    {
      return solver->__encode_binary_mul(expr, larg, rarg);
    }
  };

  template<>
  struct EncodeDispatch<QUO>
  {
    static Error encode_unary(
      Solver* const solver,
      const Expr* const expr,
      const SharedExpr& arg)
    {
      return OPCODE_ERROR;
    }

    static Error encode_binary(
      Solver* const solver,
      const Expr* const expr,
      const SharedExpr& larg,
      const SharedExpr& rarg)
    {
      return solver->__encode_binary_quo(expr, larg, rarg);
    }
  };

  template<>
  struct EncodeDispatch<REM>
  {
    static Error encode_unary(
      Solver* const solver,
      const Expr* const expr,
      const SharedExpr& arg)
    {
      return OPCODE_ERROR;
    }

    static Error encode_binary(
      Solver* const solver,
      const Expr* const expr,
      const SharedExpr& larg,
      const SharedExpr& rarg)
    {
      return solver->__encode_binary_rem(expr, larg, rarg);
    }
  };

  template<>
  struct EncodeDispatch<LSS>
  {
    static Error encode_unary(
      Solver* const solver,
      const Expr* const expr,
      const SharedExpr& arg)
    {
      return OPCODE_ERROR;
    }

    static Error encode_binary(
      Solver* const solver,
      const Expr* const expr,
      const SharedExpr& larg,
      const SharedExpr& rarg)
    {
      solver->m_stats.inequalities++;
      return solver->__encode_binary_lss(expr, larg, rarg);
    }
  };

  template<>
  struct EncodeDispatch<GTR>
  {
    static Error encode_unary(
      Solver* const solver,
      const Expr* const expr,
      const SharedExpr& arg)
    {
      return OPCODE_ERROR;
    }

    static Error encode_binary(
      Solver* const solver,
      const Expr* const expr,
      const SharedExpr& larg,
      const SharedExpr& rarg)
    {
      solver->m_stats.inequalities++;
      return solver->__encode_binary_gtr(expr, larg, rarg);
    }
  };

  template<>
  struct EncodeDispatch<NEQ>
  {
    static Error encode_unary(
      Solver* const solver,
      const Expr* const expr,
      const SharedExpr& arg)
    {
      return OPCODE_ERROR;
    }

    static Error encode_binary(
      Solver* const solver,
      const Expr* const expr,
      const SharedExpr& larg,
      const SharedExpr& rarg)
    {
      solver->m_stats.disequalities++;
      return solver->__encode_binary_neq(expr, larg, rarg);
    }
  };

  template<>
  struct EncodeDispatch<LEQ>
  {
    static Error encode_unary(
      Solver* const solver,
      const Expr* const expr,
      const SharedExpr& arg)
    {
      return OPCODE_ERROR;
    }

    static Error encode_binary(
      Solver* const solver,
      const Expr* const expr,
      const SharedExpr& larg,
      const SharedExpr& rarg)
    {
      solver->m_stats.inequalities++;
      return solver->__encode_binary_leq(expr, larg, rarg);
    }
  };

  template<>
  struct EncodeDispatch<GEQ>
  {
    static Error encode_unary(
      Solver* const solver,
      const Expr* const expr,
      const SharedExpr& arg)
    {
      return OPCODE_ERROR;
    }

    static Error encode_binary(
      Solver* const solver,
      const Expr* const expr,
      const SharedExpr& larg,
      const SharedExpr& rarg)
    {
      solver->m_stats.inequalities++;
      return solver->__encode_binary_geq(expr, larg, rarg);
    }
  };
}

template<Opcode opcode>
Error Solver::encode_unary(
  const Expr* const expr,
  const SharedExpr& arg)
{
  ElapsedTimer timer(m_stats.encode_elapsed_time, m_is_timer_on);

  assert(!arg.is_null());

  m_stats.unary_ops++;
  return internal::EncodeDispatch<opcode>::encode_unary(this, expr, arg);
}

template<Opcode opcode>
Error Solver::encode_binary(
  const Expr* const expr,
  const SharedExpr& larg,
  const SharedExpr& rarg)
{
  ElapsedTimer timer(m_stats.encode_elapsed_time, m_is_timer_on);

  assert(!larg.is_null());
  assert(!rarg.is_null());
  assert(larg.sort() == rarg.sort());

  m_stats.binary_ops++;
  return internal::EncodeDispatch<opcode>::encode_binary(
    this, expr, larg, rarg);
}

namespace internal
{
  /// Shared and well-sorted SMT expression

  /// Supported built-in operators depends on the type T.

  /// Subclasses must use the curiously recurring template pattern (CRTP)
  /// in order to support recursive sorts such as Func<T...>.
  template<typename T>
  class Term
  {
  private:
    SharedExpr m_ptr;

  protected:
    // Must be private in subclass but callable by
    // SharedExpr's conversion operator
    Term(Expr* const ptr)
    : m_ptr(ptr)
    {
      assert(is_null() || internal::sort<T>() == sort());
    }

    // Must be public in subclass; this visibility is OK
    // because MakeSharedExpr is only constructable by
    // make_shared_expr(Args&&...) function. The public
    // constructor in subclass serves as documentation.
    Term(MakeSharedExpr&& ptr)
    : m_ptr(std::move(ptr))
    {
      assert(is_null() || internal::sort<T>() == sort());
    }

    // See "Virtuality" article by Herb Sutter:
    //   [If you do not] want to allow polymorphic deletion
    //   through a base pointer, [then] the destructor
    //   should be nonvirtual and protected, the latter
    //   to prevent the unwanted usage.
    ~Term() {}

  public:
    Term() noexcept
    : m_ptr() {}

    Term(const Term& other)
    : m_ptr(other.m_ptr)
    {
      assert(is_null() || internal::sort<T>() == sort());
    }

    Term(Term&& other)
    : m_ptr(std::move(other.m_ptr))
    {
      assert(is_null() || internal::sort<T>() == sort());
    }

    Term& operator=(const Term& other) 
    {
      assert(other.is_null() || internal::sort<T>() == other.sort());

      m_ptr = other.m_ptr;
      return *this;
    }

    Term& operator=(Term&& other)
    {
      assert(other.is_null() || internal::sort<T>() == other.sort());

      m_ptr = std::move(other.m_ptr);
      return *this;
    }

    operator SharedExpr() const noexcept
    {
      return m_ptr;
    }

    bool is_null() const noexcept
    {
      return m_ptr.is_null();
    }

    /// memory address of underlying SMT expression
    uintptr_t addr() const noexcept
    {
      return m_ptr.addr();
    }

    /// \pre !is_null()
    const Expr& ref() const
    {
      return m_ptr.ref();
    }

    /// \pre !is_null()
    ExprKind expr_kind() const
    {
      return m_ptr.expr_kind();
    }

    /// \pre !is_null()
    const Sort& sort() const
    {
      return m_ptr.sort();
    }
  };
}

class Bool : public internal::Term<Bool>
{
private:
  typedef internal::Term<Bool> Super;

  friend class SharedExpr;
  Bool(Expr* const ptr) : Super(ptr) {}

public:
  Bool() : Super() {}
  Bool(const Bool& other) : Super(other) {}
  Bool(Bool&& other) : Super(std::move(other)) {}
  Bool(MakeSharedExpr&& ptr) : Super(std::move(ptr)) {}

  Bool& operator=(const Bool& other)
  {
    Super::operator=(other);
    return *this;
  }

  Bool& operator=(Bool&& other)
  {
    Super::operator=(std::move(other));
    return *this;
  }
};

class Int : public internal::Term<Int>
{
private:
  typedef internal::Term<Int> Super;

  friend class SharedExpr;
  Int(Expr* const ptr) : Super(ptr) {}

public:
  Int() : Super() {}
  Int(const Int& other) : Super(other) {}
  Int(Int&& other) : Super(std::move(other)) {}
  Int(MakeSharedExpr&& ptr) : Super(std::move(ptr)) {}

  Int& operator=(const Int& other)
  {
    Super::operator=(other);
    return *this;
  }

  Int& operator=(Int&& other)
  {
    Super::operator=(std::move(other));
    return *this;
  }
};

class Real : public internal::Term<Real>
{
private:
  typedef internal::Term<Real> Super;

  friend class SharedExpr;
  Real(Expr* const ptr) : Super(ptr) {}

public:
  Real() : Super() {}
  Real(const Real& other) : Super(other) {}
  Real(Real&& other) : Super(std::move(other)) {}
  Real(MakeSharedExpr&& ptr) : Super(std::move(ptr)) {}

  Real& operator=(const Real& other)
  {
    Super::operator=(other);
    return *this;
  }

  Real& operator=(Real&& other)
  {
    Super::operator=(std::move(other));
    return *this;
  }
};

/// Fixed-size bit vector

/// The least significant bit is at the right-most position.
template<typename T, typename Enable =
  typename std::enable_if<std::is_integral<T>::value>::type>
class Bv : public internal::Term<Bv<T>>
{
private:
  typedef internal::Term<Bv<T>> Super;

  friend class SharedExpr;
  Bv(Expr* const ptr) : Super(ptr) {}

public:
  Bv() : Super() {}
  Bv(const Bv& other) : Super(other) {}
  Bv(Bv&& other) : Super(std::move(other)) {}
  Bv(MakeSharedExpr&& ptr) : Super(std::move(ptr)) {}

  Bv& operator=(const Bv& other)
  {
    Super::operator=(other);
    return *this;
  }

  Bv& operator=(Bv&& other)
  {
    Super::operator=(std::move(other));
    return *this;
  }
};

/// McCarthy Array
template<typename Domain, typename Range>
class Array : public internal::Term<Array<Domain, Range>>
{
private:
  typedef internal::Term<Array<Domain, Range>> Super;

public:
  Array() : Super() {}
  Array(const Array& other) : Super(other) {}
  Array(Array&& other) : Super(std::move(other)) {}
  Array(MakeSharedExpr&& ptr) : Super(std::move(ptr)) {}

  Array& operator=(const Array& other)
  {
    Super::operator=(other);
    return *this;
  }

  Array& operator=(Array&& other)
  {
    Super::operator=(std::move(other));
    return *this;
  }
};

namespace internal
{
  template<typename... T>
  struct RemoveLast;

  template<typename T, typename U>
  struct RemoveLast<T, U>
  {
    typedef std::tuple<T> Type;
  };

  template<typename T, typename... U>
  struct RemoveLast<T, U...>
  {
    typedef decltype(std::tuple_cat(std::make_tuple(std::declval<T>()),
      std::declval<typename RemoveLast<U...>::Type>())) Type;
  };
}

/// Uninterpreted function
template<typename... T>
class Func : public internal::Term<Func<T...>>
{
private:
  typedef internal::Term<Func<T...>> Super;

public:
  static constexpr size_t arity = sizeof...(T) - 1;

  typedef typename internal::RemoveLast<T...>::Type Args;

  // last tuple element
  typedef typename std::tuple_element<arity,
    std::tuple<T...>>::type Range;

  Func() : Super() {}
  Func(const Func& other) : Super(other) {}
  Func(Func&& other) : Super(std::move(other)) {}
  Func(MakeSharedExpr&& ptr) : Super(std::move(ptr)) {}

  Func& operator=(const Func& other)
  {
    Super::operator=(other);
    return *this;
  }

  Func& operator=(Func&& other)
  {
    Super::operator=(std::move(other));
    return *this;
  }
};

#ifdef ENABLE_HASH_CONS
namespace internal
{
  /// Subclass must be of type T, i.e. CRTP
  template<typename T>
  class ExprDeleter
  {
  protected:
    /// \internal Raw pointer to expression store
    typedef internal::ExprStore<T>* ExprStorePtr;

  private:
    ExprStorePtr m_expr_store_ptr;

  protected:
    ExprDeleter()
    : m_expr_store_ptr(nullptr) {}

    ExprDeleter(ExprStorePtr expr_store_ptr)
    : m_expr_store_ptr(expr_store_ptr) {}

    ~ExprDeleter() {}

    /// Must be called by subclass T's destructor
    void delete_from_store(const T* const derived)
    {
      if (m_expr_store_ptr == nullptr)
        return;

      ExprStore<T>& expr_store = *m_expr_store_ptr;
      typename internal::ExprStore<T>::ConstIterator citer =
        expr_store.find(derived->hash());

      for (const typename internal::ExprStore<T>::ConstIterator
           cend = expr_store.cend();

           citer != cend;
           ++citer)
      {
        T* const expr_ptr = citer->second;
        if (derived->is_equal(*expr_ptr))
        {
          expr_store.erase(citer);
          goto OK;
        }
      }

      assert(false && "Failed to delete expression");
    OK: ;
    }

  public:
    void release_from_store()
    {
      m_expr_store_ptr = nullptr;
    }
  };
}
#endif

template<typename T>
class LiteralExpr : public Expr
#ifdef ENABLE_HASH_CONS
, public internal::ExprDeleter<LiteralExpr<T>>
#endif
{
  const T m_literal;

  virtual Error __encode(Solver& solver) const override
  {
    return solver.encode_literal(this, m_literal);
  }

public:
#ifdef ENABLE_HASH_CONS
  typedef internal::ExprDeleter<LiteralExpr<T>> Deleter;

  static Expr::Hash hash_args(const Sort& sort, T literal)
  {
    // see also http://planetmath.org/goodhashtableprimes
    constexpr size_t good_hash_table_prime = 196613;
    return hash_combine(literal * good_hash_table_prime, sort.hash());
  }

  /// \internal
  LiteralExpr(
    typename Deleter::ExprStorePtr expr_store_ptr,
    Hash hash,
    const Sort& sort,
    T literal)
  : Expr(LITERAL_EXPR_KIND, sort, hash),
    Deleter(expr_store_ptr),
    m_literal(literal) {}

  ~LiteralExpr()
  {
    Deleter::delete_from_store(this);
  }
#endif

  // Allocate sort statically!
  LiteralExpr(const Sort& sort, T literal)
  : Expr(LITERAL_EXPR_KIND, sort),
    m_literal(literal) {}

  const T literal() const
  {
    return m_literal;
  }

  bool is_equal(const LiteralExpr<T>& other) const
  {
    return is_equal(other.sort(), other.m_literal);
  }

  bool is_equal(const Sort& sort, T literal) const
  {
    return Expr::sort() == sort && m_literal == literal;
  }
};

class ConstantExpr : public Expr
#ifdef ENABLE_HASH_CONS
, public internal::ExprDeleter<ConstantExpr>
#endif
{
private:
  const UnsafeDecl m_decl;

  virtual Error __encode(Solver& solver) const override
  {
    return solver.encode_constant(this, m_decl);
  }

public:
#ifdef ENABLE_HASH_CONS
  typedef internal::ExprDeleter<ConstantExpr> Deleter;

  static Expr::Hash hash_args(const UnsafeDecl& decl)
  {
    return decl.hash();
  }

  /// \internal
  ConstantExpr(
    typename Deleter::ExprStorePtr expr_store_ptr,
    Expr::Hash hash,
    const UnsafeDecl& decl)
  : Expr(CONSTANT_EXPR_KIND, decl.sort(), hash),
    Deleter(expr_store_ptr),
    m_decl(decl) {}

  ~ConstantExpr()
  {
    Deleter::delete_from_store(this);
  }
#endif

  ConstantExpr(const UnsafeDecl& decl)
  : Expr(CONSTANT_EXPR_KIND, decl.sort()),
    m_decl(decl) {}

  const UnsafeDecl& decl() const
  {
    return m_decl;
  }

  bool is_equal(const UnsafeDecl& decl) const
  {
    return m_decl == decl;
  }

  bool is_equal(const ConstantExpr& other) const
  {
    return is_equal(other.m_decl);
  }
};

/// For example, if \c x is equal to \c #110, then \c BvZeroExtendExpr(x, 4)
/// is a bit vector of length seven (= 3+4) that is equal to \c #b0000110.
class BvZeroExtendExpr : public Expr
#ifdef ENABLE_HASH_CONS
, public internal::ExprDeleter<BvZeroExtendExpr>
#endif
{
private:
  const SharedExpr m_bv;
  const unsigned m_ext;

  virtual Error __encode(Solver& solver) const override
  {
    return solver.encode_bv_zero_extend(this, m_bv, m_ext);
  }

  void check_obj() const
  {
    assert(Expr::sort().is_bv());
    assert(!m_bv.sort().is_signed());
    assert(Expr::sort().bv_size() > m_bv.sort().bv_size());
    assert(m_ext == Expr::sort().bv_size() - m_bv.sort().bv_size());

    // no truncation in above subtraction
    assert(m_ext > 0);
  }

public:
#ifdef ENABLE_HASH_CONS
  typedef internal::ExprDeleter<BvZeroExtendExpr> Deleter;

  static Expr::Hash hash_args(
    const Sort& sort,
    const SharedExpr& bv,
    unsigned ext)
  {
    size_t h = hash_combine(sort.hash(), bv.hash());
    h = hash_combine(ext * 402653189, h);
    return h;
  }

  /// \internal
  BvZeroExtendExpr(
    typename Deleter::ExprStorePtr expr_store_ptr,
    Expr::Hash hash,
    const Sort& sort,
    const SharedExpr& bv,
    unsigned ext)
  : Expr(BV_ZERO_EXTEND_EXPR_KIND, sort, hash),
    Deleter(expr_store_ptr),
    m_bv(bv), m_ext(ext)
  {
    check_obj();
  }

  ~BvZeroExtendExpr()
  {
    Deleter::delete_from_store(this);
  }
#endif

  /// Allocate sort statically!
  BvZeroExtendExpr(const Sort& sort, const SharedExpr& bv, unsigned ext)
  : Expr(BV_ZERO_EXTEND_EXPR_KIND, sort),
    m_bv(bv), m_ext(ext)
  {
    check_obj();
  }

  bool is_equal(
    const Sort& sort,
    const SharedExpr& bv,
    unsigned ext) const
  {
    return Expr::sort() == sort &&
      m_bv.addr() == bv.addr() &&
      m_ext == ext;
  }

  bool is_equal(const BvZeroExtendExpr& other) const
  {
    return is_equal(other.sort(), other.m_bv, other.m_ext);
  }
};

/// For example, if \c x is equal to \c #110, then \c BvSignExtendExpr(x, 4)
/// is a bit vector of length seven (= 3+4) that is equal to \c #b1111110.
class BvSignExtendExpr : public Expr
#ifdef ENABLE_HASH_CONS
, public internal::ExprDeleter<BvSignExtendExpr>
#endif
{
private:
  const SharedExpr m_bv;
  const unsigned m_ext;

  virtual Error __encode(Solver& solver) const override
  {
    return solver.encode_bv_sign_extend(this, m_bv, m_ext);
  }

  void check_obj() const
  {
    assert(Expr::sort().is_bv());
    assert(m_bv.sort().is_signed());
    assert(Expr::sort().bv_size() > m_bv.sort().bv_size());
    assert(m_ext == Expr::sort().bv_size() - m_bv.sort().bv_size());

    // no truncation in above subtraction
    assert(m_ext > 0);
  }

public:
#ifdef ENABLE_HASH_CONS
  typedef internal::ExprDeleter<BvSignExtendExpr> Deleter;

  static Expr::Hash hash_args(
    const Sort& sort,
    const SharedExpr& bv,
    unsigned ext)
  {
    size_t h = hash_combine(sort.hash(), bv.hash());
    h = hash_combine(ext * 402653189, h);
    return h;
  }

  /// \internal
  BvSignExtendExpr(
    typename Deleter::ExprStorePtr expr_store_ptr,
    Expr::Hash hash,
    const Sort& sort,
    const SharedExpr& bv,
    unsigned ext)
  : Expr(BV_SIGN_EXTEND_EXPR_KIND, sort, hash),
    Deleter(expr_store_ptr),
    m_bv(bv), m_ext(ext)
  {
    check_obj();
  }

  ~BvSignExtendExpr()
  {
    Deleter::delete_from_store(this);
  }
#endif

  /// Allocate sort statically!
  BvSignExtendExpr(const Sort& sort, const SharedExpr& bv, unsigned ext)
  : Expr(BV_SIGN_EXTEND_EXPR_KIND, sort),
    m_bv(bv), m_ext(ext)
  {
    check_obj();
  }

  bool is_equal(
    const Sort& sort,
    const SharedExpr& bv,
    unsigned ext) const
  {
    return Expr::sort() == sort &&
      m_bv.addr() == bv.addr() &&
      m_ext == ext;
  }

  bool is_equal(const BvSignExtendExpr& other) const
  {
    return is_equal(other.sort(), other.m_bv, other.m_ext);
  }
};

/// For example, if \c x is equal to \c #b00011, then \c BvExtractExpr(x, 2, 0)
/// is a bit vector of length three (0..2 inclusive) that is equal to \c #b011.
class BvExtractExpr : public Expr
#ifdef ENABLE_HASH_CONS
, public internal::ExprDeleter<BvExtractExpr>
#endif
{
private:
  const SharedExpr m_bv;
  const unsigned m_high;
  const unsigned m_low;

  virtual Error __encode(Solver& solver) const override
  {
    return solver.encode_bv_extract(this, m_bv, m_high, m_low);
  }

  void check_obj() const
  {
    assert(m_high > m_low);

    assert(Expr::sort().is_bv());
    assert(Expr::sort().bv_size() == (m_high - m_low) + 1);
  }

public:
#ifdef ENABLE_HASH_CONS
  typedef internal::ExprDeleter<BvExtractExpr> Deleter;

  static Expr::Hash hash_args(
    const Sort& sort,
    const SharedExpr& bv,
    unsigned high,
    unsigned low)
  {
    size_t h = hash_combine(sort.hash(), bv.hash());
    h = hash_combine(high * 402653189, h);
    h = hash_combine(low * 402653189, h);
    return h;
  }

  /// \internal
  BvExtractExpr(
    typename Deleter::ExprStorePtr expr_store_ptr,
    Expr::Hash hash,
    const Sort& sort,
    const SharedExpr& bv,
    unsigned high,
    unsigned low)
  : Expr(BV_EXTRACT_EXPR_KIND, sort, hash),
    Deleter(expr_store_ptr),
    m_bv(bv), m_high(high), m_low(low)
  {
    check_obj();
  }

  ~BvExtractExpr()
  {
    Deleter::delete_from_store(this);
  }
#endif

  /// Allocate sort statically!

  /// \pre: high > low
  BvExtractExpr(const Sort& sort, const SharedExpr& bv, unsigned high, unsigned low)
  : Expr(BV_EXTRACT_EXPR_KIND, sort),
    m_bv(bv), m_high(high), m_low(low)
  {
    check_obj();
  }

  bool is_equal(
    const Sort& sort,
    const SharedExpr& bv,
    unsigned high,
    unsigned low) const
  {
    return Expr::sort() == sort &&
      m_bv.addr() == bv.addr() &&
      m_high == high &&
      m_low == low;
  }

  bool is_equal(const BvExtractExpr& other) const
  {
    return is_equal(other.sort(), other.m_bv, other.m_high, other.m_low);
  }
};

namespace internal
{
  struct BvZeroExtend
  {
    BvZeroExtend() = delete;

    template<typename T, typename S>
    static Bv<T> bv_cast(const Bv<S>& source)
    {
      static_assert(__Bv<T>::bv_size() > __Bv<S>::bv_size(),
        "Bit vector size of target must be strictly greater than source's bit vector size");

      constexpr unsigned ext = __Bv<T>::bv_size() - __Bv<S>::bv_size();
      return Bv<T>(make_shared_expr<BvZeroExtendExpr>(internal::sort<T>(), source, ext));
    }
  };

  struct BvSignExtend
  {
    BvSignExtend() = delete;

    template<typename T, typename S>
    static Bv<T> bv_cast(const Bv<S>& source)
    {
      static_assert(__Bv<T>::bv_size() > __Bv<S>::bv_size(),
        "Bit vector size of target must be strictly greater than source's bit vector size");

      constexpr unsigned ext = __Bv<T>::bv_size() - __Bv<S>::bv_size();
      return Bv<T>(make_shared_expr<BvSignExtendExpr>(internal::sort<T>(), source, ext));
    }
  };

  struct BvTruncate
  {
  public:
    BvTruncate() = delete;

    template<typename T, typename S>
    static Bv<T> bv_cast(const Bv<S>& source)
    {
      static_assert(0 < __Bv<T>::bv_size(),
        "Bit vector size of target must be strictly greater than zero");

      static_assert(__Bv<T>::bv_size() <= __Bv<S>::bv_size(),
        "Bit vector size of target must be less than or equal to source's bit vector size");

      constexpr unsigned high = __Bv<T>::bv_size() - 1;
      return Bv<T>(make_shared_expr<BvExtractExpr>(internal::sort<T>(), source, high, 0));
    }
  };

  struct BvExtend
  {
    BvExtend() = delete;

    template<typename T, typename S>
    static Bv<T> bv_cast(const Bv<S>& source)
    {
      // Recall that "a is congruent to b (modulo n)" if and only if n divides a - b.
      // According to the C++11 language specification, paragraph 4.7:
      //
      //   If the destination type is unsigned, the resulting value is the
      //   smallest unsigned value equal to the source value modulo 2^n
      //   where n is the number of bits used to represent the destination type.
      //
      //   \see_also:
      //     http://en.cppreference.com/w/cpp/language/implicit_cast#Integral_conversions
      //
      // Example:
      //
      //   signed int x = -1;
      //   unsigned long y = x;
      //   assert(std::numeric_limits<unsigned long>::max() == y);
      //
      // In the example, the assertion always holds because the least unsigned integer
      // congruent to -1 (modulo 2^N where N = 8 * sizeof(unsigned long)) is the max
      // value of unsigned long. Note that the modulo arithmetic is with respect to
      // mathematical numbers (as opposed to finite bit vectors).
      //
      // Thus, on 2's complement platforms (assumed here), if source is signed,
      // then we apply sign extension (regardless of target).
      return std::conditional<
        /* if */ std::is_signed<S>::value,
        /* then */ internal::BvSignExtend,
        /* else */ internal::BvZeroExtend>::type::template bv_cast<T, S>(source);
    }
  };
}

template<typename T, typename S>
Bv<T> bv_cast(const Bv<S>& source)
{
  // TODO: optimize, if sizeof(T) is equal to sizeof(S), then
  // we still truncate so that T's signedness is as expected.
  return std::conditional<
    /* if */ sizeof(T) <= sizeof(S),
    /* then */ internal::BvTruncate,
    /* else */ internal::BvExtend>::type::template bv_cast<T, S>(source);
}

template<typename T>
Bv<T> bv_cast(const Bv<T>& source)
{
  return source;
}

template<size_t arity>
class FuncAppExpr : public Expr
#ifdef ENABLE_HASH_CONS
, public internal::ExprDeleter<FuncAppExpr<arity>>
#endif
{
private:
  const UnsafeDecl m_func_decl;
  const std::array<SharedExpr, arity> m_args;

  virtual Error __encode(Solver& solver) const override
  {
    return solver.encode_func_app(this, m_func_decl, arity, m_args.data());
  }

public:
#ifdef ENABLE_HASH_CONS
  typedef internal::ExprDeleter<FuncAppExpr<arity>> Deleter;

  static Expr::Hash hash_args(
    const UnsafeDecl& func_decl,
    const std::array<SharedExpr, arity>& args)
  {
    size_t h = func_decl.sort().hash();
    for (const SharedExpr& arg : args)
      h = hash_combine(h, arg.hash());

    return h;
  }

  /// \internal
  FuncAppExpr(
    typename Deleter::ExprStorePtr expr_store_ptr,
    Expr::Hash hash,
    const UnsafeDecl& func_decl,
    std::array<SharedExpr, arity>&& args)
  : Expr(FUNC_APP_EXPR_KIND, func_decl.sort().sorts(arity), hash),
    Deleter(expr_store_ptr),
    m_func_decl(func_decl),
    m_args(std::move(args)) {}

  ~FuncAppExpr()
  {
    Deleter::delete_from_store(this);
  }
#endif

  FuncAppExpr(
    const UnsafeDecl& func_decl,
    std::array<SharedExpr, arity>&& args)
  : Expr(FUNC_APP_EXPR_KIND, func_decl.sort().sorts(arity)),
    m_func_decl(func_decl),
    m_args(std::move(args)) {}

  const std::array<SharedExpr, arity>& args() const
  {
    return m_args;
  }

  const UnsafeDecl& func_decl() const
  {
    return m_func_decl;
  }

  bool is_equal(
    const UnsafeDecl& func_decl,
    const std::array<SharedExpr, arity>& args) const
  {
    if (m_func_decl != func_decl)
      return false;

    bool args_equality = true;
    for (size_t i = 0; i < arity; ++i)
      args_equality &= m_args[i].addr() == args[i].addr();

    return args_equality;
  }

  bool is_equal(const FuncAppExpr<arity>& other) const
  {
    return is_equal(other.m_func_decl, other.m_args);
  }
};

namespace internal
{
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

  template<typename T>
  struct RemoveBv
  {
    typedef void Type;
  };

  template<typename T>
  struct RemoveBv<Bv<T>>
  {
    typedef T Type;
  };

  template<typename T>
  struct IsPrimitive :
    std::integral_constant<bool,
      std::is_integral<typename RemoveBv<T>::Type>::value
      or std::is_same<Bool, T>::value
      or std::is_same<Int, T>::value
      or std::is_same<Real, T>::value>
  {};
}

template<typename T>
inline SharedExpr literal(const Sort& sort, const T literal)
{
  return make_shared_expr<LiteralExpr<T>>(sort, literal);
}

template<typename T, typename U, typename Enable =
  typename std::enable_if<std::is_integral<U>::value and
  internal::IsPrimitive<T>::value>::type>
inline T literal(const U literal)
{
  return T(make_shared_expr<LiteralExpr<U>>(internal::sort<T>(), literal));
}

SharedExpr constant(const UnsafeDecl& decl);

template<typename T>
T constant(const Decl<T>& decl)
{
  return T(make_shared_expr<ConstantExpr>(decl));
}

SharedExpr apply(
  const UnsafeDecl& func_decl,
  const SharedExpr& arg);

SharedExpr apply(
  const UnsafeDecl& func_decl,
  const SharedExpr& larg,
  const SharedExpr& rarg);

// unary function application
template<typename Domain, typename Range, typename T,
  typename Enable = typename std::enable_if<std::is_integral<T>::value>::type>
Range apply(
  const Decl<Func<Domain, Range>>& func_decl,
  const T arg)
{
  return apply(func_decl, literal<Domain, T>(arg));
}

// unary function application
template<typename Domain, typename Range>
Range apply(
  const Decl<Func<Domain, Range>>& func_decl,
  const Domain& arg)
{
  return apply(func_decl, std::make_tuple(arg));
}

// binary function application
template<typename T, typename U, typename Range>
Range apply(
  const Decl<Func<T, U, Range>>& func_decl,
  const T& larg,
  const U& rarg)
{
  return apply(func_decl, std::make_tuple(larg, rarg));
}

// nary function application
template<typename... T>
typename Func<T...>::Range apply(
  const Decl<Func<T...>>& func_decl,
  const typename Func<T...>::Args& args)
{
  return typename Func<T...>::Range(
    make_shared_expr<FuncAppExpr<Func<T...>::arity>>(func_decl,
    internal::to_array<SharedExpr, typename Func<T...>::Args>(args)));
}

/// Counter must be globally unique

/// Prefix won't be freed by the constructed object.
/// Callers are encouraged to statically allocate prefix.
template<typename T>
T any(const char * const prefix, const unsigned counter)
{
  return constant(Decl<T>(prefix, counter));
}

/// Symbol name must be globally unique and nonempty
template<typename T>
T any(std::string&& symbol_name)
{
  return constant(Decl<T>(std::move(symbol_name)));
}

template<Opcode opcode>
class UnaryExpr : public Expr
#ifdef ENABLE_HASH_CONS
, public internal::ExprDeleter<UnaryExpr<opcode>>
#endif
{
private:
  const SharedExpr m_operand;

  virtual Error __encode(Solver& solver) const override
  {
    return solver.encode_unary<opcode>(this, m_operand);
  }

  void check_obj() const
  {
    assert(!m_operand.is_null());
  }

public:
#ifdef ENABLE_HASH_CONS
  typedef internal::ExprDeleter<UnaryExpr<opcode>> Deleter;

  static Expr::Hash hash_args(
    const Sort& sort,
    const SharedExpr& operand)
  {
    return hash_combine(sort.hash(), operand.hash());
  }

  /// \internal
  UnaryExpr(
    typename Deleter::ExprStorePtr expr_store_ptr,
    Expr::Hash hash,
    const Sort& sort,
    const SharedExpr& operand)
  : Expr(UNARY_EXPR_KIND, sort, hash),
    Deleter(expr_store_ptr),
    m_operand(operand)
  {
    check_obj();
  }

  /// \internal
  UnaryExpr(
    typename Deleter::ExprStorePtr expr_store_ptr,
    Expr::Hash hash,
    const Sort& sort,
    SharedExpr&& operand)
  : Expr(UNARY_EXPR_KIND, sort, hash),
    Deleter(expr_store_ptr),
    m_operand(std::move(operand))
  {
    check_obj();
  }

  ~UnaryExpr()
  {
    Deleter::delete_from_store(this);
  }
#endif

  // Allocate sort statically!
  UnaryExpr(
    const Sort& sort,
    const SharedExpr& operand)
  : Expr(UNARY_EXPR_KIND, sort),
    m_operand(operand)
  {
    check_obj();
  }

  // Allocate sort statically!
  UnaryExpr(
    const Sort& sort,
    SharedExpr&& operand)
  : Expr(UNARY_EXPR_KIND, sort),
    m_operand(std::move(operand))
  {
    check_obj();
  }

  const SharedExpr& operand() const
  {
    return m_operand;
  }

  bool is_equal(
    const Sort& sort,
    const SharedExpr& operand) const
  {
    return Expr::sort() == sort &&
      m_operand.addr() == operand.addr();
  }

  bool is_equal(const UnaryExpr<opcode>& other) const
  {
    return is_equal(other.sort(), other.m_operand);
  }
};

/// Two operand instruction whose operands must be the same sort
template<Opcode opcode>
class BinaryExpr : public Expr
#ifdef ENABLE_HASH_CONS
, public internal::ExprDeleter<BinaryExpr<opcode>>
#endif
{
private:
  const SharedExpr m_loperand;
  const SharedExpr m_roperand;

  virtual Error __encode(Solver& solver) const override
  {
    return solver.encode_binary<opcode>(this, m_loperand, m_roperand);
  }

  void check_obj() const
  {
    assert(!m_loperand.is_null());
    assert(!m_roperand.is_null());
    assert(m_loperand.sort() == m_roperand.sort());
  }

public:
#ifdef ENABLE_HASH_CONS
  typedef internal::ExprDeleter<BinaryExpr<opcode>> Deleter;

  static Expr::Hash hash_args(
    const Sort& sort,
    const SharedExpr& loperand,
    const SharedExpr& roperand)
  {
    size_t h = hash_combine(sort.hash(), loperand.hash());
    h = hash_combine(h, roperand.hash());
    return h;
  }

  /// \internal
  BinaryExpr(
    typename Deleter::ExprStorePtr expr_store_ptr,
    Expr::Hash hash,
    const Sort& sort,
    SharedExpr&& loperand,
    SharedExpr&& roperand)
  : Expr(BINARY_EXPR_KIND, sort, hash),
    Deleter(expr_store_ptr),
    m_loperand(std::move(loperand)),
    m_roperand(std::move(roperand))
  {
    check_obj();
  }

  /// \internal
  BinaryExpr(
    typename Deleter::ExprStorePtr expr_store_ptr,
    Expr::Hash hash,
    const Sort& sort,
    const SharedExpr& loperand,
    const SharedExpr& roperand)
  : Expr(BINARY_EXPR_KIND, sort, hash),
    Deleter(expr_store_ptr),
    m_loperand(loperand),
    m_roperand(roperand)
  {
    check_obj();
  }

  ~BinaryExpr()
  {
    Deleter::delete_from_store(this);
  }
#endif

  // Allocate sort statically, operands must have the same sort!
  BinaryExpr(
    const Sort& sort,
    const SharedExpr& loperand,
    const SharedExpr& roperand)
  : Expr(BINARY_EXPR_KIND, sort),
    m_loperand(loperand),
    m_roperand(roperand)
  {
    check_obj();
  }

  BinaryExpr(
    const Sort& sort,
    SharedExpr&& loperand,
    SharedExpr&& roperand)
  : Expr(BINARY_EXPR_KIND, sort),
    m_loperand(std::move(loperand)),
    m_roperand(std::move(roperand))
  {
    check_obj();
  }

  const SharedExpr& loperand() const
  {
    return m_loperand;
  }

  const SharedExpr& roperand() const
  {
    return m_roperand;
  }

  bool is_equal(
    const Sort& sort,
    const SharedExpr& loperand,
    const SharedExpr& roperand) const
  {
    return Expr::sort() == sort &&
      m_loperand.addr() == loperand.addr() &&
      m_roperand.addr() == roperand.addr();
  }

  bool is_equal(const BinaryExpr<opcode>& other) const
  {
    return is_equal(other.sort(), other.m_loperand, other.m_roperand);
  }
};

template<typename T>
class Terms
{
public:
  SharedExprs terms;

  Terms(size_t count)
  : terms()
  {
    terms.reserve(count);
  }

  Terms(Terms&& other)
  : terms(std::move(other.terms)) {}

  void push_back(const T& term)
  {
    terms.push_back(term);
  }

  size_t size() const
  {
    return terms.size();
  }

  T at(size_t pos) const
  {
    return static_cast<const T>(terms.at(pos));
  }
};

template<Opcode opcode>
class NaryExpr : public Expr
#ifdef ENABLE_HASH_CONS
, public internal::ExprDeleter<NaryExpr<opcode>>
#endif
{
private:
  const SharedExprs m_operands;

  virtual Error __encode(Solver& solver) const override
  {
    return solver.encode_nary(this, opcode, m_operands);
  }

  void check_obj() const
  {
    assert(!m_operands.empty());
  }

protected:
  const SharedExprs& operands() const
  {
    return m_operands;
  }

public:
#ifdef ENABLE_HASH_CONS
  typedef internal::ExprDeleter<NaryExpr<opcode>> Deleter;

  static Expr::Hash hash_args(const Sort& sort, const SharedExprs& operands)
  {
    size_t h = sort.hash();
    for (size_t i = 0; i < operands.size(); ++i)
      h = hash_combine(h, operands.at(i).hash());

    return h;
  }

  /// \internal
  NaryExpr(
    typename Deleter::ExprStorePtr expr_store_ptr,
    Expr::Hash hash,
    const Sort& sort,
    SharedExprs&& operands)
  : Expr(NARY_EXPR_KIND, sort, hash),
    Deleter(expr_store_ptr),
    m_operands(std::move(operands))
  {
    check_obj();
  }

  /// \internal
  NaryExpr(
    typename Deleter::ExprStorePtr expr_store_ptr,
    Expr::Hash hash,
    const Sort& sort,
    const SharedExprs& operands)
  : Expr(NARY_EXPR_KIND, sort, hash),
    Deleter(expr_store_ptr),
    m_operands(operands)
  {
    check_obj();
  }

  ~NaryExpr()
  {
    Deleter::delete_from_store(this);
  }
#endif

  // Sort must be statically allocated and
  // there must be at least one operand.
  NaryExpr(
    const Sort& sort,
    SharedExprs&& operands)
  : Expr(NARY_EXPR_KIND, sort),
    m_operands(std::move(operands))
  {
    check_obj();
  }

  // Sort must be statically allocated and
  // there must be at least one operand.
  NaryExpr(
    const Sort& sort,
    const SharedExprs& operands)
  : Expr(NARY_EXPR_KIND, sort),
    m_operands(operands)
  {
    check_obj();
  }

  size_t size() const
  {
    return m_operands.size();
  }

  const SharedExpr& operand(size_t n) const
  {
    return m_operands.at(n);
  }

  bool is_equal(
    const Sort& sort,
    const SharedExprs& operands) const
  {
    if (Expr::sort() != sort)
      return false;

    bool operands_equality = true;
    for (size_t i = 0; i < operands.size(); ++i)
      operands_equality &= m_operands[i].addr() == operands[i].addr();

    return operands_equality;
  }

  bool is_equal(const NaryExpr<opcode>& other) const
  {
    return is_equal(other.sort(), other.m_operands);
  }
};

SharedExpr distinct(SharedExprs&& terms);

template<typename T>
Bool distinct(Terms<T>&& terms)
{
  return Bool(make_shared_expr<NaryExpr<NEQ>>(
    internal::sort<Bool>(), std::move(terms.terms)));
}

class ConstArrayExpr : public Expr
#ifdef ENABLE_HASH_CONS
, public internal::ExprDeleter<ConstArrayExpr>
#endif
{
private:
  const SharedExpr m_init;

  virtual Error __encode(Solver& solver) const override
  {
    return solver.encode_const_array(this, m_init);
  }

  void check_obj() const
  {
    assert(!m_init.is_null());
    assert(Expr::sort().is_array());
  }

public:
#ifdef ENABLE_HASH_CONS
  typedef internal::ExprDeleter<ConstArrayExpr> Deleter;

  static Expr::Hash hash_args(const Sort& sort, const SharedExpr& init)
  {
    return hash_combine(sort.hash(), init.hash());
  }

  /// \internal
  ConstArrayExpr(
    typename Deleter::ExprStorePtr expr_store_ptr,
    Expr::Hash hash,
    const Sort& sort,
    const SharedExpr& init)
  : Expr(CONST_ARRAY_EXPR_KIND, sort, hash),
    Deleter(expr_store_ptr),
    m_init(init)
  {
    check_obj();
  }

  ~ConstArrayExpr()
  {
    Deleter::delete_from_store(this);
  }
#endif

  // Allocate sort statically!
  ConstArrayExpr(const Sort& sort, const SharedExpr& init)
  : Expr(CONST_ARRAY_EXPR_KIND, sort),
    m_init(init)
  {
    check_obj();
  }

  const SharedExpr& init() const
  {
    return m_init;
  }

  bool is_equal(
    const Sort& sort,
    const SharedExpr& init) const
  {
    return Expr::sort() == sort &&
      m_init.addr() == init.addr();
  }

  bool is_equal(const ConstArrayExpr& other) const
  {
    return is_equal(other.sort(), other.m_init);
  }
};

class ArraySelectExpr : public Expr
#ifdef ENABLE_HASH_CONS
, public internal::ExprDeleter<ArraySelectExpr>
#endif
{
private:
  const SharedExpr m_array;
  const SharedExpr m_index;

  virtual Error __encode(Solver& solver) const override
  {
    return solver.encode_array_select(this, m_array, m_index);
  }

  void check_obj() const
  {
    assert(!m_array.is_null());
    assert(!m_index.is_null());
  }

public:
#ifdef ENABLE_HASH_CONS
  typedef internal::ExprDeleter<ArraySelectExpr> Deleter;

  static Expr::Hash hash_args(
    const SharedExpr& array,
    const SharedExpr& index)
  {
    return hash_combine(array.hash(), index.hash());
  }

  /// \internal
  ArraySelectExpr(
    typename Deleter::ExprStorePtr expr_store_ptr,
    Expr::Hash hash,
    const SharedExpr& array,
    const SharedExpr& index)
  : Expr(ARRAY_SELECT_EXPR_KIND, array.sort().sorts(/* range */ 1), hash),
    Deleter(expr_store_ptr),
    m_array(array),
    m_index(index)
  {
    check_obj();
  }

  ~ArraySelectExpr()
  {
    Deleter::delete_from_store(this);
  }
#endif

  ArraySelectExpr(
    const SharedExpr& array,
    const SharedExpr& index)
  : Expr(ARRAY_SELECT_EXPR_KIND, array.sort().sorts(/* range */ 1)),
    m_array(array),
    m_index(index)
  {
    check_obj();
  }

  const SharedExpr& array() const
  {
    return m_array;
  }

  const SharedExpr& index() const
  {
    return m_index;
  }

  bool is_equal(
    const SharedExpr& array,
    const SharedExpr& index) const
  {
    return m_array.addr() == array.addr() &&
      m_index.addr() == index.addr();
  }

  bool is_equal(const ArraySelectExpr& other) const
  {
    return is_equal(other.m_array, other.m_index);
  }
};

class ArrayStoreExpr : public Expr
#ifdef ENABLE_HASH_CONS
, public internal::ExprDeleter<ArrayStoreExpr>
#endif
{
private:
  const SharedExpr m_array;
  const SharedExpr m_index;
  const SharedExpr m_value;

  virtual Error __encode(Solver& solver) const override
  {
    return solver.encode_array_store(this, m_array, m_index, m_value);
  }

  void check_obj() const
  {
    assert(!m_array.is_null());
    assert(!m_index.is_null());
    assert(!m_value.is_null());
  }

public:
#ifdef ENABLE_HASH_CONS
  typedef internal::ExprDeleter<ArrayStoreExpr> Deleter;

  static Expr::Hash hash_args(
    const SharedExpr& array,
    const SharedExpr& index,
    const SharedExpr& value)
  {
    size_t h = hash_combine(array.hash(), index.hash());
    h = hash_combine(h, value.hash());
    return h;
  }

  /// \internal
  ArrayStoreExpr(
    typename Deleter::ExprStorePtr expr_store_ptr,
    Expr::Hash hash,
    const SharedExpr& array,
    const SharedExpr& index,
    const SharedExpr& value)
  : Expr(ARRAY_STORE_EXPR_KIND, array.sort(), hash),
    Deleter(expr_store_ptr),
    m_array(array),
    m_index(index),
    m_value(value)
  {
    check_obj();
  }

  ~ArrayStoreExpr()
  {
    Deleter::delete_from_store(this);
  }
#endif

  // Allocate sort statically!
  ArrayStoreExpr(
    const SharedExpr& array,
    const SharedExpr& index,
    const SharedExpr& value)
  : Expr(ARRAY_STORE_EXPR_KIND, array.sort()),
    m_array(array),
    m_index(index),
    m_value(value)
  {
    check_obj();
  }

  const SharedExpr& array() const
  {
    return m_array;
  }

  const SharedExpr& index() const
  {
    return m_index;
  }

  const SharedExpr& value() const
  {
    return m_value;
  }

  bool is_equal(
    const SharedExpr& array,
    const SharedExpr& index,
    const SharedExpr& value) const
  {
    return m_array.addr() == array.addr() &&
      m_index.addr() == index.addr() &&
      m_value.addr() == value.addr();
  }

  bool is_equal(const ArrayStoreExpr& other) const
  {
    return is_equal(other.m_array, other.m_index, other.m_value);
  }
};

SharedExpr select(
  const SharedExpr& array,
  const SharedExpr& index);

template<typename Domain, typename Range>
Range select(
  const Array<Domain, Range>& array,
  const Domain& index)
{
  return Range(make_shared_expr<ArraySelectExpr>(array, index));
}

SharedExpr store(
  const SharedExpr& array,
  const SharedExpr& index,
  const SharedExpr& value);

template<typename Domain, typename Range>
Array<Domain, Range> store(
  const Array<Domain, Range>& array,
  const Domain& index,
  const Range& value)
{
  return Array<Domain, Range>(
    make_shared_expr<ArrayStoreExpr>(array, index, value));
}

SharedExpr implies(
  const SharedExpr& larg,
  const SharedExpr& rarg);

SharedExpr implies(
  const Bool& larg,
  const SharedExpr& rarg);

SharedExpr implies(
  const SharedExpr& larg,
  const Bool& rarg);

Bool implies(
  const Bool& larg,
  const Bool& rarg);

template<Opcode opcode, typename T>
struct Identity;

template<>
struct Identity<LAND, Bool>
{
  static Bool term;
};

}

#define SMT_BUILTIN_UNARY_OP(op, opcode)                                       \
  template<typename T, typename Enable = typename std::enable_if<              \
    std::is_base_of<smt::internal::Term<T>, T>::value>::type>                  \
  inline T operator op(const T& arg)                                           \
  {                                                                            \
    return {smt::make_shared_expr<smt::UnaryExpr<smt::opcode>>(                \
      smt::internal::sort<T>(), arg)};                                         \
  }                                                                            \
  template<typename T, typename Enable = typename std::enable_if<              \
    std::is_base_of<smt::internal::Term<T>, T>::value>::type>                  \
  inline T operator op(T&& arg)                                                \
  {                                                                            \
    return {smt::make_shared_expr<smt::UnaryExpr<smt::opcode>>(                \
      smt::internal::sort<T>(), std::move(arg))};                              \
  }                                                                            \

#define SMT_BUILTIN_BINARY_OP(op, opcode)                                      \
  template<typename T, typename Enable =  typename std::enable_if<             \
    std::is_base_of<smt::internal::Term<T>, T>::value>::type>                  \
  inline T operator op(const T& larg, const T& rarg)                           \
  {                                                                            \
    return {smt::make_shared_expr<smt::BinaryExpr<smt::opcode>>(               \
      smt::internal::sort<T>(), larg, rarg)};                                  \
  }                                                                            \
  template<typename T, typename Enable =  typename std::enable_if<             \
    std::is_base_of<smt::internal::Term<T>, T>::value>::type>                  \
  inline T operator op(T&& larg, const T& rarg)                                \
  {                                                                            \
    return {smt::make_shared_expr<smt::BinaryExpr<smt::opcode>>(               \
      smt::internal::sort<T>(), std::move(larg), rarg)};                       \
  }                                                                            \
  template<typename T, typename Enable =  typename std::enable_if<             \
    std::is_base_of<smt::internal::Term<T>, T>::value>::type>                  \
  inline T operator op(const T& larg, T&& rarg)                                \
  {                                                                            \
    return {smt::make_shared_expr<smt::BinaryExpr<smt::opcode>>(               \
      smt::internal::sort<T>(), larg, std::move(rarg))};                       \
  }                                                                            \
  template<typename T, typename Enable =  typename std::enable_if<             \
    std::is_base_of<smt::internal::Term<T>, T>::value>::type>                  \
  inline T operator op(T&& larg, T&& rarg)                                     \
  {                                                                            \
    return {smt::make_shared_expr<smt::BinaryExpr<smt::opcode>>(               \
      smt::internal::sort<T>(), std::move(larg), std::move(rarg))};            \
  }                                                                            \
  template<typename T, typename U, typename Enable =                           \
    typename std::enable_if<std::is_base_of<smt::internal::Term<T>, T>::value  \
    and std::is_integral<U>::value>::type>                                     \
  inline T operator op(const T& larg, const U rscalar)                         \
  {                                                                            \
    return larg op smt::literal<T, U>(rscalar);                                \
  }                                                                            \
  template<typename T, typename U, typename Enable =                           \
    typename std::enable_if<std::is_base_of<smt::internal::Term<T>, T>::value  \
    and std::is_integral<U>::value>::type>                                     \
  inline T operator op(T&& larg, const U rscalar)                              \
  {                                                                            \
    return std::move(larg) op smt::literal<T, U>(rscalar);                     \
  }                                                                            \
  template<typename T, typename U, typename Enable =                           \
    typename std::enable_if<std::is_base_of<smt::internal::Term<T>, T>::value  \
    and std::is_integral<U>::value>::type>                                     \
  inline T operator op(const U lscalar, const T& rarg)                         \
  {                                                                            \
    return smt::literal<T, U>(lscalar) op rarg;                                \
  }                                                                            \
  template<typename T, typename U, typename Enable =                           \
    typename std::enable_if<std::is_base_of<smt::internal::Term<T>, T>::value  \
    and std::is_integral<U>::value>::type>                                     \
  inline T operator op(const U lscalar, T&& rarg)                              \
  {                                                                            \
    return smt::literal<T, U>(lscalar) op std::move(rarg);                     \
  }                                                                            \

#define SMT_BUILTIN_BINARY_REL(op, opcode)                                     \
  template<typename T, typename Enable =                                       \
    typename std::enable_if<                                                   \
      std::is_base_of<smt::internal::Term<T>, T>::value>::type>                \
  inline smt::Bool operator op(const T& larg, const T& rarg)                   \
  {                                                                            \
    return {smt::make_shared_expr<smt::BinaryExpr<smt::opcode>>(               \
      smt::internal::sort<smt::Bool>(), larg, rarg)};                          \
  }                                                                            \
  template<typename T, typename Enable =                                       \
    typename std::enable_if<                                                   \
      std::is_base_of<smt::internal::Term<T>, T>::value>::type>                \
  inline smt::Bool operator op(T&& larg, const T& rarg)                        \
  {                                                                            \
    return {smt::make_shared_expr<smt::BinaryExpr<smt::opcode>>(               \
      smt::internal::sort<smt::Bool>(), std::move(larg), rarg)};               \
  }                                                                            \
  template<typename T, typename Enable =                                       \
    typename std::enable_if<                                                   \
      std::is_base_of<smt::internal::Term<T>, T>::value>::type>                \
  inline smt::Bool operator op(const T& larg, T&& rarg)                        \
  {                                                                            \
    return {smt::make_shared_expr<smt::BinaryExpr<smt::opcode>>(               \
      smt::internal::sort<smt::Bool>(), larg, std::move(rarg))};               \
  }                                                                            \
  template<typename T, typename Enable =                                       \
    typename std::enable_if<                                                   \
      std::is_base_of<smt::internal::Term<T>, T>::value>::type>                \
  inline smt::Bool operator op(T&& larg, T&& rarg)                             \
  {                                                                            \
    return {smt::make_shared_expr<smt::BinaryExpr<smt::opcode>>(               \
      smt::internal::sort<smt::Bool>(), std::move(larg), std::move(rarg))};    \
  }                                                                            \
  template<typename T, typename U, typename Enable =                           \
    typename std::enable_if<std::is_base_of<smt::internal::Term<T>, T>::value  \
    and std::is_integral<U>::value>::type>                                     \
  inline smt::Bool operator op(const T& larg, const U rscalar)                 \
  {                                                                            \
    return larg op smt::literal<T, U>(rscalar);                                \
  }                                                                            \
  template<typename T, typename U, typename Enable =                           \
    typename std::enable_if<std::is_base_of<smt::internal::Term<T>, T>::value  \
    and std::is_integral<U>::value>::type>                                     \
  inline smt::Bool operator op(T&& larg, const U rscalar)                      \
  {                                                                            \
    return std::move(larg) op smt::literal<T, U>(rscalar);                     \
  }                                                                            \
  template<typename T, typename U, typename Enable =                           \
    typename std::enable_if<std::is_base_of<smt::internal::Term<T>, T>::value  \
    and std::is_integral<U>::value>::type>                                     \
  inline smt::Bool operator op(const U lscalar, const T& rarg)                 \
  {                                                                            \
    return smt::literal<T, U>(lscalar) op rarg;                                \
  }                                                                            \
  template<typename T, typename U, typename Enable =                           \
    typename std::enable_if<std::is_base_of<smt::internal::Term<T>, T>::value  \
    and std::is_integral<U>::value>::type>                                     \
  inline smt::Bool operator op(const U lscalar, T&& rarg)                      \
  {                                                                            \
    return smt::literal<T, U>(lscalar) op std::move(rarg);                     \
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
  inline smt::Bv<T> operator op(const smt::Bv<T>& arg)                         \
  {                                                                            \
    return {smt::make_shared_expr<smt::UnaryExpr<smt::opcode>>(                \
      smt::internal::sort<smt::Bv<T>>(), arg)};                                \
  }                                                                            \
  template<typename T>                                                         \
  inline smt::Bv<T> operator op(smt::Bv<T>&& arg)                              \
  {                                                                            \
    return {smt::make_shared_expr<smt::UnaryExpr<smt::opcode>>(                \
      smt::internal::sort<smt::Bv<T>>(), std::move(arg))};                     \
  }                                                                            \

#define SMT_BUILTIN_BV_BINARY_OP(op, opcode)                                   \
  template<typename T>                                                         \
  inline smt::Bv<T> operator op(const smt::Bv<T>& larg, const smt::Bv<T>& rarg)\
  {                                                                            \
    return {smt::make_shared_expr<smt::BinaryExpr<smt::opcode>>(               \
      smt::internal::sort<smt::Bv<T>>(), larg, rarg)};                         \
  }                                                                            \
  template<typename T>                                                         \
  inline smt::Bv<T> operator op(smt::Bv<T>&& larg, const smt::Bv<T>& rarg)     \
  {                                                                            \
    return {smt::make_shared_expr<smt::BinaryExpr<smt::opcode>>(               \
      smt::internal::sort<smt::Bv<T>>(), std::move(larg), rarg)};              \
  }                                                                            \
  template<typename T>                                                         \
  inline smt::Bv<T> operator op(const smt::Bv<T>& larg, smt::Bv<T>&& rarg)     \
  {                                                                            \
    return {smt::make_shared_expr<smt::BinaryExpr<smt::opcode>>(               \
      smt::internal::sort<smt::Bv<T>>(), larg, std::move(rarg))};              \
  }                                                                            \
  template<typename T>                                                         \
  inline smt::Bv<T> operator op(smt::Bv<T>&& larg, smt::Bv<T>&& rarg)          \
  {                                                                            \
    return {smt::make_shared_expr<smt::BinaryExpr<smt::opcode>>(               \
      smt::internal::sort<smt::Bv<T>>(), std::move(larg), std::move(rarg))};   \
  }                                                                            \
  template<typename T>                                                         \
  inline smt::Bv<T> operator op(const smt::Bv<T>& larg, const T rscalar)       \
  {                                                                            \
    return larg op smt::literal<smt::Bv<T>>(rscalar);                          \
  }                                                                            \
  template<typename T>                                                         \
  inline smt::Bv<T> operator op(smt::Bv<T>&& larg, const T rscalar)            \
  {                                                                            \
    return std::move(larg) op smt::literal<smt::Bv<T>>(rscalar);               \
  }                                                                            \
  template<typename T>                                                         \
  inline smt::Bv<T> operator op(const T lscalar, const smt::Bv<T>& rarg)       \
  {                                                                            \
    return smt::literal<smt::Bv<T>>(lscalar) op rarg;                          \
  }                                                                            \
  template<typename T>                                                         \
  inline smt::Bv<T> operator op(const T lscalar, smt::Bv<T>&& rarg)            \
  {                                                                            \
    return smt::literal<smt::Bv<T>>(lscalar) op std::move(rarg);               \
  }                                                                            \

SMT_BUILTIN_BV_UNARY_OP(~, NOT)

SMT_BUILTIN_BV_BINARY_OP(&, AND)
SMT_BUILTIN_BV_BINARY_OP(|, OR)
SMT_BUILTIN_BV_BINARY_OP(^, XOR)

#define SMT_BUILTIN_BOOL_UNARY_OP(op, opcode)                                  \
  inline smt::Bool operator op(const smt::Bool& arg)                           \
  {                                                                            \
    return {smt::make_shared_expr<smt::UnaryExpr<smt::opcode>>(                \
      smt::internal::sort<smt::Bool>(), arg)};                                 \
  }                                                                            \
  inline smt::Bool operator op(smt::Bool&& arg)                                \
  {                                                                            \
    return {smt::make_shared_expr<smt::UnaryExpr<smt::opcode>>(                \
      smt::internal::sort<smt::Bool>(), std::move(arg))};                      \
  }                                                                            \

#define SMT_BUILTIN_BOOL_BINARY_OP(op, opcode)                                 \
  inline smt::Bool operator op(const smt::Bool& larg, const smt::Bool& rarg)   \
  {                                                                            \
    return {smt::make_shared_expr<smt::BinaryExpr<smt::opcode>>(               \
      smt::internal::sort<smt::Bool>(), larg, rarg)};                          \
  }                                                                            \
  inline smt::Bool operator op(const smt::Bool& larg, const bool rscalar)      \
  {                                                                            \
    return larg op smt::literal<smt::Bool>(rscalar);                           \
  }                                                                            \
  inline smt::Bool operator op(const bool lscalar, const smt::Bool& rarg)      \
  {                                                                            \
    return smt::literal<smt::Bool>(lscalar) op rarg;                           \
  }                                                                            \
  inline smt::Bool operator op(smt::Bool&& larg, const smt::Bool& rarg)        \
  {                                                                            \
    return {smt::make_shared_expr<smt::BinaryExpr<smt::opcode>>(               \
      smt::internal::sort<smt::Bool>(), std::move(larg), rarg)};               \
  }                                                                            \
  inline smt::Bool operator op(const smt::Bool& larg, smt::Bool&& rarg)        \
  {                                                                            \
    return {smt::make_shared_expr<smt::BinaryExpr<smt::opcode>>(               \
      smt::internal::sort<smt::Bool>(), larg, std::move(rarg))};               \
  }                                                                            \
  inline smt::Bool operator op(smt::Bool&& larg, smt::Bool&& rarg)             \
  {                                                                            \
    return {smt::make_shared_expr<smt::BinaryExpr<smt::opcode>>(               \
      smt::internal::sort<smt::Bool>(), std::move(larg), std::move(rarg))};    \
  }                                                                            \
  inline smt::Bool operator op(smt::Bool&& larg, const bool rscalar)           \
  {                                                                            \
    return std::move(larg) op smt::literal<smt::Bool>(rscalar);                \
  }                                                                            \
  inline smt::Bool operator op(const bool lscalar, smt::Bool&& rarg)           \
  {                                                                            \
    return smt::literal<smt::Bool>(lscalar) op std::move(rarg);                \
  }                                                                            \

SMT_BUILTIN_BOOL_UNARY_OP(!, LNOT)

SMT_BUILTIN_BOOL_BINARY_OP(&&, LAND)
SMT_BUILTIN_BOOL_BINARY_OP(||, LOR)
SMT_BUILTIN_BOOL_BINARY_OP(==, EQL)
SMT_BUILTIN_BOOL_BINARY_OP(!=, NEQ)

#define SMT_UNSAFE_UNARY_OP(op, opcode)                                        \
  inline smt::SharedExpr operator op(const smt::SharedExpr& arg)               \
  {                                                                            \
    return smt::make_shared_expr<smt::UnaryExpr<smt::opcode>>(arg.sort(), arg);\
  }                                                                            \

#define SMT_UNSAFE_BINARY_OP(op, opcode)                                       \
  inline smt::SharedExpr operator op(const smt::SharedExpr& larg,              \
    const smt::SharedExpr& rarg)                                               \
  {                                                                            \
    return smt::make_shared_expr<smt::BinaryExpr<smt::opcode>>(                \
      larg.sort(), larg, rarg);                                                \
  }                                                                            \
  template<typename T, typename Enable =                                       \
    typename std::enable_if<std::is_integral<T>::value>::type>                 \
  inline smt::SharedExpr operator op(const T lscalar,                          \
    const smt::SharedExpr& rarg)                                               \
  {                                                                            \
    return smt::make_shared_expr<smt::BinaryExpr<smt::opcode>>(                \
      rarg.sort(), literal(rarg.sort(), lscalar), rarg);                       \
  }                                                                            \
  template<typename T, typename Enable =                                       \
    typename std::enable_if<std::is_integral<T>::value>::type>                 \
  inline smt::SharedExpr operator op(                                          \
    const smt::SharedExpr& larg, const T rscalar)                              \
  {                                                                            \
    return smt::make_shared_expr<smt::BinaryExpr<smt::opcode>>(                \
      larg.sort(), larg, literal(larg.sort(), rscalar));                       \
  }                                                                            \

#define SMT_UNSAFE_BINARY_REL(op, opcode)                                      \
  inline smt::SharedExpr operator op(const smt::SharedExpr& larg,              \
    const smt::SharedExpr& rarg)                                               \
  {                                                                            \
    return smt::make_shared_expr<smt::BinaryExpr<smt::opcode>>(                \
      smt::internal::sort<smt::Bool>(), larg, rarg);                           \
  }                                                                            \
  inline smt::SharedExpr operator op(smt::SharedExpr&& larg,                   \
    const smt::SharedExpr& rarg)                                               \
  {                                                                            \
    return smt::make_shared_expr<smt::BinaryExpr<smt::opcode>>(                \
      smt::internal::sort<smt::Bool>(), std::move(larg), rarg);                \
  }                                                                            \
  inline smt::SharedExpr operator op(const smt::SharedExpr& larg,              \
    smt::SharedExpr&& rarg)                                                    \
  {                                                                            \
    return smt::make_shared_expr<smt::BinaryExpr<smt::opcode>>(                \
      smt::internal::sort<smt::Bool>(), larg, std::move(rarg));                \
  }                                                                            \
  inline smt::SharedExpr operator op(smt::SharedExpr&& larg,                   \
    smt::SharedExpr&& rarg)                                                    \
  {                                                                            \
    return smt::make_shared_expr<smt::BinaryExpr<smt::opcode>>(                \
      smt::internal::sort<smt::Bool>(), std::move(larg), std::move(rarg));     \
  }                                                                            \
  template<typename T, typename Enable =                                       \
    typename std::enable_if<std::is_integral<T>::value>::type>                 \
  inline smt::SharedExpr operator op(const T lscalar,                          \
    const smt::SharedExpr& rarg)                                               \
  {                                                                            \
    return smt::make_shared_expr<smt::BinaryExpr<smt::opcode>>(                \
      smt::internal::sort<smt::Bool>(), literal(rarg.sort(), lscalar), rarg);  \
  }                                                                            \
  template<typename T, typename Enable =                                       \
    typename std::enable_if<std::is_integral<T>::value>::type>                 \
  inline smt::SharedExpr operator op(                                          \
    const smt::SharedExpr& larg, const T rscalar)                              \
  {                                                                            \
    return smt::make_shared_expr<smt::BinaryExpr<smt::opcode>>(                \
      smt::internal::sort<smt::Bool>(), larg, literal(larg.sort(), rscalar));  \
  }                                                                            \
  template<typename T, typename Enable =                                       \
    typename std::enable_if<std::is_integral<T>::value>::type>                 \
  inline smt::SharedExpr operator op(const T lscalar,                          \
    smt::SharedExpr&& rarg)                                                    \
  {                                                                            \
    return smt::make_shared_expr<smt::BinaryExpr<smt::opcode>>(                \
      smt::internal::sort<smt::Bool>(), literal(rarg.sort(), lscalar),         \
      std::move(rarg));                                                        \
  }                                                                            \
  template<typename T, typename Enable =                                       \
    typename std::enable_if<std::is_integral<T>::value>::type>                 \
  inline smt::SharedExpr operator op(                                          \
    smt::SharedExpr&& larg, const T rscalar)                                   \
  {                                                                            \
    return smt::make_shared_expr<smt::BinaryExpr<smt::opcode>>(                \
      smt::internal::sort<smt::Bool>(), std::move(larg),                       \
      literal(larg.sort(), rscalar));                                          \
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
