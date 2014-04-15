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
#include <cstddef>
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

/// Note: subclasses usually provide pretty-printing functionality
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

#define SMT_ENCODE_BUILTIN_LITERAL(type)                                       \
private:                                                                       \
  virtual Error __encode_literal(                                              \
    const Sort& sort,                                                          \
    type literal)                                                              \
  {                                                                            \
    return UNSUPPORT_ERROR;                                                    \
  }                                                                            \
                                                                               \
public:                                                                        \
  Error encode_literal(                                                        \
    const Sort& sort,                                                          \
    type literal)                                                              \
  {                                                                            \
    return __encode_literal(sort, literal);                                    \
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
  virtual Error __add(const Bool& condition) = 0;
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

  void add(const Bool& condition);
  void unsafe_add(const UnsafeTerm& condition);

  CheckResult check();

  virtual ~Solver() {}
};

class Expr
{
private:
  const ExprKind m_expr_kind;
  const Sort& m_sort;

  virtual Error __encode(Solver&) const = 0;

protected:
  // Allocate sort statically!
  Expr(ExprKind expr_kind, const Sort& sort)
  : m_expr_kind(expr_kind), m_sort(sort) {}

public:
  Expr(const Expr&) = delete;
  virtual ~Expr() {}

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

/// shared but potentially not well-sorted SMT expression

/// All arithmetic and bit vector operators are overloaded.
class UnsafeTerm
{
private:
  std::shared_ptr<const Expr> m_ptr;

public:
  UnsafeTerm()
  : m_ptr(nullptr) {}

  UnsafeTerm(const std::shared_ptr<const Expr>& ptr)
  : m_ptr(ptr) {}

  UnsafeTerm(std::shared_ptr<const Expr>&& ptr)
  : m_ptr(std::move(ptr)) {}

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
  explicit operator T() const
  {
    assert(is_null() || internal::sort<T>() == sort());
    return T(m_ptr);
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

  /// \internal \pre !is_null()
  Error encode(Solver& solver) const
  {
    assert(!is_null());
    return m_ptr->encode(solver);
  }
};

namespace internal
{
  /// shared and well-sorted SMT expression 

  /// Supported built-in operators depends on the type T.
  template<typename T>
  class Term
  {
  private:
    std::shared_ptr<const Expr> m_ptr;

  protected:
    // See "Virtuality" article by Herb Sutter:
    //   [If you do not] want to allow polymorphic deletion
    //   through a base pointer, [then] the destructor
    //   should be nonvirtual and protected, the latter
    //   to prevent the unwanted usage.
    ~Term() {}

  public:
    Term()
    : m_ptr(nullptr) {}

    Term(const std::shared_ptr<const Expr>& ptr)
    : m_ptr(ptr)
    {
      assert(is_null() || internal::sort<T>() == sort());
    }

    Term(std::shared_ptr<const Expr>&& ptr)
    : m_ptr(std::move(ptr))
    {
      assert(is_null() || internal::sort<T>() == sort());
    }

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
  };
}

// Note: Curiously recurring template pattern (CRTP) is needed to
// support recursive sorts such as Func<T...>
#define SMT_TERM_DEF(name)                                         \
struct name : public internal::Term<name>                          \
{                                                                  \
  using internal::Term<name>::Term;                                \
};                                                                 \

SMT_TERM_DEF(Bool)
SMT_TERM_DEF(Int)
SMT_TERM_DEF(Real)

/// Fixed-size bit vector
template<typename T, typename Enable =
  typename std::enable_if<std::is_integral<T>::value>::type>
struct Bv : public internal::Term<Bv<T>>
{
  using internal::Term<Bv<T>>::Term;
};

/// McCarthy Array
template<typename Domain, typename Range>
struct Array : public internal::Term<Array<Domain, Range>>
{
  using internal::Term<Array<Domain, Range>>::Term;
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
struct Func : public internal::Term<Func<T...>>
{
  using internal::Term<Func<T...>>::Term;

  static constexpr size_t arity = sizeof...(T) - 1;

  typedef typename internal::RemoveLast<T...>::Type Args;

  // last tuple element
  typedef typename std::tuple_element<arity,
    std::tuple<T...>>::type Range;
};

template<typename T>
class LiteralExpr : public Expr
{
private:
  const T m_literal;

  virtual Error __encode(Solver& solver) const override
  {
    return solver.encode_literal(Expr::sort(), m_literal);
  }

public:
  // Allocate sort statically!
  LiteralExpr(const Sort& sort, T literal)
  : Expr(LITERAL_EXPR_KIND, sort),
    m_literal(literal) {}

  const T literal() const
  {
    return m_literal;
  }
};

class ConstantExpr : public Expr
{
private:
  const UnsafeDecl m_decl;

  virtual Error __encode(Solver& solver) const override
  {
    return solver.encode_constant(m_decl);
  }

public:
  ConstantExpr(const UnsafeDecl& decl)
  : Expr(CONSTANT_EXPR_KIND, decl.sort()),
    m_decl(decl) {}

  const UnsafeDecl& decl() const
  {
    return m_decl;
  }
};

template<size_t arity>
class FuncAppExpr : public Expr
{
private:
  const UnsafeDecl m_func_decl;
  const std::array<UnsafeTerm, arity> m_args;

  virtual Error __encode(Solver& solver) const override
  {
    return solver.encode_func_app(m_func_decl, arity, m_args.data());
  }

public:
  FuncAppExpr(
    const UnsafeDecl& func_decl,
    std::array<UnsafeTerm, arity>&& args)
  : Expr(FUNC_APP_EXPR_KIND, func_decl.sort().sorts(arity)),
    m_func_decl(func_decl),
    m_args(std::move(args)) {}

  const std::array<UnsafeTerm, arity>& args() const
  {
    return m_args;
  }

  const UnsafeDecl& func_decl() const
  {
    return m_func_decl;
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
inline UnsafeTerm literal(const Sort& sort, const T literal)
{
  return UnsafeTerm(std::make_shared<LiteralExpr<T>>(sort, literal));
}

template<typename T, typename U, typename Enable =
  typename std::enable_if<std::is_integral<U>::value and
  internal::IsPrimitive<T>::value>::type>
inline T literal(const U literal)
{
  return T(std::make_shared<LiteralExpr<U>>(internal::sort<T>(), literal));
}

UnsafeTerm constant(const UnsafeDecl& decl);

template<typename T>
T constant(const Decl<T>& decl)
{
  return T(std::make_shared<ConstantExpr>(decl));
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
    std::make_shared<FuncAppExpr<Func<T...>::arity>>(func_decl,
    internal::to_array<UnsafeTerm, typename Func<T...>::Args>(args)));
}

// Use globally unique symbol names!
template<typename T>
T any(const std::string& symbol)
{
  return constant(Decl<T>(symbol));
}

template<Opcode opcode>
class UnaryExpr : public Expr
{
private:
  const UnsafeTerm m_operand;

  virtual Error __encode(Solver& solver) const override
  {
    return solver.encode_unary(opcode, Expr::sort(), m_operand);
  }

public:
  // Allocate sort statically!
  UnaryExpr(
    const Sort& sort,
    const UnsafeTerm& operand)
  : Expr(UNARY_EXPR_KIND, sort),
    m_operand(operand)
  {
    assert(!m_operand.is_null());
  }

  const UnsafeTerm& operand() const
  {
    return m_operand;
  }
};

/// Two operand instruction whose operands must be the same sort
template<Opcode opcode>
class BinaryExpr : public Expr
{
private:
  const UnsafeTerm m_loperand;
  const UnsafeTerm m_roperand;

  virtual Error __encode(Solver& solver) const override
  {
    return solver.encode_binary(opcode, Expr::sort(),
      m_loperand, m_roperand);
  }

public:
  // Allocate sort statically, operands must have the same sort!
  BinaryExpr(
    const Sort& sort,
    const UnsafeTerm& loperand,
    const UnsafeTerm& roperand)
  : Expr(BINARY_EXPR_KIND, sort),
    m_loperand(loperand),
    m_roperand(roperand)
  {
    assert(!m_loperand.is_null());
    assert(!m_roperand.is_null());
    assert(m_loperand.sort() == m_roperand.sort());
  }

  const UnsafeTerm& loperand() const
  {
    return m_loperand;
  }

  const UnsafeTerm& roperand() const
  {
    return m_roperand;
  }
};

template<typename T>
class Terms
{
public:
  UnsafeTerms terms;

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
{
private:
  const UnsafeTerms m_operands;

  virtual Error __encode(Solver& solver) const override
  {
    return solver.encode_nary(opcode, Expr::sort(), m_operands);
  }

protected:
  const UnsafeTerms& operands() const
  {
    return m_operands;
  }

public:
  // Sort must be statically allocated and
  // there must be at least one operand.
  NaryExpr(
    const Sort& sort,
    UnsafeTerms&& operands)
  : Expr(NARY_EXPR_KIND, sort),
    m_operands(std::move(operands))
  {
    assert(!m_operands.empty());
  }

  // Sort must be statically allocated and
  // there must be at least one operand.
  NaryExpr(
    const Sort& sort,
    const UnsafeTerms& operands)
  : Expr(NARY_EXPR_KIND, sort),
    m_operands(operands)
  {
    assert(!m_operands.empty());
  }

  size_t size() const
  {
    return m_operands.size();
  }

  const UnsafeTerm& operand(size_t n) const
  {
    return m_operands.at(n);
  }
};

UnsafeTerm distinct(UnsafeTerms&& terms);

template<typename T>
Bool distinct(Terms<T>&& terms)
{
  return Bool(std::make_shared<NaryExpr<NEQ>>(
    internal::sort<Bool>(), std::move(terms.terms)));
}

class ConstArrayExpr : public Expr
{
private:
  const UnsafeTerm m_init;

  virtual Error __encode(Solver& solver) const override
  {
    return solver.encode_const_array(Expr::sort(), m_init);
  }

public:
  // Allocate sort statically!
  ConstArrayExpr(const Sort& sort, const UnsafeTerm& init)
  : Expr(CONST_ARRAY_EXPR_KIND, sort),
    m_init(init)
  {
    assert(!m_init.is_null());
    assert(sort.is_array());
  }

  const UnsafeTerm& init() const
  {
    return m_init;
  }
};

class ArraySelectExpr : public Expr
{
private:
  const UnsafeTerm m_array;
  const UnsafeTerm m_index;

  virtual Error __encode(Solver& solver) const override
  {
    return solver.encode_array_select(m_array, m_index);
  }

public:
  ArraySelectExpr(
    const UnsafeTerm& array,
    const UnsafeTerm& index)
  : Expr(ARRAY_SELECT_EXPR_KIND, array.sort().sorts(/* range */ 1)),
    m_array(array),
    m_index(index)
  {
    assert(!m_array.is_null());
    assert(!m_index.is_null());
  }

  const UnsafeTerm& array() const
  {
    return m_array;
  }

  const UnsafeTerm& index() const
  {
    return m_index;
  }
};

class ArrayStoreExpr : public Expr
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
  ArrayStoreExpr(
    const UnsafeTerm& array,
    const UnsafeTerm& index,
    const UnsafeTerm& value)
  : Expr(ARRAY_STORE_EXPR_KIND, array.sort()),
    m_array(array),
    m_index(index),
    m_value(value)
  {
    assert(!m_array.is_null());
    assert(!m_index.is_null());
    assert(!m_value.is_null());
  }

  const UnsafeTerm& array() const
  {
    return m_array;
  }

  const UnsafeTerm& index() const
  {
    return m_index;
  }

  const UnsafeTerm& value() const
  {
    return m_value;
  }
};

UnsafeTerm select(
  const UnsafeTerm& array,
  const UnsafeTerm& index);

template<typename Domain, typename Range>
Range select(
  const Array<Domain, Range>& array,
  const Domain& index)
{
  return Range(std::make_shared<ArraySelectExpr>(array, index));
}

UnsafeTerm store(
  const UnsafeTerm& array,
  const UnsafeTerm& index,
  const UnsafeTerm& value);

template<typename Domain, typename Range>
Array<Domain, Range> store(
  const Array<Domain, Range>& array,
  const Domain& index,
  const Range& value)
{
  return Array<Domain, Range>(
    std::make_shared<ArrayStoreExpr>(array, index, value));
}

UnsafeTerm implies(
  const UnsafeTerm& larg,
  const UnsafeTerm& rarg);

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
    return T(std::make_shared<smt::UnaryExpr<smt::opcode>>(                    \
      smt::internal::sort<T>(), arg));                                         \
  }                                                                            \

#define SMT_BUILTIN_BINARY_OP(op, opcode)                                      \
  template<typename T, typename Enable =  typename std::enable_if<             \
    std::is_base_of<smt::internal::Term<T>, T>::value>::type>                  \
  inline T operator op(const T& larg, const T& rarg)                           \
  {                                                                            \
    return T(std::make_shared<smt::BinaryExpr<smt::opcode>>(                   \
      smt::internal::sort<T>(), larg, rarg));                                  \
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
  inline T operator op(const U lscalar, const T& rarg)                         \
  {                                                                            \
    return smt::literal<T, U>(lscalar) op rarg;                                \
  }                                                                            \

#define SMT_BUILTIN_BINARY_REL(op, opcode)                                     \
  template<typename T, typename Enable =                                       \
    typename std::enable_if<                                                   \
      std::is_base_of<smt::internal::Term<T>, T>::value>::type>                \
  inline smt::Bool operator op(const T& larg, const T& rarg)                   \
  {                                                                            \
    return smt::Bool(std::make_shared<smt::BinaryExpr<smt::opcode>>(           \
      smt::internal::sort<smt::Bool>(), larg, rarg));                          \
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
  inline smt::Bool operator op(const U lscalar, const T& rarg)                 \
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
  inline smt::Bv<T> operator op(const smt::Bv<T>& arg)                         \
  {                                                                            \
    return smt::Bv<T>(std::make_shared<smt::UnaryExpr<smt::opcode>>(           \
      smt::internal::sort<smt::Bv<T>>(), arg));                                \
  }                                                                            \

#define SMT_BUILTIN_BV_BINARY_OP(op, opcode)                                   \
  template<typename T>                                                         \
  inline smt::Bv<T> operator op(const smt::Bv<T>& larg, const smt::Bv<T>& rarg)\
  {                                                                            \
    return smt::Bv<T>(std::make_shared<smt::BinaryExpr<smt::opcode>>(          \
      smt::internal::sort<smt::Bv<T>>(), larg, rarg));                         \
  }                                                                            \
  template<typename T>                                                         \
  inline smt::Bv<T> operator op(const smt::Bv<T>& larg, const T rscalar)       \
  {                                                                            \
    return larg op smt::literal<smt::Bv<T>>(rscalar);                          \
  }                                                                            \
  template<typename T>                                                         \
  inline smt::Bv<T> operator op(const T lscalar, const smt::Bv<T>& rarg)       \
  {                                                                            \
    return smt::literal<smt::Bv<T>>(lscalar) op rarg;                          \
  }                                                                            \

SMT_BUILTIN_BV_UNARY_OP(~, NOT)

SMT_BUILTIN_BV_BINARY_OP(&, AND)
SMT_BUILTIN_BV_BINARY_OP(|, OR)
SMT_BUILTIN_BV_BINARY_OP(^, XOR)

#define SMT_BUILTIN_BOOL_UNARY_OP(op, opcode)                                  \
  inline smt::Bool operator op(const smt::Bool& arg)                           \
  {                                                                            \
    return smt::Bool(std::make_shared<smt::UnaryExpr<smt::opcode>>(            \
      smt::internal::sort<smt::Bool>(), arg));                                 \
  }                                                                            \

#define SMT_BUILTIN_BOOL_BINARY_OP(op, opcode)                                 \
  inline smt::Bool operator op(const smt::Bool& larg, const smt::Bool& rarg)   \
  {                                                                            \
    return smt::Bool(std::make_shared<smt::BinaryExpr<smt::opcode>>(           \
      smt::internal::sort<smt::Bool>(), larg, rarg));                          \
  }                                                                            \
  inline smt::Bool operator op(const smt::Bool& larg, const bool rscalar)      \
  {                                                                            \
    return larg op smt::literal<smt::Bool>(rscalar);                           \
  }                                                                            \
  inline smt::Bool operator op(const bool lscalar, const smt::Bool& rarg)      \
  {                                                                            \
    return smt::literal<smt::Bool>(lscalar) op rarg;                           \
  }                                                                            \

SMT_BUILTIN_BOOL_UNARY_OP(!, LNOT)

SMT_BUILTIN_BOOL_BINARY_OP(&&, LAND)
SMT_BUILTIN_BOOL_BINARY_OP(||, LOR)
SMT_BUILTIN_BOOL_BINARY_OP(==, EQL)
SMT_BUILTIN_BOOL_BINARY_OP(!=, NEQ)

#define SMT_UNSAFE_UNARY_OP(op, opcode)                                        \
  inline smt::UnsafeTerm operator op(const smt::UnsafeTerm& arg)               \
  {                                                                            \
    return smt::UnsafeTerm(std::make_shared<smt::UnaryExpr<smt::opcode>>(      \
      arg.sort(), arg));                                                       \
  }                                                                            \

#define SMT_UNSAFE_BINARY_OP(op, opcode)                                       \
  inline smt::UnsafeTerm operator op(const smt::UnsafeTerm& larg,              \
    const smt::UnsafeTerm& rarg)                                               \
  {                                                                            \
    return smt::UnsafeTerm(std::make_shared<smt::BinaryExpr<smt::opcode>>(     \
      larg.sort(), larg, rarg));                                               \
  }                                                                            \
  template<typename T, typename Enable =                                       \
    typename std::enable_if<std::is_integral<T>::value>::type>                 \
  inline smt::UnsafeTerm operator op(const T lscalar,                          \
    const smt::UnsafeTerm& rarg)                                               \
  {                                                                            \
    return smt::UnsafeTerm(std::make_shared<smt::BinaryExpr<smt::opcode>>(     \
      rarg.sort(), literal(rarg.sort(), lscalar), rarg));                      \
  }                                                                            \
  template<typename T, typename Enable =                                       \
    typename std::enable_if<std::is_integral<T>::value>::type>                 \
  inline smt::UnsafeTerm operator op(                                          \
    const smt::UnsafeTerm& larg, const T rscalar)                              \
  {                                                                            \
    return smt::UnsafeTerm(std::make_shared<smt::BinaryExpr<smt::opcode>>(     \
      larg.sort(), larg, literal(larg.sort(), rscalar)));                      \
  }                                                                            \

#define SMT_UNSAFE_BINARY_REL(op, opcode)                                      \
  inline smt::UnsafeTerm operator op(const smt::UnsafeTerm& larg,              \
    const smt::UnsafeTerm& rarg)                                               \
  {                                                                            \
    return smt::UnsafeTerm(std::make_shared<smt::BinaryExpr<smt::opcode>>(     \
      smt::internal::sort<smt::Bool>(), larg, rarg));                          \
  }                                                                            \
  template<typename T, typename Enable =                                       \
    typename std::enable_if<std::is_integral<T>::value>::type>                 \
  inline smt::UnsafeTerm operator op(const T lscalar,                          \
    const smt::UnsafeTerm& rarg)                                               \
  {                                                                            \
    return smt::UnsafeTerm(std::make_shared<smt::BinaryExpr<smt::opcode>>(     \
      smt::internal::sort<smt::Bool>(), literal(rarg.sort(), lscalar), rarg)); \
  }                                                                            \
  template<typename T, typename Enable =                                       \
    typename std::enable_if<std::is_integral<T>::value>::type>                 \
  inline smt::UnsafeTerm operator op(                                          \
    const smt::UnsafeTerm& larg, const T rscalar)                              \
  {                                                                            \
    return smt::UnsafeTerm(std::make_shared<smt::BinaryExpr<smt::opcode>>(     \
      smt::internal::sort<smt::Bool>(), larg, literal(larg.sort(), rscalar))); \
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
