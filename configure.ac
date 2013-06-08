# Provide various options to initialize the Autoconf and configure processes.
AC_PREREQ([2.59])

AC_INIT([smt-dsl], [1.0], [alex.horn@cs.ox.ac.uk])

AC_CONFIG_SRCDIR([src/smt.cpp])
AC_CONFIG_AUX_DIR([build-aux])
AC_CONFIG_HEADERS([build-aux/config.h])
AC_CONFIG_MACRO_DIR([m4])
AC_CONFIG_FILES([Makefile])
AC_CONFIG_SUBDIRS([gtest])

AC_CHECK_PROGS([DOXYGEN], [doxygen])
if test -z "$DOXYGEN";
   then AC_MSG_WARN([Doxygen not found - API documentation cannot be generated.])
fi

AM_CONDITIONAL([HAVE_DOXYGEN], [test -n "$DOXYGEN"])
AM_COND_IF([HAVE_DOXYGEN], [AC_CONFIG_FILES([doc/Doxyfile])])

AM_INIT_AUTOMAKE([-Wall -Werror dist-zip foreign subdir-objects])

AC_PROG_CXX
AC_LANG([C++])
AX_CXX_COMPILE_STDCXX_11([noext])
AC_PROG_LIBTOOL

# Work around for internal/gtest-port.h dependency on tr1/tuple
AC_CHECK_DEFINED(__APPLE__, )

# If we compile with clang++, we'll use LLVM's C++11 standard library
AC_COMPILE_IFELSE(
[AC_LANG_PROGRAM([], [[
#ifndef __clang__
  not clang
#endif
]])],
[CLANG=yes], [CLANG=no])
AC_MSG_RESULT([$CLANG])

AS_IF([test x$CLANG = xyes], [CXXFLAGS="$CXXFLAGS -stdlib=libc++"])

Z3_DIR="solvers/z3"
MSAT_DIR="solvers/msat"
GMP_DIR="/opt/local"

# Search for SMT and SAT solver libraries
CXXFLAGS="$CXXFLAGS -I$Z3_DIR/src/api -I$Z3_DIR/src/api/c++ -I$MSAT_DIR/include"
LDFLAGS="$LDFLAGS -L$Z3_DIR/build -L$MSAT_DIR/lib -L$GMP_DIR/lib"

AC_SEARCH_LIBS([Z3_mk_config], [z3], , AC_MSG_ERROR([Unable to find Z3 theorem prover]))

AC_CHECK_LIB(stdc++, main, ,[AC_MSG_ERROR([Unable to find stdc++])])
AC_CHECK_LIB(gmp, __gmpz_init, ,[AC_MSG_ERROR([Unable to find gmp])])
AC_SEARCH_LIBS([msat_create_config], [mathsat], , AC_MSG_ERROR([Unable to find MathSAT5]), [-lstdc++ -lgmp])

# Output the generated files. No further autoconf macros may be used.
AC_OUTPUT
