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
AC_CHECK_DEFINED(__APPLE__, [CXXFLAGS="$CXXFLAGS -DGTEST_USE_OWN_TR1_TUPLE=1"])

# Search for SMT and SAT solver libraries
CXXFLAGS="$CXXFLAGS -Isolvers/z3/src/api -Isolvers/z3/src/api/c++"
LDFLAGS="$LDFLAGS -Lsolvers/z3/build"

AC_SEARCH_LIBS([Z3_mk_config], [z3], , AC_MSG_ERROR([Unable to find Z3 theorem prover]))

# Output the generated files. No further autoconf macros may be used.
AC_OUTPUT
