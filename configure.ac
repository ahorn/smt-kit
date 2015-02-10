# Provide various options to initialize the Autoconf and configure processes.
AC_PREREQ([2.59])

AC_INIT([smt-kit], [1.0], [alex.horn@cs.ox.ac.uk])

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

AC_MSG_CHECKING(for --with-address-sanitizer)
AC_ARG_WITH(address_sanitizer,
            AS_HELP_STRING([--with-address-sanitizer],
                           [enable AddressSanitizer]),
[
AC_MSG_RESULT($withval)
CXXFLAGS="-fsanitize=address -fno-omit-frame-pointer $CXXFLAGS"
LDFLAGS="-fsanitize=address $LDFLAGS"
],
[AC_MSG_RESULT(no)])

CVC4_DIR="solvers/CVC4"
GMP_DIR="/opt/local"

# Search for SMT and SAT solver libraries
CXXFLAGS="$CXXFLAGS -I$CVC4_DIR/target/include -I$GMP_DIR/include"
LDFLAGS="$LDFLAGS -L$CVC4_DIR/target/lib -L$GMP_DIR/lib -lcvc4"

AX_CXX_CHECK_LIB(cvc4, [CVC4::SmtEngine::push()], [], AC_MSG_ERROR([Unable to find CVC4 theorem prover]))

# Output the generated files. No further autoconf macros may be used.
AC_OUTPUT
