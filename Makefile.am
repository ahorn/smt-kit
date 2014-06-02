# To support AC_CHECK_DEFINED
ACLOCAL_AMFLAGS = -I m4

# Since everything we compile requires the same headers,
# we define the global AM_CPPFLAGS. We also require the
# C++11 standard to be able to use std::shared_ptr.
AM_CPPFLAGS = -I$(srcdir)/include

AUTOMAKE_OPTIONS = foreign

# Always include gtest in distributions.
DIST_SUBDIRS = gtest

if HAVE_DOXYGEN

doc:
	$(DOXYGEN) $(top_srcdir)/doc/Doxyfile

endif

# The following local target definition is copied from the Protobuf project:
#   Build gtest before we build our tests. We don't add gtest to SUBDIRS
#   because then "make check" would also build and run all of gtest's own tests,
#   which takes a lot of time and is generally not useful to us. Also, we don't
#   want "make install" to recurse into gtest since we don't want to overwrite
#   the installed version of gtest if there is one.
check-local:
	@echo "Making lib/libgtest.a lib/libgtest_main.a in gtest"
	@cd gtest && $(MAKE) $(AM_MAKEFLAGS) lib/libgtest.la lib/libgtest_main.la

# We need to create a new custom target to run the tests because Autoconf does
# not reliably add check-local before the check target.
test: check-local check

.PHONY: doc

# The following local target definition is copied from the Protobuf project:
#   We would like to clean gtest when "make clean" is invoked. But we have to
#   be careful because clean-local is also invoked during "make distclean", but
#   "make distclean" already recurses into gtest because it's listed among the
#   DIST_SUBDIRS. distclean will delete gtest/Makefile, so if we then try to
#   cd to the directory again and "make clean" it will fail. So, check that the
#   Makefile exists before recursing.
clean-local:
	@if test -e gtest/Makefile; then \
	  echo "Making clean in gtest"; \
	  cd gtest && $(MAKE) $(AM_MAKEFLAGS) clean; \
	fi

dist_doc_DATA = README.md

# Build rules for libraries.
lib_LTLIBRARIES = lib/libsmt.la

lib_libsmt_la_SOURCES = \
  src/smt.cpp \
  src/nse_sequential.cpp \
  src/crv.cpp

pkginclude_HEADERS = \
  include/smt \
  include/smt.h \
  include/smt_z3.h \
  include/smt_msat.h \
  include/smt_stp.h \
  include/smt_cvc4.h \
  include/nse_sequential.h \
  include/nse_report.h \
  include/crv.h

# Build rules for functional and unit tests.
# Recall the Automake naming conventions:
#
# TESTS -- Programs run automatically by "make check"
# check_PROGRAMS -- Programs built by "make check" but not necessarily run

# See README in Z3 source code for installation instructions
tests_library_path = $(srcdir)/solvers/z3/build

TESTS_ENVIRONMENT = \
  LIBPATH=$(tests_library_path):$$LIBPATH \
  LD_LIBRARY_PATH=$(tests_library_path):$$LD_LIBRARY_PATH \
  DYLD_LIBRARY_PATH=$(tests_library_path):$$DYLD_LIBRARY_PATH \
  LIBRARY_PATH=$(tests_library_path):$$LIBRARY_PATH \
  SHLIB_PATH=$(tests_library_path):$$SHLIB_PATH \
  LD_LIBRARY64_PATH=$(tests_library_path):$$LD_LIBRARY64_PATH \
  LD_LIBRARYN32_PATH=$(tests_library_path):$$LD_LIBRARYN32_PATH \
  LD_LIBRARY_PATH_32=$(tests_library_path):$$LD_LIBRARY_PATH_32 \
  LD_LIBRARY_PATH_64=$(tests_library_path):$$LD_LIBRARY_PATH_64

TESTS = test/smt
check_PROGRAMS = test/smt

test_smt_SOURCES = \
  test/smt_test.cpp \
  test/smt_z3_test.cpp \
  test/smt_msat_test.cpp \
  test/smt_stp_test.cpp \
  test/smt_cvc4_test.cpp \
  test/smt_functional_test.cpp \
  test/nse_sequential_test.cpp \
  test/crv_test.cpp \
  test/crv_functional_test.cpp \
  test/crv_performance_test.cpp

test_smt_CPPFLAGS = -I$(srcdir)/include -I$(top_srcdir)/gtest/include
test_smt_LDADD = $(top_builddir)/gtest/lib/libgtest.la \
  $(top_builddir)/gtest/lib/libgtest_main.la \
  lib/libsmt.la
