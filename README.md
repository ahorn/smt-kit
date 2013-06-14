# SMT Kit

SMT Kit is a type-safe C++11 domain-specific language to
create [SMT-LIB][smt-lib] 2.0 formulas.

[smt-lib]: http://www.smt-lib.org/

## Prerequisite

SMT Kit is an API to SMT solvers that must be installed separately.
Read their software licences carefully.

Currently, SMT Kit supports [Z3][z3] and [MathSAT5][msat]. Installation
instructions can be found in the `solvers/` directory.

[z3]: http://z3.codeplex.com/
[msat]: http://mathsat.fbk.eu/

## Installation

To build SMT Kit on a (mostly) POSIX-compliant operating system,
execute the following commands from the `smt-kit` folder:

    $ ./autogen.sh
    $ ./configure
    $ make
    $ make test
    $ make install

If `./configure` fails, you may have to set environment variables
such as `CXX` and `CXXFLAGS`. For example, the compiler can
be set with the command `./configure CXX=clang++`.

If `make test` fails, you can still install, but it is likely that some
features of this library will not work correctly on your system.
Proceed at your own risk.

Note that `make install` may require superuser privileges.

For advanced usage information on other configure options refer to the
[Autoconf documentation][autoconf].

[autoconf]: http://www.gnu.org/software/autoconf/

## API Usage

First, `#include <smt>`. An example with built-in operators follows:

    auto x = smt::any<smt::Bool>("x");
    auto y = smt::any<smt::Bool>("y");
    auto lhs = !(x && y);
    auto rhs = !x || !y;

    smt::Z3Solver z3_solver;
    z3_solver.add(lhs != rhs);
    assert(smt::unsat != z3_solver.check());

    smt::MsatSolver msat_solver;
    msat_solver.add(lhs != rhs);
    assert(smt::unsat == msat_solver.check());

Several more examples including incremental solving, function applications
and array logic expressions can be found in the [functional tests][api].

[api]: https://github.com/ahorn/smt-kit/blob/master/test/smt_functional_test.cpp

## Troubleshooting

Since SMT Kit uses advanced C++11 language features, older compiler
versions are likely to be troublesome. To date, we have successfully
compiled and tested the code on OS X with g++ 4.8.1 and clang++ 4.2.
But the choice of compiler also depends on the underlying SMT solvers.
In particular, MathSAT5 on OS X does not currently link with clang++
and LLVM's C++11 standard library (libc++). As a workaround, g++ from
Mac Ports works fine. This compiler portability issue has been reported
to mathsat@fbk.eu.
