# SMT Kit

SMT Kit is a C++11 library for many-sorted logics. It particularly
targets quantifier-free SMT-LIB 2.0 formulas. Currently, SMT Kit
supports CVC4, MathSAT5 and Z3.

## API Usage

To use SMT Kit, `#include <smt>`. Here's an API usage example that
encodes and checks De Morgan's law:

```C++
// Symbols (e.g. "x") must be globally unique!
smt::Bool x = smt::any<smt::Bool>("x");
smt::Bool y = smt::any<smt::Bool>("y");
smt::Bool lhs = !(x && y);
smt::Bool rhs = !x || !y;

// Other solvers include smt::MsatSolver and smt::Z3Solver 
smt::CVC4Solver solver;
solver.add(lhs != rhs);
assert(smt::unsat == solver.check());
```

The compiler will check the arguments of SMT functions at compile-time.
For example, the above example will not compile if `x` is a `smt::Int`.
However, these compile-time checks do not apply to logic signatures.
For example, when `smt::QF_BV_LOGIC` is specified for the solver but
an `smt::Array` is also used, there won't be a compile-time error.

Several more examples including incremental solving, function applications
and array logic expressions can be found in the [functional tests][api].

[api]: https://github.com/ahorn/smt-kit/blob/master/test/smt_functional_test.cpp

## Installation

For SMT Kit to work, [CVC4][cvc4], [MathSAT5][msat] and [Z3][z3] must be installed
separately. Read their software licences carefully. The SMT solver's installation
instructions can be found in the `solvers` [directory][solvers].

To build SMT Kit on a (mostly) POSIX-compliant operating system,
execute the following commands from the `smt-kit` directory:

    $ ./autogen.sh
    $ ./configure
    $ make
    $ make test
    $ make install

If `./configure` fails, you may have to set environment variables. For example,
to compile on OS X with clang++ use the command `./configure CXX=clang++`.
But see also the troubleshooting section below.

If `make test` fails, you can still install, but it is likely that some
features of this library will not work correctly on your system.
Proceed at your own risk.

Note that `make install` may require superuser privileges.

For advanced usage information on other configure options refer to the
[Autoconf documentation][autoconf].

[autoconf]: http://www.gnu.org/software/autoconf/
[cvc4]: http://cvc4.cs.nyu.edu/
[msat]: http://mathsat.fbk.eu/
[z3]: http://z3.codeplex.com/
[solvers]: https://github.com/ahorn/smt-kit/tree/master/solvers

## Troubleshooting

Since SMT Kit uses advanced C++11 language features, older compiler
versions are likely to be troublesome. To date, we have successfully
compiled and tested the code on OS X with g++ 4.8.1 and clang++ 4.2.
You should also always use the most recent version of the SMT solvers.

If `make test` fails with an error that indicates that `libstdc++.so.6`
or a specific version of `GLIBCXX` cannot be found, then check out GCC's
[libstdcxx-faq][FAQ].

[libstdcxx-faq]: http://gcc.gnu.org/onlinedocs/libstdc++/faq.html#faq.how_to_set_paths

## Bug Reports

You are warmly invited to submit patches as Github pull request,
formatted according to the existing coding style.
