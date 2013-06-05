# smt-kit

SMT Kit is a C++11 domain-specific language to create [SMT-LIB][smt-lib] 2.0
formulas that are automatically typed-checked at compile-time.

[smt-lib]: http://www.smt-lib.org/

## Prerequisite

You need to compile the [Z3 theorem prover][z3]. Its source code is available
under the [Microsoft Research License Agreement][msr-la]:

    $ git clone https://git01.codeplex.com/z3

See the `z3/README` file for instructions on how to compile the Z3 source code
with any of the following compilers: Visual Studio, g++ or clang++.

[z3]: http://z3.codeplex.com/
[msr-la]: http://z3.codeplex.com/license

## Installation

To build smt-kit on a (mostly) POSIX-compliant operating system,
execute the following commands from the smt-kit folder:

    $ ./autogen.sh
    $ ./configure
    $ make
    $ make test
    $ make install

If `./configure` fails, you may have to set the environment
variables `CXX` and `CXXFLAGS`. For example, to set the clang++
compiler execute the following command:

    $ ./configure CXX=clang++ CXXFLAGS=-stdlib=libc++

If `make test` fails, you can still install, but it is likely that some
features of this library will not work correctly on your system.
Proceed at your own risk.

Note that `make install` may require superuser privileges.

For advanced usage information on other configure options refer to the
[Autoconf documentation][autoconf].

[autoconf]: http://www.gnu.org/software/autoconf/

## Troubleshooting

Since smt-kit uses advanced C++11 language features, older compiler
versions are likely to be troublesome. To date, we have successfully
compiled and tested the code on OS X with g++ v4.8.1 and clang++ v4.2.
