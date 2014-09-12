#!/bin/bash

END_BENCHMARK_NUM=${1:-3}
PROG_SIZE=${2:-7}
BEGIN_BENCHMARK_NUM=${3:-1}

JAVA=java

# The XML schema file "seed.dtd" must be
# in the same directory as Seed's JAR file
SEED_JAR="seed.jar"
SEED="${JAVA} -jar ${SEED_JAR} test/CKA-benchmark.xml ${PROG_SIZE} -text"

usage() {
  echo "Usage: $0 [end-benchmark-number=3] [program-size=7] [begin-benchmark-number=1]"
  exit 1
}

error() {
  echo "$@" 1>&2
  exit 1
}

# invoke usage when necessary
if [ "$1" == "-h" ]; then
  usage
fi

if ! [[ -f "${SEED_JAR}" ]]; then
  error "Cannot find ${SEED_JAR}"
fi

cat <<EOF
#include <chrono>
#include <fstream>
#include <cka.h>

using namespace cka;

void cka_benchmark()
{
  Program A{'a'};
  Program B{'b'};
  Program C{'c'};
  Program D{'d'};
  Program E{'e'};
  Program F{'f'};
  Program G{'g'};
  Program H{'h'};
  Program I{'i'};
  Program J{'j'};
  Program K{'k'};
  Program L{'l'};
  Program M{'m'};
  Program N{'n'};
  Program O{'o'};
  Program P{'p'};
  Program Q{'q'};
  Program R{'r'};
  Program S{'s'};
  Program T{'t'};
  Program U{'u'};
  Program V{'v'};
  Program W{'w'};
  Program X{'x'};
  Program Y{'y'};
  Program Z{'z'};

  Refinement r;

  auto start = std::chrono::system_clock::now();
  auto end = std::chrono::system_clock::now();
  std::chrono::seconds seconds;

  std::ofstream file("cka_benchmark_results.tex");

  file << "\\\\begin{table}" << std::endl;
  file << "\\\\begin{center}" << std::endl;
  file << "\\\\begin{tabular}{l|l|l|l}" << std::endl;
  file << "\\\\toprule" << std::endl;
  file << "Benchmark & Number of Checks & Numer of Solver Calls & Time (s) \\\\\\\\ \\\\midrule" << std::endl;

EOF

  echo "  // program size: ${PROG_SIZE}"
for i in $(seq -f "%05g" ${BEGIN_BENCHMARK_NUM} ${END_BENCHMARK_NUM})
do
  LHS=`${SEED}`
  RHS=`${SEED}`

  echo "  {"
  echo "    file << \"${i} & \";"
  echo "    start = std::chrono::system_clock::now();"
  echo "    r.check(lfp<','>(${LHS}), lfp<','>(${RHS}));"
  echo "    end = std::chrono::system_clock::now();"
  echo ""
  echo "    seconds = std::chrono::duration_cast<std::chrono::seconds>(end - start);"
  echo ""
  echo "    file << r.number_of_checks() << \" & \";"
  echo "    file << r.number_of_solver_calls() << \" & \";"
  echo "    file << seconds.count() << \"\\\\\\\\\" << std::endl;"
  echo ""
  echo "    r.reset_number_of_checks();"
  echo "    r.reset_number_of_solver_calls();"
  echo "  }"
done

cat <<EOF

  file << "\\\\bottomrule" << std::endl;
  file << "\\\\end{tabular}" << std::endl;
  file << "\\\\caption{Benchmarks with a symbolic implementation of partial strings}" << std::endl;
  file << "\\\\label{table:cka-benchmarks}" << std::endl;
  file << "\\\\end{center}" << std::endl;
  file << "\\\\end{table}" << std::endl;
  file.close();
}
EOF
