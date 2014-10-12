#!/bin/bash

BENCHMARK_NUM=${1:-3}
PROG_SIZE=${2:-7}

JAVA=java

# The XML schema file "seed.dtd" must be
# in the same directory as Seed's JAR file
SEED_JAR="seed.jar"
SEED="${JAVA} -jar ${SEED_JAR} test/CKA-benchmark.xml ${PROG_SIZE} -text"

usage() {
  echo "Usage: $0 [end-benchmark-number=3] [program-size=7]"
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

typedef std::vector<std::pair<Program, Program>> ProgramBenchmarks;

void cka_benchmark()
{
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
  file << "\\\\begin{tabular}{r|r|r|r|r}" << std::endl;
  file << "\\\\toprule" << std::endl;
  file << "Benchmark & Number of Checks & Number of Shortcuts & Numer of Solver Calls & Time (s) \\\\\\\\ \\\\midrule" << std::endl;

  // program size: ${PROG_SIZE}
  ProgramBenchmarks benchmarks = {
EOF

for i in $(seq 0 ${BENCHMARK_NUM})
do
  LHS=`${SEED}`
  RHS=`${SEED}`

  echo "    /* ${i} */ {{ ${LHS} }, { ${RHS} }},"
done

cat <<EOF
  };

  for (std::size_t n = 0; n < benchmarks.size(); ++n)
  {
    r.reset_number_of_checks();
    r.reset_number_of_shortcuts();
    r.reset_number_of_solver_calls();

    file << n << " & ";
    start = std::chrono::system_clock::now();
    r.check(lfp<','>(benchmarks[n].first), lfp<','>(benchmarks[n].second));
    end = std::chrono::system_clock::now();

    seconds = std::chrono::duration_cast<std::chrono::seconds>(end - start);

    file << r.number_of_checks() << " & ";
    file << r.number_of_shortcuts() << " & ";
    file << r.number_of_solver_calls() << " & ";
    file << seconds.count() << "\\\\\\\\" << std::endl;
  }

  file << "\\\\bottomrule" << std::endl;
  file << "\\\\end{tabular}" << std::endl;
  file << "\\\\caption{Benchmarks with a symbolic implementation of partial strings}" << std::endl;
  file << "\\\\label{table:cka-benchmarks}" << std::endl;
  file << "\\\\end{center}" << std::endl;
  file << "\\\\end{table}" << std::endl;
  file.close();
}
EOF
