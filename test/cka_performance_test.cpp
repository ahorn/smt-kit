#include "gtest/gtest.h"
#include "cka.h"

#include <chrono>
#include <fstream>

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

  file << "\\begin{table}" << std::endl;
  file << "\\begin{center}" << std::endl;
  file << "\\begin{tabular}{l|l|l|l}" << std::endl;
  file << "\\toprule" << std::endl;
  file << "Benchmark & Number of Checks & Numer of Solver Calls & Time (s) \\\\ \\midrule" << std::endl;

  // program size: 11
  {
    file << "00000 & ";
    start = std::chrono::system_clock::now();
    r.check(lfp<','>((W , (P | ((D | Y) + (S , M))))), lfp<','>((I + (E | (I , (R , (E | S)))))));
    end = std::chrono::system_clock::now();

    seconds = std::chrono::duration_cast<std::chrono::seconds>(end - start);

    file << r.number_of_checks() << " & ";
    file << r.number_of_solver_calls() << " & ";
    file << seconds.count() << "\\\\" << std::endl;

    r.reset_number_of_checks();
    r.reset_number_of_solver_calls();
  }
  {
    file << "00001 & ";
    start = std::chrono::system_clock::now();
    r.check(lfp<','>((D , ((B | H) + (D + (F + N))))), lfp<','>(((B + (O | I)) , (O | (O | L)))));
    end = std::chrono::system_clock::now();

    seconds = std::chrono::duration_cast<std::chrono::seconds>(end - start);

    file << r.number_of_checks() << " & ";
    file << r.number_of_solver_calls() << " & ";
    file << seconds.count() << "\\\\" << std::endl;

    r.reset_number_of_checks();
    r.reset_number_of_solver_calls();
  }
  {
    file << "00002 & ";
    start = std::chrono::system_clock::now();
    r.check(lfp<','>((Q | (H + ((C + K) + (J | U))))), lfp<','>((Q + ((N + L) , (C , (T | J))))));
    end = std::chrono::system_clock::now();

    seconds = std::chrono::duration_cast<std::chrono::seconds>(end - start);

    file << r.number_of_checks() << " & ";
    file << r.number_of_solver_calls() << " & ";
    file << seconds.count() << "\\\\" << std::endl;

    r.reset_number_of_checks();
    r.reset_number_of_solver_calls();
  }
  {
    file << "00003 & ";
    start = std::chrono::system_clock::now();
    r.check(lfp<','>((M + (J | (T + (P | (O , J)))))), lfp<','>((K | ((Y | C) | (B + (C + L))))));
    end = std::chrono::system_clock::now();

    seconds = std::chrono::duration_cast<std::chrono::seconds>(end - start);

    file << r.number_of_checks() << " & ";
    file << r.number_of_solver_calls() << " & ";
    file << seconds.count() << "\\\\" << std::endl;

    r.reset_number_of_checks();
    r.reset_number_of_solver_calls();
  }
  {
    file << "00004 & ";
    start = std::chrono::system_clock::now();
    r.check(lfp<','>(((Y , X) , ((P + H) + (P | J)))), lfp<','>((C | ((O , T) , (J , (Q , R))))));
    end = std::chrono::system_clock::now();

    seconds = std::chrono::duration_cast<std::chrono::seconds>(end - start);

    file << r.number_of_checks() << " & ";
    file << r.number_of_solver_calls() << " & ";
    file << seconds.count() << "\\\\" << std::endl;

    r.reset_number_of_checks();
    r.reset_number_of_solver_calls();
  }
  {
    file << "00005 & ";
    start = std::chrono::system_clock::now();
    r.check(lfp<','>((K + (A + (H | (O + (F | X)))))), lfp<','>((K , ((V | K) , (Q | (W + I))))));
    end = std::chrono::system_clock::now();

    seconds = std::chrono::duration_cast<std::chrono::seconds>(end - start);

    file << r.number_of_checks() << " & ";
    file << r.number_of_solver_calls() << " & ";
    file << seconds.count() << "\\\\" << std::endl;

    r.reset_number_of_checks();
    r.reset_number_of_solver_calls();
  }
  {
    file << "00006 & ";
    start = std::chrono::system_clock::now();
    r.check(lfp<','>(((U | (S + C)) , (I + (V | J)))), lfp<','>((W , (K + (Q + (W | (U + R)))))));
    end = std::chrono::system_clock::now();

    seconds = std::chrono::duration_cast<std::chrono::seconds>(end - start);

    file << r.number_of_checks() << " & ";
    file << r.number_of_solver_calls() << " & ";
    file << seconds.count() << "\\\\" << std::endl;

    r.reset_number_of_checks();
    r.reset_number_of_solver_calls();
  }
  {
    file << "00007 & ";
    start = std::chrono::system_clock::now();
    r.check(lfp<','>((Q , (T , (O | (U , (P , Q)))))), lfp<','>(((M + B) + (P , (S , (T + A))))));
    end = std::chrono::system_clock::now();

    seconds = std::chrono::duration_cast<std::chrono::seconds>(end - start);

    file << r.number_of_checks() << " & ";
    file << r.number_of_solver_calls() << " & ";
    file << seconds.count() << "\\\\" << std::endl;

    r.reset_number_of_checks();
    r.reset_number_of_solver_calls();
  }
  {
    file << "00008 & ";
    start = std::chrono::system_clock::now();
    r.check(lfp<','>(((R , (K + O)) | (N , (J | K)))), lfp<','>((C | (P | (D | (R , (H , X)))))));
    end = std::chrono::system_clock::now();

    seconds = std::chrono::duration_cast<std::chrono::seconds>(end - start);

    file << r.number_of_checks() << " & ";
    file << r.number_of_solver_calls() << " & ";
    file << seconds.count() << "\\\\" << std::endl;

    r.reset_number_of_checks();
    r.reset_number_of_solver_calls();
  }
  {
    file << "00009 & ";
    start = std::chrono::system_clock::now();
    r.check(lfp<','>((J | (N + (V + (U + (H , L)))))), lfp<','>(((F , K) , (Q | (Y , (D + U))))));
    end = std::chrono::system_clock::now();

    seconds = std::chrono::duration_cast<std::chrono::seconds>(end - start);

    file << r.number_of_checks() << " & ";
    file << r.number_of_solver_calls() << " & ";
    file << seconds.count() << "\\\\" << std::endl;

    r.reset_number_of_checks();
    r.reset_number_of_solver_calls();
  }
  {
    file << "00010 & ";
    start = std::chrono::system_clock::now();
    r.check(lfp<','>((Q | (Z , (K | (F , (E | J)))))), lfp<','>((S + (Z | (D | (X + (O | A)))))));
    end = std::chrono::system_clock::now();

    seconds = std::chrono::duration_cast<std::chrono::seconds>(end - start);

    file << r.number_of_checks() << " & ";
    file << r.number_of_solver_calls() << " & ";
    file << seconds.count() << "\\\\" << std::endl;

    r.reset_number_of_checks();
    r.reset_number_of_solver_calls();
  }
  {
    file << "00011 & ";
    start = std::chrono::system_clock::now();
    r.check(lfp<','>(((L + G) | (H , (A + (Q | Z))))), lfp<','>((N , ((C + E) | (K , (Z + X))))));
    end = std::chrono::system_clock::now();

    seconds = std::chrono::duration_cast<std::chrono::seconds>(end - start);

    file << r.number_of_checks() << " & ";
    file << r.number_of_solver_calls() << " & ";
    file << seconds.count() << "\\\\" << std::endl;

    r.reset_number_of_checks();
    r.reset_number_of_solver_calls();
  }
  {
    file << "00012 & ";
    start = std::chrono::system_clock::now();
    r.check(lfp<','>((A + (H , (F , (K | (B | L)))))), lfp<','>((Q + (C | ((L | B) + (I | P))))));
    end = std::chrono::system_clock::now();

    seconds = std::chrono::duration_cast<std::chrono::seconds>(end - start);

    file << r.number_of_checks() << " & ";
    file << r.number_of_solver_calls() << " & ";
    file << seconds.count() << "\\\\" << std::endl;

    r.reset_number_of_checks();
    r.reset_number_of_solver_calls();
  }
  {
    file << "00013 & ";
    start = std::chrono::system_clock::now();
    r.check(lfp<','>((W | (S + (M | (G | (Y , F)))))), lfp<','>((R | ((M + V) , (A , (U + D))))));
    end = std::chrono::system_clock::now();

    seconds = std::chrono::duration_cast<std::chrono::seconds>(end - start);

    file << r.number_of_checks() << " & ";
    file << r.number_of_solver_calls() << " & ";
    file << seconds.count() << "\\\\" << std::endl;

    r.reset_number_of_checks();
    r.reset_number_of_solver_calls();
  }
  {
    file << "00014 & ";
    start = std::chrono::system_clock::now();
    r.check(lfp<','>((Z + (T | (J + (B , (I + Q)))))), lfp<','>((X + (V | (Z + (T , (X , S)))))));
    end = std::chrono::system_clock::now();

    seconds = std::chrono::duration_cast<std::chrono::seconds>(end - start);

    file << r.number_of_checks() << " & ";
    file << r.number_of_solver_calls() << " & ";
    file << seconds.count() << "\\\\" << std::endl;

    r.reset_number_of_checks();
    r.reset_number_of_solver_calls();
  }
  {
    file << "00015 & ";
    start = std::chrono::system_clock::now();
    r.check(lfp<','>((I + (W + (Z | (A + (Q + H)))))), lfp<','>(((B , J) , (J | (X + (N + C))))));
    end = std::chrono::system_clock::now();

    seconds = std::chrono::duration_cast<std::chrono::seconds>(end - start);

    file << r.number_of_checks() << " & ";
    file << r.number_of_solver_calls() << " & ";
    file << seconds.count() << "\\\\" << std::endl;

    r.reset_number_of_checks();
    r.reset_number_of_solver_calls();
  }

  file << "\\bottomrule" << std::endl;
  file << "\\end{tabular}" << std::endl;
  file << "\\caption{Benchmarks with a symbolic implementation of partial strings}" << std::endl;
  file << "\\label{table:cka-benchmarks}" << std::endl;
  file << "\\end{center}" << std::endl;
  file << "\\end{table}" << std::endl;
  file.close();
}

TEST(CkaPerformanceTest, Benchmark)
{
#if 0
  cka_benchmark();
#endif
}
