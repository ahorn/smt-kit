#include "gtest/gtest.h"
#include "cka.h"

#include <chrono>
#include <fstream>

using namespace cka;

typedef std::vector<std::pair<Program, Program>> ProgramBenchmarks;

/* These benchmarks are automatically run when "make test" is executed provided
   that `_CKA_PERFORMANCE_TEST_` is defined, i.e. `#define _CKA_PERFORMANCE_TEST_`.

   We performed all experiments on a 64-bit machine running OS X (10.9.4) with
   a single 2GHz Intel Core i7 processor (two cores), 256 KB L2 cache (per core),
   4MB L3 cache and 8GB 1600 MHz DDR3 of main memory. This hardware configuration
   gives the following results when we use the Z3 theorem prover as SMT solver:

     \begin{table}
     \begin{center}
     \begin{tabular}{r|r|r|r|r}
     \toprule
     Benchmark & Number of Checks & Number of Shortcuts & Numer of Solver Calls & Time (s) \\ \midrule
     0 & 349524 & 349520 & 4 & 22\\
     1 & 2441405 & 2439530 & 1875 & 70\\
     2 & 2015538 & 2015406 & 132 & 34\\
     3 & 349524 & 349490 & 34 & 18\\
     4 & 2015538 & 2011766 & 3772 & 58\\
     5 & 2441405 & 2440755 & 650 & 58\\
     6 & 488280 & 488242 & 38 & 15\\
     7 & 960799 & 960795 & 4 & 13\\
     8 & 2441405 & 2441399 & 6 & 182\\
     9 & 12093234 & 12092986 & 248 & 280\\
     10 & 66429 & 66186 & 243 & 2\\
     11 & 335924 & 335921 & 3 & 4\\
     12 & 2015538 & 2015481 & 57 & 38\\
     13 & 488280 & 488279 & 1 & 9\\
     14 & 47079207 & 47000273 & 78934 & 1389\\
     15 & 488280 & 488268 & 12 & 11\\
     16 & 335924 & 335922 & 2 & 9\\
     17 & 488280 & 487971 & 309 & 13\\
     18 & 2396744 & 2396736 & 8 & 23\\
     19 & 335922 & 335920 & 2 & 5\\
     20 & 19530 & 18952 & 578 & 3\\
     21 & 55986 & 55575 & 411 & 3\\
     22 & 488281 & 488280 & 1 & 11\\
     23 & 488281 & 488280 & 1 & 15\\
     24 & 2441405 & 2441236 & 169 & 141\\
     25 & 2441405 & 2440522 & 883 & 63\\
     26 & 22620 & 22164 & 456 & 3\\
     27 & 2015541 & 2015540 & 1 & 32\\
     28 & 349524 & 349460 & 64 & 17\\
     29 & 2015538 & 2015097 & 441 & 37\\
     30 & 2441405 & 2441237 & 168 & 168\\
     31 & 12093234 & 12093155 & 79 & 350\\
     32 & 488280 & 488266 & 14 & 8\\
     33 & 87380 & 87372 & 8 & 5\\
     34 & 97655 & 97654 & 1 & 5\\
     35 & 488281 & 488280 & 1 & 8\\
     36 & 2015539 & 2015538 & 1 & 67\\
     37 & 488280 & 487964 & 316 & 12\\
     38 & 2441405 & 2387860 & 53545 & 517\\
     39 & 335922 & 331174 & 4748 & 35\\
     40 & 488280 & 488273 & 7 & 10\\
     41 & 335922 & 335916 & 6 & 4\\
     42 & 349524 & 349450 & 74 & 16\\
     43 & 2015538 & 2010538 & 5000 & 66\\
     44 & 87380 & 87275 & 105 & 3\\
     45 & 2015538 & 1954008 & 61530 & 514\\
     46 & 335923 & 335922 & 1 & 17\\
     47 & 488280 & 488235 & 45 & 20\\
     48 & 349524 & 349512 & 12 & 24\\
     49 & 2441405 & 2439055 & 2350 & 94\\
     50 & 2441405 & 2440103 & 1302 & 94\\
     \bottomrule
     \end{tabular}
     \caption{Benchmarks with a symbolic implementation of partial strings}
     \label{table:z3-cka-benchmarks}
     \end{center}
     \end{table}


   Running MathSAT5 (Version 5.2.12, June 5, 2014), we get the following:

     \begin{table}
     \begin{center}
     \begin{tabular}{r|r|r|r|r}
     \toprule
     Benchmark & Number of Checks & Number of Shortcuts & Numer of Solver Calls & Time (s) \\ \midrule
     0 & 349524 & 349520 & 4 & 23\\
     1 & 2441405 & 2439530 & 1875 & 95\\
     2 & 2015538 & 2015406 & 132 & 32\\
     3 & 349524 & 349490 & 34 & 19\\
     4 & 2015538 & 2011766 & 3772 & 88\\
     5 & 2441405 & 2440755 & 650 & 63\\
     6 & 488280 & 488242 & 38 & 15\\
     7 & 960799 & 960795 & 4 & 11\\
     8 & 2441405 & 2441399 & 6 & 158\\
     9 & 12093234 & 12092986 & 248 & 267\\
     10 & 66429 & 66186 & 243 & 6\\
     11 & 335924 & 335921 & 3 & 4\\
     12 & 2015538 & 2015481 & 57 & 37\\
     13 & 488280 & 488279 & 1 & 9\\
     14 & 47079207 & 47000273 & 78934 & 2225\\
     15 & 488280 & 488268 & 12 & 11\\
     16 & 335924 & 335922 & 2 & 9\\
     17 & 488280 & 487971 & 309 & 15\\
     18 & 2396744 & 2396736 & 8 & 23\\
     19 & 335922 & 335920 & 2 & 4\\
     20 & 19530 & 18952 & 578 & 4\\
     21 & 55986 & 55575 & 411 & 4\\
     22 & 488281 & 488280 & 1 & 11\\
     23 & 488281 & 488280 & 1 & 14\\
     24 & 2441405 & 2441236 & 169 & 142\\
     25 & 2441405 & 2440522 & 883 & 75\\
     26 & 22620 & 22164 & 456 & 7\\
     27 & 2015541 & 2015540 & 1 & 32\\
     28 & 349524 & 349460 & 64 & 17\\
     29 & 2015538 & 2015097 & 441 & 37\\
     30 & 2441405 & 2441237 & 168 & 167\\
     31 & 12093234 & 12093155 & 79 & 339\\
     32 & 488280 & 488266 & 14 & 8\\
     33 & 87380 & 87372 & 8 & 5\\
     34 & 97655 & 97654 & 1 & 5\\
     35 & 488281 & 488280 & 1 & 8\\
     36 & 2015539 & 2015538 & 1 & 65\\
     37 & 488280 & 487964 & 316 & 15\\
     38 & 2441405 & 2387860 & 53545 & 1212\\
     39 & 335922 & 331174 & 4748 & 58\\
     40 & 488280 & 488273 & 7 & 9\\
     41 & 335922 & 335916 & 6 & 4\\
     42 & 349524 & 349450 & 74 & 17\\
     43 & 2015538 & 2010538 & 5000 & 87\\
     44 & 87380 & 87275 & 105 & 3\\
     45 & 2015538 & 1954008 & 61530 & 1048\\
     46 & 335923 & 335922 & 1 & 16\\
     47 & 488280 & 488235 & 45 & 21\\
     48 & 349524 & 349512 & 12 & 24\\
     49 & 2441405 & 2439055 & 2350 & 126\\
     50 & 2441405 & 2440103 & 1302 & 111\\
     \bottomrule
     \end{tabular}
     \caption{Benchmarks with a symbolic implementation of partial strings}
     \label{table:cka-benchmarks}
     \end{center}
     \end{table}
*/
#ifdef _CKA_PERFORMANCE_TEST_
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

  file << "\\begin{table}" << std::endl;
  file << "\\begin{center}" << std::endl;
  file << "\\begin{tabular}{r|r|r|r|r}" << std::endl;
  file << "\\toprule" << std::endl;
  file << "Benchmark & Number of Checks & Number of Shortcuts & Numer of Solver Calls & Time (s) \\\\ \\midrule" << std::endl;

  // program size: 15
  ProgramBenchmarks benchmarks = {
    /*  0 */ {{ ((W | X) | (U | (X , (Y | (Y | (U , Z)))))) }, { (Z + (Z | ((V | X) , (W + (Z + (Z | U)))))) }},
    /*  1 */ {{ (X | ((W , (Z | U)) | ((Y , X) , (U , Y)))) }, { ((Z , Y) + (Z + (V + (Y + (W | (W , U)))))) }},
    /*  2 */ {{ (Z , ((W , (U | Y)) | (U + (X , (V , Z))))) }, { ((U + Z) + (W , ((V , Z) + (Y + (U + Y))))) }},
    /*  3 */ {{ (Z , (V , ((U , V) | ((W | X) | (X , X))))) }, { ((X + Y) + ((Y | X) | (W + (U | (Z , Z))))) }},
    /*  4 */ {{ ((Y , (Y + V)) , (W | ((V | Z) | (Z | Y)))) }, { ((W + (X + V)) + (Z , (Z + (X + (Z , W))))) }},
    /*  5 */ {{ ((X , (Z | U)) , (U | (X , (Z , (Y , Z))))) }, { (U + (X + (Y + (Z , ((X + Y) , (Y , V)))))) }},
    /*  6 */ {{ (Z , ((U + (W , U)) , ((Z , W) | (V , X)))) }, { (V + (Z | ((U + Y) + (Y , (Z + (V , Y)))))) }},
    /*  7 */ {{ (X , ((U , (W + Y)) | (W + (U | (Z | Z))))) }, { ((Z + (X , X)) + (V + ((V + U) , (V + W)))) }},
    /*  8 */ {{ (Z | ((Z , (W , V)) , (Y , (U | (U , U))))) }, { (W + ((V | W) | ((U | W) + (Z + (X + Y))))) }},
    /*  9 */ {{ ((Y , V) | (Z | (Y | (U | (U | (U , U)))))) }, { (U + ((V , X) + (Z , ((W + V) , (W + V))))) }},
    /* 10 */ {{ (V | ((Z | V) | (Z | (V , (U , (W | Y)))))) }, { ((V + (Y + V)) , ((V , V) + (X + (U | Z)))) }},
    /* 11 */ {{ (Z | (Y + ((W + Y) , (X | (U , (X , Z)))))) }, { ((Z + (Y | Z)) + (U + (Y + (U , (W + Y))))) }},
    /* 12 */ {{ (W | (U , (V | (Z + ((Z , Y) , (V , Y)))))) }, { (((W + Z) + (Z + Y)) + (Z | (U + (V , U)))) }},
    /* 13 */ {{ ((Y , Z) | (X | (Z + ((X | Y) , (W | X))))) }, { (W + (U + (X , ((Y + U) + (Y | (X , Z)))))) }},
    /* 14 */ {{ (V | ((Y , V) , ((Y | V) , (Y , (Y | V))))) }, { (((W , Y) + (X + Z)) + ((Y + Z) + (V + W))) }},
    /* 15 */ {{ ((U , (X | W)) , (Z | (X , (Y + (U , V))))) }, { ((W | (X + Z)) + (W + (U , (X , (V + Y))))) }},
    /* 16 */ {{ (X + (X + ((U | U) , (Y | (W , (W , W)))))) }, { (X + (W | (X + (U + (Z + (W | (Z + U))))))) }},
    /* 17 */ {{ ((V + (V , U)) , (Z , (U , (Y | (V , X))))) }, { (U + (Y + ((V , Z) + (U | (Z + (W | Z)))))) }},
    /* 18 */ {{ ((Y | Y) , (Y + ((V | Z) | (U , (Z + U))))) }, { ((V + (Y + (U + Y))) + (X + (V + (Z + X)))) }},
    /* 19 */ {{ (W | (Y + (U + ((X | Z) | (X , (Y | V)))))) }, { ((Y + (X , X)) + ((W + Z) + (Z | (X + Z)))) }},
    /* 20 */ {{ (W , ((Y | U) , (X | (Z + (Y + (U + Y)))))) }, { (W + ((X + (U + Z)) + (Z , (Z , (U | X))))) }},
    /* 21 */ {{ ((U | (Y + W)) | (Z , (X , (V + (U + Y))))) }, { (Y + ((U + Z) + (U | ((U | W) + (Z + X))))) }},
    /* 22 */ {{ (U + (Y | (Y | ((Y , Z) , (W , (W | V)))))) }, { (U + (W + (Z + (Y , ((Y + Z) | (X , W)))))) }},
    /* 23 */ {{ (Z + (Y | ((W , V) | ((V | U) | (Y , Z))))) }, { (Z + ((U + W) , (Z , (U + (V | (Z | Y)))))) }},
    /* 24 */ {{ ((W , (W , U)) | ((V , X) | (Z | (X , V)))) }, { (X + ((Z + X) | (U + (Z | (V , (W , U)))))) }},
    /* 25 */ {{ ((V , Y) , (Y , (U , (U , (U | (V | Y)))))) }, { (X + ((Z + (W | Y)) + (U + (V , (X | U))))) }},
    /* 26 */ {{ ((W + U) | ((W , U) | (V | (V , (Z , Y))))) }, { ((U + (Z + X)) | (U + (U + (V , (V + X))))) }},
    /* 27 */ {{ (U + (Y | ((U , (V | Y)) , (U , (X , Z))))) }, { (Z + ((V + (U + Z)) + (Z + (Y | (W , Y))))) }},
    /* 28 */ {{ (Z | (W , (U | (X | (U | (X | (Z | X))))))) }, { ((V + U) + ((U + V) | ((Z , U) , (Z | Z)))) }},
    /* 29 */ {{ ((Z + (W , W)) | ((Y | Y) , (X | (W | V)))) }, { (W + ((U | Z) + (Z + (V , (Z + (W + Y)))))) }},
    /* 30 */ {{ (Y , ((Z | U) , (U | (W | (U , (X | U)))))) }, { (Y + (W + ((U + (U + X)) | (X | (Z | Z))))) }},
    /* 31 */ {{ (Z , (Y | (W | (X | ((Y | Y) , (X , Z)))))) }, { (U + (Z + (V + (W | (Y + (Z , (U + X))))))) }},
    /* 32 */ {{ ((Y , (X | U)) , (V + ((V | V) | (U , Y)))) }, { ((Y , X) + ((U + Z) + ((X , Y) + (Y | U)))) }},
    /* 33 */ {{ ((U | (V | U)) | ((Y | W) | (W + (W , U)))) }, { (W + (X + ((W | (V + W)) | (U | (Y | V))))) }},
    /* 34 */ {{ (V , (W , (Y + ((Y + V) , (Y | (Z | U)))))) }, { (U + (X | (Y | (V + (Y | (W + (U + X))))))) }},
    /* 35 */ {{ (V + (W | (X , (W | (U , (W | (Y , U))))))) }, { ((V + Y) + (V , (X + (V + (X , (W , Y)))))) }},
    /* 36 */ {{ (U + ((Y , (U | X)) , (Z | (Z , (V | Z))))) }, { (U + (Y | (U , ((Y + V) + (U + (Z + Y)))))) }},
    /* 37 */ {{ ((U | Z) | (U | (Y | (X | (Z | (X + W)))))) }, { ((Z + U) + ((U , W) , ((X | X) + (U + W)))) }},
    /* 38 */ {{ (Z | (Y , ((Z | Z) | (U , (W | (W | W)))))) }, { (Z + (U + ((W + V) + (Y , (W | (X | U)))))) }},
    /* 39 */ {{ ((V + U) , (U | ((Y + V) | (V | (Z | X))))) }, { (U + (Z + (U + (X + (V , (Z + (U | W))))))) }},
    /* 40 */ {{ (X | ((Y , Z) | (V | (X , (W + (U , X)))))) }, { (W + (U + ((Y , Z) , (Z + (V + (W | U)))))) }},
    /* 41 */ {{ ((U + Y) | (Z , (U | (U + (V , (X , W)))))) }, { ((V + Z) + (X + (U , (U , (W + (V + U)))))) }},
    /* 42 */ {{ (X , (U , (X , ((V , V) | (V | (U , Z)))))) }, { (Z + ((V , Y) + ((U | U) | (Z + (Z , Z))))) }},
    /* 43 */ {{ (Z , (X | (U | (X , (W , (Z + (W | V))))))) }, { ((Y + (Y | Y)) + ((U + Z) + (Z + (W | X)))) }},
    /* 44 */ {{ (W , (V , ((V | (Z , X)) , (Z + (V | V))))) }, { ((Z + (V | Z)) + (Z + (U | (V , (V | X))))) }},
    /* 45 */ {{ ((U , Y) , (Z , ((V + Y) | (X , (U | W))))) }, { (X + (Z + (W + (Z + (U + (Y | (Z | V))))))) }},
    /* 46 */ {{ (U + (W | (Z | (Z | (Z + (V , (V , X))))))) }, { (U + (U | (X + ((U + Y) | (U | (Y + X)))))) }},
    /* 47 */ {{ (U | ((X + (Z | W)) | (V | (V | (X , Y))))) }, { ((U + W) + (U | (Y | (U + (W , (W + Z)))))) }},
    /* 48 */ {{ ((Y | Y) , ((V | V) | (X | (U | (Y | W))))) }, { (Y + (U | (Y , (W | (X , (Y + (X + U))))))) }},
    /* 49 */ {{ (V | (Y | ((U | X) , (Z | (U | (X , W)))))) }, { (Y + (U + ((W | Z) + (Y | (Z + (Y , V)))))) }},
    /* 50 */ {{ ((U | U) , ((Z , (V | U)) | (Z | (Z | Y)))) }, { ((U + V) + (Y + ((W , X) | (Z + (X | W))))) }},
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
    file << seconds.count() << "\\\\" << std::endl;
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
  cka_benchmark();
}
#endif

#ifdef _DRD_PERFORMANCE_TEST_
/// Since the Seed tool does not supports neither binary nor ternary
/// function applications, we explicitly enumerate the arguments to
// the functions in the `memory` namespace.
static constexpr memory::Address s_address_a = 0U;
static constexpr memory::Address s_address_b = 1U;
static constexpr memory::Address s_address_c = 2U;

typedef memory::SymbolicProgram SymbolicProgram;

#define IF_THEN_DEF(address, byte)                                          \
static SymbolicProgram if_then_##address##_##byte(const SymbolicProgram& P) \
{                                                                           \
  return if_then(s_address_##a, '\0' + (char) (byte), P);                   \
}

IF_THEN_DEF(a, 0)
IF_THEN_DEF(b, 0)
IF_THEN_DEF(c, 0)

IF_THEN_DEF(a, 1)
IF_THEN_DEF(b, 1)
IF_THEN_DEF(c, 1)

IF_THEN_DEF(a, 2)
IF_THEN_DEF(b, 2)
IF_THEN_DEF(c, 2)

SymbolicProgram none_load(const memory::Address address)
{
  return {memory::none_load_label(address)};
}

SymbolicProgram acquire_load(const memory::Address address)
{
  return {memory::acquire_load_label(address)};
}

#define STORE_DEF(mode, address)                                            \
SymbolicProgram mode##_store_##address(const memory::Byte byte)             \
{                                                                           \
  return {memory::mode##_store_label(s_address_##address, byte)};           \
}

STORE_DEF(none, a)
STORE_DEF(none, b)
STORE_DEF(none, c)

STORE_DEF(release, a)
STORE_DEF(release, b)
STORE_DEF(release, c)

typedef std::vector<memory::SymbolicProgram> SymbolicPrograms;

/* Experimental results with random data set

   MathSAT5 results if _CKA_REAL_ is disabled:

   Benchmark & Number of instructions & Racy & Time (s) \\ \midrule
   0 & 37 & 0 & 111\\
   1 & 37 & 0 & 105\\
   2 & 39 & 0 & 161\\
   3 & 41 & 0 & 236\\
   4 & 39 & 0 & 164\\
   5 & 39 & 0 & 166\\
   6 & 41 & 0 & 241\\
   7 & 37 & 0 & 111\\
   8 & 35 & 0 & 69\\
   9 & 43 & 0 & 329\\

   Yices 2 results if _CKA_REAL_ is disabled:

   0 & 37 & 0 & 87\\
   1 & 37 & 0 & 83\\
   2 & 39 & 0 & 127\\
   3 & 41 & 0 & 178\\
   4 & 39 & 0 & 119\\
   5 & 39 & 0 & 129\\
   6 & 41 & 0 & 185\\
   7 & 37 & 0 & 80\\
   8 & 35 & 0 & 53\\
   9 & 43 & 0 & 271\\

   Z3 results if _CKA_REAL_ is disabled:

   0 & 37 & 0 & 97\\
   1 & 37 & 0 & 94\\
   2 & 39 & 0 & 139\\
   3 & 41 & 0 & 197\\
   4 & 39 & 0 & 138\\
   5 & 39 & 0 & 136\\
   6 & 41 & 0 & 202\\
   7 & 37 & 0 & 92\\
   8 & 35 & 0 & 62\\
   9 & 43 & 0 & 308\\

   In the case of MathSAT5, Yices 2 and Z3,
   if _CKA_REAL_ is enabled we get the following:

   0 & 37 & 0 & 0\\
   1 & 37 & 0 & 0\\
   2 & 39 & 0 & 0\\
   3 & 41 & 0 & 0\\
   4 & 39 & 0 & 0\\
   5 & 39 & 0 & 0\\
   6 & 41 & 0 & 0\\
   7 & 37 & 0 & 0\\
   8 & 35 & 0 & 0\\
   9 & 43 & 0 & 0\\
*/
void drd_benchmark()
{
  memory::DataRaceDetector drd;

  auto start = std::chrono::system_clock::now();
  auto end = std::chrono::system_clock::now();
  std::chrono::seconds seconds;

  std::ofstream file("drd_benchmark_results.tex");

  file << "\\begin{table}" << std::endl;
  file << "\\begin{center}" << std::endl;
  file << "\\begin{tabular}{r|r|r|r}" << std::endl;
  file << "\\toprule" << std::endl;
  file << "Benchmark & Number of instructions & Racy & Time (s) \\\\ \\midrule" << std::endl;

  SymbolicPrograms benchmarks = {
    /* 0 */ { if_then_a_2(if_then_c_2(if_then_c_2(if_then_b_2(if_then_a_1(if_then_b_1((if_then_b_1(none_load(s_address_b)) | if_then_b_2(if_then_c_1(if_then_a_1(if_then_b_1(if_then_a_0((if_then_c_2(if_then_b_1((if_then_c_2(none_store_c('\2')) | if_then_c_0((if_then_c_0(release_store_c('\2')) , if_then_b_0(if_then_c_0(release_store_c('\1')))))))) | if_then_a_2(if_then_c_0(if_then_c_0(if_then_c_0(if_then_a_2(if_then_a_2((none_store_c('\0') | if_then_c_2(if_then_a_0(if_then_b_2((if_then_a_1(none_load(s_address_a)) , if_then_a_0(none_load(s_address_c)))))))))))))))))))))))))) },
    /* 1 */ { (if_then_b_2(if_then_a_2(if_then_c_1(if_then_c_2(if_then_b_0(if_then_a_0(acquire_load(s_address_b))))))) | if_then_b_1(if_then_a_1(if_then_a_0((release_store_c('\1') , if_then_c_2(if_then_b_1(if_then_c_0(if_then_c_2(if_then_b_0(if_then_b_2((if_then_c_1(if_then_b_2(if_then_c_2((acquire_load(s_address_b) , if_then_b_1(if_then_b_2(if_then_a_1(release_store_b('\1')))))))) | if_then_b_2(if_then_a_2(if_then_c_1((none_store_b('\0') , (if_then_b_1(if_then_a_0(release_store_a('\2'))) , if_then_a_0(if_then_a_2(if_then_c_2(if_then_c_1(release_store_a('\0')))))))))))))))))))))) },
    /* 2 */ { if_then_b_1(if_then_b_0(if_then_c_0(if_then_a_2(if_then_b_2(if_then_b_2(if_then_a_2(if_then_c_2(if_then_b_1(if_then_b_1(if_then_c_0(if_then_c_2(if_then_c_2(if_then_c_1(if_then_b_1(if_then_c_2(if_then_a_0((acquire_load(s_address_b) | if_then_b_2(if_then_b_0((release_store_c('\0') | if_then_c_1(if_then_b_0(if_then_a_1(if_then_a_1((if_then_a_0(if_then_c_2(if_then_b_1(if_then_b_1(release_store_a('\1'))))) , (release_store_b('\0') , if_then_c_1(if_then_a_2(if_then_a_0((if_then_a_1(release_store_b('\2')) | if_then_a_0(if_then_c_2(release_store_b('\2')))))))))))))))))))))))))))))))))) },
    /* 3 */ { if_then_b_2(if_then_b_2(if_then_a_1(if_then_c_2(if_then_c_2((if_then_b_0(if_then_b_2(if_then_a_0(if_then_b_0(release_store_b('\0'))))) | if_then_a_2(if_then_a_1(if_then_a_2((if_then_a_0(release_store_c('\1')) , if_then_b_0(if_then_c_2(if_then_b_0(if_then_b_0(if_then_b_2(if_then_b_0(if_then_c_0((none_store_a('\0') , if_then_c_2(if_then_b_1((if_then_c_1(if_then_b_1(if_then_c_1(if_then_b_1(if_then_b_1(if_then_a_0(none_store_c('\0'))))))) , if_then_a_1(if_then_a_0(if_then_c_0(if_then_b_1(if_then_c_0(if_then_c_0(if_then_b_0(if_then_c_2(release_store_c('\1')))))))))))))))))))))))))))))) },
    /* 4 */ { if_then_a_1(if_then_b_2(if_then_a_2(if_then_a_1(if_then_a_0(if_then_b_1(if_then_b_0(if_then_b_2(if_then_c_0(if_then_a_0(if_then_c_0(if_then_a_0((if_then_b_1(release_store_c('\1')) | if_then_b_1(if_then_a_2(if_then_a_1(if_then_b_0(if_then_b_2((if_then_c_1(if_then_c_0(if_then_c_1(if_then_a_2(if_then_c_0(none_load(s_address_b)))))) | (release_store_a('\1') , if_then_c_2(if_then_c_2((if_then_c_2(if_then_b_0(if_then_b_1(if_then_b_1(none_load(s_address_b))))) , if_then_a_0(if_then_a_0((if_then_c_0(none_store_a('\1')) | if_then_b_2(acquire_load(s_address_a)))))))))))))))))))))))))))) },
    /* 5 */ { if_then_b_0((if_then_c_2(if_then_b_0(if_then_c_0(release_store_b('\1')))) , if_then_a_2((if_then_c_2(if_then_a_0((acquire_load(s_address_b) , if_then_a_0((if_then_b_1(if_then_c_0(none_store_b('\0'))) | if_then_b_1(if_then_a_0(if_then_b_1(if_then_b_1(none_store_b('\0')))))))))) | if_then_c_0(if_then_c_2(if_then_c_1(if_then_a_2(if_then_a_1(if_then_b_0(if_then_c_0(if_then_b_1((if_then_c_2(if_then_c_0(if_then_b_0(if_then_b_0(none_load(s_address_a))))) , if_then_c_1(if_then_b_2(if_then_c_1(if_then_a_2(if_then_a_1(if_then_a_0(if_then_b_1(release_store_a('\2'))))))))))))))))))))) },
    /* 6 */ { (if_then_a_0(if_then_a_1(if_then_b_2(if_then_c_0(if_then_b_1(if_then_a_1(none_store_c('\1'))))))) | if_then_b_1(if_then_b_2(if_then_a_2(if_then_c_2(if_then_a_1((if_then_c_0(if_then_a_1(if_then_c_1(if_then_c_1(if_then_a_1(if_then_b_0(if_then_a_0(if_then_c_2(if_then_b_1(if_then_c_0(if_then_b_1(if_then_b_1(release_store_b('\2'))))))))))))) , (if_then_c_0(if_then_a_2(if_then_b_2(if_then_b_2(none_store_c('\0'))))) , if_then_c_1((if_then_b_2(if_then_a_1(if_then_c_0(none_store_a('\0')))) , if_then_c_1(if_then_a_1(if_then_c_0(if_then_b_0(if_then_c_2(none_store_a('\2')))))))))))))))) },
    /* 7 */ { if_then_c_0(if_then_c_1(if_then_c_2((if_then_a_0(if_then_c_0(if_then_c_0(if_then_b_2(if_then_a_2((if_then_b_0(none_store_c('\1')) , (release_store_c('\0') , if_then_a_2(none_load(s_address_b))))))))) | if_then_b_1(if_then_c_0(if_then_b_1(if_then_c_1(if_then_c_0(if_then_c_2(if_then_a_1((release_store_c('\2') | if_then_a_0(if_then_a_0(if_then_b_1(if_then_b_1(if_then_c_1(if_then_a_2((none_store_a('\1') | if_then_a_1((if_then_a_0(if_then_a_2(none_store_b('\2'))) , if_then_c_2(if_then_c_2(if_then_a_1(if_then_c_1(none_store_a('\1')))))))))))))))))))))))))) },
    /* 8 */ { (if_then_c_2(release_store_b('\0')) | (if_then_a_0(if_then_a_2(if_then_a_1(if_then_b_0(if_then_c_1(release_store_a('\1')))))) | if_then_c_1(if_then_b_2(if_then_c_0(if_then_c_1(if_then_c_1(if_then_b_0(if_then_a_2(if_then_b_0(if_then_b_2((if_then_b_0(if_then_c_0((if_then_c_1(if_then_b_2(release_store_c('\0'))) | (none_store_c('\0') | if_then_a_1(none_store_b('\0')))))) , if_then_b_0(if_then_a_2(if_then_a_1((release_store_c('\2') | if_then_a_1(if_then_a_0(if_then_b_2((none_store_b('\0') , if_then_c_2(none_store_b('\0')))))))))))))))))))))) },
    /* 9 */ { if_then_b_0((if_then_c_1(if_then_c_2(if_then_b_0(if_then_c_2(if_then_a_2(if_then_c_0(if_then_b_1(if_then_b_1(if_then_a_2(if_then_a_2(if_then_b_0((release_store_a('\0') | if_then_c_0(if_then_a_1(if_then_b_0(if_then_b_0(if_then_b_1(if_then_b_1(if_then_a_1(release_store_b('\1')))))))))))))))))))) | if_then_c_0(if_then_c_0(if_then_b_1(if_then_a_0(if_then_a_0(if_then_a_1(if_then_b_1(if_then_a_2(if_then_b_1(if_then_c_1(if_then_a_2(if_then_a_1(if_then_a_0(if_then_b_0(if_then_b_1(if_then_c_2(if_then_b_1(if_then_c_0(if_then_b_0((none_store_a('\0') , if_then_a_1(none_store_a('\2')))))))))))))))))))))))) }
  };

  bool racy;
  for (std::size_t n = 0; n < benchmarks.size(); ++n)
  {
    file << n << " & ";
    file << benchmarks[n].p().length() << " & ";

    start = std::chrono::system_clock::now();
    racy = drd.is_racy(benchmarks[n]);
    end = std::chrono::system_clock::now();

    seconds = std::chrono::duration_cast<std::chrono::seconds>(end - start);
    file << racy << " & ";

    file << seconds.count() << "\\\\" << std::endl;
  }

  file << "\\bottomrule" << std::endl;
  file << "\\end{tabular}" << std::endl;
  file << "\\caption{Data race detection benchmarks}" << std::endl;
  file << "\\label{table:drd-benchmarks}" << std::endl;
  file << "\\end{center}" << std::endl;
  file << "\\end{table}" << std::endl;
  file.close();
}

TEST(CkaPerformanceTest, DataRaceDetection)
{
  drd_benchmark();

 EXPECT_TRUE(false);
}
#endif
