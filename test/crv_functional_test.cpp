#include "crv.h"

// Include <gtest/gtest.h> _after_ "crv.h"
#include "gtest/gtest.h"
#include <array>

TEST(CrvFunctionalTest, SafeIf)
{
  crv::tracer().reset();
  crv::dfs_prune_checker().reset();
  crv::Encoder encoder;

  bool error = false;
  do
  {
    crv::External<char> x('A');
    if (crv::dfs_prune_checker().branch(x == '?'))
      x = 'B';
    crv::Internal<char> a(x);

    crv::dfs_prune_checker().add_error(!(a == 'B' || a == 'A'));

    if (!crv::dfs_prune_checker().errors().is_null() &&
        smt::sat == encoder.check(crv::tracer(), crv::dfs_prune_checker()))
      error = true;
  }
  while (crv::dfs_prune_checker().find_next_path());
  EXPECT_FALSE(error);
}

TEST(CrvFunctionalTest, MultipathSafeIf)
{
  crv::tracer().reset();
  crv::dfs_prune_checker().reset();
  crv::Encoder encoder;

  crv::External<char> x('A');
  crv::tracer().scope_then(x == '?');
  x = 'B';
  crv::tracer().scope_end();
  crv::Internal<char> a(x);
  crv::dfs_prune_checker().add_error(!(a == 'B' || a == 'A'));
  EXPECT_EQ(smt::unsat, encoder.check(crv::tracer(), crv::dfs_prune_checker()));
}

TEST(CrvFunctionalTest, SafeCounter)
{
  constexpr unsigned N = 4;

  crv::tracer().reset();
  crv::dfs_prune_checker().reset();

  do
  {
    crv::Internal<int> n;
    crv::dfs_prune_checker().add_assertion(0 <= n && n < N);

    crv::Internal<int> x = n, y = 0;

    while (crv::dfs_prune_checker().branch(x > 0)) {
      x = x - 1;
      y = y + 1;
    }

    crv::dfs_prune_checker().add_error(0 <= y && y != n);
    EXPECT_EQ(smt::unsat, crv::dfs_prune_checker().check(crv::tracer()));
  }
  while (crv::dfs_prune_checker().find_next_path());
}

TEST(CrvFunctionalTest, UnsafeCounter)
{
  constexpr unsigned N = 4;

  crv::tracer().reset();
  crv::dfs_prune_checker().reset();

  bool error = false;
  do
  {
    crv::Internal<int> n;
    crv::dfs_prune_checker().add_assertion(0 <= n && n < N);

    crv::Internal<int> x = n, y = 0;

    while (crv::dfs_prune_checker().branch(x > 0)) {
      x = x - 1;
      y = y + 1;
    }

    crv::dfs_prune_checker().add_error(0 <= y && y == n);
    error |= smt::sat == crv::dfs_prune_checker().check(crv::tracer());
  }
  while (crv::dfs_prune_checker().find_next_path());
  EXPECT_TRUE(error);
}

// These macros and the algorithms that use them are taken from
// "Algorithms in C, Third Edition, Parts 1-4" by Robert Sedgewick.
//
// For the full and correct code, see
//   https://www.cs.princeton.edu/~rs/Algs3.c1-4/code.txt

typedef int Key;
typedef int Item;
#define key(A) (A)
#define less(A, B) (key(A) < key(B))
#define eq(A, B) (!less(A, B) && !less(B, A))
#define exch(A, B) { crv::Internal<Item> t = A; A = B; B = t; }
#define compexch(A, B) if (crv::dfs_prune_checker().branch(less(B, A))) exch(A, B)
#define NULLitem 0

void safe_insertion_sort(
  crv::Internal<Item[]>& a,
  crv::Internal<size_t> l,
  crv::Internal<size_t> r)
{
  crv::Internal<size_t> i = 0;
  for (i = l+1; crv::dfs_prune_checker().branch(i <= r); i = i+1)
    compexch(a[l], a[i]);

  for (i = l+2; crv::dfs_prune_checker().branch(i <= r); i = i+1)
  {
    crv::Internal<size_t> j = i;
    crv::Internal<Item> v = a[i];
    while (crv::dfs_prune_checker().branch(0<j) &&
      crv::dfs_prune_checker().branch(less(v, a[j-1])))
    {
      a[j] = a[j-1];
      j = j-1;
    }
    a[j] = v;
  }
}

TEST(CrvFunctionalTest, SafeInsertionSort)
{
  constexpr unsigned N = 4;

  crv::tracer().reset();
  crv::dfs_prune_checker().reset();

  do
  {
    crv::Internal<Item[]> a;
    safe_insertion_sort(a, 0, N-1);

    for (unsigned i = 0; i < N - 1; i++)
      crv::dfs_prune_checker().add_error(!(a[i] <= a[i+1]));

    EXPECT_EQ(smt::unsat, crv::dfs_prune_checker().check(crv::tracer()));
  }
  while (crv::dfs_prune_checker().find_next_path());
}

void unsafe_insertion_sort(
  crv::Internal<Item[]>& a,
  crv::Internal<size_t> l,
  crv::Internal<size_t> r)
{
  crv::Internal<size_t> i = 0;
  for (i = l+1; crv::dfs_prune_checker().branch(i <= r); i = i+1)
    compexch(a[l], a[i]);

  for (i = l+2; crv::dfs_prune_checker().branch(i <= r); i = i+1)
  {
    crv::Internal<size_t> j = i;
    crv::Internal<Item> v = a[i];
    while (crv::dfs_prune_checker().branch(0<j) &&
      crv::dfs_prune_checker().branch(less(v, a[j-1])))
    {
      a[j] = a[j];
      //       ^ bug due to wrong index (it should be j-1)
      j = j-1;
    }
    a[j] = v;
  }
}

TEST(CrvFunctionalTest, UnsafeInsertionSort)
{
  constexpr unsigned N = 4;

  crv::tracer().reset();
  crv::dfs_prune_checker().reset();

  bool error = false;
  do
  {
    crv::Internal<Item[]> a;
    unsafe_insertion_sort(a, 0, N-1);

    for (unsigned i = 0; i < N - 1; i++)
      crv::dfs_prune_checker().add_error(!(a[i] <= a[i+1]));

    error |= smt::sat == crv::dfs_prune_checker().check(crv::tracer());
  }
  while (crv::dfs_prune_checker().find_next_path() && !error);
  EXPECT_TRUE(error);
}

void safe_merge(
  crv::Internal<Item[]>& aux,
  crv::Internal<Item[]>& a,
  crv::Internal<size_t> l,
  crv::Internal<size_t> m,
  crv::Internal<size_t> r)
{
  crv::Internal<size_t> i = 0, j = 0, k = 0;
  for (i = m+1; crv::dfs_prune_checker().branch(i > l); i = i-1)
    aux[i-1] = a[i-1];

  for (j = m; crv::dfs_prune_checker().branch(j < r); j = j+1)
    aux[r+m-j] = a[j+1];

  for (k = l; crv::dfs_prune_checker().branch(k <= r); k = k+1)
  {
    if (crv::dfs_prune_checker().branch(less(aux[i], aux[j])))
    {
      a[k] = aux[i];
      i = i+1;
    }
    else
    {
      a[k] = aux[j];
      j = j-1;
    }
  }
}

void safe_merge_sort(
  crv::Internal<Item[]>& aux,
  crv::Internal<Item[]>& a,
  crv::Internal<size_t> l,
  crv::Internal<size_t> r)
{
  crv::Internal<size_t> m = (r+l)/2;
  if (crv::dfs_prune_checker().branch(r <= l)) return;
  safe_merge_sort(aux, a, l, m);
  safe_merge_sort(aux, a, m+1, r);
  safe_merge(aux, a, l, m, r);
}

TEST(CrvFunctionalTest, SafeMergeSort)
{
  constexpr unsigned N = 4;

  crv::tracer().reset();
  crv::dfs_prune_checker().reset();

  do
  {
    crv::Internal<Item[]> a;
    crv::Internal<Item[]> aux;
    safe_merge_sort(aux, a, 0, N-1);

    for (unsigned i = 0; i < N - 1; i++)
      crv::dfs_prune_checker().add_error(!(a[i] <= a[i+1]));

    EXPECT_EQ(smt::unsat, crv::dfs_prune_checker().check(crv::tracer()));
  }
  while (crv::dfs_prune_checker().find_next_path());
}

void unsafe_merge(
  crv::Internal<Item[]>& aux,
  crv::Internal<Item[]>& a,
  crv::Internal<size_t> l,
  crv::Internal<size_t> m,
  crv::Internal<size_t> r)
{
  crv::Internal<size_t> i = 0, j = 0, k = 0;
  for (i = m+1; crv::dfs_prune_checker().branch(i > l); i = i-1)
    aux[i-1] = a[i-1];

  for (j = m; crv::dfs_prune_checker().branch(j < r); j = j+1)
    aux[r+m-j] = a[j];
    //             ^ bug due to wrong offset (it should be j+1)

  for (k = l; crv::dfs_prune_checker().branch(k <= r); k = k+1)
    if (crv::dfs_prune_checker().branch(less(aux[i], aux[j])))
    {
      a[k] = aux[i];
      i = i+1;
    }
    else
    {
      a[k] = aux[j];
      j = j-1;
    }
}

void unsafe_merge_sort(
  crv::Internal<Item[]>& aux,
  crv::Internal<Item[]>& a,
  crv::Internal<size_t> l,
  crv::Internal<size_t> r)
{
  crv::Internal<size_t> m = (r+l)/2;
  if (crv::dfs_prune_checker().branch(r <= l)) return;
  unsafe_merge_sort(aux, a, l, m);
  unsafe_merge_sort(aux, a, m+1, r);
  unsafe_merge(aux, a, l, m, r);
}

TEST(CrvFunctionalTest, UnsafeMergeSort)
{
  constexpr unsigned N = 4;

  crv::tracer().reset();
  crv::dfs_prune_checker().reset();

  bool error = false;
  do
  {
    crv::Internal<Item[]> a;
    crv::Internal<Item[]> aux;
    unsafe_merge_sort(aux, a, 0, N-1);

    for (unsigned i = 0; i < N - 1; i++)
      crv::dfs_prune_checker().add_error(!(a[i] <= a[i+1]));

    error |= smt::sat == crv::dfs_prune_checker().check(crv::tracer());
  }
  while (crv::dfs_prune_checker().find_next_path() && !error);
  EXPECT_TRUE(error);
}

struct STnode;

// Binary search tree (BST)
typedef struct STnode* bst_link;

struct STnode {
  crv::Internal<Item> item;
  bst_link l, r;
  int n;

  STnode(const crv::Internal<Item>& _item,
    bst_link _l, bst_link _r, int _n)
  : item(_item), l(_l), r(_r), n(_n) {}
};

static bst_link bst_head, bst_z;

static bst_link NEW(crv::Internal<Item> item, bst_link l, bst_link r, int n) {
  bst_link x = new STnode(item, l, r, n);
  return x;
}

void STinit() {
  bst_head = (bst_z = NEW(NULLitem, 0, 0, 0));
}

int STcount() { return bst_head->n; }

static void sortR(bst_link h, void (*visit)(crv::Internal<Item>)) {
  if (h == bst_z) return;
  sortR(h->l, visit);
  visit(h->item);
  sortR(h->r, visit);
}

void STsort(void (*visit)(crv::Internal<Item>)) {
  sortR(bst_head, visit);
}

static crv::Internal<Item[]> bst_a;
static crv::Internal<size_t> bst_a_size = 0;
void bst_sorter(crv::Internal<Item> item) {
  bst_a[bst_a_size] = item;
  bst_a_size = bst_a_size + 1;
}

static bst_link safe_bst_insertR(bst_link h, crv::Internal<Item> item) {
  crv::Internal<Key> v = key(item), t = key(h->item);
  if (h == bst_z) return NEW(item, bst_z, bst_z, 1);

  if (crv::dfs_prune_checker().branch(less(v, t)))
    h->l = safe_bst_insertR(h->l, item);
  else
    h->r = safe_bst_insertR(h->r, item);

  (h->n)++; return h;
}

void STsafe_insert(crv::Internal<Item> item) { bst_head = safe_bst_insertR(bst_head, item); }

TEST(CrvFunctionalTest, SafeBst)
{
  constexpr unsigned N = 4;

  crv::tracer().reset();
  crv::dfs_prune_checker().reset();

  do
  {
    STinit();

    for (unsigned i = 0; i < N; i++)
      STsafe_insert(crv::any<Item>());

    crv::make_any(bst_a);
    bst_a_size = 0;
    STsort(bst_sorter);

    crv::dfs_prune_checker().add_error(!(bst_a_size == N));
    for (unsigned i = 0; i < N - 1; i++)
      crv::dfs_prune_checker().add_error(!(bst_a[i] <= bst_a[i+1]));

    EXPECT_EQ(smt::unsat, crv::dfs_prune_checker().check(crv::tracer()));
  }
  while (crv::dfs_prune_checker().find_next_path());
}

static bst_link unsafe_bst_insertR(bst_link h, crv::Internal<Item> item) {
  crv::Internal<Key> v = key(item), t = key(h->item);
  if (h == bst_z) return NEW(item, bst_z, bst_z, 1);

  if (crv::dfs_prune_checker().branch(less(v, t)))
    h->l = unsafe_bst_insertR(h->r, item);
    //                           ^ bug due to wrong variable (it should be l)
  else
    h->r = unsafe_bst_insertR(h->r, item);

  (h->n)++; return h;
}

void STunsafe_insert(crv::Internal<Item> item) {
  bst_head = unsafe_bst_insertR(bst_head, item);
}

// Note that this bug is not trivial. For example,
// let N = 4 and insert the following:
//
//  STinsert(2);
//  STinsert(1);
//  STinsert(4);
//  STinsert(3);
//
// Then the array bst_a is sorted (i.e. the bug
// goes unnoticed). And there are other permutations
// for which the output is as expected, e.g. call
// STinsert with "1", "2", "4", "3" in that order.
TEST(CrvFunctionalTest, UnsafeBst)
{
  constexpr unsigned N = 4;

  crv::tracer().reset();
  crv::dfs_prune_checker().reset();

  bool error = false;
  do
  {
    STinit();

    for (unsigned i = 0; i < N; i++)
      STunsafe_insert(crv::any<Item>());

    crv::make_any(bst_a);
    bst_a_size = 0;
    STsort(bst_sorter);

    crv::dfs_prune_checker().add_error(!(bst_a_size == N));
    for (unsigned i = 0; i < N - 1; i++)
      crv::dfs_prune_checker().add_error(!(bst_a[i] <= bst_a[i+1]));

    error |= smt::sat == crv::dfs_prune_checker().check(crv::tracer());
  }
  while (crv::dfs_prune_checker().find_next_path() && !error);
  EXPECT_TRUE(error);
}

// For more explanations, see Section 2.2 (Sums and Recurrences)
// in "Concrete Mathematics", Second Edition, by Ronald L. Graham,
// Donald E. Knuth, and Oren Patashnik
crv::Internal<int> sumR(
  crv::Internal<int> a,
  crv::Internal<int> b,
  crv::Internal<int> k)
{
  crv::Internal<int> sum = a + b*k;
  if (crv::dfs_checker().branch(k > 0))
    return sum + sumR(a, b, k-1);
  else
    return sum;
}

// uses reals, so no overflow detection
TEST(CrvFunctionalTest, SafeRecurrenceSum)
{
  // N must be even
  constexpr int N = 2;

  crv::tracer().reset();
  crv::dfs_checker().reset();
  crv::Encoder encoder;

  crv::Internal<int> a;
  crv::Internal<int> b;
  crv::Internal<int> result = sumR(a, b, N);
  crv::dfs_checker().add_error(result != ((a*(N+1)) + (b*(N+1)*(N/2))));
  EXPECT_EQ(smt::unsat, encoder.check(crv::tracer(), crv::dfs_checker()));
}

TEST(CrvFunctionalTest, UnsafeRecurrenceSum)
{
  // N must be even
  constexpr unsigned N = 2;

  crv::tracer().reset();
  crv::dfs_checker().reset();
  crv::Encoder encoder;

  crv::Internal<int> a;
  crv::Internal<int> b;
  crv::Internal<int> result = sumR(a, b, N);
  crv::dfs_checker().add_error(result == ((a*(N+1)) + (b*(N+1)*(N/2))));
  EXPECT_EQ(smt::sat, encoder.check(crv::tracer(), crv::dfs_checker()));
}

void unsafe_simple_assign_1(crv::External<int>& i)
{
  i = 1;
  crv::dfs_checker().add_error(i != 1);
}

void unsafe_simple_assign_2(crv::External<int>& i)
{
  i = 2;
}

TEST(CrvFunctionalTest, UnsafeThreads)
{
  crv::tracer().reset();
  crv::dfs_checker().reset();
  crv::Encoder encoder;

  crv::External<int> i = 0;
  crv::Thread t1(unsafe_simple_assign_1, i);
  crv::Thread t2(unsafe_simple_assign_2, i);

  EXPECT_EQ(smt::sat, encoder.check(crv::tracer(), crv::dfs_checker()));
}

void safe_simple_assign_1(crv::External<int>& i)
{
  i = 1;
  crv::Internal<int> r = i;
  crv::dfs_checker().add_error(r != 0 && r != 1 && r != 2);
}

void safe_simple_assign_2(crv::External<int>& i)
{
  i = 2;
}

TEST(CrvFunctionalTest, SafeThreads)
{
  crv::tracer().reset();
  crv::dfs_checker().reset();
  crv::Encoder encoder;

  crv::External<int> i = 0;
  crv::Thread t1(safe_simple_assign_1, i);
  crv::Thread t2(safe_simple_assign_2, i);

  EXPECT_EQ(smt::unsat, encoder.check(crv::tracer(), crv::dfs_checker()));
}

#ifndef _BV_THEORY_

void fib_t0(
  const unsigned N,
  crv::External<int>& i,
  crv::External<int>& j)
{
  int k;
  for (k = 0; k < N; k++)
  {
    i = i + j;
  }
}

void fib_t1(
  const unsigned N,
  crv::External<int>& i,
  crv::External<int>& j)
{
  int k;
  for (k = 0; k < N; k++)
  {
    j = j + i;
  }
}

// Adapted from SV-COMP'13 benchmark:
//   https://svn.sosy-lab.org/software/sv-benchmarks/trunk/c/pthread/fib_bench_longer_true.c
TEST(CrvFunctionalTest, UnsatFib6)
{
  constexpr unsigned N = 6;

  crv::tracer().reset();
  crv::dfs_checker().reset();
  crv::Encoder encoder;

  crv::External<int> i = 1, j = 1;
  crv::Thread t0(fib_t0, N, i, j);
  crv::Thread t1(fib_t1, N, i, j);

  crv::dfs_checker().add_error(377 < i || 377 < j);

  t0.join();
  t1.join();

  EXPECT_TRUE(crv::dfs_checker().assertions().is_null());
  EXPECT_FALSE(crv::dfs_checker().errors().is_null());
  EXPECT_TRUE(smt::unsat == encoder.check(crv::tracer(), crv::dfs_checker()));
  EXPECT_FALSE(crv::dfs_checker().find_next_path());
}

// Adapted from SV-COMP'13 benchmark:
//  https://svn.sosy-lab.org/software/sv-benchmarks/trunk/c/pthread/fib_bench_longer_false-unreach-label.c
TEST(CrvFunctionalTest, SatFib6)
{
  constexpr unsigned N = 6;

  crv::tracer().reset();
  crv::dfs_checker().reset();
  crv::Encoder encoder;

  crv::External<int> i = 1, j = 1;
  crv::Thread t0(fib_t0, N, i, j);
  crv::Thread t1(fib_t1, N, i, j);

  crv::dfs_checker().add_error(377 <= i || 377 <= j);

  t0.join();
  t1.join();

  EXPECT_TRUE(crv::dfs_checker().assertions().is_null());
  EXPECT_FALSE(crv::dfs_checker().errors().is_null());
  EXPECT_TRUE(smt::sat == encoder.check(crv::tracer(), crv::dfs_checker()));
  EXPECT_FALSE(crv::dfs_checker().find_next_path());
}

#endif

void stateful_t0(
  crv::Mutex& mutex,
  crv::External<int>& i,
  crv::External<int>& j)
{
  mutex.lock();
  i = i + 1;
  mutex.unlock();

  mutex.lock();
  j = j + 1;
  mutex.unlock();
}

void stateful_t1(
  crv::Mutex& mutex,
  crv::External<int>& i,
  crv::External<int>& j)
{
  mutex.lock();
  i = i + 5;
  mutex.unlock();

  mutex.lock();
  j = j - 6;
  mutex.unlock();
}

// Adapted from SV-COMP'13 benchmark:
//  https://svn.sosy-lab.org/software/sv-benchmarks/trunk/c/pthread/stateful01_true.c
TEST(CrvFunctionalTest, UnsatStateful)
{
  crv::tracer().reset();
  crv::dfs_checker().reset();
  crv::Encoder encoder;

  bool error = false;
  do
  {
    crv::Mutex mutex;
    crv::External<int> i(10), j(10);

    crv::Thread t0(stateful_t0, mutex, i, j);
    crv::Thread t1(stateful_t1, mutex, i, j);

    t0.join();
    t1.join();

    crv::dfs_checker().add_error(i != 16 || j != 5);

    if (!crv::dfs_checker().errors().is_null() &&
        smt::sat == encoder.check(crv::tracer(), crv::dfs_checker()))
      error = true;
  }
  while (crv::dfs_checker().find_next_path());
  EXPECT_FALSE(error);
}

// Adapted from SV-COMP'13 benchmark:
//  https://svn.sosy-lab.org/software/sv-benchmarks/trunk/c/pthread/stateful01_false-unreach-label.c
TEST(CrvFunctionalTest, SatStateful)
{
  crv::tracer().reset();
  crv::dfs_checker().reset();
  crv::Encoder encoder;

  bool error = false;
  do
  {
    crv::Mutex mutex;
    crv::External<int> i(10), j(10);

    crv::Thread t0(stateful_t0, mutex, i, j);
    crv::Thread t1(stateful_t1, mutex, i, j);

    t0.join();
    t1.join();

    crv::dfs_checker().add_error(i == 16 && j == 5);

    if (!crv::dfs_checker().errors().is_null() &&
        smt::sat == encoder.check(crv::tracer(), crv::dfs_checker()))
      error = true;
  }
  while (crv::dfs_checker().find_next_path());
  EXPECT_TRUE(error);
}

#ifndef _BV_THEORY_

void sat_stack_t0(
  const unsigned N,
  crv::Mutex& mutex,
  crv::External<unsigned int>& top,
  crv::External<int>& flag)
{
  int i;
  for (i = 0; i < N; i++)
  {
    mutex.lock();
    top = top + 1U;
    flag = 1;
    mutex.unlock();
  }
}

void sat_stack_t1(
const unsigned N,
  crv::Mutex& mutex,
  crv::External<unsigned int>& top,
  crv::External<int>& flag)
{
  int i;
  for (i = 0; i < N; i++)
  {
    mutex.lock();
    if (crv::dfs_checker().branch(flag == 1))
    {
      crv::dfs_checker().add_error(top == 0U);
      top = top - 1U;
    }
    mutex.unlock();
  }
}

TEST(CrvFunctionalTest, SatStack)
{
  constexpr unsigned N = 5;

  crv::tracer().reset();
  crv::dfs_checker().reset();
  crv::Encoder encoder;

  bool error = false;
  do
  {
    crv::Mutex mutex;
    crv::External<unsigned int> top(0U);
    crv::External<int> flag(0);

    crv::Thread t0(sat_stack_t0, N, mutex, top, flag);
    crv::Thread t1(sat_stack_t1, N, mutex, top, flag);

    if (!crv::dfs_checker().errors().is_null() &&
        smt::sat == encoder.check(crv::tracer(), crv::dfs_checker()))
      error = true;
  }
  while (crv::dfs_checker().find_next_path());
  EXPECT_TRUE(error);
}

void unsat_stack_t0(
  const unsigned N,
  crv::Mutex& mutex,
  crv::External<unsigned int>& top)
{
  int i;
  for (i = 0; i < N; i++)
  {
    mutex.lock();
    top = top + 1U;
    mutex.unlock();
  }
}

void unsat_stack_t1(
  const unsigned N,
  crv::Mutex& mutex,
  crv::External<unsigned int>& top)
{
  int i;
  for (i = 0; i < N; i++)
  {
    mutex.lock();
    if (crv::dfs_checker().branch(0U < top))
    {
      crv::dfs_checker().add_error(top == 0U);
      top = top - 1U;
    }
    mutex.unlock();
  }
}

TEST(CrvFunctionalTest, UnsatStack)
{
  constexpr unsigned N = 5;

  crv::tracer().reset();
  crv::dfs_checker().reset();
  crv::Encoder encoder;

  bool error = false;
  do
  {
    crv::Mutex mutex;
    crv::External<unsigned int> top(0U);

    crv::Thread t0(unsat_stack_t0, N, mutex, top);
    crv::Thread t1(unsat_stack_t1, N, mutex, top);

    if (!crv::dfs_checker().errors().is_null() &&
        smt::sat == encoder.check(crv::tracer(), crv::dfs_checker()))
      error = true;
  }
  while (crv::dfs_checker().find_next_path());
  EXPECT_FALSE(error);
}

#endif

void sat_communication_f(crv::Channel<int>& s, crv::Channel<int>& t)
{
  t.send(1);
  crv::Internal<int> r(s.recv());
  s.send(r);
}

void sat_communication_g(crv::Channel<int>& s, crv::Channel<int>& t)
{
  crv::Internal<int> r(t.recv());
  s.send(r);
}

void sat_communication_h(crv::Channel<int>& s)
{
  s.recv();
}

TEST(CrvFunctionalTest, SatCommunication)
{
  crv::tracer().reset();
  crv::dfs_checker().reset();
  crv::Encoder encoder;

  crv::Channel<int> s, t;
  crv::Thread f(sat_communication_f, s, t);
  crv::Thread g(sat_communication_g, s, t);
  crv::Thread h(sat_communication_h, s);

  EXPECT_TRUE(crv::dfs_checker().errors().is_null());
  EXPECT_EQ(smt::sat, encoder.check_deadlock(crv::tracer(), crv::dfs_checker()));
}

void sat_communication_g_prime(crv::Channel<int>& s, crv::Channel<int>& t)
{
  crv::Internal<int> r(t.recv());
  s.send(r);
  s.recv();
}

TEST(CrvFunctionalTest, UnsatCommunication)
{
  crv::tracer().reset();
  crv::dfs_checker().reset();
  crv::Encoder encoder;

  crv::Channel<int> s, t;
  crv::Thread f(sat_communication_f, s, t);
  crv::Thread g_prime(sat_communication_g_prime, s, t);

  EXPECT_TRUE(crv::dfs_checker().errors().is_null());
  EXPECT_EQ(smt::unsat, encoder.check_deadlock(crv::tracer(), crv::dfs_checker()));
}

void unsat_communication_deadlock_with_guard_f(crv::Channel<int>& c)
{
  EXPECT_FALSE(crv::dfs_checker().branch(6 != c.recv()));
  c.send(7);
}

void unsat_communication_deadlock_with_guard_g(crv::Channel<int>& c)
{
  c.send(6);
  c.recv();
}

TEST(CrvFunctionalTest, UnsatCommunicationDeadlockWithGuard)
{
  crv::tracer().reset();
  crv::dfs_checker().reset();
  crv::Encoder encoder;

  crv::Channel<int> c;
  crv::Thread f(unsat_communication_deadlock_with_guard_f, c);
  crv::Thread g(unsat_communication_deadlock_with_guard_g, c);

  EXPECT_EQ(smt::unsat, encoder.check_deadlock(crv::tracer(), crv::dfs_checker()));
}

void sat_communication_deadlock_with_guard_f(crv::Channel<int>& c)
{
  EXPECT_FALSE(crv::dfs_checker().branch(6 == c.recv()));
  c.send(7);
}

void sat_communication_deadlock_with_guard_g(crv::Channel<int>& c)
{
  c.send(6);
  c.recv();
}

TEST(CrvFunctionalTest, SatCommunicationDeadlockWithGuard)
{
  crv::tracer().reset();
  crv::dfs_checker().reset();
  crv::Encoder encoder;

  crv::Channel<int> c;
  crv::Thread f(sat_communication_deadlock_with_guard_f, c);
  crv::Thread g(sat_communication_deadlock_with_guard_g, c);

  EXPECT_EQ(smt::sat, encoder.check_deadlock(crv::tracer(), crv::dfs_checker()));
}

// N is the number of philosophers

// For comparison, the equivalent CSP code of
// {Sat,Unsat}DiningPhilosophersDeadlock:
//
// N = 5
// 
// FORK_ID = {0..N-1}
// PHIL_ID = {0..N-1}
// 
// channel picksup, putsdown:FORK_ID.PHIL_ID
// 
// PHIL(i) = picksup!i!i -> picksup!((i+1)%N)!i ->
//   putsdown!((i+1)%N)!i -> putsdown!i!i -> PHIL(i)
// 
// FORK(i) = picksup!i?j -> putsdown!i!j -> FORK(i)
// 
// PHILS = ||| i:PHIL_ID@ PHIL(i)
// FORKS = ||| i:FORK_ID@ FORK(i)
// 
// SAT_SYSTEM = PHILS[|{|picksup, putsdown|}|]FORKS
// assert SAT_SYSTEM :[deadlock free [F]]
// 
// LPHIL(i) = picksup!((i+1)%N)!i -> picksup!i!i ->
//   putsdown!((i+1)%N)!i -> putsdown!i!i -> LPHIL(i)
// 
// PHILS' = ||| i:PHIL_ID @ if i==0 then LPHIL(0) else PHIL(i)
// 
// UNSAT_SYSTEM = PHILS'[|{|picksup, putsdown|}|]FORKS
// assert UNSAT_SYSTEM :[deadlock free [F]]
template<size_t N>
struct DiningTable
{
  std::array<crv::Channel<int>, N> picksup;
  std::array<crv::Channel<int>, N> putsdown;
};

// Allow fork to be used twice, so it can be picked up and put
// down by the person to the fork's right and left
template<size_t N>
void phil_fork(size_t i, DiningTable<N>& t)
{
  t.picksup.at(i).recv();
  t.putsdown.at(i).recv();
  t.picksup.at(i).recv();
  t.putsdown.at(i).recv();
}

// Picks up left and then right fork;
// finally, puts down both forks
template<size_t N>
void phil_person(size_t i, DiningTable<N>& t)
{
  t.picksup.at(i).send(i);
  t.picksup.at((i + 1) % N).send(i);
  t.putsdown.at(i).send(i);
  t.putsdown.at((i + 1) % N).send(i);
}

// Picks up right fork then left fork;
// finally, puts down both forks
template<size_t N>
void phil_different_person(size_t i, DiningTable<N>& t)
{
  t.picksup.at((i + 1) % N).send(i);
  t.picksup.at(i).send(i);
  t.putsdown.at(i).send(i);
  t.putsdown.at((i + 1) % N).send(i);
}

TEST(CrvFunctionalTest, UnsatDiningPhilosophersDeadlock)
{
  crv::tracer().reset();
  crv::dfs_checker().reset();
  crv::Encoder encoder;

  constexpr size_t N = 5;
  DiningTable<N> t;

  for (int i = 0; i < N; i++)
  {
    crv::Thread fork(phil_fork<N>, i, t);

    if (i == 0)
      crv::Thread person(phil_different_person<N>, i, t);
    else
      crv::Thread person(phil_person<N>, i, t);
  }

  EXPECT_EQ(smt::unsat, encoder.check_deadlock(crv::tracer(), crv::dfs_checker()));
}

TEST(CrvFunctionalTest, SatDiningPhilosophersDeadlock)
{
  crv::tracer().reset();
  crv::dfs_checker().reset();
  crv::Encoder encoder;

  constexpr size_t N = 2;
  DiningTable<N> t;

  for (int i = 0; i < N; i++)
  {
    crv::Thread fork(phil_fork<N>, i, t);
    crv::Thread person(phil_person<N>, i, t);
  }

  EXPECT_EQ(smt::sat, encoder.check_deadlock(crv::tracer(), crv::dfs_checker()));
}

void barrier_test_f(crv::External<int>& i)
{
  i = 1;
  i = 2;
  crv::tracer().barrier();
}

void barrier_test_g(const crv::External<int>& i)
{
  crv::tracer().barrier();
  crv::dfs_checker().add_error(i == 1);
}

void barrier_test_h(const crv::External<int>& i)
{
  crv::dfs_checker().add_error(i == 2);
}

TEST(CrvFunctionalTest, UnsatBarrier)
{
  crv::tracer().reset();
  crv::dfs_checker().reset();
  crv::Encoder encoder;

  crv::External<int> i(0);
  crv::Thread f(barrier_test_f, i);
  crv::Thread g(barrier_test_g, i);

  EXPECT_EQ(smt::unsat, encoder.check(crv::tracer(), crv::dfs_checker()));

  crv::tracer().barrier();
  EXPECT_EQ(smt::unsat, encoder.check(i == 0, crv::tracer(), crv::dfs_checker()));
  EXPECT_EQ(smt::unsat, encoder.check(i == 1, crv::tracer(), crv::dfs_checker()));
  EXPECT_EQ(smt::sat, encoder.check(i == 2, crv::tracer(), crv::dfs_checker()));
}

TEST(CrvFunctionalTest, SatBarrier)
{
  crv::tracer().reset();
  crv::dfs_checker().reset();
  crv::Encoder encoder;

  crv::External<int> i(0);
  crv::Thread f(barrier_test_f, i);
  crv::Thread h(barrier_test_h, i);

  EXPECT_EQ(smt::sat, encoder.check(crv::tracer(), crv::dfs_checker()));

  // no barrier in main thread
  EXPECT_EQ(smt::sat, encoder.check(i == 0, crv::tracer(), crv::dfs_checker()));
  EXPECT_EQ(smt::sat, encoder.check(i == 1, crv::tracer(), crv::dfs_checker()));
  EXPECT_EQ(smt::sat, encoder.check(i == 2, crv::tracer(), crv::dfs_checker()));
}

TEST(CrvFunctionalTest, MpiDeadlockFree)
{
  crv::tracer().reset();
  crv::dfs_checker().reset();
  crv::Encoder encoder;

  const char some_data = 'A';

  // 2
  crv::tracer().append_thread_begin_event();
  crv::Message::send(3, some_data);
  crv::tracer().append_thread_end_event();

  // 3
  crv::tracer().append_thread_begin_event();
  crv::Message::recv_any<char>();
  crv::tracer().append_thread_end_event();

  EXPECT_EQ(smt::unsat, encoder.check_deadlock(crv::tracer(), crv::dfs_checker()));
}

// See dtg.c benchmark for MOPPER, http://www.cprover.org/mpi/
TEST(CrvFunctionalTest, DtgMpiDeadlock)
{
  crv::tracer().reset();
  crv::dfs_checker().reset();
  crv::Encoder encoder;

  const char some_data = 'A';

  // 2
  crv::tracer().append_thread_begin_event();
  crv::Message::recv_any<char>();
  crv::Message::send(5, some_data);
  crv::Message::recv_any<char>();
  crv::tracer().append_thread_end_event();

  // 3
  crv::tracer().append_thread_begin_event();
  crv::Message::send(2, some_data);
  crv::Message::send(5, some_data);
  crv::tracer().append_thread_end_event();

  // 4
  crv::tracer().append_thread_begin_event();
  crv::Message::recv_any<char>();
  crv::Message::send(2, some_data);
  crv::tracer().append_thread_end_event();

  // 5
  crv::tracer().append_thread_begin_event();
  crv::Message::recv<char>(3);
  crv::Message::recv<char>(2);
  crv::tracer().append_thread_end_event();

  // 6
  crv::tracer().append_thread_begin_event();
  crv::Message::send(4, some_data);
  crv::tracer().append_thread_end_event();

  EXPECT_EQ(smt::sat, encoder.check_deadlock(crv::tracer(), crv::dfs_checker()));
}

