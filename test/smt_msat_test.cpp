#include "gtest/gtest.h"

#include "smt.h"
#include "smt_msat.h"

#include <cstdint>

using namespace smt;

TEST(SmtMsatTest, PositiveBvLiteral)
{
  MsatSolver s;

  constexpr size_t long_bv_size = sizeof(long) * 8;
  const ExprPtr<long> e0 = literal<long>(42);

  EXPECT_EQ(OK, e0->encode(s));

  const msat_env env = s.env();
  const msat_term t0 = s.term();

  EXPECT_TRUE(msat_term_is_number(env, t0));

  size_t bv_size;
  const msat_type type = msat_term_get_type(t0);
  EXPECT_TRUE(msat_is_bv_type(env, type, &bv_size));
  EXPECT_EQ(long_bv_size, bv_size);

  msat_term vc, t1, t2;

  EXPECT_EQ(0, msat_push_backtrack_point(env));
  {
    t1 = msat_make_bv_number(env, "42", long_bv_size, 10);
    vc = msat_make_equal(env, t0, t1);

    EXPECT_FALSE(MSAT_ERROR_TERM(t1));
    EXPECT_FALSE(MSAT_ERROR_TERM(vc));

    EXPECT_EQ(0, msat_assert_formula(env, vc));
    EXPECT_EQ(MSAT_SAT, msat_solve(env));
  }
  EXPECT_EQ(0, msat_pop_backtrack_point(env));

  EXPECT_EQ(0, msat_push_backtrack_point(env));
  {
    vc = msat_make_not(env, vc);
    EXPECT_FALSE(MSAT_ERROR_TERM(vc));

    EXPECT_EQ(0, msat_assert_formula(env, vc));
    EXPECT_EQ(MSAT_UNSAT, msat_solve(env));
  }
  EXPECT_EQ(0, msat_pop_backtrack_point(env));

  EXPECT_EQ(0, msat_push_backtrack_point(env));
  {
    t2 = msat_make_bv_number(env, "43", long_bv_size, 10);
    vc = msat_make_equal(env, t0, t2);
    EXPECT_FALSE(MSAT_ERROR_TERM(t2));
    EXPECT_FALSE(MSAT_ERROR_TERM(vc));

    EXPECT_EQ(0, msat_assert_formula(env, vc));
    EXPECT_EQ(MSAT_UNSAT, msat_solve(env));
  }
  EXPECT_EQ(0, msat_pop_backtrack_point(env));
}

TEST(SmtMsatTest, NegativeBvLiteral)
{
  MsatSolver s;

  constexpr size_t long_bv_size = sizeof(long) * 8;
  const ExprPtr<long> e0 = literal<long>(-42);

  EXPECT_EQ(OK, e0->encode(s));

  const msat_env env = s.env();
  const msat_term t0 = s.term();
  EXPECT_FALSE(MSAT_ERROR_TERM(t0));

  EXPECT_TRUE(msat_term_is_number(env, t0));

  size_t bv_size;
  const msat_type type = msat_term_get_type(t0);
  EXPECT_TRUE(msat_is_bv_type(env, type, &bv_size));
  EXPECT_EQ(long_bv_size, bv_size);

  msat_term vc, t1, t2;

  EXPECT_EQ(0, msat_push_backtrack_point(env));
  {
    t1 = msat_make_bv_number(env, "42", long_bv_size, 10);
    vc = msat_make_equal(env, t0, t1);

    EXPECT_FALSE(MSAT_ERROR_TERM(t1));
    EXPECT_FALSE(MSAT_ERROR_TERM(vc));

    EXPECT_EQ(0, msat_assert_formula(env, vc));
    EXPECT_EQ(MSAT_UNSAT, msat_solve(env));
  }
  EXPECT_EQ(0, msat_pop_backtrack_point(env));

  EXPECT_EQ(0, msat_push_backtrack_point(env));
  {
    vc = msat_make_not(env, vc);
    EXPECT_FALSE(MSAT_ERROR_TERM(vc));

    EXPECT_EQ(0, msat_assert_formula(env, vc));
    EXPECT_EQ(MSAT_SAT, msat_solve(env));
  }
  EXPECT_EQ(0, msat_pop_backtrack_point(env));

  EXPECT_EQ(0, msat_push_backtrack_point(env));
  {
    t2 = msat_make_bv_neg(env, t1);
    vc = msat_make_equal(env, t0, t2);
    EXPECT_FALSE(MSAT_ERROR_TERM(t2));
    EXPECT_FALSE(MSAT_ERROR_TERM(vc));

    EXPECT_EQ(0, msat_assert_formula(env, vc));
    EXPECT_EQ(MSAT_SAT, msat_solve(env));
  }
  EXPECT_EQ(0, msat_pop_backtrack_point(env));

  EXPECT_EQ(0, msat_push_backtrack_point(env));
  {
    vc = msat_make_not(env, vc);
    EXPECT_FALSE(MSAT_ERROR_TERM(vc));

    EXPECT_EQ(0, msat_assert_formula(env, vc));
    EXPECT_EQ(MSAT_UNSAT, msat_solve(env));
  }
  EXPECT_EQ(0, msat_pop_backtrack_point(env));

  EXPECT_EQ(0, msat_push_backtrack_point(env));
  {
    const msat_term eq_term = msat_make_bv_plus(env, t0, t1);
    const msat_term zero_term = msat_make_bv_number(env, "0", long_bv_size, 10);
    vc = msat_make_equal(env, eq_term, zero_term);
    EXPECT_FALSE(MSAT_ERROR_TERM(vc));

    EXPECT_EQ(0, msat_assert_formula(env, vc));
    EXPECT_EQ(MSAT_SAT, msat_solve(env));
  }
  EXPECT_EQ(0, msat_pop_backtrack_point(env));

  EXPECT_EQ(0, msat_push_backtrack_point(env));
  {
    vc = msat_make_not(env, vc);
    EXPECT_EQ(0, msat_assert_formula(env, vc));
    EXPECT_EQ(MSAT_UNSAT, msat_solve(env));
  }
  EXPECT_EQ(0, msat_pop_backtrack_point(env));
}

TEST(SmtMsatTest, PositiveIntLiteral)
{
  MsatSolver s;

  const ExprPtr<sort::Int> e0 = literal<sort::Int>(42L);

  EXPECT_EQ(OK, e0->encode(s));

  const msat_env env = s.env();
  const msat_term t0 = s.term();
  EXPECT_FALSE(MSAT_ERROR_TERM(t0));

  EXPECT_TRUE(msat_term_is_number(env, t0));

  const msat_type type = msat_term_get_type(t0);
  EXPECT_TRUE(msat_is_integer_type(env, type));

  char *str = msat_term_repr(t0);
  EXPECT_EQ("42", std::string(str));
}

TEST(SmtMsatTest, NegativeIntLiteral)
{
  MsatSolver s;

  const ExprPtr<sort::Int> e0 = literal<sort::Int>(-42L);

  EXPECT_EQ(OK, e0->encode(s));

  const msat_env env = s.env();
  const msat_term t0 = s.term();
  EXPECT_FALSE(MSAT_ERROR_TERM(t0));

  EXPECT_TRUE(msat_term_is_number(env, t0));

  const msat_type type = msat_term_get_type(t0);
  EXPECT_TRUE(msat_is_integer_type(env, type));

  char *str = msat_term_repr(t0);
  EXPECT_EQ("-42", std::string(str));
}

TEST(SmtMsatTest, BoolFalseLiteral)
{
  MsatSolver s;

  const ExprPtr<sort::Bool> e0 = literal<sort::Bool>(false);

  EXPECT_EQ(OK, e0->encode(s));

  const msat_env env = s.env();
  const msat_term t0 = s.term();
  EXPECT_FALSE(MSAT_ERROR_TERM(t0));

  EXPECT_TRUE(msat_term_is_false(env, t0));

  const msat_type type = msat_term_get_type(t0);
  EXPECT_TRUE(msat_is_bool_type(env, type));

  char *str = msat_term_repr(t0);
  EXPECT_EQ("`false`", std::string(str));
}

TEST(SmtMsatTest, BoolTrueLiteral)
{
  MsatSolver s;

  const ExprPtr<sort::Bool> e0 = literal<sort::Bool>(true);

  EXPECT_EQ(OK, e0->encode(s));

  const msat_env env = s.env();
  const msat_term t0 = s.term();
  EXPECT_FALSE(MSAT_ERROR_TERM(t0));

  EXPECT_TRUE(msat_term_is_true(env, t0));

  const msat_type type = msat_term_get_type(t0);
  EXPECT_TRUE(msat_is_bool_type(env, type));

  char *str = msat_term_repr(t0);
  EXPECT_EQ("`true`", std::string(str));
}

TEST(SmtMsatTest, BvDeclExpr)
{
  MsatSolver s;

  const ExprPtr<long> e0 = any<long>("x");

  EXPECT_EQ(OK, e0->encode(s));

  const msat_env env = s.env();
  const msat_term t0 = s.term();
  EXPECT_TRUE(msat_term_is_constant(env, t0));

  const msat_type type = msat_term_get_type(t0);
  size_t bv_size;
  EXPECT_TRUE(msat_is_bv_type(env, type, &bv_size));
  EXPECT_EQ(sizeof(long) * 8, bv_size);

  EXPECT_EQ(sat, s.check());
  s.push();
  {
    s.add(42 == e0);
    EXPECT_EQ(sat, s.check());
  }
  s.pop();

  s.push();
  {
    s.add(42 != e0);
    EXPECT_EQ(sat, s.check());
  }
  s.pop();

  msat_type bv_long_type;
  msat_decl x_decl;
  msat_term x_term, eq_term, neq_term;
  s.push();
  {
    bv_long_type = msat_get_bv_type(env, sizeof(long) * 8);
    EXPECT_FALSE(MSAT_ERROR_TYPE(bv_long_type));
    x_decl = msat_declare_function(env, "x", bv_long_type);
    EXPECT_FALSE(MSAT_ERROR_DECL(x_decl));
    x_term = msat_make_constant(env, x_decl);
    EXPECT_FALSE(MSAT_ERROR_TERM(x_term));
    eq_term = msat_make_equal(env, x_term, t0);
    EXPECT_FALSE(MSAT_ERROR_TERM(eq_term));
    EXPECT_EQ(0, msat_assert_formula(env, eq_term));
    EXPECT_EQ(sat, s.check());
  }
  s.pop();

  s.push();
  {
    neq_term = msat_make_not(env, eq_term);
    EXPECT_FALSE(MSAT_ERROR_TERM(neq_term));
    EXPECT_EQ(0, msat_assert_formula(env, neq_term));
    EXPECT_EQ(unsat, s.check());
  }
  s.pop();

  s.push();
  {
    bv_long_type = msat_get_bv_type(env, sizeof(long) * 8);
    EXPECT_FALSE(MSAT_ERROR_TYPE(bv_long_type));
    x_decl = msat_declare_function(env, "x", bv_long_type);
    EXPECT_FALSE(MSAT_ERROR_DECL(x_decl));
    x_term = msat_make_constant(env, x_decl);
    EXPECT_FALSE(MSAT_ERROR_TERM(x_term));
    eq_term = msat_make_equal(env, x_term, t0);
    EXPECT_FALSE(MSAT_ERROR_TERM(eq_term));
    neq_term = msat_make_not(env, eq_term);
    EXPECT_FALSE(MSAT_ERROR_TERM(neq_term));
    EXPECT_EQ(0, msat_assert_formula(env, neq_term));
    EXPECT_EQ(unsat, s.check());
  }
  s.pop();
}

TEST(SmtMsatTest, IntDeclExpr)
{
  MsatSolver s;

  const ExprPtr<sort::Int> e0 = any<sort::Int>("x");

  EXPECT_EQ(OK, e0->encode(s));

  const msat_env env = s.env();
  const msat_term t0 = s.term();
  EXPECT_TRUE(msat_term_is_constant(env, t0));

  const msat_type type = msat_term_get_type(t0);
  EXPECT_TRUE(msat_is_integer_type(env, type));

  EXPECT_EQ(sat, s.check());
  s.push();
  {
    s.add(42 == e0);
    EXPECT_EQ(sat, s.check());
  }
  s.pop();

  s.push();
  {
    s.add(42 != e0);
    EXPECT_EQ(sat, s.check());
  }
  s.pop();

  msat_type int_type;
  msat_decl x_decl;
  msat_term x_term, eq_term, neq_term;
  s.push();
  {
    int_type = msat_get_integer_type(env);
    EXPECT_FALSE(MSAT_ERROR_TYPE(int_type));
    x_decl = msat_declare_function(env, "x", int_type);
    EXPECT_FALSE(MSAT_ERROR_DECL(x_decl));
    x_term = msat_make_constant(env, x_decl);
    EXPECT_FALSE(MSAT_ERROR_TERM(x_term));
    eq_term = msat_make_equal(env, x_term, t0);
    EXPECT_FALSE(MSAT_ERROR_TERM(eq_term));
    EXPECT_EQ(0, msat_assert_formula(env, eq_term));
    EXPECT_EQ(sat, s.check());
  }
  s.pop();

  s.push();
  {
    neq_term = msat_make_not(env, eq_term);
    EXPECT_FALSE(MSAT_ERROR_TERM(neq_term));
    EXPECT_EQ(0, msat_assert_formula(env, neq_term));
    EXPECT_EQ(unsat, s.check());
  }
  s.pop();

  s.push();
  {
    int_type = msat_get_integer_type(env);
    EXPECT_FALSE(MSAT_ERROR_TYPE(int_type));
    x_decl = msat_declare_function(env, "x", int_type);
    EXPECT_FALSE(MSAT_ERROR_DECL(x_decl));
    x_term = msat_make_constant(env, x_decl);
    EXPECT_FALSE(MSAT_ERROR_TERM(x_term));
    eq_term = msat_make_equal(env, x_term, t0);
    EXPECT_FALSE(MSAT_ERROR_TERM(eq_term));
    neq_term = msat_make_not(env, eq_term);
    EXPECT_FALSE(MSAT_ERROR_TERM(neq_term));
    EXPECT_EQ(0, msat_assert_formula(env, neq_term));
    EXPECT_EQ(unsat, s.check());
  }
  s.pop();
}

// Note that we have seen (Array Int Bool) to cause MathSAT5 to crash
TEST(SmtMsatTest, ArrayDecl)
{
  MsatSolver s;

  const ExprPtr<sort::Array<size_t, int>> e0 =
    any<sort::Array<size_t, int>>("array");

  EXPECT_EQ(OK, e0->encode(s));

  const msat_env env = s.env();
  const msat_term t0 = s.term();

  const msat_type type = msat_term_get_type(t0);
  msat_type domain_type, range_type;
  EXPECT_TRUE(msat_is_array_type(env, type, &domain_type, &range_type));

  size_t domain_bv_size;
  EXPECT_TRUE(msat_is_bv_type(env, domain_type, &domain_bv_size));
  EXPECT_EQ(sizeof(size_t) * 8, domain_bv_size);

  size_t range_bv_size;
  EXPECT_TRUE(msat_is_bv_type(env, range_type, &range_bv_size));
  EXPECT_EQ(sizeof(int) * 8, range_bv_size);
}

TEST(SmtMsatTest, UnaryFuncAppExpr)
{
  MsatSolver s;

  Decl<sort::Func<sort::Int, sort::Bool>> func_decl("f");
  const ExprPtr<sort::Int> e0 = any<sort::Int>("x");
  const ExprPtr<sort::Bool> e1 = apply(func_decl, e0);

  EXPECT_EQ(OK, e1->encode(s));

  const msat_env env = s.env();
  const msat_term t0 = s.term();
  EXPECT_TRUE(msat_term_is_uf(env, t0));

  const msat_type type = msat_term_get_type(t0);
  EXPECT_TRUE(msat_is_bool_type(env, type));

  char *str = msat_term_repr(t0);
  EXPECT_EQ("(f x)", std::string(str));
}

TEST(SmtMsatTest, BinaryFuncAppExpr)
{
  MsatSolver s;

  Decl<sort::Func<sort::Int, long, sort::Bool>> func_decl("f");
  const ExprPtr<sort::Int> e0 = any<sort::Int>("x");
  const ExprPtr<long> e1 = any<long>("y");
  const ExprPtr<sort::Bool> e2 = apply(func_decl, e0, e1);

  EXPECT_EQ(OK, e2->encode(s));

  const msat_env env = s.env();
  const msat_term t0 = s.term();
  EXPECT_TRUE(msat_term_is_uf(env, t0));

  const msat_type type = msat_term_get_type(t0);
  EXPECT_TRUE(msat_is_bool_type(env, type));

  char *str = msat_term_repr(t0);
  EXPECT_EQ("(f x y)", std::string(str));
}

TEST(SmtMsatTest, ArraySelectExpr)
{
  MsatSolver s;

  const ExprPtr<sort::Array<uint64_t, sort::Int>> e0 =
    any<sort::Array<uint64_t, sort::Int>>("array");
  const ExprPtr<uint64_t> e1 = any<uint64_t>("x");
  const ExprPtr<sort::Int> e2 = select(e0, e1);

  EXPECT_EQ(OK, e2->encode(s));

  const msat_env env = s.env();
  const msat_term t0 = s.term();
  EXPECT_TRUE(msat_term_is_array_read(env, t0));

  const msat_type type = msat_term_get_type(t0);
  EXPECT_TRUE(msat_is_integer_type(env, type));

  char *str = msat_term_repr(t0);
  EXPECT_EQ("(`read_<BitVec, 64, >_int` array x)", std::string(str));
}

TEST(SmtMsatTest, ArrayStoreExpr)
{
  MsatSolver s;

  const ExprPtr<sort::Array<uint64_t, sort::Int>> e0 =
    any<sort::Array<uint64_t, sort::Int>>("array");
  const ExprPtr<uint64_t> e1 = any<uint64_t>("x");
  const ExprPtr<sort::Int> e2 = any<sort::Int>("y");
  const ExprPtr<sort::Array<uint64_t, sort::Int>> e3 = store(e0, e1, e2);

  EXPECT_EQ(OK, e3->encode(s));

  const msat_env env = s.env();
  const msat_term t0 = s.term();

  const msat_type type = msat_term_get_type(t0);
  msat_type domain_type, range_type;
  EXPECT_TRUE(msat_is_array_type(env, type, &domain_type, &range_type));

  size_t domain_bv_size;
  EXPECT_TRUE(msat_is_bv_type(env, domain_type, &domain_bv_size));
  EXPECT_EQ(64, domain_bv_size);

  EXPECT_TRUE(msat_is_integer_type(env, range_type));

  char *str = msat_term_repr(t0);
  EXPECT_EQ("(`write_<BitVec, 64, >_int` array x y)", std::string(str));
}

TEST(SmtMsatTest, BvSignedOperatorNOT)
{
  MsatSolver s;

   constexpr size_t long_bv_size = sizeof(int64_t) * 8;
  const ExprPtr<int64_t> e0 = any<int64_t>("x");
  const ExprPtr<int64_t> e1(~e0);

  EXPECT_EQ(OK, e1->encode(s));

  const msat_env env = s.env();
  const msat_term t0 = s.term();
  EXPECT_TRUE(msat_term_is_bv_not(env, t0));

  const msat_type type = msat_term_get_type(t0);
  size_t bv_size;
  EXPECT_TRUE(msat_is_bv_type(env, type, &bv_size));
  EXPECT_EQ(long_bv_size, bv_size);

  char *str = msat_term_repr(t0);
  EXPECT_EQ("(`bvnot_64` x)", std::string(str));
}

TEST(SmtMsatTest, BvUnsignedOperatorNOT)
{
  MsatSolver s;

   constexpr size_t long_bv_size = sizeof(uint64_t) * 8;
  const ExprPtr<uint64_t> e0 = any<uint64_t>("x");
  const ExprPtr<uint64_t> e1(~e0);

  EXPECT_EQ(OK, e1->encode(s));

  const msat_env env = s.env();
  const msat_term t0 = s.term();
  EXPECT_TRUE(msat_term_is_bv_not(env, t0));

  const msat_type type = msat_term_get_type(t0);
  size_t bv_size;
  EXPECT_TRUE(msat_is_bv_type(env, type, &bv_size));
  EXPECT_EQ(long_bv_size, bv_size);

  char *str = msat_term_repr(t0);
  EXPECT_EQ("(`bvnot_64` x)", std::string(str));
}

#define SMT_MSAT_TEST_BV_BINARY_OP(op, opcode, opname, sign, literal)   \
  {                                                                     \
    MsatSolver s;                                                       \
                                                                        \
    constexpr size_t long_bv_size = sizeof(sign long) * 8;              \
    const ExprPtr<sign long> e0 = any<sign long>("x");                  \
    const ExprPtr<sign long> e1(literal op e0);                         \
                                                                        \
    EXPECT_EQ(OK, e1->encode(s));                                       \
                                                                        \
    const msat_env env = s.env();                                       \
    const msat_term t0 = s.term();                                      \
    EXPECT_TRUE(msat_term_is_bv_##opname(env, t0));                     \
                                                                        \
    size_t bv_size;                                                     \
    const msat_type type = msat_term_get_type(t0);                      \
    EXPECT_TRUE(msat_is_bv_type(env, type, &bv_size));                  \
    EXPECT_EQ(long_bv_size, bv_size);                                   \
  }                                                                     \

#define SMT_MSAT_TEST_BV_SIGNED_BINARY_OP(op, opcode, opname)           \
  TEST(SmtMsatTest, BvSignedBinaryOperator##opcode)                     \
  SMT_MSAT_TEST_BV_BINARY_OP(op, opcode, opname, signed, 42L)           \

#define SMT_MSAT_TEST_BV_UNSIGNED_BINARY_OP(op, opcode, opname)         \
  TEST(SmtMsatTest, BvUnsignedBinaryOperator##opcode)                   \
  SMT_MSAT_TEST_BV_BINARY_OP(op, opcode, opname, unsigned, 42UL)        \

TEST(SmtMsatTest, BvSignedOperatorSUB)
{
  MsatSolver s;

  constexpr size_t long_bv_size = sizeof(int64_t) * 8;
  const ExprPtr<int64_t> e0 = any<int64_t>("x");
  const ExprPtr<int64_t> e1(42L - e0);

  EXPECT_EQ(OK, e1->encode(s));

  const msat_env env = s.env();
  const msat_term t0 = s.term();

  size_t bv_size;
  const msat_type type = msat_term_get_type(t0);
  EXPECT_TRUE(msat_is_bv_type(env, type, &bv_size));
  EXPECT_EQ(long_bv_size, bv_size);

  char *str = msat_term_repr(t0);
  EXPECT_EQ("(`bvadd_64` 42_64 (`bvneg_64` x))", std::string(str));
}

SMT_MSAT_TEST_BV_SIGNED_BINARY_OP(&, AND, and)
SMT_MSAT_TEST_BV_SIGNED_BINARY_OP(|, OR, or)
SMT_MSAT_TEST_BV_SIGNED_BINARY_OP(^, XOR, xor)
SMT_MSAT_TEST_BV_SIGNED_BINARY_OP(+, ADD, plus)
SMT_MSAT_TEST_BV_SIGNED_BINARY_OP(*, MUL, times)
SMT_MSAT_TEST_BV_SIGNED_BINARY_OP(/, QUO, sdiv)
SMT_MSAT_TEST_BV_SIGNED_BINARY_OP(%, REM, srem)

TEST(SmtMsatTest, BvUnsignedOperatorSUB)
{
  MsatSolver s;

  constexpr size_t long_bv_size = sizeof(uint64_t) * 8;
  const ExprPtr<uint64_t> e0 = any<uint64_t>("x");
  const ExprPtr<uint64_t> e1(42L - e0);

  EXPECT_EQ(OK, e1->encode(s));

  const msat_env env = s.env();
  const msat_term t0 = s.term();

  size_t bv_size;
  const msat_type type = msat_term_get_type(t0);
  EXPECT_TRUE(msat_is_bv_type(env, type, &bv_size));
  EXPECT_EQ(long_bv_size, bv_size);

  char *str = msat_term_repr(t0);
  EXPECT_EQ("(`bvadd_64` 42_64 (`bvneg_64` x))", std::string(str));
}

SMT_MSAT_TEST_BV_UNSIGNED_BINARY_OP(&, AND, and)
SMT_MSAT_TEST_BV_UNSIGNED_BINARY_OP(|, OR, or)
SMT_MSAT_TEST_BV_UNSIGNED_BINARY_OP(^, XOR, xor)
SMT_MSAT_TEST_BV_UNSIGNED_BINARY_OP(+, ADD, plus)
SMT_MSAT_TEST_BV_UNSIGNED_BINARY_OP(*, MUL, times)
SMT_MSAT_TEST_BV_UNSIGNED_BINARY_OP(/, QUO, udiv)
SMT_MSAT_TEST_BV_UNSIGNED_BINARY_OP(%, REM, urem)

TEST(SmtMsatTest, BvSignedBinaryOperatorEQL)
{
  MsatSolver s;

  const ExprPtr<int64_t> e0 = any<int64_t>("x");
  const ExprPtr<sort::Bool> e1(42 == e0);

  EXPECT_EQ(OK, e1->encode(s));

  const msat_env env = s.env();
  const msat_term t0 = s.term();
  EXPECT_TRUE(msat_term_is_equal(env, t0));

  const msat_type type = msat_term_get_type(t0);
  EXPECT_TRUE(msat_is_bool_type(env, type));

  char *str = msat_term_repr(t0);
  EXPECT_EQ("(`=_<BitVec, 64, >` x 42_64)", std::string(str));
}

TEST(SmtMsatTest, BvSignedBinaryOperatorLSS)
{
  MsatSolver s;

  const ExprPtr<int64_t> e0 = any<int64_t>("x");
  const ExprPtr<sort::Bool> e1(42 < e0);

  EXPECT_EQ(OK, e1->encode(s));

  const msat_env env = s.env();
  const msat_term t0 = s.term();
  EXPECT_TRUE(msat_term_is_bv_slt(env, t0));

  const msat_type type = msat_term_get_type(t0);
  EXPECT_TRUE(msat_is_bool_type(env, type));

  char *str = msat_term_repr(t0);
  EXPECT_EQ("(`bvslt_64` 42_64 x)", std::string(str));
}

TEST(SmtMsatTest, BvSignedBinaryOperatorGTR)
{
  MsatSolver s;

  const ExprPtr<int64_t> e0 = any<int64_t>("x");
  const ExprPtr<sort::Bool> e1(42 > e0);

  EXPECT_EQ(OK, e1->encode(s));

  const msat_env env = s.env();
  const msat_term t0 = s.term();
  EXPECT_TRUE(msat_term_is_bv_slt(env, t0));

  const msat_type type = msat_term_get_type(t0);
  EXPECT_TRUE(msat_is_bool_type(env, type));

  char *str = msat_term_repr(t0);
  EXPECT_EQ("(`bvslt_64` x 42_64)", std::string(str));
}

TEST(SmtMsatTest, BvSignedBinaryOperatorNEQ)
{
  MsatSolver s;

  const ExprPtr<int64_t> e0 = any<int64_t>("x");
  const ExprPtr<sort::Bool> e1(42 != e0);

  EXPECT_EQ(OK, e1->encode(s));

  const msat_env env = s.env();
  const msat_term t0 = s.term();
  EXPECT_TRUE(msat_term_is_not(env, t0));

  const msat_type type = msat_term_get_type(t0);
  EXPECT_TRUE(msat_is_bool_type(env, type));

  char *str = msat_term_repr(t0);
  EXPECT_EQ("(`not` (`=_<BitVec, 64, >` x 42_64))", std::string(str));
}

TEST(SmtMsatTest, BvSignedBinaryOperatorLEQ)
{
  MsatSolver s;

  const ExprPtr<int64_t> e0 = any<int64_t>("x");
  const ExprPtr<sort::Bool> e1(42 <= e0);

  EXPECT_EQ(OK, e1->encode(s));

  const msat_env env = s.env();
  const msat_term t0 = s.term();
  EXPECT_TRUE(msat_term_is_not(env, t0));

  const msat_type type = msat_term_get_type(t0);
  EXPECT_TRUE(msat_is_bool_type(env, type));

  char *str = msat_term_repr(t0);
  EXPECT_EQ("(`not` (`bvslt_64` x 42_64))", std::string(str));
}

TEST(SmtMsatTest, BvSignedBinaryOperatorGEQ)
{
  MsatSolver s;

  const ExprPtr<int64_t> e0 = any<int64_t>("x");
  const ExprPtr<sort::Bool> e1(42 >= e0);

  EXPECT_EQ(OK, e1->encode(s));

  const msat_env env = s.env();
  const msat_term t0 = s.term();
  EXPECT_TRUE(msat_term_is_not(env, t0));

  const msat_type type = msat_term_get_type(t0);
  EXPECT_TRUE(msat_is_bool_type(env, type));

  char *str = msat_term_repr(t0);
  EXPECT_EQ("(`not` (`bvslt_64` 42_64 x))", std::string(str));
}

TEST(SmtMsatTest, BvUnsignedBinaryOperatorEQL)
{
  MsatSolver s;

  const ExprPtr<uint64_t> e0 = any<uint64_t>("x");
  const ExprPtr<sort::Bool> e1(42 == e0);

  EXPECT_EQ(OK, e1->encode(s));

  const msat_env env = s.env();
  const msat_term t0 = s.term();
  EXPECT_TRUE(msat_term_is_equal(env, t0));

  const msat_type type = msat_term_get_type(t0);
  EXPECT_TRUE(msat_is_bool_type(env, type));

  char *str = msat_term_repr(t0);
  EXPECT_EQ("(`=_<BitVec, 64, >` x 42_64)", std::string(str));
}

TEST(SmtMsatTest, BvUnsignedBinaryOperatorLSS)
{
  MsatSolver s;

  const ExprPtr<uint64_t> e0 = any<uint64_t>("x");
  const ExprPtr<sort::Bool> e1(42 < e0);

  EXPECT_EQ(OK, e1->encode(s));

  const msat_env env = s.env();
  const msat_term t0 = s.term();
  EXPECT_TRUE(msat_term_is_bv_ult(env, t0));

  const msat_type type = msat_term_get_type(t0);
  EXPECT_TRUE(msat_is_bool_type(env, type));

  char *str = msat_term_repr(t0);
  EXPECT_EQ("(`bvult_64` 42_64 x)", std::string(str));
}

TEST(SmtMsatTest, BvUnsignedBinaryOperatorGTR)
{
  MsatSolver s;

  const ExprPtr<uint64_t> e0 = any<uint64_t>("x");
  const ExprPtr<sort::Bool> e1(42 > e0);

  EXPECT_EQ(OK, e1->encode(s));

  const msat_env env = s.env();
  const msat_term t0 = s.term();
  EXPECT_TRUE(msat_term_is_bv_ult(env, t0));

  const msat_type type = msat_term_get_type(t0);
  EXPECT_TRUE(msat_is_bool_type(env, type));

  char *str = msat_term_repr(t0);
  EXPECT_EQ("(`bvult_64` x 42_64)", std::string(str));
}

TEST(SmtMsatTest, BvUnsignedBinaryOperatorNEQ)
{
  MsatSolver s;

  const ExprPtr<uint64_t> e0 = any<uint64_t>("x");
  const ExprPtr<sort::Bool> e1(42 != e0);

  EXPECT_EQ(OK, e1->encode(s));

  const msat_env env = s.env();
  const msat_term t0 = s.term();
  EXPECT_TRUE(msat_term_is_not(env, t0));

  const msat_type type = msat_term_get_type(t0);
  EXPECT_TRUE(msat_is_bool_type(env, type));

  char *str = msat_term_repr(t0);
  EXPECT_EQ("(`not` (`=_<BitVec, 64, >` x 42_64))", std::string(str));
}

TEST(SmtMsatTest, BvUnsignedBinaryOperatorLEQ)
{
  MsatSolver s;

  const ExprPtr<uint64_t> e0 = any<uint64_t>("x");
  const ExprPtr<sort::Bool> e1(42 <= e0);

  EXPECT_EQ(OK, e1->encode(s));

  const msat_env env = s.env();
  const msat_term t0 = s.term();
  EXPECT_TRUE(msat_term_is_not(env, t0));

  const msat_type type = msat_term_get_type(t0);
  EXPECT_TRUE(msat_is_bool_type(env, type));

  char *str = msat_term_repr(t0);
  EXPECT_EQ("(`not` (`bvult_64` x 42_64))", std::string(str));
}

TEST(SmtMsatTest, BvUnsignedBinaryOperatorGEQ)
{
  MsatSolver s;

  const ExprPtr<uint64_t> e0 = any<uint64_t>("x");
  const ExprPtr<sort::Bool> e1(42 >= e0);

  EXPECT_EQ(OK, e1->encode(s));

  const msat_env env = s.env();
  const msat_term t0 = s.term();
  EXPECT_TRUE(msat_term_is_not(env, t0));

  const msat_type type = msat_term_get_type(t0);
  EXPECT_TRUE(msat_is_bool_type(env, type));

  char *str = msat_term_repr(t0);
  EXPECT_EQ("(`not` (`bvult_64` 42_64 x))", std::string(str));
}

#define SMT_MSAT_TEST_MATH_BINARY_OP(op, opcode, opname)                \
  TEST(SmtMsatTest, MathBinaryOperatorq##opcode)                        \
  {                                                                     \
    MsatSolver s;                                                       \
                                                                        \
    const ExprPtr<sort::Int> e0 = any<sort::Int>("x");                  \
    const ExprPtr<sort::Int> e1(42 op e0);                              \
                                                                        \
    EXPECT_EQ(OK, e1->encode(s));                                       \
                                                                        \
    const msat_env env = s.env();                                       \
    const msat_term t0 = s.term();                                      \
    EXPECT_TRUE(msat_term_is_##opname(env, t0));                        \
                                                                        \
    const msat_type type = msat_term_get_type(t0);                      \
    EXPECT_TRUE(msat_is_integer_type(env, type));                       \
                                                                        \
    char *str = msat_term_repr(t0);                                     \
    EXPECT_EQ("(`" #op "_int` 42 x)", std::string(str));                \
  }                                                                     \

// most other integer operators are unsupported by MathSAT5
SMT_MSAT_TEST_MATH_BINARY_OP(+, ADD, plus)
SMT_MSAT_TEST_MATH_BINARY_OP(*, MUL, times)

TEST(SmtMsatTest, MathBinaryOperatorEQL)
{
  MsatSolver s;

  const ExprPtr<sort::Int> e0 = any<sort::Int>("x");
  const ExprPtr<sort::Bool> e1(42 == e0);

  EXPECT_EQ(OK, e1->encode(s));

  const msat_env env = s.env();
  const msat_term t0 = s.term();
  EXPECT_TRUE(msat_term_is_equal(env, t0));

  const msat_type type = msat_term_get_type(t0);
  EXPECT_TRUE(msat_is_bool_type(env, type));

  char *str = msat_term_repr(t0);
  EXPECT_EQ("(`=_int` x 42)", std::string(str));
}

TEST(SmtMsatTest, MathBinaryOperatorLSS)
{
  MsatSolver s;

  const ExprPtr<sort::Int> e0 = any<sort::Int>("x");
  const ExprPtr<sort::Bool> e1(42 < e0);

  EXPECT_EQ(OK, e1->encode(s));

  const msat_env env = s.env();
  const msat_term t0 = s.term();
  EXPECT_TRUE(msat_term_is_and(env, t0));

  const msat_type type = msat_term_get_type(t0);
  EXPECT_TRUE(msat_is_bool_type(env, type));

  char *str = msat_term_repr(t0);
  EXPECT_EQ("(`and` (`<=_int` 42 x) (`not` (`=_int` x 42)))", std::string(str));
}

TEST(SmtMsatTest, MathBinaryOperatorGTR)
{
  MsatSolver s;

  const ExprPtr<sort::Int> e0 = any<sort::Int>("x");
  const ExprPtr<sort::Bool> e1(42 > e0);

  EXPECT_EQ(OK, e1->encode(s));

  const msat_env env = s.env();
  const msat_term t0 = s.term();
  EXPECT_TRUE(msat_term_is_and(env, t0));

  const msat_type type = msat_term_get_type(t0);
  EXPECT_TRUE(msat_is_bool_type(env, type));

  char *str = msat_term_repr(t0);
  EXPECT_EQ("(`and` (`<=_int` x 42) (`not` (`=_int` x 42)))", std::string(str));
}

TEST(SmtMsatTest, MathBinaryOperatorNEQ)
{
  MsatSolver s;

  const ExprPtr<sort::Int> e0 = any<sort::Int>("x");
  const ExprPtr<sort::Bool> e1(42 != e0);

  EXPECT_EQ(OK, e1->encode(s));

  const msat_env env = s.env();
  const msat_term t0 = s.term();
  EXPECT_TRUE(msat_term_is_not(env, t0));

  const msat_type type = msat_term_get_type(t0);
  EXPECT_TRUE(msat_is_bool_type(env, type));

  char *str = msat_term_repr(t0);
  EXPECT_EQ("(`not` (`=_int` x 42))", std::string(str));
}

TEST(SmtMsatTest, MathBinaryOperatorLEQ)
{
  MsatSolver s;

  const ExprPtr<sort::Int> e0 = any<sort::Int>("x");
  const ExprPtr<sort::Bool> e1(42 <= e0);

  EXPECT_EQ(OK, e1->encode(s));

  const msat_env env = s.env();
  const msat_term t0 = s.term();
  EXPECT_TRUE(msat_term_is_leq(env, t0));

  const msat_type type = msat_term_get_type(t0);
  EXPECT_TRUE(msat_is_bool_type(env, type));

  char *str = msat_term_repr(t0);
  EXPECT_EQ("(`<=_int` 42 x)", std::string(str));
}

TEST(SmtMsatTest, MathBinaryOperatorGEQ)
{
  MsatSolver s;

  const ExprPtr<sort::Int> e0 = any<sort::Int>("x");
  const ExprPtr<sort::Bool> e1(42 >= e0);

  EXPECT_EQ(OK, e1->encode(s));

  const msat_env env = s.env();
  const msat_term t0 = s.term();
  EXPECT_TRUE(msat_term_is_leq(env, t0));

  const msat_type type = msat_term_get_type(t0);
  EXPECT_TRUE(msat_is_bool_type(env, type));

  char *str = msat_term_repr(t0);
  EXPECT_EQ("(`<=_int` x 42)", std::string(str));
}

TEST(SmtMsatTest, BoolUnaryOperatorLNOT)
{
  MsatSolver s;

  const ExprPtr<sort::Bool> e0 = any<sort::Bool>("x");
  const ExprPtr<sort::Bool> e1(!e0);

  EXPECT_EQ(OK, e1->encode(s));

  const msat_env env = s.env();
  const msat_term t0 = s.term();
  EXPECT_TRUE(msat_term_is_not(env, t0));

  const msat_type type = msat_term_get_type(t0);
  EXPECT_TRUE(msat_is_bool_type(env, type));

  char *str = msat_term_repr(t0);
  EXPECT_EQ("(`not` x)", std::string(str));
}

#define SMT_MSAT_TEST_BOOL_BINARY_OP(op, opcode, opname)                \
  TEST(SmtMsatTest, BoolBinaryOperator##opcode)                         \
  {                                                                     \
    MsatSolver s;                                                       \
                                                                        \
    const ExprPtr<sort::Bool> e0 = any<sort::Bool>("x");                \
    const ExprPtr<sort::Bool> e1 = any<sort::Bool>("y");                \
    const ExprPtr<sort::Bool> e2(e0 op e1);                             \
                                                                        \
    EXPECT_EQ(OK, e2->encode(s));                                       \
                                                                        \
    const msat_env env = s.env();                                       \
    const msat_term t0 = s.term();                                      \
    EXPECT_TRUE(msat_term_is_##opname(env, t0));                        \
                                                                        \
    const msat_type type = msat_term_get_type(t0);                      \
    EXPECT_TRUE(msat_is_bool_type(env, type));                          \
                                                                        \
    char *str = msat_term_repr(t0);                                     \
    EXPECT_EQ("(`" #opname "` x y)", std::string(str));                 \
  }                                                                     \

SMT_MSAT_TEST_BOOL_BINARY_OP(&&, LAND, and)
SMT_MSAT_TEST_BOOL_BINARY_OP(||, LOR, or)
SMT_MSAT_TEST_BOOL_BINARY_OP(==, EQL, iff)

TEST(SmtMsatTest, LogicalImplication)
{
  MsatSolver s;

  const ExprPtr<sort::Bool> e0 = any<sort::Bool>("x");
  const ExprPtr<sort::Bool> e1 = any<sort::Bool>("y");
  const ExprPtr<sort::Bool> e2(implies(e0, e1));

  EXPECT_EQ(OK, e2->encode(s));

  const msat_env env = s.env();
  const msat_term t0 = s.term();
  EXPECT_TRUE(msat_term_is_or(env, t0));

  const msat_type type = msat_term_get_type(t0);
  EXPECT_TRUE(msat_is_bool_type(env, type));

  char *str = msat_term_repr(t0);
  EXPECT_EQ("(`or` y (`not` x))", std::string(str));
}

TEST(SmtMsatTest, Reset)
{
  MsatSolver s;

  EXPECT_EQ(sat, s.check());
  s.add(literal<sort::Bool>(false));
  EXPECT_EQ(unsat, s.check());
  s.reset();
  EXPECT_EQ(sat, s.check());
}

TEST(SmtMsatTest, Distinct)
{
  MsatSolver s;

  const ExprPtr<long> x = any<long>("x");
  const ExprPtr<long> y = any<long>("y");
  const ExprPtr<long> z = any<long>("z");
  const ExprPtr<long> w = any<long>("w");

  ExprPtrs<long> operand_ptrs(3);
  operand_ptrs.push_back(x);
  operand_ptrs.push_back(y);
  operand_ptrs.push_back(z);

  ExprPtr<sort::Bool> d(distinct(std::move(operand_ptrs)));

  d->encode(s);
  char *str = msat_term_repr(s.term());
  EXPECT_EQ("(`and` (`and` (`not` (`=_<BitVec, 64, >` x y))"
            " (`not` (`=_<BitVec, 64, >` x z)))"
            " (`not` (`=_<BitVec, 64, >` y z)))", std::string(str));

  s.add(d);

  EXPECT_EQ(sat, s.check());

  s.push();
  {
    s.add(x == y);
    EXPECT_EQ(unsat, s.check());
  }
  s.pop();

  s.push();
  {
    s.add(x == z);
    EXPECT_EQ(unsat, s.check());
  }
  s.pop();

  s.push();
  {
    s.add(y == z);
    EXPECT_EQ(unsat, s.check());
  }
  s.pop();

  s.push();
  {
    s.add(x == w);
    EXPECT_EQ(sat, s.check());
  }
  s.pop();

  s.push();
  {
    s.add(y == w);
    EXPECT_EQ(sat, s.check());
  }
  s.pop();

  s.push();
  {
    s.add(z == w);
    EXPECT_EQ(sat, s.check());
  }
  s.pop();
}

TEST(SmtMsatTest, UnsafeAdd)
{
  MsatSolver s;

  const Sort& bv_sort = internal::sort<int64_t>();
  const Sort& func_sort = internal::sort<sort::Func<int64_t, int64_t>>();
  const UnsafeDecl const_decl("x", bv_sort);
  const UnsafeDecl func_decl("f", func_sort);
  const UnsafeExprPtr seven_ptr(literal(bv_sort, 7));
  const UnsafeExprPtr x_ptr(constant(const_decl));
  const UnsafeExprPtr app_ptr(apply(func_decl, seven_ptr));

  UnsafeExprPtrs ptrs;
  ptrs.push_back(seven_ptr);
  ptrs.push_back(x_ptr);
  ptrs.push_back(app_ptr);

  const UnsafeExprPtr distinct_ptr(distinct(std::move(ptrs)));

  const Sort& array_sort = internal::sort<sort::Array<uint32_t, int64_t>>();
  const Sort& index_sort = internal::sort<uint32_t>();
  const UnsafeDecl array_decl("array", array_sort);
  const UnsafeDecl index_decl("index", index_sort);
  const UnsafeExprPtr array_ptr(constant(array_decl));
  const UnsafeExprPtr index_ptr(constant(index_decl));
  const UnsafeExprPtr store_ptr(store(array_ptr, index_ptr, app_ptr));
  const UnsafeExprPtr select_ptr(select(store_ptr, index_ptr));

  const UnsafeExprPtr eq_ptr(select_ptr == x_ptr);
  const UnsafeExprPtr and_ptr(eq_ptr && distinct_ptr);

  s.unsafe_add(and_ptr);
  EXPECT_EQ(unsat, s.check());

  char *str = msat_term_repr(s.term());
  EXPECT_EQ(
    "(`and` (`=_<BitVec, 64, >` "
      "(`read_<BitVec, 32, >_<BitVec, 64, >` "
        "(`write_<BitVec, 32, >_<BitVec, 64, >` array index (f 7_64)) index) x) "
    "(`and` (`and` (`not` (`=_<BitVec, 64, >` x 7_64)) "
      "(`not` (`=_<BitVec, 64, >` (f 7_64) 7_64))) "
      "(`not` (`=_<BitVec, 64, >` (f 7_64) x))))", std::string(str));
}
