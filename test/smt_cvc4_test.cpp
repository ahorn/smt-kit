#include "smt_cvc4.h"

// Include gtest/gtest.h _after_ smt_cvc4.h!
#include "gtest/gtest.h"

#include <sstream>
#include <cstdint>
#include <climits>

using namespace smt;

TEST(SmtCVC4Test, PositiveBvLiteral)
{
  CVC4Solver s;

  const Bv<int32_t> e0 = literal<Bv<int32_t>>(42);

  EXPECT_EQ(OK, static_cast<SharedExpr>(e0).encode(s));

  CVC4::Expr expr = s.expr();
  EXPECT_TRUE(expr.isConst());
  EXPECT_TRUE(expr.getType().isBitVector());

  const CVC4::BitVectorType bv_type(expr.getType());
  EXPECT_EQ(32, bv_type.getSize());

  std::stringstream out;
  out << expr;
  EXPECT_EQ("(_ bv42 32)", out.str());
}

TEST(SmtCVC4Test, NegativeBvLiteral)
{
  CVC4Solver s;

  const Bv<long> e0 = literal<Bv<long>>(-42);
  const Bv<long> e1 = literal<Bv<long>>(42);
  const Bv<long> e3 = literal<Bv<long>>(0);

  EXPECT_EQ(OK, static_cast<SharedExpr>(e0).encode(s));

  CVC4::Expr expr = s.expr();
  EXPECT_TRUE(expr.isConst());
  EXPECT_TRUE(expr.getType().isBitVector());

  const CVC4::BitVectorType bv_type(expr.getType());
  EXPECT_EQ(sizeof(long) * 8, bv_type.getSize());

  s.push();
  {
    s.add(e3 != e0 + e1);
    EXPECT_EQ(unsat, s.check());
  }
  s.pop();

  s.push();
  {
    s.add(0 != e0 + e1);
    EXPECT_EQ(unsat, s.check());
  }
  s.pop();

  s.push();
  {
    s.add(e3 == e0 + e1);
    EXPECT_EQ(sat, s.check());
  }
  s.pop();
}

TEST(SmtCVC4Test, InternalStringBvLiteral)
{
  CVC4Solver s;

  constexpr long long v = std::numeric_limits<long long>::max();
  const Bv<long long> e0 = literal<Bv<long long>>(v);

  EXPECT_EQ(OK, static_cast<SharedExpr>(e0).encode(s));

  CVC4::Expr expr = s.expr();
  EXPECT_TRUE(expr.isConst());
  EXPECT_TRUE(expr.getType().isBitVector());

  const CVC4::BitVectorType bv_type(expr.getType());
  EXPECT_EQ(sizeof(long long) * 8, bv_type.getSize());

  std::stringstream out;
  out << expr;
  EXPECT_EQ(std::string("(_ bv") + std::to_string(v) + " " +
            std::to_string(sizeof(long long) * 8)+ ")", out.str());
}

TEST(SmtCVC4Test, PositiveIntLiteral)
{
  CVC4Solver s;
  CVC4::Expr expr;
  std::stringstream out;

  const Int e0 = literal<Int>(42);

  EXPECT_EQ(OK, static_cast<SharedExpr>(e0).encode(s));

  expr = s.expr();
  EXPECT_TRUE(expr.isConst());
  EXPECT_TRUE(expr.getType().isInteger());

  out << expr;
  EXPECT_EQ("42", out.str());

  out.str(std::string());
  out.clear();

  const Int e1 = literal<Int>(42L);
  EXPECT_EQ(OK, static_cast<SharedExpr>(e1).encode(s));

  expr = s.expr();
  EXPECT_TRUE(expr.isConst());
  EXPECT_TRUE(expr.getType().isInteger());

  out << expr;
  EXPECT_EQ("42", out.str());
}

TEST(SmtCVC4Test, NegativeIntLiteral)
{
  CVC4Solver s;
  CVC4::Expr expr;
  std::stringstream out;

  const Int e0 = literal<Int>(-42);

  EXPECT_EQ(OK, static_cast<SharedExpr>(e0).encode(s));

  expr = s.expr();
  EXPECT_TRUE(expr.isConst());
  EXPECT_TRUE(expr.getType().isInteger());

  out << expr;
  EXPECT_EQ("(- 42)", out.str());

  out.str(std::string());
  out.clear();

  const Int e1 = literal<Int>(-42L);
  EXPECT_EQ(OK, static_cast<SharedExpr>(e1).encode(s));

  expr = s.expr();
  EXPECT_TRUE(expr.isConst());
  EXPECT_TRUE(expr.getType().isInteger());

  out << expr;
  EXPECT_EQ("(- 42)", out.str());
}

TEST(SmtCVC4Test, BoolTrueLiteral)
{
  CVC4Solver s;

  const Bool e0 = literal<Bool>(true);

  EXPECT_EQ(OK, static_cast<SharedExpr>(e0).encode(s));

  CVC4::Expr expr = s.expr();
  EXPECT_TRUE(expr.isConst());
  EXPECT_TRUE(expr.getType().isBoolean());

  std::stringstream out;
  out << expr;
  EXPECT_EQ("true", out.str());
}

TEST(SmtCVC4Test, BoolFalseLiteral)
{
  CVC4Solver s;

  const Bool e0 = literal<Bool>(false);

  EXPECT_EQ(OK, static_cast<SharedExpr>(e0).encode(s));

  CVC4::Expr expr = s.expr();
  EXPECT_TRUE(expr.isConst());
  EXPECT_TRUE(expr.getType().isBoolean());

  std::stringstream out;
  out << expr;
  EXPECT_EQ("false", out.str());
}

TEST(SmtCVC4Test, ArrayDecl)
{
  CVC4Solver s;

  const Array<Bv<size_t>, Bv<int>> e0 = any<Array<Bv<size_t>, Bv<int>>>("array");

  EXPECT_EQ(OK, static_cast<SharedExpr>(e0).encode(s));

  const CVC4::Expr expr(s.expr());
  EXPECT_TRUE(expr.getType().isArray());

  const CVC4::ArrayType array_type(expr.getType());
  EXPECT_TRUE(array_type.getIndexType().isBitVector());
  EXPECT_TRUE(array_type.getConstituentType().isBitVector());

  const CVC4::BitVectorType domain_type(array_type.getIndexType());
  EXPECT_EQ(sizeof(size_t) * 8, domain_type.getSize());

  const CVC4::BitVectorType range_type(array_type.getConstituentType());
  EXPECT_EQ(sizeof(int) * 8, range_type.getSize());
}

TEST(SmtCVC4Test, ConstArrayExpr)
{
  CVC4Solver s;

  const Int init_term(make_shared_expr<LiteralExpr<int>>(internal::sort<Int>(), 7));
  const ConstArrayExpr e0(internal::sort<Array<Int, Int>>(), init_term);

  EXPECT_EQ(OK, e0.encode(s));

  const CVC4::Expr const_array_expr(s.expr());
  EXPECT_TRUE(const_array_expr.getType().isArray());

  CVC4::ExprManager& expr_manager = s.expr_manager();
  CVC4::SmtEngine& smt_engine = s.smt_engine();

  const CVC4::Expr i_expr(expr_manager.mkVar("i", expr_manager.integerType()));

  smt_engine.push();
  {
    smt_engine.assertFormula(expr_manager.mkExpr(CVC4::kind::DISTINCT,
      expr_manager.mkExpr(CVC4::kind::SELECT, const_array_expr, i_expr),
      expr_manager.mkConst(CVC4::Rational(7))));
    EXPECT_EQ(CVC4::Result::Sat::UNSAT, smt_engine.checkSat().isSat());
  }
  smt_engine.pop();

  smt_engine.push();
  {
    smt_engine.assertFormula(expr_manager.mkExpr(CVC4::kind::EQUAL,
      expr_manager.mkExpr(CVC4::kind::SELECT, const_array_expr, i_expr),
      expr_manager.mkConst(CVC4::Rational(7))));
    EXPECT_EQ(CVC4::Result::Sat::SAT, smt_engine.checkSat().isSat());
  }
  smt_engine.pop();
}

TEST(SmtCVC4Test, UnaryFuncAppExpr)
{
  CVC4Solver s;

  Decl<Func<Int, Bool>> func_decl("f");
  const Int e0 = any<Int>("x");
  const Bool e1 = apply(func_decl, e0);

  EXPECT_EQ(OK, static_cast<SharedExpr>(e1).encode(s));

  std::stringstream out;
  out << s.expr();
  EXPECT_EQ("(f x)", out.str());
  EXPECT_EQ(CVC4::kind::APPLY_UF, s.expr().getKind());
  EXPECT_TRUE(s.expr().getType().isBoolean());
}

#define SMT_CVC4_TEST_BV_UNARY_OP(op, opcode, opname, kind, sign)       \
  {                                                                     \
    CVC4Solver s;                                                       \
                                                                        \
    const Bv<sign int> e0 = any<Bv<sign int>>("x");                     \
    const Bv<sign int> e1(op e0);                                       \
                                                                        \
    EXPECT_EQ(OK, static_cast<SharedExpr>(e1).encode(s));               \
                                                                        \
    const CVC4::Expr expr(s.expr());                                    \
    EXPECT_EQ(kind, expr.getKind());                                    \
    EXPECT_TRUE(expr.getType(true).isBitVector());                      \
                                                                        \
    std::stringstream out;                                              \
    out << s.expr();                                                    \
    EXPECT_EQ("(" #opname " x)", out.str());                            \
  }                                                                     \

#define SMT_CVC4_TEST_BV_SIGNED_UNARY_OP(op, opcode, opname, kind)      \
  TEST(SmtCVC4Test, BvSignedUnaryOperator##opcode)                      \
  SMT_CVC4_TEST_BV_UNARY_OP(op, opcode, opname, kind, signed)           \

#define SMT_CVC4_TEST_BV_UNSIGNED_UNARY_OP(op, opcode, opname, kind)    \
  TEST(SmtCVC4Test, BvUnsignedUnaryOperator##opcode)                    \
  SMT_CVC4_TEST_BV_BINARY_OP(op, opcode, opname, kind, unsigned)        \

SMT_CVC4_TEST_BV_SIGNED_UNARY_OP(-, SUB, bvneg, CVC4::kind::BITVECTOR_NEG)
SMT_CVC4_TEST_BV_SIGNED_UNARY_OP(~, NOT, bvnot, CVC4::kind::BITVECTOR_NOT)

#define SMT_CVC4_TEST_BV_BINARY_REL(op, opcode, opname, kind, sign)     \
  {                                                                     \
    CVC4Solver s;                                                       \
                                                                        \
    const Bv<sign int> e0 = any<Bv<sign int>>("x");                     \
    const Bv<sign int> e1 = any<Bv<sign int>>("y");                     \
    const Bool e2(e0 op e1);                                            \
                                                                        \
    EXPECT_EQ(OK, static_cast<SharedExpr>(e2).encode(s));               \
                                                                        \
    const CVC4::Expr expr(s.expr());                                    \
    EXPECT_EQ(kind, expr.getKind());                                    \
    EXPECT_TRUE(expr.getType(true).isBoolean());                        \
                                                                        \
    std::stringstream out;                                              \
    out << s.expr();                                                    \
    EXPECT_EQ("(" #opname " x y)", out.str());                          \
  }                                                                     \

#define SMT_CVC4_TEST_BV_SIGNED_BINARY_REL(op, opcode, opname, kind)    \
  TEST(SmtCVC4Test, BvSignedBinaryOperator##opcode)                     \
  SMT_CVC4_TEST_BV_BINARY_REL(op, opcode, opname, kind, signed)         \

#define SMT_CVC4_TEST_BV_UNSIGNED_BINARY_REL(op, opcode, opname, kind)  \
  TEST(SmtCVC4Test, BvUnsignedBinaryOperator##opcode)                   \
  SMT_CVC4_TEST_BV_BINARY_REL(op, opcode, opname, kind, unsigned)       \

SMT_CVC4_TEST_BV_SIGNED_BINARY_REL(==, EQL, =, CVC4::kind::EQUAL)
SMT_CVC4_TEST_BV_SIGNED_BINARY_REL(<, LSS, bvslt, CVC4::kind::BITVECTOR_SLT)
SMT_CVC4_TEST_BV_SIGNED_BINARY_REL(>, GTR, bvsgt, CVC4::kind::BITVECTOR_SGT)
SMT_CVC4_TEST_BV_SIGNED_BINARY_REL(!=, NEQ, distinct, CVC4::kind::DISTINCT)
SMT_CVC4_TEST_BV_SIGNED_BINARY_REL(<=, LEQ, bvsle, CVC4::kind::BITVECTOR_SLE)
SMT_CVC4_TEST_BV_SIGNED_BINARY_REL(>=, GEQ, bvsge, CVC4::kind::BITVECTOR_SGE)

SMT_CVC4_TEST_BV_UNSIGNED_BINARY_REL(==, EQL, =, CVC4::kind::EQUAL)
SMT_CVC4_TEST_BV_UNSIGNED_BINARY_REL(<, LSS, bvult, CVC4::kind::BITVECTOR_ULT)
SMT_CVC4_TEST_BV_UNSIGNED_BINARY_REL(>, GTR, bvugt, CVC4::kind::BITVECTOR_UGT)
SMT_CVC4_TEST_BV_UNSIGNED_BINARY_REL(!=, NEQ, distinct, CVC4::kind::DISTINCT)
SMT_CVC4_TEST_BV_UNSIGNED_BINARY_REL(<=, LEQ, bvule, CVC4::kind::BITVECTOR_ULE)
SMT_CVC4_TEST_BV_UNSIGNED_BINARY_REL(>=, GEQ, bvuge, CVC4::kind::BITVECTOR_UGE)

#define SMT_CVC4_TEST_BV_BINARY_OP(op, opcode, opname, kind, sign)      \
  {                                                                     \
    CVC4Solver s;                                                       \
                                                                        \
    const Bv<sign int> e0 = any<Bv<sign int>>("x");                     \
    const Bv<sign int> e1 = any<Bv<sign int>>("y");                     \
    const Bv<sign int> e2(e0 op e1);                                    \
                                                                        \
    EXPECT_EQ(OK, static_cast<SharedExpr>(e2).encode(s));               \
                                                                        \
    const CVC4::Expr expr(s.expr());                                    \
    EXPECT_EQ(kind, expr.getKind());                                    \
    EXPECT_TRUE(expr.getType(true).isBitVector());                      \
                                                                        \
    std::stringstream out;                                              \
    out << s.expr();                                                    \
    EXPECT_EQ("(" #opname " x y)", out.str());                          \
  }                                                                     \

#define SMT_CVC4_TEST_BV_SIGNED_BINARY_OP(op, opcode, opname, kind)     \
  TEST(SmtCVC4Test, BvSignedBinaryOperator##opcode)                     \
  SMT_CVC4_TEST_BV_BINARY_OP(op, opcode, opname, kind, signed)          \

#define SMT_CVC4_TEST_BV_UNSIGNED_BINARY_OP(op, opcode, opname, kind)   \
  TEST(SmtCVC4Test, BvUnsignedBinaryOperator##opcode)                   \
  SMT_CVC4_TEST_BV_BINARY_OP(op, opcode, opname, kind, unsigned)        \

SMT_CVC4_TEST_BV_SIGNED_BINARY_OP(-, SUB, bvsub, CVC4::kind::BITVECTOR_SUB)
SMT_CVC4_TEST_BV_SIGNED_BINARY_OP(+, ADD, bvadd, CVC4::kind::BITVECTOR_PLUS)
SMT_CVC4_TEST_BV_SIGNED_BINARY_OP(*, MUL, bvmul, CVC4::kind::BITVECTOR_MULT)
SMT_CVC4_TEST_BV_SIGNED_BINARY_OP(/, QUO, bvsdiv, CVC4::kind::BITVECTOR_SDIV)
SMT_CVC4_TEST_BV_SIGNED_BINARY_OP(%, REM, bvsrem, CVC4::kind::BITVECTOR_SREM)

SMT_CVC4_TEST_BV_UNSIGNED_BINARY_OP(-, SUB, bvsub, CVC4::kind::BITVECTOR_SUB)
SMT_CVC4_TEST_BV_UNSIGNED_BINARY_OP(+, ADD, bvadd, CVC4::kind::BITVECTOR_PLUS)
SMT_CVC4_TEST_BV_UNSIGNED_BINARY_OP(*, MUL, bvmul, CVC4::kind::BITVECTOR_MULT)
SMT_CVC4_TEST_BV_UNSIGNED_BINARY_OP(/, QUO, bvudiv, CVC4::kind::BITVECTOR_UDIV)
SMT_CVC4_TEST_BV_UNSIGNED_BINARY_OP(%, REM, bvurem, CVC4::kind::BITVECTOR_UREM)

#define SMT_CVC4_TEST_MATH_UNARY_OP(op, opcode, opname, kind)           \
  TEST(SmtCVC4Test, MathUnaryOperator##opcode)                          \
  {                                                                     \
    CVC4Solver s;                                                       \
                                                                        \
    const Int e0 = any<Int>("x");                                       \
    const Int e1(op e0);                                                \
                                                                        \
    EXPECT_EQ(OK, static_cast<SharedExpr>(e1).encode(s));               \
                                                                        \
    const CVC4::Expr expr(s.expr());                                    \
    EXPECT_EQ(kind, expr.getKind());                                    \
    EXPECT_TRUE(expr.getType(true).isInteger());                        \
                                                                        \
    std::stringstream out;                                              \
    out << s.expr();                                                    \
    EXPECT_EQ("(" #opname " x)", out.str());                            \
  }                                                                     \

SMT_CVC4_TEST_MATH_UNARY_OP(-, SUB, -, CVC4::kind::UMINUS)

#define SMT_CVC4_TEST_MATH_BINARY_REL(op, opcode, opname, kind)         \
  TEST(SmtCVC4Test, MathBinaryOperator##opcode)                         \
  {                                                                     \
    CVC4Solver s;                                                       \
                                                                        \
    const Int e0 = any<Int>("x");                                       \
    const Int e1 = any<Int>("y");                                       \
    const Bool e2(e0 op e1);                                            \
                                                                        \
    EXPECT_EQ(OK, static_cast<SharedExpr>(e2).encode(s));               \
                                                                        \
    const CVC4::Expr expr(s.expr());                                    \
    EXPECT_EQ(kind, expr.getKind());                                    \
    EXPECT_TRUE(expr.getType(true).isBoolean());                        \
                                                                        \
    std::stringstream out;                                              \
    out << s.expr();                                                    \
    EXPECT_EQ("(" #opname " x y)", out.str());                          \
  }                                                                     \

SMT_CVC4_TEST_MATH_BINARY_REL(==, EQL, =, CVC4::kind::EQUAL)
SMT_CVC4_TEST_MATH_BINARY_REL(<, LSS, <, CVC4::kind::LT)
SMT_CVC4_TEST_MATH_BINARY_REL(>, GTR, >, CVC4::kind::GT)
SMT_CVC4_TEST_MATH_BINARY_REL(!=, NEQ, distinct, CVC4::kind::DISTINCT)
SMT_CVC4_TEST_MATH_BINARY_REL(<=, LEQ, <=, CVC4::kind::LEQ)
SMT_CVC4_TEST_MATH_BINARY_REL(>=, GEQ, >=, CVC4::kind::GEQ)

#define SMT_CVC4_TEST_MATH_BINARY_OP(op, opcode, opname, kind)          \
  TEST(SmtCVC4Test, MathBinaryOperator##opcode)                         \
  {                                                                     \
    CVC4Solver s;                                                       \
                                                                        \
    const Int e0 = any<Int>("x");                                       \
    const Int e1 = any<Int>("y");                                       \
    const Int e2(e0 op e1);                                             \
                                                                        \
    EXPECT_EQ(OK, static_cast<SharedExpr>(e2).encode(s));               \
                                                                        \
    const CVC4::Expr expr(s.expr());                                    \
    EXPECT_EQ(kind, expr.getKind());                                    \
    EXPECT_TRUE(expr.getType(true).isInteger());                        \
                                                                        \
    std::stringstream out;                                              \
    out << s.expr();                                                    \
    EXPECT_EQ("(" #opname " x y)", out.str());                          \
  }                                                                     \

SMT_CVC4_TEST_MATH_BINARY_OP(-, SUB, -, CVC4::kind::MINUS)
SMT_CVC4_TEST_MATH_BINARY_OP(+, ADD, +, CVC4::kind::PLUS)
SMT_CVC4_TEST_MATH_BINARY_OP(*, MUL, *, CVC4::kind::MULT)
SMT_CVC4_TEST_MATH_BINARY_OP(/, QUO, div, CVC4::kind::INTS_DIVISION)
SMT_CVC4_TEST_MATH_BINARY_OP(%, REM, mod, CVC4::kind::INTS_MODULUS)

#define SMT_CVC4_TEST_BOOL_BINARY_OP(op, opcode, opname, kind)          \
  TEST(SmtCVC4Test, BoolBinaryOperator##opcode)                         \
  {                                                                     \
    CVC4Solver s;                                                       \
                                                                        \
    const Bool e0 = any<Bool>("x");                                     \
    const Bool e1 = any<Bool>("y");                                     \
    const Bool e2(e0 op e1);                                            \
                                                                        \
    EXPECT_EQ(OK, static_cast<SharedExpr>(e2).encode(s));               \
                                                                        \
    const CVC4::Expr expr(s.expr());                                    \
    EXPECT_EQ(kind, expr.getKind());                                    \
    EXPECT_TRUE(expr.getType(true).isBoolean());                        \
                                                                        \
    std::stringstream out;                                              \
    out << s.expr();                                                    \
    EXPECT_EQ("(" #opname " x y)", out.str());                          \
  }                                                                     \

SMT_CVC4_TEST_BOOL_BINARY_OP(&&, LAND, and, CVC4::kind::AND)
SMT_CVC4_TEST_BOOL_BINARY_OP(||, LOR, or,  CVC4::kind::OR)
SMT_CVC4_TEST_BOOL_BINARY_OP(==, EQL, =,  CVC4::kind::IFF)

TEST(SmtCVC4Test, LogicalImplication)
{
  CVC4Solver s;

  const Bool e0 = any<Bool>("x");
  const Bool e1 = any<Bool>("y");
  const Bool e2(implies(e0, e1));

  EXPECT_EQ(OK, static_cast<SharedExpr>(e2).encode(s));
  EXPECT_TRUE(s.expr().getType(true).isBoolean());
  EXPECT_EQ(CVC4::kind::IMPLIES, s.expr().getKind());

  std::stringstream out;
  out << s.expr();
  EXPECT_EQ("(=> x y)", out.str());
}

TEST(SmtCVC4Test, Distinct)
{
  CVC4Solver s;

  const Bv<long> x = any<Bv<long>>("x");
  const Bv<long> y = any<Bv<long>>("y");
  const Bv<long> z = any<Bv<long>>("z");
  const Bv<long> w = any<Bv<long>>("w");

  Terms<Bv<long>> operand_terms(3);
  operand_terms.push_back(x);
  operand_terms.push_back(y);
  operand_terms.push_back(z);

  Bool d(distinct(std::move(operand_terms)));

  static_cast<SharedExpr>(d).encode(s);

  std::stringstream out;
  out << s.expr();
  EXPECT_EQ("(distinct x y z)", out.str());

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

TEST(SmtCVC4Test, Conjunction)
{
  CVC4Solver s;

  const Bool x = any<Bool>("x");
  const Bool y = any<Bool>("y");
  const Bool z = any<Bool>("z");
  const Bool w = any<Bool>("w");

  Terms<Bool> operand_terms(3);
  operand_terms.push_back(x);
  operand_terms.push_back(y);
  operand_terms.push_back(z);

  Bool d(conjunction(std::move(operand_terms)));

  EXPECT_EQ(OK, static_cast<SharedExpr>(d).encode(s));
  s.add(d);

  EXPECT_EQ(sat, s.check());

  s.push();
  {
    s.add(not x);
    EXPECT_EQ(unsat, s.check());
  }
  s.pop();

  s.push();
  {
    s.add(not y);
    EXPECT_EQ(unsat, s.check());
  }
  s.pop();

  s.push();
  {
    s.add(not z);
    EXPECT_EQ(unsat, s.check());
  }
  s.pop();

  s.push();
  {
    s.add(not w);
    EXPECT_EQ(sat, s.check());
  }
  s.pop();
}

TEST(SmtCVC4Test, Disjunction)
{
  CVC4Solver s;

  const Bool x = any<Bool>("x");
  const Bool y = any<Bool>("y");
  const Bool z = any<Bool>("z");
  const Bool w = any<Bool>("w");

  Terms<Bool> operand_terms(3);
  operand_terms.push_back(x);
  operand_terms.push_back(y);
  operand_terms.push_back(z);

  Bool d(disjunction(std::move(operand_terms)));

  EXPECT_EQ(OK, static_cast<SharedExpr>(d).encode(s));

  s.add(d);

  EXPECT_EQ(sat, s.check());

  s.push();
  {
    s.add(not x and not y and not z);
    EXPECT_EQ(unsat, s.check());
  }
  s.pop();

  s.push();
  {
    s.add(not x);
    s.add(not y);
    s.add(not z);
    EXPECT_EQ(unsat, s.check());
  }
  s.pop();

  s.push();
  {
    s.add(not x);
    EXPECT_EQ(sat, s.check());
  }
  s.pop();

  s.push();
  {
    s.add(not y);
    EXPECT_EQ(sat, s.check());
  }
  s.pop();

  s.push();
  {
    s.add(not z);
    EXPECT_EQ(sat, s.check());
  }
  s.pop();

  s.push();
  {
    s.add(not w);
    EXPECT_EQ(sat, s.check());
  }
  s.pop();
}

TEST(SmtCVC4Test, UnsafeAdd)
{
  CVC4Solver s;

  const Sort& bv_sort = internal::sort<Bv<int64_t>>();
  const Sort& func_sort = internal::sort<Func<Bv<int64_t>, Bv<int64_t>>>();
  const UnsafeDecl const_decl("x", bv_sort);
  const UnsafeDecl func_decl("f", func_sort);
  const SharedExpr seven_term(literal(bv_sort, 7));
  const SharedExpr x_term(constant(const_decl));
  const SharedExpr app_term(apply(func_decl, seven_term));

  SharedExprs terms;
  terms.push_back(seven_term);
  terms.push_back(x_term);
  terms.push_back(app_term);

  const SharedExpr distinct_term(distinct(std::move(terms)));

  const Sort& array_sort = internal::sort<Array<Bv<uint32_t>, Bv<int64_t>>>();
  const Sort& index_sort = internal::sort<Bv<uint32_t>>();
  const UnsafeDecl array_decl("array", array_sort);
  const UnsafeDecl index_decl("index", index_sort);
  const SharedExpr array_term(constant(array_decl));
  const SharedExpr index_term(constant(index_decl));
  const SharedExpr store_term(store(array_term, index_term, app_term));
  const SharedExpr select_term(select(store_term, index_term));

  const SharedExpr eq_term(select_term == x_term);
  const SharedExpr and_term(eq_term && distinct_term);

  s.push();
  {
    s.unsafe_add(and_term);
    EXPECT_EQ(unsat, s.check());

    std::stringstream out;
    out << s.expr();
    EXPECT_EQ(
      "(let ((_let_0 (f (_ bv7 64)))) "
        "(and (= (select (store array index _let_0) index) x)"
        " (distinct (_ bv7 64) x _let_0)))", out.str());
  }
  s.pop();

  s.push();
  {
    s.unsafe_add(seven_term != 7);
    EXPECT_EQ(unsat, s.check());
  }
  s.pop();

  s.push();
  {
    s.unsafe_add(7 == seven_term);
    EXPECT_EQ(sat, s.check());
  }
  s.pop();

  s.push();
  {
    s.unsafe_add(x_term == x_term + 1);
    EXPECT_EQ(unsat, s.check());
  }
  s.pop();

  s.push();
  {
    s.unsafe_add(x_term + 1 == x_term);
    EXPECT_EQ(unsat, s.check());
  }
  s.pop();
}

// Usually there isn't a theory to mix bit vectors and integers.
// But CVC4 is likely to internally convert these sorts. This
// is generally only acceptable for early prototyping.
TEST(SmtCVC4Test, AutoConfig)
{
  CVC4Solver solver;

  auto x = any<Bv<long>>("x");
  solver.add(0 < x);

  auto y = any<Int>("y");
  solver.add(0 < y);

  EXPECT_EQ(smt::sat, solver.check());

  solver.push();
  {
    solver.add(3 == x);
    EXPECT_EQ(smt::sat, solver.check());
  }
  solver.pop();

  EXPECT_EQ(smt::sat, solver.check());

  solver.push();

  {
    solver.add(0 > x);
    EXPECT_EQ(smt::unsat, solver.check());
  }
  solver.pop();

  EXPECT_EQ(smt::sat, solver.check());

  solver.push();
  {
    solver.add(3 == y);
    EXPECT_EQ(smt::sat, solver.check());
  }
  solver.pop();

  EXPECT_EQ(smt::sat, solver.check());

  solver.push();
  {
    solver.add(0 > y);
    EXPECT_EQ(smt::unsat, solver.check());
  }
  solver.pop();

  EXPECT_EQ(smt::sat, solver.check());
}

TEST(SmtCVC4Test, QF_BV)
{
  CVC4Solver solver(QF_BV_LOGIC);

  auto x = any<Bv<long>>("x");
  solver.add(0 < x);

  EXPECT_EQ(smt::sat, solver.check());

  solver.push();
  {
    solver.add(3 == x);
    EXPECT_EQ(smt::sat, solver.check());
  }
  solver.pop();

  EXPECT_EQ(smt::sat, solver.check());

  solver.push();

  {
    solver.add(0 > x);
    EXPECT_EQ(smt::unsat, solver.check());
  }
  solver.pop();

  EXPECT_EQ(smt::sat, solver.check());
}

TEST(SmtCVC4Test, QF_IDL)
{
  CVC4Solver solver(QF_IDL_LOGIC);

  auto y = any<Int>("y");
  solver.add(0 < y);

  EXPECT_EQ(smt::sat, solver.check());

  solver.push();
  {
    solver.add(3 == y);
    EXPECT_EQ(smt::sat, solver.check());
  }
  solver.pop();

  EXPECT_EQ(smt::sat, solver.check());

  solver.push();
  {
    solver.add(0 > y);
    EXPECT_EQ(smt::unsat, solver.check());
  }
  solver.pop();

  EXPECT_EQ(smt::sat, solver.check());
}

TEST(SmtCVC4Test, BvSignExtend)
{
  CVC4Solver s(QF_BV_LOGIC);

  Bv<int8_t> x = any<Bv<int8_t>>("x");
  Bv<int16_t> y = any<Bv<int16_t>>("y");
  Bv<uint16_t> z = any<Bv<uint16_t>>("z");

  s.push();
  {
    s.add(x == 0x07);
    s.add(y == bv_cast<int16_t>(x));
    s.add(y == 0x0007);

    EXPECT_EQ(sat, s.check());
  }
  s.pop();

  s.push();
  {
    s.add(x == 0x07);
    s.add(y == bv_cast<int16_t>(x));
    s.add(y != 0x0007);

    EXPECT_EQ(unsat, s.check());
  }
  s.pop();

  s.push();
  {
    s.add(x == 0x87);
    s.add(y == bv_cast<int16_t>(x));
    s.add(y == 0xff87);

    EXPECT_EQ(sat, s.check());
  }
  s.pop();

  s.push();
  {
    s.add(x == 0x87);
    s.add(y == bv_cast<int16_t>(x));
    s.add(y != 0xff87);

    EXPECT_EQ(unsat, s.check());
  }
  s.pop();

  s.push();
  {
    s.add(x == 0x87);

    // we cast from a signed to an unsigned integer so sign extension is required,
    // see inline comments in bv_cast<T>(const Bv<S>&) about C++ specification
    s.add(z == bv_cast<uint16_t>(x));
    s.add(z == 0xff87U);

    EXPECT_EQ(sat, s.check());
  }
  s.pop();

  s.push();
  {
    s.add(x == 0x87);

    // we cast from a signed to an unsigned integer so sign extension is required,
    // see inline comments in bv_cast<T>(const Bv<S>&) about C++ specification
    s.add(z == bv_cast<uint16_t>(x));
    s.add(z != 0xff87U);

    EXPECT_EQ(unsat, s.check());
  }
  s.pop();
}

TEST(SmtCVC4Test, BvZeroExtend)
{
  CVC4Solver s(QF_BV_LOGIC);

  Bv<uint8_t> x = any<Bv<uint8_t>>("x");
  Bv<int16_t> y = any<Bv<int16_t>>("y");
  Bv<uint16_t> z = any<Bv<uint16_t>>("z");

  s.push();
  {
    s.add(x == 0x07);
    s.add(y == bv_cast<int16_t>(x));
    s.add(y == 0x0007);

    EXPECT_EQ(sat, s.check());
  }
  s.pop();

  s.push();
  {
    s.add(x == 0x07);
    s.add(y == bv_cast<int16_t>(x));
    s.add(y != 0x0007);

    EXPECT_EQ(unsat, s.check());
  }
  s.pop();

  s.push();
  {
    s.add(x == 0x87);

    // we cast from an unsigned to a signed integer so extend by zeros.
    s.add(y == bv_cast<int16_t>(x));
    s.add(y == 0x0087);

    EXPECT_EQ(sat, s.check());
  }
  s.pop();

  s.push();
  {
    s.add(x == 0x87);

    // we cast from an unsigned to a signed integer so extend by zeros.
    s.add(y == bv_cast<int16_t>(x));
    s.add(y != 0x0087);

    EXPECT_EQ(unsat, s.check());
  }
  s.pop();

  s.push();
  {
    s.add(x == 0x87);
    s.add(z == bv_cast<uint16_t>(x));
    s.add(z == 0x0087U);

    EXPECT_EQ(sat, s.check());
  }
  s.pop();

  s.push();
  {
    s.add(x == 0x87);
    s.add(z == bv_cast<uint16_t>(x));
    s.add(z != 0x0087U);

    EXPECT_EQ(unsat, s.check());
  }
  s.pop();
}

TEST(SmtCVC4Test, BvTruncate)
{
  CVC4Solver s(QF_BV_LOGIC);

  Bv<int16_t> x = any<Bv<int16_t>>("x");
  Bv<int8_t> y = any<Bv<int8_t>>("y");
  Bv<uint8_t> z = any<Bv<uint8_t>>("z");

  s.push();
  {
    s.add(x == 0xbeef);
    s.add(y == bv_cast<int8_t>(x));
    s.add(y == 0xef);

    EXPECT_EQ(sat, s.check());
  }
  s.pop();

  s.push();
  {
    s.add(x == 0xbeef);
    s.add(y == bv_cast<int8_t>(x));
    s.add(y != 0xefU);

    EXPECT_EQ(unsat, s.check());
  }
  s.pop();

  s.push();
  {
    s.add(x == 0xbeef);
    s.add(z == bv_cast<uint8_t>(x));
    s.add(z != 0xefU);

    EXPECT_EQ(unsat, s.check());
  }
  s.pop();
}
