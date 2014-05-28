#include "gtest/gtest.h"

#include "smt.h"
#include "smt_stp.h"

#include <cstdint>

using namespace smt;

static char buffer[1024];
static char* buf = buffer;

static size_t constexpr buf_size(size_t bv_size)
{
  // divide by nibbles and account for "0x"
  // hex prefix as well as trailing "\0"
  return bv_size/4 + 4;
}

void print(VC vc, VCExpr e, unsigned long& len)
{
  vc_printExprToBuffer(vc, e, &buf, &len);
}

TEST(SmtStpTest, BvLiteral)
{
  StpSolver s;

  constexpr size_t int_bv_size = sizeof(int) * 8;
  constexpr size_t long_bv_size = sizeof(long) * 8;
  constexpr size_t long_long_bv_size = sizeof(long long) * 8;
  const VC vc = s.vc();
  unsigned long len;

  const Bv<int> l0 = literal<Bv<int>>(0x15);
  EXPECT_EQ(OK, static_cast<SharedExpr>(l0).encode(s));
  print(vc, s.expr(), len);
  EXPECT_EQ(buf_size(int_bv_size), len);
  EXPECT_EQ("00015 ", std::string(buf).substr(len-7));
  EXPECT_EQ(int_bv_size, vc_getBVLength(vc, s.expr()));

  const Bv<unsigned> l1 = literal<Bv<unsigned>>(0x17);
  EXPECT_EQ(OK, static_cast<SharedExpr>(l1).encode(s));
  print(vc, s.expr(), len);
  EXPECT_EQ(buf_size(int_bv_size), len);
  EXPECT_EQ("00017 ", std::string(buf).substr(len-7));
  EXPECT_EQ(int_bv_size, vc_getBVLength(vc, s.expr()));

  const Bv<long> l2 = literal<Bv<long>>(0x2A);
  EXPECT_EQ(OK, static_cast<SharedExpr>(l2).encode(s));
  print(vc, s.expr(), len);
  EXPECT_EQ(buf_size(long_bv_size), len);
  EXPECT_EQ("0002A ", std::string(buf).substr(len-7));
  EXPECT_EQ(long_bv_size, vc_getBVLength(vc, s.expr()));

  const Bv<unsigned long> l3 = literal<Bv<unsigned long>>(0x2B);
  EXPECT_EQ(OK, static_cast<SharedExpr>(l3).encode(s));
  print(vc, s.expr(), len);
  EXPECT_EQ(buf_size(long_bv_size), len);
  EXPECT_EQ("0002B ", std::string(buf).substr(len-7));
  EXPECT_EQ(long_bv_size, vc_getBVLength(vc, s.expr()));

  const Bv<long long> l4 = literal<Bv<long long>>(0x2C);
  EXPECT_EQ(OK, static_cast<SharedExpr>(l4).encode(s));
  print(vc, s.expr(), len);
  EXPECT_EQ(buf_size(long_long_bv_size), len);
  EXPECT_EQ("0002C ", std::string(buf).substr(len-7));
  EXPECT_EQ(long_long_bv_size, vc_getBVLength(vc, s.expr()));

  const Bv<unsigned long long> l5 = literal<Bv<unsigned long long>>(0x2D);
  EXPECT_EQ(OK, static_cast<SharedExpr>(l5).encode(s));
  print(vc, s.expr(), len);
  EXPECT_EQ(buf_size(long_long_bv_size), len);
  EXPECT_EQ("0002D ", std::string(buf).substr(len-7));
  EXPECT_EQ(long_long_bv_size, vc_getBVLength(vc, s.expr()));
}

TEST(SmtStpTest, NonBvLiteral)
{
  StpSolver s;

  const Int e0 = literal<Int>(42L);
  const Int e1 = literal<Int>(-42L);
  const Real e2 = literal<Real>(-42L);

  EXPECT_EQ(UNSUPPORT_ERROR, static_cast<SharedExpr>(e0).encode(s));
  EXPECT_EQ(UNSUPPORT_ERROR, static_cast<SharedExpr>(e1).encode(s));
  EXPECT_EQ(UNSUPPORT_ERROR, static_cast<SharedExpr>(e2).encode(s));
}

TEST(SmtStpTest, BoolLiteral)
{
  StpSolver s;

  const VC vc = s.vc();
  unsigned long len;

  const Bool e0 = literal<Bool>(false);
  EXPECT_EQ(OK, static_cast<SharedExpr>(e0).encode(s));
  print(vc, s.expr(), len);
  EXPECT_EQ(7, len);
  EXPECT_EQ("FALSE ", std::string(buf));

  const Bool e1 = literal<Bool>(true);
  EXPECT_EQ(OK, static_cast<SharedExpr>(e1).encode(s));
  print(vc, s.expr(), len);
  EXPECT_EQ(6, len);
  EXPECT_EQ("TRUE ", std::string(buf));
}

TEST(SmtStpTest, BvDeclExpr)
{
  constexpr size_t long_bv_size = sizeof(long) * 8;

  StpSolver s;

  const VC vc = s.vc();
  unsigned long len;

  const Bv<long> e0 = any<Bv<long>>("x");
  EXPECT_EQ(OK, static_cast<SharedExpr>(e0).encode(s));
  print(vc, s.expr(), len);
  EXPECT_EQ(3, len);
  EXPECT_EQ("x ", std::string(buf));
  EXPECT_EQ(long_bv_size, vc_getBVLength(vc, s.expr()));
}

TEST(SmtStpTest, IntAndRealDeclExpr)
{
  StpSolver s;

  const Int e0 = any<Int>("x");
  const Real e1 = any<Real>("y");

  EXPECT_EQ(UNSUPPORT_ERROR, static_cast<SharedExpr>(e0).encode(s));
  EXPECT_EQ(UNSUPPORT_ERROR, static_cast<SharedExpr>(e1).encode(s));
}

TEST(SmtStpTest, ArrayDecl)
{
  constexpr size_t size_t_bv_size = sizeof(size_t) * 8;
  constexpr size_t short_bv_size = sizeof(short) * 8;

  StpSolver s;
  const VC vc = s.vc();

  const Array<Bv<size_t>, Bv<short>> e0 = any<Array<Bv<size_t>, Bv<short>>>("array");
  EXPECT_EQ(OK, static_cast<SharedExpr>(e0).encode(s));
  EXPECT_EQ(size_t_bv_size, getIWidth(s.expr()));
  EXPECT_EQ(short_bv_size, getVWidth(s.expr()));

  const Array<Bv<short>, Bv<size_t>> e1 = any<Array<Bv<short>, Bv<size_t>>>("rev_array");
  EXPECT_EQ(OK, static_cast<SharedExpr>(e1).encode(s));
  EXPECT_EQ(short_bv_size, getIWidth(s.expr()));
  EXPECT_EQ(size_t_bv_size, getVWidth(s.expr()));
}


TEST(SmtStpTest, UnaryFuncAppExpr)
{
  StpSolver s;

  Decl<Func<Int, Bool>> func_decl("f");
  const Int e0 = any<Int>("x");
  const Bool e1 = apply(func_decl, e0);

  EXPECT_EQ(UNSUPPORT_ERROR, static_cast<SharedExpr>(e1).encode(s));
}

TEST(SmtStpTest, BinaryFuncAppExpr)
{
  StpSolver s;

  Decl<Func<Int, Bv<long>, Bool>> func_decl("f");
  const Int e0 = any<Int>("x");
  const Bv<long> e1 = any<Bv<long>>("y");
  const Bool e2 = apply(func_decl, e0, e1);

  EXPECT_EQ(UNSUPPORT_ERROR, static_cast<SharedExpr>(e2).encode(s));
}

TEST(SmtStpTest, ArraySelectExpr)
{
  StpSolver s;

  const Array<Bv<uint64_t>, Bv<uint16_t>> e0 = any<Array<Bv<uint64_t>, Bv<uint16_t>>>("array");
  const Bv<uint64_t> e1 = any<Bv<uint64_t>>("x");
  const Bv<uint16_t> e2 = select(e0, e1);

  EXPECT_EQ(OK, static_cast<SharedExpr>(e2).encode(s));
  EXPECT_EQ(16, vc_getBVLength(s.vc(), s.expr()));

  unsigned long len;
  print(s.vc(), s.expr(), len);
  EXPECT_EQ(10, len);
  EXPECT_EQ("array[x] ", std::string(buf));
}


TEST(SmtStpTest, ArrayStoreExpr)
{
  StpSolver s;

  const Array<Bv<uint64_t>, Bv<uint16_t>> e0 = any<Array<Bv<uint64_t>, Bv<uint16_t>>>("array");
  const Bv<uint64_t> e1 = any<Bv<uint64_t>>("x");
  const Bv<uint16_t> e2 = any<Bv<uint16_t>>("y");
  const Array<Bv<uint64_t>, Bv<uint16_t>> e3 = store(e0, e1, e2);

  EXPECT_EQ(OK, static_cast<SharedExpr>(e3).encode(s));

  EXPECT_EQ(64, getIWidth(s.expr()));
  EXPECT_EQ(16, getVWidth(s.expr()));

  unsigned long len;
  print(s.vc(), s.expr(), len);
  EXPECT_EQ(24, len);
  EXPECT_EQ("(array WITH [x] := y)\n ", std::string(buf));
}

TEST(SmtStpTest, BvSignedOperatorNOT)
{
  StpSolver s;

  const Bv<int64_t> e0 = any<Bv<int64_t>>("x");
  const Bv<int64_t> e1(~e0);

  EXPECT_EQ(OK, static_cast<SharedExpr>(e1).encode(s));
  EXPECT_EQ(64, vc_getBVLength(s.vc(), s.expr()));

  unsigned long len;
  print(s.vc(), s.expr(), len);
  EXPECT_EQ(10, len);
  EXPECT_EQ("( ~( x)) ", std::string(buf));
}

TEST(SmtStpTest, BvUnsignedOperatorNOT)
{
  StpSolver s;

  const Bv<uint64_t> e0 = any<Bv<uint64_t>>("x");
  const Bv<uint64_t> e1(~e0);

  EXPECT_EQ(OK, static_cast<SharedExpr>(e1).encode(s));
  EXPECT_EQ(64, vc_getBVLength(s.vc(), s.expr()));

  unsigned long len;
  print(s.vc(), s.expr(), len);
  EXPECT_EQ(10, len);
  EXPECT_EQ("( ~( x)) ", std::string(buf));
}

TEST(SmtStpTest, BvSignedUnaryOperatorSUB)
{
  StpSolver s;

  const Bv<int64_t> e0 = any<Bv<int64_t>>("x");
  const Bv<int64_t> e1(-e0);

  EXPECT_EQ(OK, static_cast<SharedExpr>(e1).encode(s));
  EXPECT_EQ(64, vc_getBVLength(s.vc(), s.expr()));

  unsigned long len;
  print(s.vc(), s.expr(), len);
  EXPECT_EQ(17, len);
  EXPECT_EQ("( BVUMINUS( x)) ", std::string(buf));
}

TEST(SmtStpTest, BvUnsignedUnaryOperatorSUB)
{
  StpSolver s;

  const Bv<uint64_t> e0 = any<Bv<uint64_t>>("x");
  const Bv<uint64_t> e1(-e0);

  EXPECT_EQ(OK, static_cast<SharedExpr>(e1).encode(s));
  EXPECT_EQ(64, vc_getBVLength(s.vc(), s.expr()));

  unsigned long len;
  print(s.vc(), s.expr(), len);
  EXPECT_EQ(17, len);
  EXPECT_EQ("( BVUMINUS( x)) ", std::string(buf));
}

// type can be either signed or unsigned but must be 16 bits short
#define SMT_STP_TEST_BV_BINARY_OP(op, opcode, opname, type, hex)        \
  {                                                                     \
    StpSolver s;                                                        \
                                                                        \
    const Bv<type> e0 = any<Bv<type>>("x");                             \
    const Bv<type> e1(static_cast<type>(hex) op e0);                    \
                                                                        \
    EXPECT_EQ(OK, static_cast<SharedExpr>(e1).encode(s));               \
    EXPECT_EQ(16, vc_getBVLength(s.vc(), s.expr()));                    \
                                                                        \
    unsigned long len;                                                  \
    print(s.vc(), s.expr(), len);                                       \
    EXPECT_EQ(#opname "(16, \n" #hex ", \nx)\n ", std::string(buf));    \
  }                                                                     \

#define SMT_STP_TEST_BV_SIGNED_BINARY_OP(op, opcode, opname)            \
  TEST(SmtStpTest, BvSignedBinaryOperator##opcode)                      \
  SMT_STP_TEST_BV_BINARY_OP(op, opcode, opname, int16_t, 0x002A)        \

#define SMT_STP_TEST_BV_UNSIGNED_BINARY_OP(op, opcode, opname)          \
  TEST(SmtStpTest, BvUnsignedBinaryOperator##opcode)                    \
  SMT_STP_TEST_BV_BINARY_OP(op, opcode, opname, uint16_t, 0x002A)       \

TEST(SmtStpTest, BvSignedOperatorSUB)
{
  StpSolver s;

  constexpr size_t long_bv_size = sizeof(int64_t) * 8;
  const Bv<int64_t> e0 = any<Bv<int64_t>>("x");
  const Bv<int64_t> e1(0x2AL - e0);

  EXPECT_EQ(OK, static_cast<SharedExpr>(e1).encode(s));
  EXPECT_EQ(64, vc_getBVLength(s.vc(), s.expr()));

  unsigned long len;
  print(s.vc(), s.expr(), len);
  EXPECT_EQ(52, len);
  EXPECT_EQ("BVPLUS(64, \n0x000000000000002A, \n( BVUMINUS( x)))\n ", std::string(buf));
}

TEST(SmtStpTest, BvSignedOperatorAND)
{
  StpSolver s;

  constexpr size_t long_bv_size = sizeof(int64_t) * 8;
  const Bv<int64_t> e0 = any<Bv<int64_t>>("x");
  const Bv<int64_t> e1(0x2AL & e0);

  EXPECT_EQ(OK, static_cast<SharedExpr>(e1).encode(s));
  EXPECT_EQ(64, vc_getBVLength(s.vc(), s.expr()));

  unsigned long len;
  print(s.vc(), s.expr(), len);
  EXPECT_EQ(27, len);
  EXPECT_EQ("(0x000000000000002A & x\n) ", std::string(buf));
}

TEST(SmtStpTest, BvSignedOperatorOR)
{
  StpSolver s;

  constexpr size_t long_bv_size = sizeof(int64_t) * 8;
  const Bv<int64_t> e0 = any<Bv<int64_t>>("x");
  const Bv<int64_t> e1(0x2AL | e0);

  EXPECT_EQ(OK, static_cast<SharedExpr>(e1).encode(s));
  EXPECT_EQ(64, vc_getBVLength(s.vc(), s.expr()));

  unsigned long len;
  print(s.vc(), s.expr(), len);
  EXPECT_EQ(27, len);
  EXPECT_EQ("(0x000000000000002A | x\n) ", std::string(buf));
}

TEST(SmtStpTest, BvSignedOperatorXOR)
{
  StpSolver s;

  constexpr size_t long_bv_size = sizeof(int64_t) * 8;
  const Bv<int64_t> e0 = any<Bv<int64_t>>("x");
  const Bv<int64_t> e1(0x2AL ^ e0);

  EXPECT_EQ(OK, static_cast<SharedExpr>(e1).encode(s));
  EXPECT_EQ(64, vc_getBVLength(s.vc(), s.expr()));

  unsigned long len;
  print(s.vc(), s.expr(), len);
  EXPECT_EQ(30, len);
  EXPECT_EQ("BVXOR(0x000000000000002A,x)\n ", std::string(buf));
}

SMT_STP_TEST_BV_SIGNED_BINARY_OP(+, ADD, BVPLUS)
SMT_STP_TEST_BV_SIGNED_BINARY_OP(*, MUL, BVMULT)
SMT_STP_TEST_BV_SIGNED_BINARY_OP(/, QUO, SBVDIV)
SMT_STP_TEST_BV_SIGNED_BINARY_OP(%, REM, SBVMOD)

TEST(SmtStpTest, BvUnsignedOperatorSUB)
{
  StpSolver s;

  constexpr size_t long_bv_size = sizeof(uint64_t) * 8;
  const Bv<uint64_t> e0 = any<Bv<uint64_t>>("x");
  const Bv<uint64_t> e1(0x2ALU - e0);

  EXPECT_EQ(OK, static_cast<SharedExpr>(e1).encode(s));
  EXPECT_EQ(64, vc_getBVLength(s.vc(), s.expr()));

  unsigned long len;
  print(s.vc(), s.expr(), len);
  EXPECT_EQ(52, len);
  EXPECT_EQ("BVPLUS(64, \n0x000000000000002A, \n( BVUMINUS( x)))\n ", std::string(buf));
}

TEST(SmtStpTest, BvUnsignedOperatorAND)
{
  StpSolver s;

  constexpr size_t long_bv_size = sizeof(uint64_t) * 8;
  const Bv<uint64_t> e0 = any<Bv<uint64_t>>("x");
  const Bv<uint64_t> e1(0x2ALU & e0);

  EXPECT_EQ(OK, static_cast<SharedExpr>(e1).encode(s));
  EXPECT_EQ(64, vc_getBVLength(s.vc(), s.expr()));

  unsigned long len;
  print(s.vc(), s.expr(), len);
  EXPECT_EQ(27, len);
  EXPECT_EQ("(0x000000000000002A & x\n) ", std::string(buf));
}

TEST(SmtStpTest, BvUnsignedOperatorOR)
{
  StpSolver s;

  constexpr size_t long_bv_size = sizeof(uint64_t) * 8;
  const Bv<uint64_t> e0 = any<Bv<uint64_t>>("x");
  const Bv<uint64_t> e1(0x2ALU | e0);

  EXPECT_EQ(OK, static_cast<SharedExpr>(e1).encode(s));
  EXPECT_EQ(64, vc_getBVLength(s.vc(), s.expr()));

  unsigned long len;
  print(s.vc(), s.expr(), len);
  EXPECT_EQ(27, len);
  EXPECT_EQ("(0x000000000000002A | x\n) ", std::string(buf));
}

TEST(SmtStpTest, BvUnsignedOperatorXOR)
{
  StpSolver s;

  constexpr size_t long_bv_size = sizeof(uint64_t) * 8;
  const Bv<uint64_t> e0 = any<Bv<uint64_t>>("x");
  const Bv<uint64_t> e1(0x2ALU ^ e0);

  EXPECT_EQ(OK, static_cast<SharedExpr>(e1).encode(s));
  EXPECT_EQ(64, vc_getBVLength(s.vc(), s.expr()));

  unsigned long len;
  print(s.vc(), s.expr(), len);
  EXPECT_EQ(30, len);
  EXPECT_EQ("BVXOR(0x000000000000002A,x)\n ", std::string(buf));
}

SMT_STP_TEST_BV_UNSIGNED_BINARY_OP(+, ADD, BVPLUS)
SMT_STP_TEST_BV_UNSIGNED_BINARY_OP(*, MUL, BVMULT)
SMT_STP_TEST_BV_UNSIGNED_BINARY_OP(/, QUO, BVDIV)
SMT_STP_TEST_BV_UNSIGNED_BINARY_OP(%, REM, BVMOD)

TEST(SmtStpTest, BvSignedBinaryOperatorEQL)
{
  StpSolver s;

  const Bv<int64_t> e0 = any<Bv<int64_t>>("x");
  const Bool e1(42 == e0);

  EXPECT_EQ(OK, static_cast<SharedExpr>(e1).encode(s));

  unsigned long len;
  print(s.vc(), s.expr(), len);
  EXPECT_EQ(27, len);
  EXPECT_EQ("(0x000000000000002A = x\n) ", std::string(buf));
}

TEST(SmtStpTest, BvUnsignedBinaryOperatorEQL)
{
  StpSolver s;

  const Bv<uint64_t> e0 = any<Bv<uint64_t>>("x");
  const Bool e1(42 == e0);

  EXPECT_EQ(OK, static_cast<SharedExpr>(e1).encode(s));

  unsigned long len;
  print(s.vc(), s.expr(), len);
  EXPECT_EQ(27, len);
  EXPECT_EQ("(0x000000000000002A = x\n) ", std::string(buf));
}

// type can be either signed or unsigned
#define SMT_STP_TEST_BV_BINARY_REL(op, type, hex)                       \
  StpSolver s;                                                          \
                                                                        \
  const Bv<type> e0 = any<Bv<type>>("x");                               \
  const Bool e1(static_cast<type>(hex) op e0);                          \
                                                                        \
  EXPECT_EQ(OK, static_cast<SharedExpr>(e1).encode(s));                 \
                                                                        \
  unsigned long len;                                                    \
  print(s.vc(), s.expr(), len);                                         \

TEST(SmtStpTest, BvSignedBinaryOperatorLSS)
{
  SMT_STP_TEST_BV_BINARY_REL(<, int16_t, 0x002A)
  EXPECT_EQ("SBVGT(x,0x002A)\n ", std::string(buf));
}

TEST(SmtStpTest, BvSignedBinaryOperatorGTR)
{
  SMT_STP_TEST_BV_BINARY_REL(>, int16_t, 0x002A)
  EXPECT_EQ("SBVGT(0x002A,x)\n ", std::string(buf));
}

TEST(SmtStpTest, BvSignedBinaryOperatorLEQ)
{
  SMT_STP_TEST_BV_BINARY_REL(<=, int16_t, 0x002A)
  EXPECT_EQ("( NOT( SBVGT(0x002A,x)\n)) ", std::string(buf));
}

TEST(SmtStpTest, BvSignedBinaryOperatorGEQ)
{
  SMT_STP_TEST_BV_BINARY_REL(>=, int16_t, 0x002A)
  EXPECT_EQ("( NOT( SBVGT(x,0x002A)\n)) ", std::string(buf));
}

TEST(SmtStpTest, BvSignedBinaryOperatorNEQ)
{
  SMT_STP_TEST_BV_BINARY_REL(!=, int16_t, 0x002A)
  EXPECT_EQ("( NOT( (0x002A = x\n))) ", std::string(buf));
}

TEST(SmtStpTest, BvUnsignedBinaryOperatorLSS)
{
  SMT_STP_TEST_BV_BINARY_REL(<, uint16_t, 0x002A)
  EXPECT_EQ("BVGT(x,0x002A)\n ", std::string(buf));
}

TEST(SmtStpTest, BvUnsignedBinaryOperatorGTR)
{
  SMT_STP_TEST_BV_BINARY_REL(>, uint16_t, 0x002A)
  EXPECT_EQ("BVGT(0x002A,x)\n ", std::string(buf));
}

TEST(SmtStpTest, BvUnsignedBinaryOperatorLEQ)
{
  SMT_STP_TEST_BV_BINARY_REL(<=, uint16_t, 0x002A)
  EXPECT_EQ("( NOT( BVGT(0x002A,x)\n)) ", std::string(buf));
}

TEST(SmtStpTest, BvUnsignedBinaryOperatorGEQ)
{
  SMT_STP_TEST_BV_BINARY_REL(>=, uint16_t, 0x002A)
  EXPECT_EQ("( NOT( BVGT(x,0x002A)\n)) ", std::string(buf));
}

TEST(SmtStpTest, BvUnsignedBinaryOperatorNEQ)
{
  SMT_STP_TEST_BV_BINARY_REL(!=, uint16_t, 0x002A)
  EXPECT_EQ("( NOT( (0x002A = x\n))) ", std::string(buf));
}

TEST(SmtStpTest, MathBinaryOperators)
{
  StpSolver s;

  const Int e0 = any<Int>("x");
  EXPECT_EQ(UNSUPPORT_ERROR, static_cast<SharedExpr>(42 - e0).encode(s));
  EXPECT_EQ(UNSUPPORT_ERROR, static_cast<SharedExpr>(42 + e0).encode(s));
  EXPECT_EQ(UNSUPPORT_ERROR, static_cast<SharedExpr>(42 * e0).encode(s));
  EXPECT_EQ(UNSUPPORT_ERROR, static_cast<SharedExpr>(42 == e0).encode(s));
  EXPECT_EQ(UNSUPPORT_ERROR, static_cast<SharedExpr>(42 / e0).encode(s));
  EXPECT_EQ(UNSUPPORT_ERROR, static_cast<SharedExpr>(42 % e0).encode(s));
  EXPECT_EQ(UNSUPPORT_ERROR, static_cast<SharedExpr>(42 < e0).encode(s));
  EXPECT_EQ(UNSUPPORT_ERROR, static_cast<SharedExpr>(42 > e0).encode(s));
  EXPECT_EQ(UNSUPPORT_ERROR, static_cast<SharedExpr>(42 != e0).encode(s));
  EXPECT_EQ(UNSUPPORT_ERROR, static_cast<SharedExpr>(42 <= e0).encode(s));
  EXPECT_EQ(UNSUPPORT_ERROR, static_cast<SharedExpr>(42 >= e0).encode(s));
}

TEST(SmtStpTest, BoolUnaryOperatorLNOT)
{
  StpSolver s;

  const Bool e0 = any<Bool>("x");
  const Bool e1(!e0);

  EXPECT_EQ(OK, static_cast<SharedExpr>(e1).encode(s));

  unsigned long len;
  print(s.vc(), s.expr(), len);
  EXPECT_EQ(12, len);
  EXPECT_EQ("( NOT( x)) ", std::string(buf));
}

#define SMT_STP_TEST_BOOL_BINARY_OP(op, opcode, opname)                 \
  TEST(SmtStpTest, BoolBinaryOperator##opcode)                          \
  {                                                                     \
    StpSolver s;                                                        \
                                                                        \
    const Bool e0 = any<Bool>("x");                                     \
    const Bool e1 = any<Bool>("y");                                     \
    const Bool e2(e0 op e1);                                            \
                                                                        \
    EXPECT_EQ(OK, static_cast<SharedExpr>(e2).encode(s));               \
                                                                        \
    unsigned long len;                                                  \
    print(s.vc(), s.expr(), len);                                       \
    EXPECT_EQ("(x " #opname " y\n) ", std::string(buf));                \
  }                                                                     \

SMT_STP_TEST_BOOL_BINARY_OP(&&, LAND, AND)
SMT_STP_TEST_BOOL_BINARY_OP(||, LOR, OR)

TEST(SmtStpTest, BoolBinaryOperatorEQL)
{
  StpSolver s;

  const Bool e0 = any<Bool>("x");
  const Bool e1 = any<Bool>("y");
  const Bool e2(e0 == e1);

  EXPECT_EQ(OK, static_cast<SharedExpr>(e2).encode(s));

  unsigned long len;
  print(s.vc(), s.expr(), len);
  EXPECT_EQ(21, len);
  EXPECT_EQ("(y XOR ( NOT( x))\n) ", std::string(buf));
}

TEST(SmtStpTest, BoolBinaryOperatorIMP)
{
  StpSolver s;

  const Bool e0 = any<Bool>("x");
  const Bool e1 = any<Bool>("y");
  const Bool e2(implies(e0, e1));

  EXPECT_EQ(OK, static_cast<SharedExpr>(e2).encode(s));

  unsigned long len;
  print(s.vc(), s.expr(), len);
  EXPECT_EQ(20, len);
  EXPECT_EQ("(y OR ( NOT( x))\n) ", std::string(buf));
}


TEST(SmtStpTest, Reset)
{
  StpSolver s;

  EXPECT_EQ(sat, s.check());
  s.add(literal<Bool>(false));
  EXPECT_EQ(unsat, s.check());
  s.reset();
  EXPECT_EQ(sat, s.check());
}

TEST(SmtStpTest, Distinct)
{
  StpSolver s;

  const Bv<long> x = any<Bv<long>>("x");
  const Bv<long> y = any<Bv<long>>("y");
  const Bv<long> z = any<Bv<long>>("z");
  const Bv<long> w = any<Bv<long>>("w");

  Terms<Bv<long>> operand_terms(3);
  operand_terms.push_back(x);
  operand_terms.push_back(y);
  operand_terms.push_back(z);

  Bool d(distinct(std::move(operand_terms)));

  EXPECT_EQ(OK, static_cast<SharedExpr>(d).encode(s));

  unsigned long len;
  print(s.vc(), s.expr(), len);
  EXPECT_EQ(69, len);
  EXPECT_EQ("((( NOT( (x = y\n))) AND "
              "( NOT( (x = z\n)))\n) AND "
              "( NOT( (y = z\n)))\n) ", std::string(buf));

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

TEST(SmtStpTest, Conjunction)
{
  StpSolver s;

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

TEST(SmtStpTest, Disjunction)
{
  StpSolver s;

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

TEST(SmtStpTest, AutoConfig)
{
  StpSolver solver;

  auto x = any<Bv<long>>("x");
  solver.add(0 < x);

  auto y = any<Bv<unsigned short>>("y");
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

TEST(SmtStpTest, QF_BV)
{
  StpSolver solver(QF_BV_LOGIC);

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

TEST(SmtStpTest, Assertions)
{
  StpSolver s(QF_BV_LOGIC);

  Bv<int8_t> x = any<Bv<int8_t>>("x");

  s.push();
  {
    s.add(x == 1);
    s.add(3 != x + 2);

    EXPECT_EQ(unsat, s.check());
  }
  s.pop();

  s.push();
  {
    s.add(x == 1);
    s.add(3 == x + 2);

    EXPECT_EQ(sat, s.check());
  }
  s.pop();
}

TEST(SmtStpTest, BvSignExtend)
{
  StpSolver s(QF_BV_LOGIC);

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

TEST(SmtStpTest, BvZeroExtend)
{
  StpSolver s(QF_BV_LOGIC);

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

TEST(SmtStpTest, BvTruncate)
{
  StpSolver s(QF_BV_LOGIC);

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
