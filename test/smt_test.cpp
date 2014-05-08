#include "gtest/gtest.h"

#include "smt.h"

#include <thread>

using namespace smt;

#define STATIC_EXPECT_TRUE(condition) static_assert((condition), "")
#define STATIC_EXPECT_FALSE(condition) static_assert(!(condition), "")

TEST(SmtTest, SortInference)
{
  STATIC_EXPECT_TRUE(internal::sort<Bv<bool>>().is_bv());
  STATIC_EXPECT_FALSE(internal::sort<Bv<bool>>().is_bool());

  STATIC_EXPECT_TRUE(internal::sort<Bv<unsigned long>>().is_bv());
  STATIC_EXPECT_FALSE(internal::sort<Bv<unsigned long>>().is_signed());

  STATIC_EXPECT_TRUE(internal::sort<Bv<signed int>>().is_bv());
  STATIC_EXPECT_TRUE(internal::sort<Bv<signed int>>().is_signed());

  STATIC_EXPECT_TRUE(internal::sort<Bool>().is_bool());
  STATIC_EXPECT_FALSE(internal::sort<Bool>().is_int());
  STATIC_EXPECT_FALSE(internal::sort<Bool>().is_real());
  STATIC_EXPECT_FALSE(internal::sort<Bool>().is_bv());
  STATIC_EXPECT_FALSE(internal::sort<Bool>().is_array());
  STATIC_EXPECT_FALSE(internal::sort<Int>().is_func());

  STATIC_EXPECT_FALSE(internal::sort<Int>().is_bool());
  STATIC_EXPECT_TRUE(internal::sort<Int>().is_int());
  STATIC_EXPECT_FALSE(internal::sort<Int>().is_real());
  STATIC_EXPECT_FALSE(internal::sort<Int>().is_bv());
  STATIC_EXPECT_FALSE(internal::sort<Int>().is_array());
  STATIC_EXPECT_FALSE(internal::sort<Int>().is_func());

  STATIC_EXPECT_FALSE(internal::sort<Real>().is_bool());
  STATIC_EXPECT_FALSE(internal::sort<Real>().is_int());
  STATIC_EXPECT_TRUE(internal::sort<Real>().is_real());
  STATIC_EXPECT_FALSE(internal::sort<Real>().is_bv());
  STATIC_EXPECT_FALSE(internal::sort<Real>().is_array());
  STATIC_EXPECT_FALSE(internal::sort<Real>().is_func());

  STATIC_EXPECT_FALSE((internal::sort<Func<Int, Bool>>().is_bool()));
  STATIC_EXPECT_FALSE((internal::sort<Func<Int, Bool>>().is_int()));
  STATIC_EXPECT_FALSE((internal::sort<Func<Int, Bool>>().is_real()));
  STATIC_EXPECT_FALSE((internal::sort<Func<Int, Bool>>().is_bv()));
  STATIC_EXPECT_FALSE((internal::sort<Func<Int, Bool>>().is_array()));
  STATIC_EXPECT_TRUE((internal::sort<Func<Int, Bool>>().is_func()));

  STATIC_EXPECT_FALSE((internal::sort<Array<Int, Bool>>().is_bool()));
  STATIC_EXPECT_FALSE((internal::sort<Array<Int, Bool>>().is_int()));
  STATIC_EXPECT_FALSE((internal::sort<Array<Int, Bool>>().is_real()));
  STATIC_EXPECT_FALSE((internal::sort<Array<Int, Bool>>().is_bv()));
  STATIC_EXPECT_TRUE((internal::sort<Array<Int, Bool>>().is_array()));
  STATIC_EXPECT_FALSE((internal::sort<Array<Int, Bool>>().is_func()));

  STATIC_EXPECT_TRUE((internal::sort<Array<Int, Bool>>().sorts_size()) == 2);
  STATIC_EXPECT_TRUE(((internal::sort<Array<Int, Bool>>().sorts(0)).is_int()));
  STATIC_EXPECT_TRUE(((internal::sort<Array<Int, Bool>>().sorts(1)).is_bool()));

  typedef Array<Bv<long>, Bool> NestedArray;
  STATIC_EXPECT_TRUE((internal::sort<Array<Int, NestedArray>>().sorts_size()) == 2);
  STATIC_EXPECT_TRUE((internal::sort<Array<Int, NestedArray>>().sorts(0).is_int()));
  STATIC_EXPECT_TRUE((internal::sort<Array<Int, NestedArray>>().sorts(1).is_array()));
  STATIC_EXPECT_TRUE((internal::sort<Array<Int, NestedArray>>().sorts(1).sorts(0).is_bv()));
  STATIC_EXPECT_TRUE((internal::sort<Array<Int, NestedArray>>().sorts(1).sorts(1).is_bool()));
}

TEST(SmtTest, RemoveLast)
{
  STATIC_EXPECT_TRUE((std::is_same<internal::RemoveLast<Bv<long>, Int>::Type,
    std::tuple<Bv<long>>>::value));

  STATIC_EXPECT_TRUE((std::is_same<internal::RemoveLast<Bv<long>, Int, Real>::Type,
    std::tuple<Bv<long>, Int>>::value));

  internal::RemoveLast<Bv<long>, Int>::Type(
    std::make_tuple(Bv<long>(nullptr)));
}

struct SomethingElse {};

TEST(SmtTest, IsPrimitive)
{
  STATIC_EXPECT_TRUE(internal::IsPrimitive<Bv<bool>>::value);
  STATIC_EXPECT_TRUE(internal::IsPrimitive<Bv<char>>::value);
  STATIC_EXPECT_TRUE(internal::IsPrimitive<Bv<signed char>>::value);
  STATIC_EXPECT_TRUE(internal::IsPrimitive<Bv<unsigned char>>::value);
  STATIC_EXPECT_TRUE(internal::IsPrimitive<Bv<wchar_t>>::value);
  STATIC_EXPECT_TRUE(internal::IsPrimitive<Bv<char16_t>>::value);
  STATIC_EXPECT_TRUE(internal::IsPrimitive<Bv<char32_t>>::value);
  STATIC_EXPECT_TRUE(internal::IsPrimitive<Bv<short>>::value);
  STATIC_EXPECT_TRUE(internal::IsPrimitive<Bv<unsigned short>>::value);
  STATIC_EXPECT_TRUE(internal::IsPrimitive<Bv<int>>::value);
  STATIC_EXPECT_TRUE(internal::IsPrimitive<Bv<unsigned int>>::value);
  STATIC_EXPECT_TRUE(internal::IsPrimitive<Bv<long>>::value);
  STATIC_EXPECT_TRUE(internal::IsPrimitive<Bv<unsigned long>>::value);
  STATIC_EXPECT_TRUE(internal::IsPrimitive<Bv<long long>>::value);
  STATIC_EXPECT_TRUE(internal::IsPrimitive<Bv<unsigned long long>>::value);

  STATIC_EXPECT_TRUE(internal::IsPrimitive<Bool>::value);
  STATIC_EXPECT_TRUE(internal::IsPrimitive<Int>::value);
  STATIC_EXPECT_TRUE(internal::IsPrimitive<Real>::value);

  STATIC_EXPECT_FALSE(internal::IsPrimitive<SomethingElse>::value);
  STATIC_EXPECT_FALSE(internal::IsPrimitive<float>::value);
  STATIC_EXPECT_FALSE(internal::IsPrimitive<double>::value);
  STATIC_EXPECT_FALSE(internal::IsPrimitive<int>::value);
  STATIC_EXPECT_FALSE(internal::IsPrimitive<int*>::value);
  STATIC_EXPECT_FALSE(internal::IsPrimitive<void>::value);
}

TEST(SmtTest, Ok)
{
  STATIC_EXPECT_TRUE(OK == 0);
  STATIC_EXPECT_TRUE(OK == false);
}

// Sort::operator==(const Sort&) is not constexpr because it causes a g++ 4.8 bug
TEST(SmtTest, BvSort)
{
  const Sort& sbv_1 = bv_sort(true, 1);
  const Sort& ubv_1 = bv_sort(false, 1);
  const Sort& ubv_2 = bv_sort(false, 2);
  const Sort& ubv_16 = bv_sort(false, 16);

  EXPECT_NE(&sbv_1, &ubv_1);
  EXPECT_NE(&sbv_1, &ubv_2);
  EXPECT_NE(&ubv_1, &ubv_2);
  EXPECT_NE(&ubv_16, &internal::sort<Bv<uint16_t>>());
  EXPECT_EQ(ubv_16, internal::sort<Bv<uint16_t>>());

  EXPECT_EQ(&sbv_1, &bv_sort(true, 1));
  EXPECT_EQ(&ubv_1, &bv_sort(false, 1));
}

TEST(SmtTest, LiteralExpr)
{
  const LiteralExpr<long> e0(
    internal::sort<Bv<long>>(), 42L);

  EXPECT_EQ(LITERAL_EXPR_KIND, e0.expr_kind());
  EXPECT_FALSE(e0.sort().is_bool());
  EXPECT_FALSE(e0.sort().is_int());
  EXPECT_FALSE(e0.sort().is_real());
  EXPECT_TRUE(e0.sort().is_bv());
  EXPECT_TRUE(e0.sort().is_signed());
  EXPECT_FALSE(e0.sort().is_array());
  EXPECT_FALSE(e0.sort().is_func());
  EXPECT_EQ(sizeof(long) * 8, e0.sort().bv_size());
  EXPECT_EQ(42L, e0.literal());

  const LiteralExpr<unsigned long> e1(
    internal::sort<Bv<unsigned long>>(), 42UL);

  EXPECT_EQ(LITERAL_EXPR_KIND, e1.expr_kind());
  EXPECT_FALSE(e1.sort().is_bool());
  EXPECT_FALSE(e1.sort().is_int());
  EXPECT_FALSE(e1.sort().is_real());
  EXPECT_TRUE(e1.sort().is_bv());
  EXPECT_FALSE(e1.sort().is_signed());
  EXPECT_FALSE(e1.sort().is_array());
  EXPECT_FALSE(e1.sort().is_func());
  EXPECT_EQ(sizeof(long) * 8, e1.sort().bv_size());
  EXPECT_EQ(42L, e1.literal());

  const LiteralExpr<char> e2(internal::sort<Int>(), 'A');

  EXPECT_EQ(LITERAL_EXPR_KIND, e2.expr_kind());
  EXPECT_FALSE(e2.sort().is_bool());
  EXPECT_TRUE(e2.sort().is_int());
  EXPECT_FALSE(e2.sort().is_real());
  EXPECT_FALSE(e2.sort().is_bv());
  EXPECT_FALSE(e2.sort().is_array());
  EXPECT_FALSE(e2.sort().is_func());
  EXPECT_EQ('A', e2.literal());
}

TEST(SmtTest, Decl)
{
  const Decl<Bv<long>> d0("x");

  EXPECT_FALSE(d0.sort().is_bool());
  EXPECT_FALSE(d0.sort().is_int());
  EXPECT_FALSE(d0.sort().is_real());
  EXPECT_TRUE(d0.sort().is_bv());
  EXPECT_FALSE(d0.sort().is_array());
  EXPECT_FALSE(d0.sort().is_func());
  EXPECT_EQ(sizeof(long) * 8, d0.sort().bv_size());
  EXPECT_EQ("x", d0.symbol());

  const Decl<Int> d1("y");

  EXPECT_FALSE(d1.sort().is_bool());
  EXPECT_TRUE(d1.sort().is_int());
  EXPECT_FALSE(d1.sort().is_real());
  EXPECT_FALSE(d1.sort().is_bv());
  EXPECT_FALSE(d1.sort().is_array());
  EXPECT_FALSE(d1.sort().is_func());
  EXPECT_EQ("y", d1.symbol());

  const Decl<Array<Int, Bool>> d2("z");

  EXPECT_FALSE(d2.sort().is_bool());
  EXPECT_FALSE(d2.sort().is_int());
  EXPECT_FALSE(d2.sort().is_real());
  EXPECT_FALSE(d2.sort().is_bv());
  EXPECT_TRUE(d2.sort().is_array());
  EXPECT_FALSE(d2.sort().is_func());
  EXPECT_EQ("z", d2.symbol());

  EXPECT_EQ(2, d2.sort().sorts_size());

  EXPECT_FALSE(d2.sort().sorts(0).is_bool());
  EXPECT_TRUE(d2.sort().sorts(0).is_int());
  EXPECT_FALSE(d2.sort().sorts(0).is_real());
  EXPECT_FALSE(d2.sort().sorts(0).is_bv());
  EXPECT_FALSE(d2.sort().sorts(0).is_array());
  EXPECT_FALSE(d2.sort().sorts(0).is_func());

  EXPECT_TRUE(d2.sort().sorts(1).is_bool());
  EXPECT_FALSE(d2.sort().sorts(1).is_int());
  EXPECT_FALSE(d2.sort().sorts(1).is_real());
  EXPECT_FALSE(d2.sort().sorts(1).is_bv());
  EXPECT_FALSE(d2.sort().sorts(1).is_array());
  EXPECT_FALSE(d2.sort().sorts(1).is_func());
}

TEST(SmtTest, FuncDecl)
{
  const Decl<Func<Bv<long>, Int>> d0("f");

  EXPECT_FALSE(d0.sort().is_bool());
  EXPECT_FALSE(d0.sort().is_int());
  EXPECT_FALSE(d0.sort().is_real());
  EXPECT_FALSE(d0.sort().is_bv());
  EXPECT_TRUE(d0.sort().is_func());
  EXPECT_FALSE(d0.sort().is_array());

  EXPECT_EQ(2, d0.sort().sorts_size());

  EXPECT_FALSE(d0.sort().sorts(0).is_bool());
  EXPECT_FALSE(d0.sort().sorts(0).is_int());
  EXPECT_FALSE(d0.sort().sorts(0).is_real());
  EXPECT_TRUE(d0.sort().sorts(0).is_bv());
  EXPECT_FALSE(d0.sort().sorts(0).is_func());
  EXPECT_FALSE(d0.sort().sorts(0).is_array());

  EXPECT_FALSE(d0.sort().sorts(1).is_bool());
  EXPECT_TRUE(d0.sort().sorts(1).is_int());
  EXPECT_FALSE(d0.sort().sorts(1).is_real());
  EXPECT_FALSE(d0.sort().sorts(1).is_bv());
  EXPECT_FALSE(d0.sort().sorts(1).is_array());
  EXPECT_FALSE(d0.sort().sorts(1).is_func());

  const Decl<Func<Bv<long>, Int, Real>> d1("g");

  EXPECT_FALSE(d1.sort().is_bool());
  EXPECT_FALSE(d1.sort().is_int());
  EXPECT_FALSE(d1.sort().is_real());
  EXPECT_FALSE(d1.sort().is_bv());
  EXPECT_TRUE(d1.sort().is_func());
  EXPECT_FALSE(d1.sort().is_array());

  EXPECT_EQ(3, d1.sort().sorts_size());

  EXPECT_FALSE(d1.sort().sorts(0).is_bool());
  EXPECT_FALSE(d1.sort().sorts(0).is_int());
  EXPECT_FALSE(d1.sort().sorts(0).is_real());
  EXPECT_TRUE(d1.sort().sorts(0).is_bv());
  EXPECT_FALSE(d1.sort().sorts(0).is_func());
  EXPECT_FALSE(d1.sort().sorts(0).is_array());

  EXPECT_FALSE(d1.sort().sorts(1).is_bool());
  EXPECT_TRUE(d1.sort().sorts(1).is_int());
  EXPECT_FALSE(d1.sort().sorts(1).is_real());
  EXPECT_FALSE(d1.sort().sorts(1).is_bv());
  EXPECT_FALSE(d1.sort().sorts(1).is_array());
  EXPECT_FALSE(d1.sort().sorts(1).is_func());

  EXPECT_FALSE(d1.sort().sorts(2).is_bool());
  EXPECT_FALSE(d1.sort().sorts(2).is_int());
  EXPECT_TRUE(d1.sort().sorts(2).is_real());
  EXPECT_FALSE(d1.sort().sorts(2).is_bv());
  EXPECT_FALSE(d1.sort().sorts(2).is_array());
  EXPECT_FALSE(d1.sort().sorts(2).is_func());
}

TEST(SmtTest, UnaryFuncAppExpr)
{
  const Decl<Func<Bv<long>, Int>> func_decl("f");
  const Bv<long> arg_term(std::make_shared<LiteralExpr<long>>(
    internal::sort<Bv<long>>(), 7L));

  const FuncAppExpr<1> app(func_decl, { arg_term });

  EXPECT_EQ(FUNC_APP_EXPR_KIND, app.expr_kind());
  EXPECT_EQ(func_decl, app.func_decl());
  EXPECT_EQ(app.func_decl(), func_decl);

  STATIC_EXPECT_TRUE((std::tuple_size<Func<Bv<long>, Int>::Args>::value == 1));
  const std::array<UnsafeTerm, 1>& arg_terms = app.args();
  Bv<long> get0_arg_term(std::get<0>(arg_terms));
  EXPECT_EQ(LITERAL_EXPR_KIND, get0_arg_term.expr_kind());

  EXPECT_FALSE(app.sort().is_bool());
  EXPECT_TRUE(app.sort().is_int());
  EXPECT_FALSE(app.sort().is_real());
  EXPECT_FALSE(app.sort().is_bv());
  EXPECT_FALSE(app.sort().is_func());
  EXPECT_FALSE(app.sort().is_array());
}

TEST(SmtTest, BinaryFuncAppExpr)
{
  const Decl<Func<Bv<long>, Int, Real>> func_decl("g");
  const Bv<long> larg_term(std::make_shared<LiteralExpr<long>>(
    internal::sort<Bv<long>>(), 7L));
  const Int rarg_term(any<Int>("x"));

  const FuncAppExpr<2> app(func_decl, { larg_term, rarg_term });

  EXPECT_EQ(FUNC_APP_EXPR_KIND, app.expr_kind());
  EXPECT_EQ(func_decl, app.func_decl());
  EXPECT_EQ(app.func_decl(), func_decl);

  STATIC_EXPECT_TRUE((std::tuple_size<Func<Bv<long>, Int, Real>::Args>::value == 2));
  const std::array<UnsafeTerm, 2>& arg_terms = app.args();
  Bv<long> get0_arg_term(std::get<0>(arg_terms));
  EXPECT_EQ(LITERAL_EXPR_KIND, get0_arg_term.expr_kind());
  Int get1_arg_term(std::get<1>(arg_terms));
  EXPECT_EQ(CONSTANT_EXPR_KIND, get1_arg_term.expr_kind());

  EXPECT_FALSE(app.sort().is_bool());
  EXPECT_FALSE(app.sort().is_int());
  EXPECT_TRUE(app.sort().is_real());
  EXPECT_FALSE(app.sort().is_bv());
  EXPECT_FALSE(app.sort().is_func());
  EXPECT_FALSE(app.sort().is_array());
}

TEST(SmtTest, Apply)
{
  const Decl<Func<Bv<long>, Real>> bv_unary_func_decl("f");
  const Decl<Func<Int, Real>> math_unary_func_decl("g");
  const Decl<Func<Bv<long>, Int, Real>> binary_func_decl("h");
  const Bv<long> larg_term(std::make_shared<LiteralExpr<long>>(
    internal::sort<Bv<long>>(), 7L));
  const Int rarg_term(any<Int>("x"));

  const Real app_term0 = apply(binary_func_decl,
    std::make_tuple(larg_term, rarg_term));
  const Expr& app0 = app_term0.ref();

  EXPECT_EQ(FUNC_APP_EXPR_KIND, app0.expr_kind());
  EXPECT_FALSE(app0.sort().is_bool());
  EXPECT_FALSE(app0.sort().is_int());
  EXPECT_TRUE(app0.sort().is_real());
  EXPECT_FALSE(app0.sort().is_bv());
  EXPECT_FALSE(app0.sort().is_func());
  EXPECT_FALSE(app0.sort().is_array());

  const Real app_term1 = apply(bv_unary_func_decl, larg_term);
  const Expr& app1 = app_term1.ref();

  EXPECT_EQ(FUNC_APP_EXPR_KIND, app1.expr_kind());
  EXPECT_FALSE(app1.sort().is_bool());
  EXPECT_FALSE(app1.sort().is_int());
  EXPECT_TRUE(app1.sort().is_real());
  EXPECT_FALSE(app1.sort().is_bv());
  EXPECT_FALSE(app1.sort().is_func());
  EXPECT_FALSE(app1.sort().is_array());

  const Real app_term2 = apply(bv_unary_func_decl, 7L);
  const Expr& app2 = app_term2.ref();

  EXPECT_EQ(FUNC_APP_EXPR_KIND, app2.expr_kind());
  EXPECT_FALSE(app2.sort().is_bool());
  EXPECT_FALSE(app2.sort().is_int());
  EXPECT_TRUE(app2.sort().is_real());
  EXPECT_FALSE(app2.sort().is_bv());
  EXPECT_FALSE(app2.sort().is_func());
  EXPECT_FALSE(app2.sort().is_array());

  const Real app_term3 = apply(math_unary_func_decl, 7);
  const Expr& app3 = app_term3.ref();

  EXPECT_EQ(FUNC_APP_EXPR_KIND, app3.expr_kind());
  EXPECT_FALSE(app3.sort().is_bool());
  EXPECT_FALSE(app3.sort().is_int());
  EXPECT_TRUE(app3.sort().is_real());
  EXPECT_FALSE(app3.sort().is_bv());
  EXPECT_FALSE(app3.sort().is_func());
  EXPECT_FALSE(app3.sort().is_array());

  const Real app_term4 = apply(math_unary_func_decl, 7L);
  const Expr& app4 = app_term4.ref();

  EXPECT_EQ(FUNC_APP_EXPR_KIND, app4.expr_kind());
  EXPECT_FALSE(app4.sort().is_bool());
  EXPECT_FALSE(app4.sort().is_int());
  EXPECT_TRUE(app4.sort().is_real());
  EXPECT_FALSE(app4.sort().is_bv());
  EXPECT_FALSE(app4.sort().is_func());
  EXPECT_FALSE(app4.sort().is_array());

  const Real app_term5 = apply(binary_func_decl,
    larg_term, rarg_term);
  const Expr& app5 = app_term5.ref();

  EXPECT_EQ(FUNC_APP_EXPR_KIND, app5.expr_kind());
  EXPECT_FALSE(app5.sort().is_bool());
  EXPECT_FALSE(app5.sort().is_int());
  EXPECT_TRUE(app5.sort().is_real());
  EXPECT_FALSE(app5.sort().is_bv());
  EXPECT_FALSE(app5.sort().is_func());
  EXPECT_FALSE(app5.sort().is_array());
}

TEST(SmtTest, Literal)
{
  const Bool ffexpr_term = literal<Bool>(false);
  const LiteralExpr<bool>& ffexpr =
    static_cast<const LiteralExpr<bool>&>(ffexpr_term.ref());
  EXPECT_FALSE(ffexpr.literal());

  const Bool ttexpr_term = literal<Bool>(true);
  const LiteralExpr<bool>& ttexpr =
    static_cast<const LiteralExpr<bool>&>(ttexpr_term.ref());
  EXPECT_TRUE(ttexpr.literal());
}

TEST(SmtTest, Any)
{
  const Bv<long> e0_term = any<Bv<long>>("x");
  const ConstantExpr& e0 = static_cast<const ConstantExpr&>(e0_term.ref());
  const UnsafeDecl& d0 = e0.decl();

  EXPECT_FALSE(d0.sort().is_bool());
  EXPECT_FALSE(d0.sort().is_int());
  EXPECT_FALSE(d0.sort().is_real());
  EXPECT_TRUE(d0.sort().is_bv());
  EXPECT_FALSE(d0.sort().is_array());
  EXPECT_FALSE(d0.sort().is_func());
  EXPECT_EQ(sizeof(long) * 8, d0.sort().bv_size());
  EXPECT_EQ("x", d0.symbol());

  const Int e1_term = any<Int>("y");
  const ConstantExpr& e1 =
    static_cast<const ConstantExpr&>(e1_term.ref());
  const UnsafeDecl& d1 = e1.decl();

  EXPECT_FALSE(d1.sort().is_bool());
  EXPECT_TRUE(d1.sort().is_int());
  EXPECT_FALSE(d1.sort().is_real());
  EXPECT_FALSE(d1.sort().is_bv());
  EXPECT_FALSE(d1.sort().is_array());
  EXPECT_FALSE(d1.sort().is_func());
  EXPECT_EQ("y", d1.symbol());

  const Array<Int, Bool> e2_term = any<Array<Int, Bool>>("z");
  const ConstantExpr& e2 =
    static_cast<const ConstantExpr&>(e2_term.ref());
  const UnsafeDecl& d2 = e2.decl();

  EXPECT_FALSE(d2.sort().is_bool());
  EXPECT_FALSE(d2.sort().is_int());
  EXPECT_FALSE(d2.sort().is_real());
  EXPECT_FALSE(d2.sort().is_bv());
  EXPECT_TRUE(d2.sort().is_array());
  EXPECT_FALSE(d2.sort().is_func());
  EXPECT_EQ("z", d2.symbol());

  EXPECT_EQ(2, d2.sort().sorts_size());

  EXPECT_FALSE(d2.sort().sorts(0).is_bool());
  EXPECT_TRUE(d2.sort().sorts(0).is_int());
  EXPECT_FALSE(d2.sort().sorts(0).is_real());
  EXPECT_FALSE(d2.sort().sorts(0).is_bv());
  EXPECT_FALSE(d2.sort().sorts(0).is_array());
  EXPECT_FALSE(d2.sort().sorts(0).is_func());

  EXPECT_TRUE(d2.sort().sorts(1).is_bool());
  EXPECT_FALSE(d2.sort().sorts(1).is_int());
  EXPECT_FALSE(d2.sort().sorts(1).is_real());
  EXPECT_FALSE(d2.sort().sorts(1).is_bv());
  EXPECT_FALSE(d2.sort().sorts(1).is_array());
  EXPECT_FALSE(d2.sort().sorts(1).is_func());
}

TEST(SmtTest, UnaryExpr)
{
  const Bv<long> e0_term(literal<Bv<long>>(42L));
  const UnaryExpr<NOT> e1(internal::sort<Bv<long>>(), e0_term);
  const UnsafeTerm& operand = e1.operand();

  EXPECT_EQ(UNARY_EXPR_KIND, e1.expr_kind());
  EXPECT_FALSE(e1.sort().is_bool());
  EXPECT_FALSE(e1.sort().is_int());
  EXPECT_FALSE(e1.sort().is_real());
  EXPECT_TRUE(e1.sort().is_bv());
  EXPECT_FALSE(e1.sort().is_array());
  EXPECT_FALSE(e1.sort().is_func());
  EXPECT_EQ(sizeof(long) * 8, e1.sort().bv_size());

  EXPECT_EQ(e0_term.addr(), operand.addr());

  const Bool e2_term(literal<Bool>(true));
  const UnaryExpr<LNOT> e3(internal::sort<Bool>(), e2_term);

  EXPECT_EQ(UNARY_EXPR_KIND, e3.expr_kind());
  EXPECT_TRUE(e3.sort().is_bool());
  EXPECT_FALSE(e3.sort().is_int());
  EXPECT_FALSE(e3.sort().is_real());
  EXPECT_FALSE(e3.sort().is_bv());
  EXPECT_FALSE(e3.sort().is_array());
  EXPECT_FALSE(e3.sort().is_func());
}

TEST(SmtTest, BinaryExpr)
{
  const Bv<long> e0_term(literal<Bv<long>>(42L));
  const Bv<long> e1_term(literal<Bv<long>>(7L));
  const BinaryExpr<ADD> e2(internal::sort<Bv<long>>(), e0_term, e1_term);
  const Bv<long> loperand(e2.loperand());
  const Bv<long> roperand(e2.roperand());

  EXPECT_EQ(BINARY_EXPR_KIND, e2.expr_kind());
  EXPECT_FALSE(e2.sort().is_bool());
  EXPECT_FALSE(e2.sort().is_int());
  EXPECT_FALSE(e2.sort().is_real());
  EXPECT_TRUE(e2.sort().is_bv());
  EXPECT_FALSE(e2.sort().is_array());
  EXPECT_FALSE(e2.sort().is_func());
  EXPECT_EQ(sizeof(long) * 8, e2.sort().bv_size());

  EXPECT_EQ(e0_term.addr(), loperand.addr());
  EXPECT_EQ(e1_term.addr(), roperand.addr());

  const BinaryExpr<LSS> e3(internal::sort<Bool>(), e0_term, e1_term);

  EXPECT_EQ(BINARY_EXPR_KIND, e3.expr_kind());
  EXPECT_TRUE(e3.sort().is_bool());
  EXPECT_FALSE(e3.sort().is_int());
  EXPECT_FALSE(e3.sort().is_real());
  EXPECT_FALSE(e3.sort().is_bv());
  EXPECT_FALSE(e3.sort().is_array());
  EXPECT_FALSE(e3.sort().is_func());

  const Bool e4_term(literal<Bool>(true));
  const Bool e5_term(literal<Bool>(false));
  const BinaryExpr<LAND> e6(internal::sort<Bool>(), e4_term, e5_term);

  EXPECT_EQ(BINARY_EXPR_KIND, e6.expr_kind());
  EXPECT_TRUE(e6.sort().is_bool());
  EXPECT_FALSE(e6.sort().is_int());
  EXPECT_FALSE(e6.sort().is_real());
  EXPECT_FALSE(e6.sort().is_bv());
  EXPECT_FALSE(e6.sort().is_array());
  EXPECT_FALSE(e6.sort().is_func());
}

TEST(SmtTest, Terms)
{
  const Bv<long> e0_term(literal<Bv<long>>(42L));
  const Bv<long> e1_term(literal<Bv<long>>(7L));
  const Bv<long> e2_term(any<Bv<long>>("x"));

  Terms<Bv<long>> operand_terms(3);
  operand_terms.push_back(e0_term);
  operand_terms.push_back(e1_term);
  operand_terms.push_back(e2_term);

  EXPECT_EQ(3, operand_terms.size());
  EXPECT_EQ(e0_term.addr(), operand_terms.at(0).addr());
  EXPECT_EQ(e1_term.addr(), operand_terms.at(1).addr());
  EXPECT_EQ(e2_term.addr(), operand_terms.at(2).addr());
}

TEST(SmtTest, NaryExpr)
{
  const Bv<long> e0_term(literal<Bv<long>>(42L));
  const Bv<long> e1_term(literal<Bv<long>>(7L));
  const Bv<long> e2_term(any<Bv<long>>("x"));

  Terms<Bv<long>> operand_terms(3);
  operand_terms.push_back(e0_term);
  operand_terms.push_back(e1_term);
  operand_terms.push_back(e2_term);

  const NaryExpr<ADD> e3(internal::sort<Bv<long>>(), std::move(operand_terms.terms));

  EXPECT_EQ(3, e3.size());
  EXPECT_EQ(e0_term.addr(), e3.operand(0).addr());
  EXPECT_EQ(e1_term.addr(), e3.operand(1).addr());
  EXPECT_EQ(e2_term.addr(), e3.operand(2).addr());

  EXPECT_EQ(NARY_EXPR_KIND, e3.expr_kind());
  EXPECT_FALSE(e3.sort().is_bool());
  EXPECT_FALSE(e3.sort().is_int());
  EXPECT_FALSE(e3.sort().is_real());
  EXPECT_TRUE(e3.sort().is_bv());
  EXPECT_FALSE(e3.sort().is_array());
  EXPECT_FALSE(e3.sort().is_func());
  EXPECT_EQ(sizeof(long) * 8, e3.sort().bv_size());
}

TEST(SmtTest, Distinct)
{
  const Bv<long> e0_term(literal<Bv<long>>(42L));
  const Bv<long> e1_term(literal<Bv<long>>(7L));
  const Bv<long> e2_term(any<Bv<long>>("x"));

  Terms<Bv<long>> operand_terms(3);
  operand_terms.push_back(e0_term);
  operand_terms.push_back(e1_term);
  operand_terms.push_back(e2_term);

  Bool e3_term(distinct(std::move(operand_terms)));

  const NaryExpr<NEQ>& e3 =
    static_cast<const NaryExpr<NEQ>&>(e3_term.ref());
  EXPECT_EQ(3, e3.size());
  EXPECT_EQ(NARY_EXPR_KIND, e3.expr_kind());
  EXPECT_TRUE(e3.sort().is_bool());
  EXPECT_FALSE(e3.sort().is_int());
  EXPECT_FALSE(e3.sort().is_real());
  EXPECT_FALSE(e3.sort().is_bv());
  EXPECT_FALSE(e3.sort().is_array());
  EXPECT_FALSE(e3.sort().is_func());
}

TEST(SmtTest, ConstArrayExpr)
{
  const Int init_term(literal<Int>(7));
  const ConstArrayExpr e0(internal::sort<Array<Int, Int>>(), init_term);

  EXPECT_EQ(CONST_ARRAY_EXPR_KIND, e0.expr_kind());
  EXPECT_EQ(init_term.addr(), e0.init().addr());
}

TEST(SmtTest, ArraySelectExpr)
{
  const Array<Int, Bool> array_term(any<Array<Int, Bool>>("x"));
  const Int index_term(any<Int>("i"));
  const ArraySelectExpr select(array_term, index_term);

  EXPECT_EQ(ARRAY_SELECT_EXPR_KIND, select.expr_kind());
  EXPECT_EQ(array_term.addr(), select.array().addr());
  EXPECT_EQ(index_term.addr(), select.index().addr());
}

TEST(SmtTest, ArrayStoreExpr)
{
  const Array<Int, Bool> array_term(any<Array<Int, Bool>>("x"));
  const Int index_term(any<Int>("i"));
  const Bool value_term(literal<Bool>(true));
  const ArrayStoreExpr store(array_term, index_term, value_term);

  EXPECT_EQ(ARRAY_STORE_EXPR_KIND, store.expr_kind());
  EXPECT_EQ(array_term.addr(), store.array().addr());
  EXPECT_EQ(index_term.addr(), store.index().addr());
  EXPECT_EQ(value_term.addr(), store.value().addr());
}

TEST(SmtTest, Select)
{
  const Array<Int, Bool> array_term(any<Array<Int, Bool>>("x"));
  const Int index_term(any<Int>("i"));
  const Bool select_term = select(array_term, index_term);

  EXPECT_EQ(ARRAY_SELECT_EXPR_KIND, select_term.expr_kind());
}

TEST(SmtTest, Store)
{
  const Array<Int, Bool> array_term(any<Array<Int, Bool>>("x"));
  const Int index_term(any<Int>("i"));
  const Bool value_term(literal<Bool>(true));
  const Array<Int, Bool> store_term = store(array_term, index_term, value_term);

  EXPECT_EQ(ARRAY_STORE_EXPR_KIND, store_term.expr_kind());
}

TEST(SmtTest, BvUnaryOperatorNOT)
{
  const Bv<long> e0_term(any<Bv<long>>("i"));
  const Bv<long> e1_term(~e0_term);
  const UnaryExpr<NOT>& e2 =
    static_cast<const UnaryExpr<NOT>&>(e1_term.ref());

  EXPECT_EQ(UNARY_EXPR_KIND, e2.expr_kind());
  EXPECT_FALSE(e2.sort().is_bool());
  EXPECT_TRUE(e2.sort().is_bv());
  EXPECT_EQ(e0_term.addr(), e2.operand().addr());
}

TEST(SmtTest, BvUnaryOperatorSUB)
{
  const Bv<long> e0_term(literal<Bv<long>>(42L));
  const Bv<long> e1_term(-e0_term);
  const UnaryExpr<SUB>& e2 =
    static_cast<const UnaryExpr<SUB>&>(e1_term.ref());

  EXPECT_EQ(UNARY_EXPR_KIND, e2.expr_kind());
  EXPECT_FALSE(e2.sort().is_bool());
  EXPECT_TRUE(e2.sort().is_bv());
  EXPECT_EQ(e0_term.addr(), e2.operand().addr());
}

#define SMT_TEST_BUILTIN_BV_BINARY_OP(op, opcode)                              \
  TEST(SmtTest, BvBinaryOperator##opcode)                                      \
  {                                                                            \
    const Bv<long> e0_term(any<Bv<long>>("i"));                                \
    const Bv<long> e1_term(literal<Bv<long>>(42L));                            \
    const Bv<long> e2_term(e0_term op e1_term);                                \
    const BinaryExpr<opcode>& e3 =                                             \
      static_cast<const BinaryExpr<opcode>&>(e2_term.ref());                   \
                                                                               \
    EXPECT_EQ(BINARY_EXPR_KIND, e3.expr_kind());                               \
    EXPECT_FALSE(e3.sort().is_bool());                                         \
    EXPECT_TRUE(e3.sort().is_bv());                                            \
    EXPECT_TRUE(e3.sort().is_signed());                                        \
    EXPECT_EQ(e0_term.addr(), e3.loperand().addr());                           \
    EXPECT_EQ(e1_term.addr(), e3.roperand().addr());                           \
                                                                               \
    const Bv<long> e4_term(e0_term op 7L);                                     \
    const BinaryExpr<opcode>& e5 =                                             \
      static_cast<const BinaryExpr<opcode>&>(e4_term.ref());                   \
    const LiteralExpr<long>& rexpr =                                           \
      static_cast<const LiteralExpr<long>&>(e5.roperand().ref());              \
                                                                               \
    EXPECT_EQ(BINARY_EXPR_KIND, e5.expr_kind());                               \
    EXPECT_FALSE(e5.sort().is_bool());                                         \
    EXPECT_TRUE(e5.sort().is_bv());                                            \
    EXPECT_TRUE(e5.sort().is_signed());                                        \
    EXPECT_EQ(e0_term.addr(), e5.loperand().addr());                           \
    EXPECT_EQ(7L, rexpr.literal());                                            \
                                                                               \
    const Bv<long> e6_term(7L op e0_term);                                     \
    const BinaryExpr<opcode>& e7 =                                             \
      static_cast<const BinaryExpr<opcode>&>(e6_term.ref());                   \
    const LiteralExpr<long>& lexpr =                                           \
      static_cast<const LiteralExpr<long>&>(e7.loperand().ref());              \
                                                                               \
    EXPECT_EQ(BINARY_EXPR_KIND, e7.expr_kind());                               \
    EXPECT_FALSE(e7.sort().is_bool());                                         \
    EXPECT_TRUE(e7.sort().is_bv());                                            \
    EXPECT_TRUE(e7.sort().is_signed());                                        \
    EXPECT_EQ(7L, lexpr.literal());                                            \
    EXPECT_EQ(e0_term.addr(), e7.roperand().addr());                           \
  }                                                                            \

#define SMT_TEST_BUILTIN_BV_BINARY_REL(op, opcode)                             \
  TEST(SmtTest, BvBinaryRelation##opcode)                                      \
  {                                                                            \
    const Bv<long> e0_term(any<Bv<long>>("i"));                                \
    const Bv<long> e1_term(literal<Bv<long>>(42L));                            \
    const Bool e2_term(e0_term op e1_term);                                    \
    const BinaryExpr<opcode>& e3 =                                             \
      static_cast<const BinaryExpr<opcode>&>(e2_term.ref());                   \
                                                                               \
    EXPECT_EQ(BINARY_EXPR_KIND, e3.expr_kind());                               \
    EXPECT_TRUE(e3.sort().is_bool());                                          \
    EXPECT_FALSE(e3.sort().is_bv());                                           \
    EXPECT_EQ(e0_term.addr(), e3.loperand().addr());                           \
    EXPECT_EQ(e1_term.addr(), e3.roperand().addr());                           \
                                                                               \
    const Bool e4_term(e0_term op 7L);                                         \
    const BinaryExpr<opcode>& e5 =                                             \
      static_cast<const BinaryExpr<opcode>&>(e4_term.ref());                   \
    const LiteralExpr<long>& rexpr =                                           \
      static_cast<const LiteralExpr<long>&>(e5.roperand().ref());              \
                                                                               \
    EXPECT_EQ(BINARY_EXPR_KIND, e5.expr_kind());                               \
    EXPECT_TRUE(e5.sort().is_bool());                                          \
    EXPECT_FALSE(e5.sort().is_bv());                                           \
    EXPECT_EQ(e0_term.addr(), e5.loperand().addr());                           \
    EXPECT_EQ(7L, rexpr.literal());                                            \
                                                                               \
    const Bool e6_term(7L op e0_term);                                         \
    const BinaryExpr<opcode>& e7 =                                             \
      static_cast<const BinaryExpr<opcode>&>(e6_term.ref());                   \
    const LiteralExpr<long>& lexpr =                                           \
      static_cast<const LiteralExpr<long>&>(e7.loperand().ref());              \
                                                                               \
    EXPECT_EQ(BINARY_EXPR_KIND, e7.expr_kind());                               \
    EXPECT_TRUE(e7.sort().is_bool());                                          \
    EXPECT_FALSE(e7.sort().is_bv());                                           \
    EXPECT_EQ(7L, lexpr.literal());                                            \
    EXPECT_EQ(e0_term.addr(), e7.roperand().addr());                           \
  }                                                                            \

SMT_TEST_BUILTIN_BV_BINARY_OP(-, SUB)
SMT_TEST_BUILTIN_BV_BINARY_OP(&, AND)
SMT_TEST_BUILTIN_BV_BINARY_OP(|, OR)
SMT_TEST_BUILTIN_BV_BINARY_OP(^, XOR)
SMT_TEST_BUILTIN_BV_BINARY_OP(+, ADD)
SMT_TEST_BUILTIN_BV_BINARY_OP(*, MUL)
SMT_TEST_BUILTIN_BV_BINARY_OP(/, QUO)
SMT_TEST_BUILTIN_BV_BINARY_OP(%, REM)

SMT_TEST_BUILTIN_BV_BINARY_REL(<, LSS)
SMT_TEST_BUILTIN_BV_BINARY_REL(>, GTR)
SMT_TEST_BUILTIN_BV_BINARY_REL(!=, NEQ)
SMT_TEST_BUILTIN_BV_BINARY_REL(<=, LEQ)
SMT_TEST_BUILTIN_BV_BINARY_REL(>=, GEQ)
SMT_TEST_BUILTIN_BV_BINARY_REL(==, EQL)

#define SMT_TEST_BUILTIN_MATH_BINARY_OP(op, opcode)                            \
  TEST(SmtTest, MathBinaryOperator##opcode)                                    \
  {                                                                            \
    const Int e0_term(any<Int>("i"));                                          \
    const Int e1_term(literal<Int>(42L));                                      \
    const Int e2_term(e0_term op e1_term);                                     \
    const BinaryExpr<opcode>& e3 =                                             \
      static_cast<const BinaryExpr<opcode>&>(e2_term.ref());                   \
                                                                               \
    EXPECT_EQ(BINARY_EXPR_KIND, e3.expr_kind());                               \
    EXPECT_FALSE(e3.sort().is_bool());                                         \
    EXPECT_TRUE(e3.sort().is_int());                                           \
    EXPECT_FALSE(e3.sort().is_bv());                                           \
    EXPECT_EQ(e0_term.addr(), e3.loperand().addr());                           \
    EXPECT_EQ(e1_term.addr(), e3.roperand().addr());                           \
                                                                               \
    const Int e4_term(e0_term op 7L);                                          \
    const BinaryExpr<opcode>& e5 =                                             \
      static_cast<const BinaryExpr<opcode>&>(e4_term.ref());                   \
    const LiteralExpr<long>& rexpr =                                           \
      static_cast<const LiteralExpr<long>&>(e5.roperand().ref());              \
                                                                               \
    EXPECT_EQ(BINARY_EXPR_KIND, e5.expr_kind());                               \
    EXPECT_FALSE(e5.sort().is_bool());                                         \
    EXPECT_TRUE(e5.sort().is_int());                                           \
    EXPECT_FALSE(e5.sort().is_bv());                                           \
    EXPECT_EQ(e0_term.addr(), e5.loperand().addr());                           \
    EXPECT_EQ(7L, rexpr.literal());                                            \
                                                                               \
    const Int e6_term(7L op e0_term);                                          \
    const BinaryExpr<opcode>& e7 =                                             \
      static_cast<const BinaryExpr<opcode>&>(e6_term.ref());                   \
    const LiteralExpr<long>& lexpr =                                           \
      static_cast<const LiteralExpr<long>&>(e7.loperand().ref());              \
                                                                               \
    EXPECT_EQ(BINARY_EXPR_KIND, e7.expr_kind());                               \
    EXPECT_FALSE(e7.sort().is_bool());                                         \
    EXPECT_TRUE(e7.sort().is_int());                                           \
    EXPECT_FALSE(e7.sort().is_bv());                                           \
    EXPECT_EQ(7L, lexpr.literal());                                            \
    EXPECT_EQ(e0_term.addr(), e7.roperand().addr());                           \
  }                                                                            \

#define SMT_TEST_BUILTIN_MATH_BINARY_REL(op, opcode)                           \
  TEST(SmtTest, MathBinaryRelation##opcode)                                    \
  {                                                                            \
    const Int e0_term(any<Int>("i"));                                          \
    const Int e1_term(literal<Int>(42L));                                      \
    const Bool e2_term(e0_term op e1_term);                                    \
    const BinaryExpr<opcode>& e3 =                                             \
      static_cast<const BinaryExpr<opcode>&>(e2_term.ref());                   \
                                                                               \
    EXPECT_EQ(BINARY_EXPR_KIND, e3.expr_kind());                               \
    EXPECT_TRUE(e3.sort().is_bool());                                          \
    EXPECT_FALSE(e3.sort().is_int());                                          \
    EXPECT_FALSE(e3.sort().is_bv());                                           \
    EXPECT_EQ(e0_term.addr(), e3.loperand().addr());                           \
    EXPECT_EQ(e1_term.addr(), e3.roperand().addr());                           \
                                                                               \
    const Bool e4_term(e0_term op 7L);                                         \
    const BinaryExpr<opcode>& e5 =                                             \
      static_cast<const BinaryExpr<opcode>&>(e4_term.ref());                   \
                                                                               \
    const LiteralExpr<long>& rexpr =                                           \
      static_cast<const LiteralExpr<long>&>(e5.roperand().ref());              \
                                                                               \
    EXPECT_EQ(BINARY_EXPR_KIND, e5.expr_kind());                               \
    EXPECT_TRUE(e5.sort().is_bool());                                          \
    EXPECT_FALSE(e5.sort().is_int());                                          \
    EXPECT_FALSE(e5.sort().is_bv());                                           \
    EXPECT_EQ(e0_term.addr(), e5.loperand().addr());                           \
    EXPECT_EQ(7L, rexpr.literal());                                            \
                                                                               \
    const Bool e6_term(7L op e0_term);                                         \
    const BinaryExpr<opcode>& e7 =                                             \
      static_cast<const BinaryExpr<opcode>&>(e6_term.ref());                   \
                                                                               \
    const LiteralExpr<long>& lexpr =                                           \
      static_cast<const LiteralExpr<long>&>(e7.loperand().ref());              \
                                                                               \
    EXPECT_EQ(BINARY_EXPR_KIND, e7.expr_kind());                               \
    EXPECT_TRUE(e7.sort().is_bool());                                          \
    EXPECT_FALSE(e7.sort().is_int());                                          \
    EXPECT_FALSE(e7.sort().is_bv());                                           \
    EXPECT_EQ(7L, lexpr.literal());                                            \
    EXPECT_EQ(e0_term.addr(), e7.roperand().addr());                           \
  }                                                                            \

SMT_TEST_BUILTIN_MATH_BINARY_OP(-, SUB)
SMT_TEST_BUILTIN_MATH_BINARY_OP(+, ADD)
SMT_TEST_BUILTIN_MATH_BINARY_OP(*, MUL)
SMT_TEST_BUILTIN_MATH_BINARY_OP(/, QUO)
SMT_TEST_BUILTIN_MATH_BINARY_OP(%, REM)

SMT_TEST_BUILTIN_MATH_BINARY_REL(<, LSS)
SMT_TEST_BUILTIN_MATH_BINARY_REL(>, GTR)
SMT_TEST_BUILTIN_MATH_BINARY_REL(!=, NEQ)
SMT_TEST_BUILTIN_MATH_BINARY_REL(<=, LEQ)
SMT_TEST_BUILTIN_MATH_BINARY_REL(>=, GEQ)
SMT_TEST_BUILTIN_MATH_BINARY_REL(==, EQL)

TEST(SmtTest, BoolUnaryOperatorLNOT)
{
  const Bool e0_term(any<Bool>("x"));
  const Bool e1_term(!e0_term);
  const UnaryExpr<LNOT>& e2 =
    static_cast<const UnaryExpr<LNOT>&>(e1_term.ref());

  EXPECT_EQ(UNARY_EXPR_KIND, e2.expr_kind());
  EXPECT_TRUE(e2.sort().is_bool());
  EXPECT_FALSE(e2.sort().is_bv());
  EXPECT_EQ(e0_term.addr(), e2.operand().addr());
}

#define SMT_TEST_BUILTIN_BOOL_BINARY_OP(op, opcode)                            \
  TEST(SmtTest, BoolBinaryOperator##opcode)                                    \
  {                                                                            \
    const Bool e0_term(any<Bool>("x"));                                        \
    const Bool e1_term(literal<Bool>(true));                                   \
    const Bool e2_term(e0_term op e1_term);                                    \
    const BinaryExpr<opcode>& e3 =                                             \
      static_cast<const BinaryExpr<opcode>&>(e2_term.ref());                   \
                                                                               \
    EXPECT_EQ(BINARY_EXPR_KIND, e3.expr_kind());                               \
    EXPECT_TRUE(e3.sort().is_bool());                                          \
    EXPECT_FALSE(e3.sort().is_bv());                                           \
    EXPECT_EQ(e0_term.addr(), e3.loperand().addr());                           \
    EXPECT_EQ(e1_term.addr(), e3.roperand().addr());                           \
                                                                               \
    const Bool e4_term(e0_term op true);                                       \
    const BinaryExpr<opcode>& e5 =                                             \
      static_cast<const BinaryExpr<opcode>&>(e4_term.ref());                   \
    const LiteralExpr<bool>& rexpr =                                           \
      static_cast<const LiteralExpr<bool>&>(e5.roperand().ref());              \
                                                                               \
    EXPECT_EQ(BINARY_EXPR_KIND, e5.expr_kind());                               \
    EXPECT_TRUE(e5.sort().is_bool());                                          \
    EXPECT_FALSE(e5.sort().is_bv());                                           \
    EXPECT_EQ(e0_term.addr(), e5.loperand().addr());                           \
    EXPECT_TRUE(rexpr.literal());                                              \
                                                                               \
    const Bool e6_term(false op e0_term);                                      \
    const BinaryExpr<opcode>& e7 =                                             \
      static_cast<const BinaryExpr<opcode>&>(e6_term.ref());                   \
    const LiteralExpr<bool>& lexpr =                                           \
      static_cast<const LiteralExpr<bool>&>(e7.loperand().ref());              \
                                                                               \
    EXPECT_EQ(BINARY_EXPR_KIND, e7.expr_kind());                               \
    EXPECT_TRUE(e7.sort().is_bool());                                          \
    EXPECT_FALSE(e7.sort().is_bv());                                           \
    EXPECT_FALSE(lexpr.literal());                                             \
    EXPECT_EQ(e0_term.addr(), e7.roperand().addr());                           \
  }                                                                            \

SMT_TEST_BUILTIN_BOOL_BINARY_OP(&&, LAND)
SMT_TEST_BUILTIN_BOOL_BINARY_OP(||, LOR)
SMT_TEST_BUILTIN_BOOL_BINARY_OP(==, EQL)
SMT_TEST_BUILTIN_BOOL_BINARY_OP(!=, NEQ)

TEST(SmtTest, Identity)
{
  const Bool ttexpr_term = Identity<LAND, Bool>::term;
  const LiteralExpr<bool>& ttexpr =
    static_cast<const LiteralExpr<bool>&>(ttexpr_term.ref());
  EXPECT_TRUE(ttexpr.literal());
}

TEST(SmtTest, Signedness)
{
  const Bv<unsigned> e0_term(any<Bv<unsigned>>("x"));
  const Bv<unsigned> e1_term(e0_term + 1);
  const Bv<unsigned> e2_term(2 + e0_term);

  EXPECT_TRUE(e1_term.sort().is_bv());
  EXPECT_FALSE(e1_term.sort().is_signed());
  EXPECT_TRUE(e2_term.sort().is_bv());
  EXPECT_FALSE(e2_term.sort().is_signed());
}

TEST(SmtTest, UnsafeExpr)
{
  constexpr size_t bv_long_size = sizeof(long) * 8;
  const Sort& bv_sort = internal::sort<Bv<long>>();
  const Sort& func_sort = internal::sort<Func<Bv<long>, Bv<long>>>();
  const UnsafeDecl const_decl("x", bv_sort);
  const UnsafeDecl func_decl("f", func_sort);

  const UnsafeTerm seven_term(literal(bv_sort, 7));
  EXPECT_TRUE(seven_term.sort().is_bv());
  EXPECT_EQ(bv_long_size, seven_term.sort().bv_size());

  const UnsafeTerm x_term(constant(const_decl));
  EXPECT_TRUE(x_term.sort().is_bv());
  EXPECT_EQ(bv_long_size, x_term.sort().bv_size());

  const UnsafeTerm app_term(apply(func_decl, seven_term));
  EXPECT_TRUE(app_term.sort().is_bv());
  EXPECT_EQ(bv_long_size, app_term.sort().bv_size());

  UnsafeTerms terms;
  terms.push_back(seven_term);
  terms.push_back(x_term);
  terms.push_back(app_term);

  const UnsafeTerm distinct_term(distinct(std::move(terms)));
  EXPECT_TRUE(distinct_term.sort().is_bool());

  const Sort& array_sort = internal::sort<Array<Bv<size_t>, Bv<long>>>();
  const Sort& index_sort = internal::sort<Bv<size_t>>();
  const UnsafeDecl array_decl("array", array_sort);
  const UnsafeDecl index_decl("index", index_sort);
  const UnsafeTerm array_term(constant(array_decl));
  EXPECT_TRUE(array_term.sort().is_array());
  EXPECT_TRUE(array_term.sort().sorts(0).is_bv());
  EXPECT_TRUE(array_term.sort().sorts(1).is_bv());
  EXPECT_EQ(sizeof(size_t) * 8, array_term.sort().sorts(0).bv_size());
  EXPECT_EQ(bv_long_size, array_term.sort().sorts(1).bv_size());

  const UnsafeTerm index_term(constant(index_decl));
  EXPECT_TRUE(index_term.sort().is_bv());
  EXPECT_EQ(sizeof(size_t) * 8, index_term.sort().bv_size());

  const UnsafeTerm store_term(store(array_term, index_term, app_term));
  EXPECT_TRUE(store_term.sort().is_array());
  EXPECT_TRUE(store_term.sort().sorts(0).is_bv());
  EXPECT_TRUE(store_term.sort().sorts(1).is_bv());
  EXPECT_EQ(sizeof(size_t) * 8, store_term.sort().sorts(0).bv_size());
  EXPECT_EQ(bv_long_size, store_term.sort().sorts(1).bv_size());

  const UnsafeTerm select_term(select(store_term, index_term));
  EXPECT_TRUE(select_term.sort().is_bv());
  EXPECT_EQ(bv_long_size, select_term.sort().bv_size());

  const UnsafeTerm eq_term(select_term == x_term);
  EXPECT_TRUE(eq_term.sort().is_bool());

  const UnsafeTerm and_term(eq_term && distinct_term);
  EXPECT_TRUE(and_term.sort().is_bool());

  const UnsafeTerm ladd_term(7 + x_term);
  EXPECT_TRUE(ladd_term.sort().is_bv());
  EXPECT_EQ(bv_long_size, ladd_term.sort().bv_size());

  const UnsafeTerm radd_term(x_term + 8);
  EXPECT_TRUE(radd_term.sort().is_bv());
  EXPECT_EQ(bv_long_size, radd_term.sort().bv_size());

  const UnsafeTerm llss_term(7 < x_term);
  EXPECT_TRUE(llss_term.sort().is_bool());

  const UnsafeTerm rlss_term(x_term < 8);
  EXPECT_TRUE(rlss_term.sort().is_bool());
}

// UnsafeTerm to internal::Term<T> conversion calls the
// UnsafeTerm::T() operator. Failed casts are detected by
// a runtime assertion that checks for an empty pointer.
TEST(SmtTest, Implies)
{
  const smt::Bool a(smt::literal<smt::Bool>(true));
  const smt::UnsafeTerm b(smt::literal<smt::Bool>(true));

  smt::UnsafeTerm c(smt::implies(a, b));
  smt::UnsafeTerm d(smt::implies(b, a));
  smt::Bool e(smt::implies(a, a));
  smt::UnsafeTerm f(smt::implies(b, b));

  EXPECT_FALSE(c.is_null());
  EXPECT_FALSE(d.is_null());
  EXPECT_FALSE(e.is_null());
  EXPECT_FALSE(f.is_null());
}

TEST(SmtTest, BvSignExtend)
{
  const smt::Bv<signed short> a(smt::literal<smt::Bv<signed short>>(7));
  const smt::Bv<signed long long> b = smt::bv_cast<signed long long>(a);
  EXPECT_TRUE(a.sort().is_bv());
  EXPECT_TRUE(a.sort().is_signed());
  EXPECT_TRUE(b.sort().is_signed());
  EXPECT_TRUE(b.sort().is_bv());
  EXPECT_TRUE(a.sort().bv_size() < b.sort().bv_size());

  const smt::Bv<signed short> c(smt::literal<smt::Bv<signed short>>(7));
  const smt::Bv<unsigned long long> d = smt::bv_cast<unsigned long long>(c);
  EXPECT_TRUE(c.sort().is_bv());
  EXPECT_TRUE(c.sort().is_signed());
  EXPECT_FALSE(d.sort().is_signed());
  EXPECT_TRUE(d.sort().is_bv());
  EXPECT_TRUE(c.sort().bv_size() < d.sort().bv_size());
}

TEST(SmtTest, BvZeroExtend)
{
  const smt::Bv<unsigned short> a(smt::literal<smt::Bv<unsigned short>>(7));
  const smt::Bv<signed long long> b = smt::bv_cast<signed long long>(a);
  EXPECT_TRUE(a.sort().is_bv());
  EXPECT_FALSE(a.sort().is_signed());
  EXPECT_TRUE(b.sort().is_signed());
  EXPECT_TRUE(b.sort().is_bv());
  EXPECT_TRUE(a.sort().bv_size() < b.sort().bv_size());

  const smt::Bv<unsigned short> c(smt::literal<smt::Bv<unsigned short>>(7));
  const smt::Bv<unsigned long long> d = smt::bv_cast<unsigned long long>(c);
  EXPECT_TRUE(c.sort().is_bv());
  EXPECT_FALSE(c.sort().is_signed());
  EXPECT_FALSE(d.sort().is_signed());
  EXPECT_TRUE(d.sort().is_bv());
  EXPECT_TRUE(c.sort().bv_size() < d.sort().bv_size());
}

TEST(SmtTest, BvTruncate)
{
  const smt::Bv<unsigned long> a(smt::literal<smt::Bv<unsigned long>>(7));
  const smt::Bv<unsigned short> b = smt::bv_cast<unsigned short>(a);
  EXPECT_FALSE(a.sort().is_signed());
  EXPECT_TRUE(a.sort().is_bv());
  EXPECT_FALSE(b.sort().is_signed());
  EXPECT_TRUE(b.sort().is_bv());
  EXPECT_TRUE(a.sort().bv_size() > b.sort().bv_size());

  const smt::Bv<signed long> c(smt::literal<smt::Bv<signed long>>(7));
  const smt::Bv<signed short> d = smt::bv_cast<signed short>(c);
  EXPECT_TRUE(c.sort().is_signed());
  EXPECT_TRUE(c.sort().is_bv());
  EXPECT_TRUE(d.sort().is_signed());
  EXPECT_TRUE(d.sort().is_bv());
  EXPECT_TRUE(c.sort().bv_size() > d.sort().bv_size());
}

TEST(SmtTest, BvChangeSignedness)
{
  const smt::Bv<signed short> a(smt::literal<smt::Bv<signed short>>(7));
  const smt::Bv<unsigned short> b = smt::bv_cast<unsigned short>(a);
  EXPECT_TRUE(a.sort().is_signed());
  EXPECT_TRUE(a.sort().is_bv());
  EXPECT_FALSE(b.sort().is_signed());
  EXPECT_TRUE(b.sort().is_bv());
  EXPECT_EQ(a.sort().bv_size(), b.sort().bv_size());

  const smt::Bv<unsigned short> c(smt::literal<smt::Bv<unsigned short>>(7));
  const smt::Bv<signed short> d = smt::bv_cast<signed short>(c);
  EXPECT_FALSE(c.sort().is_signed());
  EXPECT_TRUE(c.sort().is_bv());
  EXPECT_TRUE(d.sort().is_signed());
  EXPECT_TRUE(d.sort().is_bv());
  EXPECT_EQ(c.sort().bv_size(), d.sort().bv_size());
}

TEST(SmtTest, Timer)
{
  std::chrono::milliseconds a(smt::Solver::ElapsedTime::zero());
  std::chrono::milliseconds b(smt::Solver::ElapsedTime::zero());
  {
    NonReentrantTimer<std::chrono::milliseconds> timer(a);

    bool is_active;
    ReentrantTimer<std::chrono::milliseconds> timer0(b, is_active);
    ReentrantTimer<std::chrono::milliseconds> timer1(b, is_active);

    // sleep at least 1000 milliseconds, possibly longer
    std::this_thread::sleep_for(std::chrono::seconds(1));
  }

#if __cplusplus > 201103L
  using namespace std::literals::chrono_literals;

  EXPECT_TRUE(a <= 3000ms);
  EXPECT_TRUE(500ms <= a);

  EXPECT_TRUE(b <= (a + 100ms));
  EXPECT_TRUE((a - 100ms) <= b);
#else
  EXPECT_TRUE(a.count() <= 3000);
  EXPECT_TRUE(500 <= a.count());

  EXPECT_TRUE(b.count() <= (a.count() + 100));
  EXPECT_TRUE((a.count() - 100) <= b.count());
#endif
}
