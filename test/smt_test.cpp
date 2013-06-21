#include "gtest/gtest.h"

#include "smt.h"

using namespace smt;

#define STATIC_EXPECT_TRUE(condition) static_assert((condition), "")
#define STATIC_EXPECT_FALSE(condition) static_assert(!(condition), "")

TEST(SmtTest, Logics)
{
  STATIC_EXPECT_TRUE("AUFLIA" == Logics::acronyms[AUFLIA_LOGIC]);
  STATIC_EXPECT_TRUE("AUFLIRA" == Logics::acronyms[AUFLIRA_LOGIC]);
  STATIC_EXPECT_TRUE("AUFNIRA" == Logics::acronyms[AUFNIRA_LOGIC]);
  STATIC_EXPECT_TRUE("LRA" == Logics::acronyms[LRA_LOGIC]);
  STATIC_EXPECT_TRUE("QF_ABV" == Logics::acronyms[QF_ABV_LOGIC]);
  STATIC_EXPECT_TRUE("QF_AUFBV" == Logics::acronyms[QF_AUFBV_LOGIC]);
  STATIC_EXPECT_TRUE("QF_UFBV" == Logics::acronyms[QF_UFBV_LOGIC]);
  STATIC_EXPECT_TRUE("QF_AUFLIA" == Logics::acronyms[QF_AUFLIA_LOGIC]);
  STATIC_EXPECT_TRUE("QF_AX" == Logics::acronyms[QF_AX_LOGIC]);
  STATIC_EXPECT_TRUE("QF_BV" == Logics::acronyms[QF_BV_LOGIC]);
  STATIC_EXPECT_TRUE("QF_IDL" == Logics::acronyms[QF_IDL_LOGIC]);
  STATIC_EXPECT_TRUE("QF_RDL" == Logics::acronyms[QF_RDL_LOGIC]);
  STATIC_EXPECT_TRUE("QF_LIA" == Logics::acronyms[QF_LIA_LOGIC]);
  STATIC_EXPECT_TRUE("QF_LRA" == Logics::acronyms[QF_LRA_LOGIC]);
  STATIC_EXPECT_TRUE("QF_NIA" == Logics::acronyms[QF_NIA_LOGIC]);
  STATIC_EXPECT_TRUE("QF_NRA" == Logics::acronyms[QF_NRA_LOGIC]);
  STATIC_EXPECT_TRUE("QF_UF" == Logics::acronyms[QF_UF_LOGIC]);
  STATIC_EXPECT_TRUE("QF_UFIDL" == Logics::acronyms[QF_UFIDL_LOGIC]);
  STATIC_EXPECT_TRUE("QF_UFLIA" == Logics::acronyms[QF_UFLIA_LOGIC]);
  STATIC_EXPECT_TRUE("QF_UFLRA" == Logics::acronyms[QF_UFLRA_LOGIC]);
  STATIC_EXPECT_TRUE("QF_UFNRA" == Logics::acronyms[QF_UFNRA_LOGIC]);
  STATIC_EXPECT_TRUE("UFLRA" == Logics::acronyms[UFLRA_LOGIC]);
  STATIC_EXPECT_TRUE("UFNIA" == Logics::acronyms[UFNIA_LOGIC]);

  // sanity check
  STATIC_EXPECT_FALSE("Foo" == Logics::acronyms[UFNIA_LOGIC]);
}

TEST(SmtTest, SortInference)
{
  STATIC_EXPECT_TRUE(internal::sort<bool>().is_bv());
  STATIC_EXPECT_FALSE(internal::sort<bool>().is_bool());

  STATIC_EXPECT_TRUE(internal::sort<unsigned long>().is_bv());
  STATIC_EXPECT_FALSE(internal::sort<unsigned long>().is_signed());

  STATIC_EXPECT_TRUE(internal::sort<signed int>().is_bv());
  STATIC_EXPECT_TRUE(internal::sort<signed int>().is_signed());

  STATIC_EXPECT_TRUE(internal::sort<sort::Bool>().is_bool());
  STATIC_EXPECT_FALSE(internal::sort<sort::Bool>().is_int());
  STATIC_EXPECT_FALSE(internal::sort<sort::Bool>().is_real());
  STATIC_EXPECT_FALSE(internal::sort<sort::Bool>().is_bv());
  STATIC_EXPECT_FALSE(internal::sort<sort::Bool>().is_array());
  STATIC_EXPECT_FALSE(internal::sort<sort::Int>().is_func());

  STATIC_EXPECT_FALSE(internal::sort<sort::Int>().is_bool());
  STATIC_EXPECT_TRUE(internal::sort<sort::Int>().is_int());
  STATIC_EXPECT_FALSE(internal::sort<sort::Int>().is_real());
  STATIC_EXPECT_FALSE(internal::sort<sort::Int>().is_bv());
  STATIC_EXPECT_FALSE(internal::sort<sort::Int>().is_array());
  STATIC_EXPECT_FALSE(internal::sort<sort::Int>().is_func());

  STATIC_EXPECT_FALSE(internal::sort<sort::Real>().is_bool());
  STATIC_EXPECT_FALSE(internal::sort<sort::Real>().is_int());
  STATIC_EXPECT_TRUE(internal::sort<sort::Real>().is_real());
  STATIC_EXPECT_FALSE(internal::sort<sort::Real>().is_bv());
  STATIC_EXPECT_FALSE(internal::sort<sort::Real>().is_array());
  STATIC_EXPECT_FALSE(internal::sort<sort::Real>().is_func());

  STATIC_EXPECT_FALSE((internal::sort<sort::Func<sort::Int, sort::Bool>>().is_bool()));
  STATIC_EXPECT_FALSE((internal::sort<sort::Func<sort::Int, sort::Bool>>().is_int()));
  STATIC_EXPECT_FALSE((internal::sort<sort::Func<sort::Int, sort::Bool>>().is_real()));
  STATIC_EXPECT_FALSE((internal::sort<sort::Func<sort::Int, sort::Bool>>().is_bv()));
  STATIC_EXPECT_FALSE((internal::sort<sort::Func<sort::Int, sort::Bool>>().is_array()));
  STATIC_EXPECT_TRUE((internal::sort<sort::Func<sort::Int, sort::Bool>>().is_func()));

  STATIC_EXPECT_FALSE((internal::sort<sort::Array<sort::Int, sort::Bool>>().is_bool()));
  STATIC_EXPECT_FALSE((internal::sort<sort::Array<sort::Int, sort::Bool>>().is_int()));
  STATIC_EXPECT_FALSE((internal::sort<sort::Array<sort::Int, sort::Bool>>().is_real()));
  STATIC_EXPECT_FALSE((internal::sort<sort::Array<sort::Int, sort::Bool>>().is_bv()));
  STATIC_EXPECT_TRUE((internal::sort<sort::Array<sort::Int, sort::Bool>>().is_array()));
  STATIC_EXPECT_FALSE((internal::sort<sort::Array<sort::Int, sort::Bool>>().is_func()));

  STATIC_EXPECT_TRUE((internal::sort<sort::Array<sort::Int, sort::Bool>>().sorts_size()) == 2);
  STATIC_EXPECT_TRUE(((internal::sort<sort::Array<sort::Int, sort::Bool>>().sorts(0)).is_int()));
  STATIC_EXPECT_TRUE(((internal::sort<sort::Array<sort::Int, sort::Bool>>().sorts(1)).is_bool()));

  typedef sort::Array<long, sort::Bool> NestedArray;
  STATIC_EXPECT_TRUE((internal::sort<sort::Array<sort::Int, NestedArray>>().sorts_size()) == 2);
  STATIC_EXPECT_TRUE((internal::sort<sort::Array<sort::Int, NestedArray>>().sorts(0).is_int()));
  STATIC_EXPECT_TRUE((internal::sort<sort::Array<sort::Int, NestedArray>>().sorts(1).is_array()));
  STATIC_EXPECT_TRUE((internal::sort<sort::Array<sort::Int, NestedArray>>().sorts(1).sorts(0).is_bv()));
  STATIC_EXPECT_TRUE((internal::sort<sort::Array<sort::Int, NestedArray>>().sorts(1).sorts(1).is_bool()));
}

TEST(SmtTest, TermFold)
{
  STATIC_EXPECT_TRUE((std::is_same<internal::TermFold<long, sort::Int>::Type,
    std::tuple<Term<long>, Term<sort::Int>>>::value));

  STATIC_EXPECT_TRUE((std::is_same<internal::TermFold<long, sort::Int, sort::Real>::Type,
    std::tuple<Term<long>, Term<sort::Int>, Term<sort::Real>>>::value));

  STATIC_EXPECT_TRUE((std::is_same<internal::TermFoldExceptLast<long, sort::Int>::Type,
    std::tuple<Term<long>>>::value));

  STATIC_EXPECT_TRUE((std::is_same<internal::TermFoldExceptLast<long, sort::Int, sort::Real>::Type,
    std::tuple<Term<long>, Term<sort::Int>>>::value));

  internal::TermFoldExceptLast<long, sort::Int>::Type(
    std::make_tuple(Term<long>(nullptr)));

  internal::TermFold<long, sort::Int>::Type(
    std::make_tuple(Term<long>(nullptr), Term<sort::Int>(nullptr)));
}

struct SomethingElse {};

TEST(SmtTest, IsPrimitive)
{
  STATIC_EXPECT_TRUE(internal::IsPrimitive<bool>::value);
  STATIC_EXPECT_TRUE(internal::IsPrimitive<char>::value);
  STATIC_EXPECT_TRUE(internal::IsPrimitive<signed char>::value);
  STATIC_EXPECT_TRUE(internal::IsPrimitive<unsigned char>::value);
  STATIC_EXPECT_TRUE(internal::IsPrimitive<wchar_t>::value);
  STATIC_EXPECT_TRUE(internal::IsPrimitive<char16_t>::value);
  STATIC_EXPECT_TRUE(internal::IsPrimitive<char32_t>::value);
  STATIC_EXPECT_TRUE(internal::IsPrimitive<short>::value);
  STATIC_EXPECT_TRUE(internal::IsPrimitive<unsigned short>::value);
  STATIC_EXPECT_TRUE(internal::IsPrimitive<int>::value);
  STATIC_EXPECT_TRUE(internal::IsPrimitive<unsigned int>::value);
  STATIC_EXPECT_TRUE(internal::IsPrimitive<long>::value);
  STATIC_EXPECT_TRUE(internal::IsPrimitive<unsigned long>::value);
  STATIC_EXPECT_TRUE(internal::IsPrimitive<long long>::value);
  STATIC_EXPECT_TRUE(internal::IsPrimitive<unsigned long long>::value);

  STATIC_EXPECT_TRUE(internal::IsPrimitive<sort::Bool>::value);
  STATIC_EXPECT_TRUE(internal::IsPrimitive<sort::Int>::value);
  STATIC_EXPECT_TRUE(internal::IsPrimitive<sort::Real>::value);

  STATIC_EXPECT_FALSE(internal::IsPrimitive<SomethingElse>::value);
  STATIC_EXPECT_FALSE(internal::IsPrimitive<float>::value);
  STATIC_EXPECT_FALSE(internal::IsPrimitive<double>::value);
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
  EXPECT_NE(&ubv_16, &internal::sort<uint16_t>());
  EXPECT_EQ(ubv_16, internal::sort<uint16_t>());

  EXPECT_EQ(&sbv_1, &bv_sort(true, 1));
  EXPECT_EQ(&ubv_1, &bv_sort(false, 1));
}

TEST(SmtTest, LiteralExpr)
{
  const LiteralExpr<long> e0(42L);

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

  const LiteralExpr<unsigned long> e1(42L);

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

  const LiteralExpr<sort::Int, char> e2('A');

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
  const Decl<long> d0("x");

  EXPECT_FALSE(d0.sort().is_bool());
  EXPECT_FALSE(d0.sort().is_int());
  EXPECT_FALSE(d0.sort().is_real());
  EXPECT_TRUE(d0.sort().is_bv());
  EXPECT_FALSE(d0.sort().is_array());
  EXPECT_FALSE(d0.sort().is_func());
  EXPECT_EQ(sizeof(long) * 8, d0.sort().bv_size());
  EXPECT_EQ("x", d0.symbol());

  const Decl<sort::Int> d1("y");

  EXPECT_FALSE(d1.sort().is_bool());
  EXPECT_TRUE(d1.sort().is_int());
  EXPECT_FALSE(d1.sort().is_real());
  EXPECT_FALSE(d1.sort().is_bv());
  EXPECT_FALSE(d1.sort().is_array());
  EXPECT_FALSE(d1.sort().is_func());
  EXPECT_EQ("y", d1.symbol());

  const Decl<sort::Array<sort::Int, sort::Bool>> d2("z");

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
  const Decl<sort::Func<long, sort::Int>> d0("f");

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

  const Decl<sort::Func<long, sort::Int, sort::Real>> d1("g");

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
  const Decl<sort::Func<long, sort::Int>> func_decl("f");
  const Term<long> arg_term(new LiteralExpr<long>(7L));

  const FuncAppExpr<long, sort::Int> app(func_decl, std::make_tuple(arg_term));

  EXPECT_EQ(FUNC_APP_EXPR_KIND, app.expr_kind());
  EXPECT_EQ(func_decl, app.func_decl());

  STATIC_EXPECT_TRUE((std::tuple_size<FuncAppExpr<long, sort::Int>::Args>::value == 1));
  const FuncAppExpr<long, sort::Int>::Args& arg_terms = app.args();
  Term<long> get0_arg_term(std::get<0>(arg_terms));
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
  const Decl<sort::Func<long, sort::Int, sort::Real>> func_decl("g");
  const Term<long> larg_term(new LiteralExpr<long>(7L));
  const Term<sort::Int> rarg_term(any<sort::Int>("x"));

  const FuncAppExpr<long, sort::Int, sort::Real> app(func_decl,
    std::make_tuple(larg_term, rarg_term));

  EXPECT_EQ(FUNC_APP_EXPR_KIND, app.expr_kind());
  EXPECT_EQ(func_decl, app.func_decl());

  STATIC_EXPECT_TRUE((std::tuple_size<FuncAppExpr<long, sort::Int, sort::Real>::Args>::value == 2));
  const FuncAppExpr<long, sort::Int, sort::Real>::Args& arg_terms = app.args();
  Term<long> get0_arg_term(std::get<0>(arg_terms));
  EXPECT_EQ(LITERAL_EXPR_KIND, get0_arg_term.expr_kind());
  Term<sort::Int> get1_arg_term(std::get<1>(arg_terms));
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
  const Decl<sort::Func<long, sort::Real>> bv_unary_func_decl("f");
  const Decl<sort::Func<sort::Int, sort::Real>> math_unary_func_decl("g");
  const Decl<sort::Func<long, sort::Int, sort::Real>> binary_func_decl("h");
  const Term<long> larg_term(new LiteralExpr<long>(7L));
  const Term<sort::Int> rarg_term(any<sort::Int>("x"));

  const Term<sort::Real> app_term0 = apply(binary_func_decl,
    std::make_tuple(larg_term, rarg_term));
  const Expr<sort::Real>& app0 = app_term0.ref();

  EXPECT_EQ(FUNC_APP_EXPR_KIND, app0.expr_kind());
  EXPECT_FALSE(app0.sort().is_bool());
  EXPECT_FALSE(app0.sort().is_int());
  EXPECT_TRUE(app0.sort().is_real());
  EXPECT_FALSE(app0.sort().is_bv());
  EXPECT_FALSE(app0.sort().is_func());
  EXPECT_FALSE(app0.sort().is_array());

  const Term<sort::Real> app_term1 = apply(bv_unary_func_decl, larg_term);
  const Expr<sort::Real>& app1 = app_term1.ref();

  EXPECT_EQ(FUNC_APP_EXPR_KIND, app1.expr_kind());
  EXPECT_FALSE(app1.sort().is_bool());
  EXPECT_FALSE(app1.sort().is_int());
  EXPECT_TRUE(app1.sort().is_real());
  EXPECT_FALSE(app1.sort().is_bv());
  EXPECT_FALSE(app1.sort().is_func());
  EXPECT_FALSE(app1.sort().is_array());

  const Term<sort::Real> app_term2 = apply(bv_unary_func_decl, 7L);
  const Expr<sort::Real>& app2 = app_term2.ref();

  EXPECT_EQ(FUNC_APP_EXPR_KIND, app2.expr_kind());
  EXPECT_FALSE(app2.sort().is_bool());
  EXPECT_FALSE(app2.sort().is_int());
  EXPECT_TRUE(app2.sort().is_real());
  EXPECT_FALSE(app2.sort().is_bv());
  EXPECT_FALSE(app2.sort().is_func());
  EXPECT_FALSE(app2.sort().is_array());

  const Term<sort::Real> app_term3 = apply(math_unary_func_decl, 7);
  const Expr<sort::Real>& app3 = app_term3.ref();

  EXPECT_EQ(FUNC_APP_EXPR_KIND, app3.expr_kind());
  EXPECT_FALSE(app3.sort().is_bool());
  EXPECT_FALSE(app3.sort().is_int());
  EXPECT_TRUE(app3.sort().is_real());
  EXPECT_FALSE(app3.sort().is_bv());
  EXPECT_FALSE(app3.sort().is_func());
  EXPECT_FALSE(app3.sort().is_array());

  const Term<sort::Real> app_term4 = apply(math_unary_func_decl, 7L);
  const Expr<sort::Real>& app4 = app_term4.ref();

  EXPECT_EQ(FUNC_APP_EXPR_KIND, app4.expr_kind());
  EXPECT_FALSE(app4.sort().is_bool());
  EXPECT_FALSE(app4.sort().is_int());
  EXPECT_TRUE(app4.sort().is_real());
  EXPECT_FALSE(app4.sort().is_bv());
  EXPECT_FALSE(app4.sort().is_func());
  EXPECT_FALSE(app4.sort().is_array());

  const Term<sort::Real> app_term5 = apply(binary_func_decl,
    larg_term, rarg_term);
  const Expr<sort::Real>& app5 = app_term5.ref();

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
  const Term<sort::Bool> ffexpr_term = literal<sort::Bool>(false);
  const LiteralExpr<sort::Bool, bool>& ffexpr =
    static_cast<const LiteralExpr<sort::Bool, bool>&>(ffexpr_term.ref());
  EXPECT_FALSE(ffexpr.literal());

  const Term<sort::Bool> ttexpr_term = literal<sort::Bool>(true);
  const LiteralExpr<sort::Bool, bool>& ttexpr =
    static_cast<const LiteralExpr<sort::Bool, bool>&>(ttexpr_term.ref());
  EXPECT_TRUE(ttexpr.literal());
}

TEST(SmtTest, Any)
{
  const Term<long> e0_term = any<long>("x");
  const ConstantExpr<long>& e0 = static_cast<const ConstantExpr<long>&>(e0_term.ref());
  const Decl<long>& d0 = e0.decl();

  EXPECT_FALSE(d0.sort().is_bool());
  EXPECT_FALSE(d0.sort().is_int());
  EXPECT_FALSE(d0.sort().is_real());
  EXPECT_TRUE(d0.sort().is_bv());
  EXPECT_FALSE(d0.sort().is_array());
  EXPECT_FALSE(d0.sort().is_func());
  EXPECT_EQ(sizeof(long) * 8, d0.sort().bv_size());
  EXPECT_EQ("x", d0.symbol());

  const Term<sort::Int> e1_term = any<sort::Int>("y");
  const ConstantExpr<sort::Int>& e1 =
    static_cast<const ConstantExpr<sort::Int>&>(e1_term.ref());
  const Decl<sort::Int>& d1 = e1.decl();

  EXPECT_FALSE(d1.sort().is_bool());
  EXPECT_TRUE(d1.sort().is_int());
  EXPECT_FALSE(d1.sort().is_real());
  EXPECT_FALSE(d1.sort().is_bv());
  EXPECT_FALSE(d1.sort().is_array());
  EXPECT_FALSE(d1.sort().is_func());
  EXPECT_EQ("y", d1.symbol());

  const Term<sort::Array<sort::Int, sort::Bool>> e2_term =
    any<sort::Array<sort::Int, sort::Bool>>("z");
  const ConstantExpr<sort::Array<sort::Int, sort::Bool>>& e2 =
    static_cast<const ConstantExpr<sort::Array<sort::Int, sort::Bool>>&>(e2_term.ref());
  const Decl<sort::Array<sort::Int, sort::Bool>>& d2 = e2.decl();

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
  const Term<long> e0_term(literal<long>(42L));
  const UnaryExpr<NOT, long> e1(e0_term);
  const Term<long> operand(e1.operand());

  EXPECT_EQ(UNARY_EXPR_KIND, e1.expr_kind());
  EXPECT_FALSE(e1.sort().is_bool());
  EXPECT_FALSE(e1.sort().is_int());
  EXPECT_FALSE(e1.sort().is_real());
  EXPECT_TRUE(e1.sort().is_bv());
  EXPECT_FALSE(e1.sort().is_array());
  EXPECT_FALSE(e1.sort().is_func());
  EXPECT_EQ(sizeof(long) * 8, e1.sort().bv_size());

  EXPECT_EQ(e0_term.addr(), operand.addr());

  const Term<sort::Bool> e2_term(literal<sort::Bool>(true));
  const UnaryExpr<LNOT, sort::Bool> e3(e2_term);

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
  const Term<long> e0_term(literal<long>(42L));
  const Term<long> e1_term(literal<long>(7L));
  const BinaryExpr<ADD, long> e2(e0_term, e1_term);
  const Term<long> loperand(e2.loperand());
  const Term<long> roperand(e2.roperand());

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

  const BinaryExpr<LSS, long, sort::Bool> e3(e0_term, e1_term);

  EXPECT_EQ(BINARY_EXPR_KIND, e3.expr_kind());
  EXPECT_TRUE(e3.sort().is_bool());
  EXPECT_FALSE(e3.sort().is_int());
  EXPECT_FALSE(e3.sort().is_real());
  EXPECT_FALSE(e3.sort().is_bv());
  EXPECT_FALSE(e3.sort().is_array());
  EXPECT_FALSE(e3.sort().is_func());

  const Term<sort::Bool> e4_term(literal<sort::Bool>(true));
  const Term<sort::Bool> e5_term(literal<sort::Bool>(false));
  const BinaryExpr<LAND, sort::Bool> e6(e4_term, e5_term);

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
  const Term<long> e0_term(literal<long>(42L));
  const Term<long> e1_term(literal<long>(7L));
  const Term<long> e2_term(any<long>("x"));

  Terms<long> operand_terms(3);
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
  const Term<long> e0_term(literal<long>(42L));
  const Term<long> e1_term(literal<long>(7L));
  const Term<long> e2_term(any<long>("x"));

  Terms<long> operand_terms(3);
  operand_terms.push_back(e0_term);
  operand_terms.push_back(e1_term);
  operand_terms.push_back(e2_term);

  const NaryExpr<ADD, long> e3(operand_terms);

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
  const Term<long> e0_term(literal<long>(42L));
  const Term<long> e1_term(literal<long>(7L));
  const Term<long> e2_term(any<long>("x"));

  Terms<long> operand_terms(3);
  operand_terms.push_back(e0_term);
  operand_terms.push_back(e1_term);
  operand_terms.push_back(e2_term);

  Term<sort::Bool> e3_term(distinct(std::move(operand_terms)));

  const NaryExpr<NEQ, long, sort::Bool>& e3 =
    static_cast<const NaryExpr<NEQ, long, sort::Bool>&>(e3_term.ref());
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
  const Term<sort::Int> init_term(literal<sort::Int>(7));
  const ConstArrayExpr<sort::Int, sort::Int> e0(init_term);

  EXPECT_EQ(CONST_ARRAY_EXPR_KIND, e0.expr_kind());
  EXPECT_EQ(init_term.addr(), e0.init().addr());
}

TEST(SmtTest, ArraySelectExpr)
{
  const Term<sort::Array<sort::Int, sort::Bool>> array_term(
    any<sort::Array<sort::Int, sort::Bool>>("x"));

  const Term<sort::Int> index_term(any<sort::Int>("i"));
  const ArraySelectExpr<sort::Int, sort::Bool> select(array_term, index_term);

  EXPECT_EQ(ARRAY_SELECT_EXPR_KIND, select.expr_kind());
  EXPECT_EQ(array_term.addr(), select.array().addr());
  EXPECT_EQ(index_term.addr(), select.index().addr());
}

TEST(SmtTest, ArrayStoreExpr)
{
  const Term<sort::Array<sort::Int, sort::Bool>> array_term(
    any<sort::Array<sort::Int, sort::Bool>>("x"));

  const Term<sort::Int> index_term(any<sort::Int>("i"));
  const Term<sort::Bool> value_term(literal<sort::Bool>(true));
  const ArrayStoreExpr<sort::Int, sort::Bool> store(array_term, index_term, value_term);

  EXPECT_EQ(ARRAY_STORE_EXPR_KIND, store.expr_kind());
  EXPECT_EQ(array_term.addr(), store.array().addr());
  EXPECT_EQ(index_term.addr(), store.index().addr());
  EXPECT_EQ(value_term.addr(), store.value().addr());
}

TEST(SmtTest, Select)
{
  const Term<sort::Array<sort::Int, sort::Bool>> array_term(
    any<sort::Array<sort::Int, sort::Bool>>("x"));

  const Term<sort::Int> index_term(any<sort::Int>("i"));
  const Term<sort::Bool> select_term = select(array_term, index_term);

  EXPECT_EQ(ARRAY_SELECT_EXPR_KIND, select_term.expr_kind());
}

TEST(SmtTest, Store)
{
  const Term<sort::Array<sort::Int, sort::Bool>> array_term(
    any<sort::Array<sort::Int, sort::Bool>>("x"));

  const Term<sort::Int> index_term(any<sort::Int>("i"));
  const Term<sort::Bool> value_term(literal<sort::Bool>(true));
  const Term<sort::Array<sort::Int, sort::Bool>> store_term = store(array_term, index_term, value_term);

  EXPECT_EQ(ARRAY_STORE_EXPR_KIND, store_term.expr_kind());
}

TEST(SmtTest, BvUnaryOperatorNOT)
{
  const Term<long> e0_term(any<long>("i"));
  const Term<long> e1_term(~e0_term);
  const UnaryExpr<NOT, long>& e2 =
    static_cast<const UnaryExpr<NOT, long>&>(e1_term.ref());

  EXPECT_EQ(UNARY_EXPR_KIND, e2.expr_kind());
  EXPECT_FALSE(e2.sort().is_bool());
  EXPECT_TRUE(e2.sort().is_bv());
  EXPECT_EQ(e0_term.addr(), e2.operand().addr());
}

TEST(SmtTest, BvUnaryOperatorSUB)
{
  const Term<long> e0_term(literal<long>(42L));
  const Term<long> e1_term(-e0_term);
  const UnaryExpr<SUB, long>& e2 =
    static_cast<const UnaryExpr<SUB, long>&>(e1_term.ref());

  EXPECT_EQ(UNARY_EXPR_KIND, e2.expr_kind());
  EXPECT_FALSE(e2.sort().is_bool());
  EXPECT_TRUE(e2.sort().is_bv());
  EXPECT_EQ(e0_term.addr(), e2.operand().addr());
}

#define SMT_TEST_BUILTIN_BV_BINARY_OP(op, opcode)                              \
  TEST(SmtTest, BvBinaryOperator##opcode)                                      \
  {                                                                            \
    const Term<long> e0_term(any<long>("i"));                                  \
    const Term<long> e1_term(literal<long>(42L));                              \
    const Term<long> e2_term(e0_term op e1_term);                              \
    const BinaryExpr<opcode, long>& e3 =                                       \
      static_cast<const BinaryExpr<opcode, long>&>(e2_term.ref());             \
                                                                               \
    EXPECT_EQ(BINARY_EXPR_KIND, e3.expr_kind());                               \
    EXPECT_FALSE(e3.sort().is_bool());                                         \
    EXPECT_TRUE(e3.sort().is_bv());                                            \
    EXPECT_TRUE(e3.sort().is_signed());                                        \
    EXPECT_EQ(e0_term.addr(), e3.loperand().addr());                           \
    EXPECT_EQ(e1_term.addr(), e3.roperand().addr());                           \
                                                                               \
    const Term<long> e4_term(e0_term op 7L);                                   \
    const BinaryExpr<opcode, long>& e5 =                                       \
      static_cast<const BinaryExpr<opcode, long>&>(e4_term.ref());             \
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
    const Term<long> e6_term(7L op e0_term);                                   \
    const BinaryExpr<opcode, long>& e7 =                                       \
      static_cast<const BinaryExpr<opcode, long>&>(e6_term.ref());             \
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
    const Term<long> e0_term(any<long>("i"));                                  \
    const Term<long> e1_term(literal<long>(42L));                              \
    const Term<sort::Bool> e2_term(e0_term op e1_term);                        \
    const BinaryExpr<opcode, long, sort::Bool>& e3 =                           \
      static_cast<const BinaryExpr<opcode, long, sort::Bool>&>(e2_term.ref()); \
                                                                               \
    EXPECT_EQ(BINARY_EXPR_KIND, e3.expr_kind());                               \
    EXPECT_TRUE(e3.sort().is_bool());                                          \
    EXPECT_FALSE(e3.sort().is_bv());                                           \
    EXPECT_EQ(e0_term.addr(), e3.loperand().addr());                           \
    EXPECT_EQ(e1_term.addr(), e3.roperand().addr());                           \
                                                                               \
    const Term<sort::Bool> e4_term(e0_term op 7L);                             \
    const BinaryExpr<opcode, long, sort::Bool>& e5 =                           \
      static_cast<const BinaryExpr<opcode, long, sort::Bool>&>(e4_term.ref()); \
    const LiteralExpr<long>& rexpr =                                           \
      static_cast<const LiteralExpr<long>&>(e5.roperand().ref());              \
                                                                               \
    EXPECT_EQ(BINARY_EXPR_KIND, e5.expr_kind());                               \
    EXPECT_TRUE(e5.sort().is_bool());                                          \
    EXPECT_FALSE(e5.sort().is_bv());                                           \
    EXPECT_EQ(e0_term.addr(), e5.loperand().addr());                           \
    EXPECT_EQ(7L, rexpr.literal());                                            \
                                                                               \
    const Term<sort::Bool> e6_term(7L op e0_term);                             \
    const BinaryExpr<opcode, long, sort::Bool>& e7 =                           \
      static_cast<const BinaryExpr<opcode, long, sort::Bool>&>(e6_term.ref()); \
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
    const Term<sort::Int> e0_term(any<sort::Int>("i"));                        \
    const Term<sort::Int> e1_term(literal<sort::Int>(42L));                    \
    const Term<sort::Int> e2_term(e0_term op e1_term);                         \
    const BinaryExpr<opcode, sort::Int>& e3 =                                  \
      static_cast<const BinaryExpr<opcode, sort::Int>&>(e2_term.ref());        \
                                                                               \
    EXPECT_EQ(BINARY_EXPR_KIND, e3.expr_kind());                               \
    EXPECT_FALSE(e3.sort().is_bool());                                         \
    EXPECT_TRUE(e3.sort().is_int());                                           \
    EXPECT_FALSE(e3.sort().is_bv());                                           \
    EXPECT_EQ(e0_term.addr(), e3.loperand().addr());                           \
    EXPECT_EQ(e1_term.addr(), e3.roperand().addr());                           \
                                                                               \
    const Term<sort::Int> e4_term(e0_term op 7L);                              \
    const BinaryExpr<opcode, sort::Int>& e5 =                                  \
      static_cast<const BinaryExpr<opcode, sort::Int>&>(e4_term.ref());        \
    const LiteralExpr<sort::Int, long>& rexpr =                                \
      static_cast<const LiteralExpr<sort::Int,long>&>(e5.roperand().ref());    \
                                                                               \
    EXPECT_EQ(BINARY_EXPR_KIND, e5.expr_kind());                               \
    EXPECT_FALSE(e5.sort().is_bool());                                         \
    EXPECT_TRUE(e5.sort().is_int());                                           \
    EXPECT_FALSE(e5.sort().is_bv());                                           \
    EXPECT_EQ(e0_term.addr(), e5.loperand().addr());                           \
    EXPECT_EQ(7L, rexpr.literal());                                            \
                                                                               \
    const Term<sort::Int> e6_term(7L op e0_term);                              \
    const BinaryExpr<opcode, sort::Int>& e7 =                                  \
      static_cast<const BinaryExpr<opcode, sort::Int>&>(e6_term.ref());        \
    const LiteralExpr<sort::Int, long>& lexpr =                                \
      static_cast<const LiteralExpr<sort::Int, long>&>(                        \
        e7.loperand().ref());                                                  \
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
    const Term<sort::Int> e0_term(any<sort::Int>("i"));                        \
    const Term<sort::Int> e1_term(literal<sort::Int>(42L));                    \
    const Term<sort::Bool> e2_term(e0_term op e1_term);                        \
    const BinaryExpr<opcode, sort::Int, sort::Bool>& e3 =                      \
      static_cast<const BinaryExpr<opcode, sort::Int, sort::Bool>&>(           \
        e2_term.ref());                                                        \
                                                                               \
    EXPECT_EQ(BINARY_EXPR_KIND, e3.expr_kind());                               \
    EXPECT_TRUE(e3.sort().is_bool());                                          \
    EXPECT_FALSE(e3.sort().is_int());                                          \
    EXPECT_FALSE(e3.sort().is_bv());                                           \
    EXPECT_EQ(e0_term.addr(), e3.loperand().addr());                           \
    EXPECT_EQ(e1_term.addr(), e3.roperand().addr());                           \
                                                                               \
    const Term<sort::Bool> e4_term(e0_term op 7L);                             \
    const BinaryExpr<opcode, sort::Int, sort::Bool>& e5 =                      \
      static_cast<const BinaryExpr<opcode, sort::Int, sort::Bool>&>(           \
        e4_term.ref());                                                        \
    const LiteralExpr<sort::Int, long>& rexpr =                                \
      static_cast<const LiteralExpr<sort::Int, long>&>(                        \
        e5.roperand().ref());                                                  \
                                                                               \
    EXPECT_EQ(BINARY_EXPR_KIND, e5.expr_kind());                               \
    EXPECT_TRUE(e5.sort().is_bool());                                          \
    EXPECT_FALSE(e5.sort().is_int());                                          \
    EXPECT_FALSE(e5.sort().is_bv());                                           \
    EXPECT_EQ(e0_term.addr(), e5.loperand().addr());                           \
    EXPECT_EQ(7L, rexpr.literal());                                            \
                                                                               \
    const Term<sort::Bool> e6_term(7L op e0_term);                             \
    const BinaryExpr<opcode, sort::Int, sort::Bool>& e7 =                      \
      static_cast<const BinaryExpr<opcode, sort::Int, sort::Bool>&>(           \
        e6_term.ref());                                                        \
    const LiteralExpr<sort::Int, long>& lexpr =                                \
      static_cast<const LiteralExpr<sort::Int, long>&>(                        \
        e7.loperand().ref());                                                  \
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
  const Term<sort::Bool> e0_term(any<sort::Bool>("x"));
  const Term<sort::Bool> e1_term(!e0_term);
  const UnaryExpr<LNOT, sort::Bool>& e2 =
    static_cast<const UnaryExpr<LNOT, sort::Bool>&>(e1_term.ref());

  EXPECT_EQ(UNARY_EXPR_KIND, e2.expr_kind());
  EXPECT_TRUE(e2.sort().is_bool());
  EXPECT_FALSE(e2.sort().is_bv());
  EXPECT_EQ(e0_term.addr(), e2.operand().addr());
}

#define SMT_TEST_BUILTIN_BOOL_BINARY_OP(op, opcode)                            \
  TEST(SmtTest, BoolBinaryOperator##opcode)                                    \
  {                                                                            \
    const Term<sort::Bool> e0_term(any<sort::Bool>("x"));                      \
    const Term<sort::Bool> e1_term(literal<sort::Bool>(true));                 \
    const Term<sort::Bool> e2_term(e0_term op e1_term);                        \
    const BinaryExpr<opcode, sort::Bool>& e3 =                                 \
      static_cast<const BinaryExpr<opcode, sort::Bool>&>(e2_term.ref());       \
                                                                               \
    EXPECT_EQ(BINARY_EXPR_KIND, e3.expr_kind());                               \
    EXPECT_TRUE(e3.sort().is_bool());                                          \
    EXPECT_FALSE(e3.sort().is_bv());                                           \
    EXPECT_EQ(e0_term.addr(), e3.loperand().addr());                           \
    EXPECT_EQ(e1_term.addr(), e3.roperand().addr());                           \
                                                                               \
    const Term<sort::Bool> e4_term(e0_term op true);                           \
    const BinaryExpr<opcode, sort::Bool>& e5 =                                 \
      static_cast<const BinaryExpr<opcode, sort::Bool>&>(e4_term.ref());       \
    const LiteralExpr<sort::Bool, bool>& rexpr =                               \
      static_cast<const LiteralExpr<sort::Bool, bool>&>(                       \
        e5.roperand().ref());                                                  \
                                                                               \
    EXPECT_EQ(BINARY_EXPR_KIND, e5.expr_kind());                               \
    EXPECT_TRUE(e5.sort().is_bool());                                          \
    EXPECT_FALSE(e5.sort().is_bv());                                           \
    EXPECT_EQ(e0_term.addr(), e5.loperand().addr());                           \
    EXPECT_TRUE(rexpr.literal());                                              \
                                                                               \
    const Term<sort::Bool> e6_term(false op e0_term);                          \
    const BinaryExpr<opcode, sort::Bool>& e7 =                                 \
      static_cast<const BinaryExpr<opcode, sort::Bool>&>(e6_term.ref());       \
    const LiteralExpr<sort::Bool, bool>& lexpr =                               \
      static_cast<const LiteralExpr<sort::Bool, bool>&>(                       \
        e7.loperand().ref());                                                  \
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
  const Term<sort::Bool> ttexpr_term = Identity<LAND, sort::Bool>::term;
  const LiteralExpr<sort::Bool, bool>& ttexpr =
    static_cast<const LiteralExpr<sort::Bool, bool>&>(ttexpr_term.ref());
  EXPECT_TRUE(ttexpr.literal());
}

TEST(SmtTest, Signedness)
{
  const Term<unsigned> e0_term(any<unsigned>("x"));
  const Term<unsigned> e1_term(e0_term + 1);
  const Term<unsigned> e2_term(2 + e0_term);

  EXPECT_TRUE(e1_term.sort().is_bv());
  EXPECT_FALSE(e1_term.sort().is_signed());
  EXPECT_TRUE(e2_term.sort().is_bv());
  EXPECT_FALSE(e2_term.sort().is_signed());
}

TEST(SmtTest, UnsafeExpr)
{
  constexpr size_t bv_long_size = sizeof(long) * 8;
  const Sort& bv_sort = internal::sort<long>();
  const Sort& func_sort = internal::sort<sort::Func<long, long>>();
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

  const Sort& array_sort = internal::sort<sort::Array<size_t, long>>();
  const Sort& index_sort = internal::sort<size_t>();
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
