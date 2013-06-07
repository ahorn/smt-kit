#include "gtest/gtest.h"

#include "smt.h"

using namespace smt;

#define STATIC_EXPECT_TRUE(condition) static_assert((condition), "")
#define STATIC_EXPECT_FALSE(condition) static_assert(!(condition), "")

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

TEST(SmtTest, ExprPtrFold)
{
  STATIC_EXPECT_TRUE((std::is_same<internal::ExprPtrFold<long, sort::Int>::Type,
    std::tuple<ExprPtr<long>, ExprPtr<sort::Int>>>::value));

  STATIC_EXPECT_TRUE((std::is_same<internal::ExprPtrFold<long, sort::Int, sort::Real>::Type,
    std::tuple<ExprPtr<long>, ExprPtr<sort::Int>, ExprPtr<sort::Real>>>::value));

  STATIC_EXPECT_TRUE((std::is_same<internal::ExprPtrFoldExceptLast<long, sort::Int>::Type,
    std::tuple<ExprPtr<long>>>::value));

  STATIC_EXPECT_TRUE((std::is_same<internal::ExprPtrFoldExceptLast<long, sort::Int, sort::Real>::Type,
    std::tuple<ExprPtr<long>, ExprPtr<sort::Int>>>::value));

  internal::ExprPtrFoldExceptLast<long, sort::Int>::Type(
    std::make_tuple(ExprPtr<long>(nullptr)));

  internal::ExprPtrFold<long, sort::Int>::Type(
    std::make_tuple(ExprPtr<long>(nullptr), ExprPtr<sort::Int>(nullptr)));
}

struct SomethingElse {};

TEST(SmtTest, IsBuiltin)
{
  STATIC_EXPECT_TRUE(IsBuiltin<bool>::value);
  STATIC_EXPECT_TRUE(IsBuiltin<char>::value);
  STATIC_EXPECT_TRUE(IsBuiltin<signed char>::value);
  STATIC_EXPECT_TRUE(IsBuiltin<unsigned char>::value);
  STATIC_EXPECT_TRUE(IsBuiltin<wchar_t>::value);
  STATIC_EXPECT_TRUE(IsBuiltin<char16_t>::value);
  STATIC_EXPECT_TRUE(IsBuiltin<char32_t>::value);
  STATIC_EXPECT_TRUE(IsBuiltin<short>::value);
  STATIC_EXPECT_TRUE(IsBuiltin<unsigned short>::value);
  STATIC_EXPECT_TRUE(IsBuiltin<int>::value);
  STATIC_EXPECT_TRUE(IsBuiltin<unsigned int>::value);
  STATIC_EXPECT_TRUE(IsBuiltin<long>::value);
  STATIC_EXPECT_TRUE(IsBuiltin<unsigned long>::value);
  STATIC_EXPECT_TRUE(IsBuiltin<long long>::value);
  STATIC_EXPECT_TRUE(IsBuiltin<unsigned long long>::value);

  STATIC_EXPECT_TRUE(IsBuiltin<sort::Bool>::value);
  STATIC_EXPECT_TRUE(IsBuiltin<sort::Int>::value);
  STATIC_EXPECT_TRUE(IsBuiltin<sort::Real>::value);

  STATIC_EXPECT_FALSE(IsBuiltin<SomethingElse>::value);
  STATIC_EXPECT_FALSE(IsBuiltin<float>::value);
  STATIC_EXPECT_FALSE(IsBuiltin<double>::value);
  STATIC_EXPECT_FALSE(IsBuiltin<int*>::value);
  STATIC_EXPECT_FALSE(IsBuiltin<void>::value);
}

TEST(SmtTest, Ok)
{
  STATIC_EXPECT_TRUE(OK == 0);
  STATIC_EXPECT_TRUE(OK == false);
}

TEST(SmtTest, BuiltinLiteralExpr)
{
  const BuiltinLiteralExpr<long> e0(42L);

  EXPECT_EQ(LITERAL_EXPR_KIND, e0.expr_kind());
  EXPECT_FALSE(e0.sort().is_bool());
  EXPECT_FALSE(e0.sort().is_int());
  EXPECT_FALSE(e0.sort().is_real());
  EXPECT_TRUE(e0.sort().is_bv());
  EXPECT_FALSE(e0.sort().is_array());
  EXPECT_FALSE(e0.sort().is_func());
  EXPECT_EQ(sizeof(long) * 8, e0.sort().bv_size());
  EXPECT_EQ(42L, e0.literal());

  const BuiltinLiteralExpr<sort::Int, char> e1('A');

  EXPECT_EQ(LITERAL_EXPR_KIND, e1.expr_kind());
  EXPECT_FALSE(e1.sort().is_bool());
  EXPECT_TRUE(e1.sort().is_int());
  EXPECT_FALSE(e1.sort().is_real());
  EXPECT_FALSE(e1.sort().is_bv());
  EXPECT_FALSE(e1.sort().is_array());
  EXPECT_FALSE(e1.sort().is_func());
  EXPECT_EQ('A', e1.literal());
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
  const ExprPtr<long> arg_ptr(new BuiltinLiteralExpr<long>(7L));

  const FuncAppExpr<long, sort::Int> app(func_decl, std::make_tuple(arg_ptr));

  EXPECT_EQ(FUNC_APP_EXPR_KIND, app.expr_kind());
  //EXPECT_EQ(func_decl, app.func_decl());

  STATIC_EXPECT_TRUE((std::tuple_size<FuncAppExpr<long, sort::Int>::DomainPtrs>::value == 1));
  const FuncAppExpr<long, sort::Int>::DomainPtrs& arg_ptrs = app.arg_ptrs();
  ExprPtr<long> get0_arg_ptr(std::get<0>(arg_ptrs));
  EXPECT_EQ(LITERAL_EXPR_KIND, get0_arg_ptr->expr_kind());

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
  const ExprPtr<long> larg_ptr(new BuiltinLiteralExpr<long>(7L));
  const ExprPtr<sort::Int> rarg_ptr(any<sort::Int>("x"));

  const FuncAppExpr<long, sort::Int, sort::Real> app(func_decl,
    std::make_tuple(larg_ptr, rarg_ptr));

  EXPECT_EQ(FUNC_APP_EXPR_KIND, app.expr_kind());
  //EXPECT_EQ(func_decl, app.func_decl());

  STATIC_EXPECT_TRUE((std::tuple_size<FuncAppExpr<long, sort::Int, sort::Real>::DomainPtrs>::value == 2));
  const FuncAppExpr<long, sort::Int, sort::Real>::DomainPtrs& arg_ptrs = app.arg_ptrs();
  ExprPtr<long> get0_arg_ptr(std::get<0>(arg_ptrs));
  EXPECT_EQ(LITERAL_EXPR_KIND, get0_arg_ptr->expr_kind());
  ExprPtr<sort::Int> get1_arg_ptr(std::get<1>(arg_ptrs));
  EXPECT_EQ(CONSTANT_EXPR_KIND, get1_arg_ptr->expr_kind());

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
  const ExprPtr<long> larg_ptr(new BuiltinLiteralExpr<long>(7L));
  const ExprPtr<sort::Int> rarg_ptr(any<sort::Int>("x"));

  const ExprPtr<sort::Real> app_ptr0 = apply(binary_func_decl,
    std::make_tuple(larg_ptr, rarg_ptr));
  const Expr<sort::Real>& app0 = *app_ptr0;

  EXPECT_EQ(FUNC_APP_EXPR_KIND, app0.expr_kind());
  EXPECT_FALSE(app0.sort().is_bool());
  EXPECT_FALSE(app0.sort().is_int());
  EXPECT_TRUE(app0.sort().is_real());
  EXPECT_FALSE(app0.sort().is_bv());
  EXPECT_FALSE(app0.sort().is_func());
  EXPECT_FALSE(app0.sort().is_array());

  const ExprPtr<sort::Real> app_ptr1 = apply(bv_unary_func_decl, larg_ptr);
  const Expr<sort::Real>& app1 = *app_ptr1;

  EXPECT_EQ(FUNC_APP_EXPR_KIND, app1.expr_kind());
  EXPECT_FALSE(app1.sort().is_bool());
  EXPECT_FALSE(app1.sort().is_int());
  EXPECT_TRUE(app1.sort().is_real());
  EXPECT_FALSE(app1.sort().is_bv());
  EXPECT_FALSE(app1.sort().is_func());
  EXPECT_FALSE(app1.sort().is_array());

  const ExprPtr<sort::Real> app_ptr2 = apply(bv_unary_func_decl, 7L);
  const Expr<sort::Real>& app2 = *app_ptr2;

  EXPECT_EQ(FUNC_APP_EXPR_KIND, app2.expr_kind());
  EXPECT_FALSE(app2.sort().is_bool());
  EXPECT_FALSE(app2.sort().is_int());
  EXPECT_TRUE(app2.sort().is_real());
  EXPECT_FALSE(app2.sort().is_bv());
  EXPECT_FALSE(app2.sort().is_func());
  EXPECT_FALSE(app2.sort().is_array());

  const ExprPtr<sort::Real> app_ptr3 = apply(math_unary_func_decl, 7);
  const Expr<sort::Real>& app3 = *app_ptr3;

  EXPECT_EQ(FUNC_APP_EXPR_KIND, app3.expr_kind());
  EXPECT_FALSE(app3.sort().is_bool());
  EXPECT_FALSE(app3.sort().is_int());
  EXPECT_TRUE(app3.sort().is_real());
  EXPECT_FALSE(app3.sort().is_bv());
  EXPECT_FALSE(app3.sort().is_func());
  EXPECT_FALSE(app3.sort().is_array());

  const ExprPtr<sort::Real> app_ptr4 = apply(math_unary_func_decl, 7L);
  const Expr<sort::Real>& app4 = *app_ptr4;

  EXPECT_EQ(FUNC_APP_EXPR_KIND, app4.expr_kind());
  EXPECT_FALSE(app4.sort().is_bool());
  EXPECT_FALSE(app4.sort().is_int());
  EXPECT_TRUE(app4.sort().is_real());
  EXPECT_FALSE(app4.sort().is_bv());
  EXPECT_FALSE(app4.sort().is_func());
  EXPECT_FALSE(app4.sort().is_array());

  const ExprPtr<sort::Real> app_ptr5 = apply(binary_func_decl,
    larg_ptr, rarg_ptr);
  const Expr<sort::Real>& app5 = *app_ptr5;

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
  const ExprPtr<sort::Bool> ffexpr_ptr = literal<sort::Bool>(false);
  const BuiltinLiteralExpr<sort::Bool, bool>& ffexpr =
    static_cast<const BuiltinLiteralExpr<sort::Bool, bool>&>(*ffexpr_ptr);
  EXPECT_FALSE(ffexpr.literal());

  const ExprPtr<sort::Bool> ttexpr_ptr = literal<sort::Bool>(true);
  const BuiltinLiteralExpr<sort::Bool, bool>& ttexpr =
    static_cast<const BuiltinLiteralExpr<sort::Bool, bool>&>(*ttexpr_ptr);
  EXPECT_TRUE(ttexpr.literal());
}

TEST(SmtTest, Any)
{
  const ExprPtr<long> e0_ptr = any<long>("x");
  const ConstantExpr<long>& e0 = static_cast<const ConstantExpr<long>&>(*e0_ptr);
  const Decl<long>& d0 = e0.decl();

  EXPECT_FALSE(d0.sort().is_bool());
  EXPECT_FALSE(d0.sort().is_int());
  EXPECT_FALSE(d0.sort().is_real());
  EXPECT_TRUE(d0.sort().is_bv());
  EXPECT_FALSE(d0.sort().is_array());
  EXPECT_FALSE(d0.sort().is_func());
  EXPECT_EQ(sizeof(long) * 8, d0.sort().bv_size());
  EXPECT_EQ("x", d0.symbol());

  const ExprPtr<sort::Int> e1_ptr = any<sort::Int>("y");
  const ConstantExpr<sort::Int>& e1 =
    static_cast<const ConstantExpr<sort::Int>&>(*e1_ptr);
  const Decl<sort::Int>& d1 = e1.decl();

  EXPECT_FALSE(d1.sort().is_bool());
  EXPECT_TRUE(d1.sort().is_int());
  EXPECT_FALSE(d1.sort().is_real());
  EXPECT_FALSE(d1.sort().is_bv());
  EXPECT_FALSE(d1.sort().is_array());
  EXPECT_FALSE(d1.sort().is_func());
  EXPECT_EQ("y", d1.symbol());

  const ExprPtr<sort::Array<sort::Int, sort::Bool>> e2_ptr =
    any<sort::Array<sort::Int, sort::Bool>>("z");
  const ConstantExpr<sort::Array<sort::Int, sort::Bool>>& e2 =
    static_cast<const ConstantExpr<sort::Array<sort::Int, sort::Bool>>&>(*e2_ptr);
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

/*
TEST(SmtTest, AnyFunc)
{
  const ExprPtr<sort::Func<long, sort::Int>> e0_ptr =
    any<sort::Func<long, sort::Int>>("f");
  const DeclExpr<sort::Func<long, sort::Int>>& e0 =
    static_cast<const DeclExpr<sort::Func<long, sort::Int>>&>(*e0_ptr);

  EXPECT_EQ(DECL_EXPR_KIND, e0.expr_kind());
  EXPECT_FALSE(e0.sort().is_bool());
  EXPECT_FALSE(e0.sort().is_int());
  EXPECT_FALSE(e0.sort().is_real());
  EXPECT_FALSE(e0.sort().is_bv());
  EXPECT_TRUE(e0.sort().is_func());
  EXPECT_FALSE(e0.sort().is_array());

  EXPECT_EQ(2, e0.sort().sorts_size());

  EXPECT_FALSE(e0.sort().sorts(0).is_bool());
  EXPECT_FALSE(e0.sort().sorts(0).is_int());
  EXPECT_FALSE(e0.sort().sorts(0).is_real());
  EXPECT_TRUE(e0.sort().sorts(0).is_bv());
  EXPECT_FALSE(e0.sort().sorts(0).is_func());
  EXPECT_FALSE(e0.sort().sorts(0).is_array());

  EXPECT_FALSE(e0.sort().sorts(1).is_bool());
  EXPECT_TRUE(e0.sort().sorts(1).is_int());
  EXPECT_FALSE(e0.sort().sorts(1).is_real());
  EXPECT_FALSE(e0.sort().sorts(1).is_bv());
  EXPECT_FALSE(e0.sort().sorts(1).is_array());
  EXPECT_FALSE(e0.sort().sorts(1).is_func());
}
*/

TEST(SmtTest, BuiltinUnaryExpr)
{
  const ExprPtr<long> e0_ptr(literal<long>(42L));
  const BuiltinUnaryExpr<NOT, long> e1(e0_ptr);
  const ExprPtr<long> operand_ptr(e1.operand_ptr());

  EXPECT_EQ(UNARY_EXPR_KIND, e1.expr_kind());
  EXPECT_FALSE(e1.sort().is_bool());
  EXPECT_FALSE(e1.sort().is_int());
  EXPECT_FALSE(e1.sort().is_real());
  EXPECT_TRUE(e1.sort().is_bv());
  EXPECT_FALSE(e1.sort().is_array());
  EXPECT_FALSE(e1.sort().is_func());
  EXPECT_EQ(sizeof(long) * 8, e1.sort().bv_size());

  EXPECT_EQ(e0_ptr.get(), operand_ptr.get());

  const ExprPtr<sort::Bool> e2_ptr(literal<sort::Bool>(true));
  const BuiltinUnaryExpr<LNOT, sort::Bool> e3(e2_ptr);

  EXPECT_EQ(UNARY_EXPR_KIND, e3.expr_kind());
  EXPECT_TRUE(e3.sort().is_bool());
  EXPECT_FALSE(e3.sort().is_int());
  EXPECT_FALSE(e3.sort().is_real());
  EXPECT_FALSE(e3.sort().is_bv());
  EXPECT_FALSE(e3.sort().is_array());
  EXPECT_FALSE(e3.sort().is_func());
}

TEST(SmtTest, BuiltinBinaryExpr)
{
  const ExprPtr<long> e0_ptr(literal<long>(42L));
  const ExprPtr<long> e1_ptr(literal<long>(7L));
  const BuiltinBinaryExpr<ADD, long> e2(e0_ptr, e1_ptr);
  const ExprPtr<long> loperand_ptr(e2.loperand_ptr());
  const ExprPtr<long> roperand_ptr(e2.roperand_ptr());

  EXPECT_EQ(BINARY_EXPR_KIND, e2.expr_kind());
  EXPECT_FALSE(e2.sort().is_bool());
  EXPECT_FALSE(e2.sort().is_int());
  EXPECT_FALSE(e2.sort().is_real());
  EXPECT_TRUE(e2.sort().is_bv());
  EXPECT_FALSE(e2.sort().is_array());
  EXPECT_FALSE(e2.sort().is_func());
  EXPECT_EQ(sizeof(long) * 8, e2.sort().bv_size());

  EXPECT_EQ(e0_ptr.get(), loperand_ptr.get());
  EXPECT_EQ(e1_ptr.get(), roperand_ptr.get());

  const BuiltinBinaryExpr<LSS, long, sort::Bool> e3(e0_ptr, e1_ptr);

  EXPECT_EQ(BINARY_EXPR_KIND, e3.expr_kind());
  EXPECT_TRUE(e3.sort().is_bool());
  EXPECT_FALSE(e3.sort().is_int());
  EXPECT_FALSE(e3.sort().is_real());
  EXPECT_FALSE(e3.sort().is_bv());
  EXPECT_FALSE(e3.sort().is_array());
  EXPECT_FALSE(e3.sort().is_func());

  const ExprPtr<sort::Bool> e4_ptr(literal<sort::Bool>(true));
  const ExprPtr<sort::Bool> e5_ptr(literal<sort::Bool>(false));
  const BuiltinBinaryExpr<LAND, sort::Bool> e6(e4_ptr, e5_ptr);

  EXPECT_EQ(BINARY_EXPR_KIND, e6.expr_kind());
  EXPECT_TRUE(e6.sort().is_bool());
  EXPECT_FALSE(e6.sort().is_int());
  EXPECT_FALSE(e6.sort().is_real());
  EXPECT_FALSE(e6.sort().is_bv());
  EXPECT_FALSE(e6.sort().is_array());
  EXPECT_FALSE(e6.sort().is_func());
}

TEST(SmtTest, ConstArrayExpr)
{
  const ExprPtr<sort::Int> init_ptr(literal<sort::Int>(7));
  const ConstArrayExpr<sort::Int, sort::Int> e0(init_ptr);

  EXPECT_EQ(CONST_ARRAY_EXPR_KIND, e0.expr_kind());
  EXPECT_EQ(init_ptr.get(), e0.init_ptr().get());
}

TEST(SmtTest, ArraySelectExpr)
{
  const ExprPtr<sort::Array<sort::Int, sort::Bool>> array_ptr(
    any<sort::Array<sort::Int, sort::Bool>>("x"));

  const ExprPtr<sort::Int> index_ptr(any<sort::Int>("i"));
  const ArraySelectExpr<sort::Int, sort::Bool> select(array_ptr, index_ptr);

  EXPECT_EQ(ARRAY_SELECT_EXPR_KIND, select.expr_kind());
  EXPECT_EQ(array_ptr.get(), select.array_ptr().get());
  EXPECT_EQ(index_ptr.get(), select.index_ptr().get());
}

TEST(SmtTest, ArrayStoreExpr)
{
  const ExprPtr<sort::Array<sort::Int, sort::Bool>> array_ptr(
    any<sort::Array<sort::Int, sort::Bool>>("x"));

  const ExprPtr<sort::Int> index_ptr(any<sort::Int>("i"));
  const ExprPtr<sort::Bool> value_ptr(literal<sort::Bool>(true));
  const ArrayStoreExpr<sort::Int, sort::Bool> store(array_ptr, index_ptr, value_ptr);

  EXPECT_EQ(ARRAY_STORE_EXPR_KIND, store.expr_kind());
  EXPECT_EQ(array_ptr.get(), store.array_ptr().get());
  EXPECT_EQ(index_ptr.get(), store.index_ptr().get());
  EXPECT_EQ(value_ptr.get(), store.value_ptr().get());
}

TEST(SmtTest, Select)
{
  const ExprPtr<sort::Array<sort::Int, sort::Bool>> array_ptr(
    any<sort::Array<sort::Int, sort::Bool>>("x"));

  const ExprPtr<sort::Int> index_ptr(any<sort::Int>("i"));
  const ExprPtr<sort::Bool> select_ptr = select(array_ptr, index_ptr);

  EXPECT_EQ(ARRAY_SELECT_EXPR_KIND, select_ptr->expr_kind());
}

TEST(SmtTest, Store)
{
  const ExprPtr<sort::Array<sort::Int, sort::Bool>> array_ptr(
    any<sort::Array<sort::Int, sort::Bool>>("x"));

  const ExprPtr<sort::Int> index_ptr(any<sort::Int>("i"));
  const ExprPtr<sort::Bool> value_ptr(literal<sort::Bool>(true));
  const ExprPtr<sort::Array<sort::Int, sort::Bool>> store_ptr = store(array_ptr, index_ptr, value_ptr);

  EXPECT_EQ(ARRAY_STORE_EXPR_KIND, store_ptr->expr_kind());
}

TEST(SmtTest, BvUnaryOperatorNOT)
{
  const ExprPtr<long> e0_ptr(any<long>("i"));
  const ExprPtr<long> e1_ptr(~e0_ptr);
  const BuiltinUnaryExpr<NOT, long>& e2 = static_cast<
    const BuiltinUnaryExpr<NOT, long>&>(*e1_ptr);

  EXPECT_EQ(UNARY_EXPR_KIND, e2.expr_kind());
  EXPECT_FALSE(e2.sort().is_bool());
  EXPECT_TRUE(e2.sort().is_bv());
  EXPECT_EQ(e0_ptr.get(), e2.operand_ptr().get());
}

TEST(SmtTest, BvUnaryOperatorSUB)
{
  const ExprPtr<long> e0_ptr(literal<long>(42L));
  const ExprPtr<long> e1_ptr(-e0_ptr);
  const BuiltinUnaryExpr<SUB, long>& e2 = static_cast<
    const BuiltinUnaryExpr<SUB, long>&>(*e1_ptr);

  EXPECT_EQ(UNARY_EXPR_KIND, e2.expr_kind());
  EXPECT_FALSE(e2.sort().is_bool());
  EXPECT_TRUE(e2.sort().is_bv());
  EXPECT_EQ(e0_ptr.get(), e2.operand_ptr().get());
}

#define SMT_TEST_BUILTIN_BV_BINARY_OP(op, opcode)                              \
  TEST(SmtTest, BvBinaryOperator##opcode)                                      \
  {                                                                            \
    const ExprPtr<long> e0_ptr(any<long>("i"));                                \
    const ExprPtr<long> e1_ptr(literal<long>(42L));                            \
    const ExprPtr<long> e2_ptr(e0_ptr op e1_ptr);                              \
    const BuiltinBinaryExpr<opcode, long>& e3 =                                \
      static_cast<const BuiltinBinaryExpr<opcode, long>&>(*e2_ptr);            \
                                                                               \
    EXPECT_EQ(BINARY_EXPR_KIND, e3.expr_kind());                               \
    EXPECT_FALSE(e3.sort().is_bool());                                         \
    EXPECT_TRUE(e3.sort().is_bv());                                            \
    EXPECT_EQ(e0_ptr.get(), e3.loperand_ptr().get());                          \
    EXPECT_EQ(e1_ptr.get(), e3.roperand_ptr().get());                          \
                                                                               \
    const ExprPtr<long> e4_ptr(e0_ptr op 7L);                                  \
    const BuiltinBinaryExpr<opcode, long>& e5 =                                \
      static_cast<const BuiltinBinaryExpr<opcode, long>&>(*e4_ptr);            \
    const BuiltinLiteralExpr<long>& rexpr =                                    \
      static_cast<const BuiltinLiteralExpr<long>&>(*e5.roperand_ptr());        \
                                                                               \
    EXPECT_EQ(BINARY_EXPR_KIND, e5.expr_kind());                               \
    EXPECT_FALSE(e5.sort().is_bool());                                         \
    EXPECT_TRUE(e5.sort().is_bv());                                            \
    EXPECT_EQ(e0_ptr.get(), e5.loperand_ptr().get());                          \
    EXPECT_EQ(7L, rexpr.literal());                                            \
                                                                               \
    const ExprPtr<long> e6_ptr(7L op e0_ptr);                                  \
    const BuiltinBinaryExpr<opcode, long>& e7 =                                \
      static_cast<const BuiltinBinaryExpr<opcode, long>&>(*e6_ptr);            \
    const BuiltinLiteralExpr<long>& lexpr =                                    \
      static_cast<const BuiltinLiteralExpr<long>&>(*e7.loperand_ptr());        \
                                                                               \
    EXPECT_EQ(BINARY_EXPR_KIND, e7.expr_kind());                               \
    EXPECT_FALSE(e7.sort().is_bool());                                         \
    EXPECT_TRUE(e7.sort().is_bv());                                            \
    EXPECT_EQ(7L, lexpr.literal());                                            \
    EXPECT_EQ(e0_ptr.get(), e7.roperand_ptr().get());                          \
  }                                                                            \

#define SMT_TEST_BUILTIN_BV_BINARY_REL(op, opcode)                             \
  TEST(SmtTest, BvBinaryRelation##opcode)                                      \
  {                                                                            \
    const ExprPtr<long> e0_ptr(any<long>("i"));                                \
    const ExprPtr<long> e1_ptr(literal<long>(42L));                            \
    const ExprPtr<sort::Bool> e2_ptr(e0_ptr op e1_ptr);                        \
    const BuiltinBinaryExpr<opcode, long, sort::Bool>& e3 =                    \
      static_cast<const BuiltinBinaryExpr<opcode, long, sort::Bool>&>(*e2_ptr);\
                                                                               \
    EXPECT_EQ(BINARY_EXPR_KIND, e3.expr_kind());                               \
    EXPECT_TRUE(e3.sort().is_bool());                                          \
    EXPECT_FALSE(e3.sort().is_bv());                                           \
    EXPECT_EQ(e0_ptr.get(), e3.loperand_ptr().get());                          \
    EXPECT_EQ(e1_ptr.get(), e3.roperand_ptr().get());                          \
                                                                               \
    const ExprPtr<sort::Bool> e4_ptr(e0_ptr op 7L);                            \
    const BuiltinBinaryExpr<opcode, long, sort::Bool>& e5 =                    \
      static_cast<const BuiltinBinaryExpr<opcode, long, sort::Bool>&>(*e4_ptr);\
    const BuiltinLiteralExpr<long>& rexpr =                                    \
      static_cast<const BuiltinLiteralExpr<long>&>(*e5.roperand_ptr());        \
                                                                               \
    EXPECT_EQ(BINARY_EXPR_KIND, e5.expr_kind());                               \
    EXPECT_TRUE(e5.sort().is_bool());                                          \
    EXPECT_FALSE(e5.sort().is_bv());                                           \
    EXPECT_EQ(e0_ptr.get(), e5.loperand_ptr().get());                          \
    EXPECT_EQ(7L, rexpr.literal());                                            \
                                                                               \
    const ExprPtr<sort::Bool> e6_ptr(7L op e0_ptr);                            \
    const BuiltinBinaryExpr<opcode, long, sort::Bool>& e7 =                    \
      static_cast<const BuiltinBinaryExpr<opcode, long, sort::Bool>&>(*e6_ptr);\
    const BuiltinLiteralExpr<long>& lexpr =                                    \
      static_cast<const BuiltinLiteralExpr<long>&>(*e7.loperand_ptr());        \
                                                                               \
    EXPECT_EQ(BINARY_EXPR_KIND, e7.expr_kind());                               \
    EXPECT_TRUE(e7.sort().is_bool());                                          \
    EXPECT_FALSE(e7.sort().is_bv());                                           \
    EXPECT_EQ(7L, lexpr.literal());                                            \
    EXPECT_EQ(e0_ptr.get(), e7.roperand_ptr().get());                          \
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
    const ExprPtr<sort::Int> e0_ptr(any<sort::Int>("i"));                      \
    const ExprPtr<sort::Int> e1_ptr(literal<sort::Int>(42L));                  \
    const ExprPtr<sort::Int> e2_ptr(e0_ptr op e1_ptr);                         \
    const BuiltinBinaryExpr<opcode, sort::Int>& e3 =                           \
      static_cast<const BuiltinBinaryExpr<opcode, sort::Int>&>(*e2_ptr);       \
                                                                               \
    EXPECT_EQ(BINARY_EXPR_KIND, e3.expr_kind());                               \
    EXPECT_FALSE(e3.sort().is_bool());                                         \
    EXPECT_TRUE(e3.sort().is_int());                                           \
    EXPECT_FALSE(e3.sort().is_bv());                                           \
    EXPECT_EQ(e0_ptr.get(), e3.loperand_ptr().get());                          \
    EXPECT_EQ(e1_ptr.get(), e3.roperand_ptr().get());                          \
                                                                               \
    const ExprPtr<sort::Int> e4_ptr(e0_ptr op 7L);                             \
    const BuiltinBinaryExpr<opcode, sort::Int>& e5 =                           \
      static_cast<const BuiltinBinaryExpr<opcode, sort::Int>&>(*e4_ptr);       \
    const BuiltinLiteralExpr<sort::Int, long>& rexpr = static_cast<            \
      const BuiltinLiteralExpr<sort::Int,long>&>(*e5.roperand_ptr());          \
                                                                               \
    EXPECT_EQ(BINARY_EXPR_KIND, e5.expr_kind());                               \
    EXPECT_FALSE(e5.sort().is_bool());                                         \
    EXPECT_TRUE(e5.sort().is_int());                                           \
    EXPECT_FALSE(e5.sort().is_bv());                                           \
    EXPECT_EQ(e0_ptr.get(), e5.loperand_ptr().get());                          \
    EXPECT_EQ(7L, rexpr.literal());                                            \
                                                                               \
    const ExprPtr<sort::Int> e6_ptr(7L op e0_ptr);                             \
    const BuiltinBinaryExpr<opcode, sort::Int>& e7 =                           \
      static_cast<const BuiltinBinaryExpr<opcode, sort::Int>&>(*e6_ptr);       \
    const BuiltinLiteralExpr<sort::Int, long>& lexpr = static_cast<            \
      const BuiltinLiteralExpr<sort::Int, long>&>(*e7.loperand_ptr());         \
                                                                               \
    EXPECT_EQ(BINARY_EXPR_KIND, e7.expr_kind());                               \
    EXPECT_FALSE(e7.sort().is_bool());                                         \
    EXPECT_TRUE(e7.sort().is_int());                                           \
    EXPECT_FALSE(e7.sort().is_bv());                                           \
    EXPECT_EQ(7L, lexpr.literal());                                            \
    EXPECT_EQ(e0_ptr.get(), e7.roperand_ptr().get());                          \
  }                                                                            \

#define SMT_TEST_BUILTIN_MATH_BINARY_REL(op, opcode)                           \
  TEST(SmtTest, MathBinaryRelation##opcode)                                    \
  {                                                                            \
    const ExprPtr<sort::Int> e0_ptr(any<sort::Int>("i"));                      \
    const ExprPtr<sort::Int> e1_ptr(literal<sort::Int>(42L));                  \
    const ExprPtr<sort::Bool> e2_ptr(e0_ptr op e1_ptr);                        \
    const BuiltinBinaryExpr<opcode, sort::Int, sort::Bool>& e3 = static_cast<  \
      const BuiltinBinaryExpr<opcode, sort::Int, sort::Bool>&>(*e2_ptr);       \
                                                                               \
    EXPECT_EQ(BINARY_EXPR_KIND, e3.expr_kind());                               \
    EXPECT_TRUE(e3.sort().is_bool());                                          \
    EXPECT_FALSE(e3.sort().is_int());                                          \
    EXPECT_FALSE(e3.sort().is_bv());                                           \
    EXPECT_EQ(e0_ptr.get(), e3.loperand_ptr().get());                          \
    EXPECT_EQ(e1_ptr.get(), e3.roperand_ptr().get());                          \
                                                                               \
    const ExprPtr<sort::Bool> e4_ptr(e0_ptr op 7L);                            \
    const BuiltinBinaryExpr<opcode, sort::Int, sort::Bool>& e5 = static_cast<  \
      const BuiltinBinaryExpr<opcode, sort::Int, sort::Bool>&>(*e4_ptr);       \
    const BuiltinLiteralExpr<sort::Int, long>& rexpr = static_cast<            \
      const BuiltinLiteralExpr<sort::Int, long>&>(*e5.roperand_ptr());         \
                                                                               \
    EXPECT_EQ(BINARY_EXPR_KIND, e5.expr_kind());                               \
    EXPECT_TRUE(e5.sort().is_bool());                                          \
    EXPECT_FALSE(e5.sort().is_int());                                          \
    EXPECT_FALSE(e5.sort().is_bv());                                           \
    EXPECT_EQ(e0_ptr.get(), e5.loperand_ptr().get());                          \
    EXPECT_EQ(7L, rexpr.literal());                                            \
                                                                               \
    const ExprPtr<sort::Bool> e6_ptr(7L op e0_ptr);                            \
    const BuiltinBinaryExpr<opcode, sort::Int, sort::Bool>& e7 = static_cast<  \
      const BuiltinBinaryExpr<opcode, sort::Int, sort::Bool>&>(*e6_ptr);       \
    const BuiltinLiteralExpr<sort::Int, long>& lexpr = static_cast<            \
      const BuiltinLiteralExpr<sort::Int, long>&>(*e7.loperand_ptr());         \
                                                                               \
    EXPECT_EQ(BINARY_EXPR_KIND, e7.expr_kind());                               \
    EXPECT_TRUE(e7.sort().is_bool());                                          \
    EXPECT_FALSE(e7.sort().is_int());                                          \
    EXPECT_FALSE(e7.sort().is_bv());                                           \
    EXPECT_EQ(7L, lexpr.literal());                                            \
    EXPECT_EQ(e0_ptr.get(), e7.roperand_ptr().get());                          \
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
  const ExprPtr<sort::Bool> e0_ptr(any<sort::Bool>("x"));
  const ExprPtr<sort::Bool> e1_ptr(!e0_ptr);
  const BuiltinUnaryExpr<LNOT, sort::Bool>& e2 = static_cast<
    const BuiltinUnaryExpr<LNOT, sort::Bool>&>(*e1_ptr);

  EXPECT_EQ(UNARY_EXPR_KIND, e2.expr_kind());
  EXPECT_TRUE(e2.sort().is_bool());
  EXPECT_FALSE(e2.sort().is_bv());
  EXPECT_EQ(e0_ptr.get(), e2.operand_ptr().get());
}

#define SMT_TEST_BUILTIN_BOOL_BINARY_OP(op, opcode)                            \
  TEST(SmtTest, BoolBinaryOperator##opcode)                                    \
  {                                                                            \
    const ExprPtr<sort::Bool> e0_ptr(any<sort::Bool>("x"));                    \
    const ExprPtr<sort::Bool> e1_ptr(literal<sort::Bool>(true));               \
    const ExprPtr<sort::Bool> e2_ptr(e0_ptr op e1_ptr);                        \
    const BuiltinBinaryExpr<opcode, sort::Bool>& e3 =                          \
      static_cast<const BuiltinBinaryExpr<opcode, sort::Bool>&>(*e2_ptr);      \
                                                                               \
    EXPECT_EQ(BINARY_EXPR_KIND, e3.expr_kind());                               \
    EXPECT_TRUE(e3.sort().is_bool());                                          \
    EXPECT_FALSE(e3.sort().is_bv());                                           \
    EXPECT_EQ(e0_ptr.get(), e3.loperand_ptr().get());                          \
    EXPECT_EQ(e1_ptr.get(), e3.roperand_ptr().get());                          \
                                                                               \
    const ExprPtr<sort::Bool> e4_ptr(e0_ptr op true);                          \
    const BuiltinBinaryExpr<opcode, sort::Bool>& e5 = static_cast<             \
      const BuiltinBinaryExpr<opcode, sort::Bool>&>(*e4_ptr);                  \
    const BuiltinLiteralExpr<sort::Bool, bool>& rexpr = static_cast<           \
      const BuiltinLiteralExpr<sort::Bool, bool>&>(*e5.roperand_ptr());        \
                                                                               \
    EXPECT_EQ(BINARY_EXPR_KIND, e5.expr_kind());                               \
    EXPECT_TRUE(e5.sort().is_bool());                                          \
    EXPECT_FALSE(e5.sort().is_bv());                                           \
    EXPECT_EQ(e0_ptr.get(), e5.loperand_ptr().get());                          \
    EXPECT_TRUE(rexpr.literal());                                              \
                                                                               \
    const ExprPtr<sort::Bool> e6_ptr(false op e0_ptr);                         \
    const BuiltinBinaryExpr<opcode, sort::Bool>& e7 =                          \
      static_cast<const BuiltinBinaryExpr<opcode, sort::Bool>&>(*e6_ptr);      \
    const BuiltinLiteralExpr<sort::Bool, bool>& lexpr = static_cast<           \
      const BuiltinLiteralExpr<sort::Bool, bool>&>(*e7.loperand_ptr());        \
                                                                               \
    EXPECT_EQ(BINARY_EXPR_KIND, e7.expr_kind());                               \
    EXPECT_TRUE(e7.sort().is_bool());                                          \
    EXPECT_FALSE(e7.sort().is_bv());                                           \
    EXPECT_FALSE(lexpr.literal());                                             \
    EXPECT_EQ(e0_ptr.get(), e7.roperand_ptr().get());                          \
  }                                                                            \

SMT_TEST_BUILTIN_BOOL_BINARY_OP(&&, LAND)
SMT_TEST_BUILTIN_BOOL_BINARY_OP(||, LOR)
SMT_TEST_BUILTIN_BOOL_BINARY_OP(==, EQL)
SMT_TEST_BUILTIN_BOOL_BINARY_OP(!=, NEQ)

TEST(SmtTest, Identity)
{
  const ExprPtr<sort::Bool> ttexpr_ptr = Identity<LAND, sort::Bool>::expr_ptr;
  const BuiltinLiteralExpr<sort::Bool, bool>& ttexpr =
    static_cast<const BuiltinLiteralExpr<sort::Bool, bool>&>(*ttexpr_ptr);
  EXPECT_TRUE(ttexpr.literal());
}
