#include "cka.h"
#include "gtest/gtest.h"
#include <cstddef>

using namespace cka;

TEST(CkaTest, EmptyPartialString)
{
  EXPECT_EQ(0, PartialString::empty().length());
}

TEST(CkaTest, InitPartialString)
{
  PartialString x{'x'};

  EXPECT_EQ('x', x.label_function().at(0));
  EXPECT_TRUE(x.strict_partial_order().empty());
  EXPECT_EQ(1, x.length());
  EXPECT_TRUE(x.incomparables().empty());
  EXPECT_EQ(1, x.minimals().size());
  EXPECT_EQ(0, x.minimals().front());
  EXPECT_EQ(1, x.maximals().size());
  EXPECT_EQ(0, x.maximals().front());
  EXPECT_EQ('x', x.min_label());
  EXPECT_EQ('x', x.max_label());
}

TEST(CkaTest, PartialStringConcurrentComposition)
{
  PartialString x{'x'};
  PartialString y{'y'};
  PartialString z{(x | y)};

  EXPECT_EQ(2, z.length());
  EXPECT_EQ(0, z.strict_partial_order().size());

  EXPECT_EQ('x', z.label_function().at(0));
  EXPECT_EQ('y', z.label_function().at(1));
  EXPECT_EQ(1, z.incomparables().size());
  EXPECT_EQ(2, z.minimals().size());
  EXPECT_EQ(0, z.minimals().front());
  EXPECT_EQ(1, z.minimals().back());
  EXPECT_EQ(2, z.maximals().size());
  EXPECT_EQ(0, z.maximals().front());
  EXPECT_EQ(1, z.maximals().back());
  EXPECT_EQ('x', z.min_label());
  EXPECT_EQ('y', z.max_label());
}

TEST(CkaTest, SequentialPartialStringComposition)
{
  PartialString x{'x'};
  PartialString y{'y'};
  PartialString z{(x , y)};

  EXPECT_EQ(2, z.length());
  EXPECT_EQ(1, z.strict_partial_order().size());
  EXPECT_EQ(0, z.strict_partial_order().front().first);
  EXPECT_EQ(1, z.strict_partial_order().front().second);

  EXPECT_EQ('x', z.label_function().at(0));
  EXPECT_EQ('y', z.label_function().at(1));
  EXPECT_TRUE(z.incomparables().empty());
  EXPECT_EQ(1, z.minimals().size());
  EXPECT_EQ(0, z.minimals().front());
  EXPECT_EQ(1, z.maximals().size());
  EXPECT_EQ(1, z.maximals().front());
  EXPECT_EQ('x', z.min_label());
  EXPECT_EQ('y', z.max_label());
}

TEST(CkaTest, PartialStringMinimals)
{
  PartialString x{'x'};
  EXPECT_EQ(1, x.minimals().size());
}

TEST(CkaTest, PartialStringMaximals)
{
  PartialString x{'x'};
  EXPECT_EQ(1, x.maximals().size());
}

TEST(CkaTest, PartialStringComposition)
{
  PartialString x{'x'};
  PartialString y{'y'};
  PartialString z{'z'};
  PartialString p{'p'};

  {
    p = (x | y);

    EXPECT_EQ(2, p.length());
    EXPECT_TRUE(p.strict_partial_order().empty());
    EXPECT_EQ(1, p.incomparables().size());

    PartialString::EventPairs::const_iterator citer;
    citer = p.incomparables().cbegin();

    EXPECT_EQ(0, citer->first);
    EXPECT_EQ(1, citer->second);

    ++citer;
    EXPECT_EQ(p.incomparables().cend(), citer);
  }

  {
    p = (x , y);

    EXPECT_EQ(2, p.length());
    EXPECT_EQ(1, p.strict_partial_order().size());

    PartialString::EventPairs::const_iterator citer;
    citer = p.strict_partial_order().cbegin();

    EXPECT_EQ(0, citer->first);
    EXPECT_EQ(1, citer->second);

    ++citer;
    EXPECT_EQ(p.strict_partial_order().cend(), citer);
  }

  {
    p = ((x | y) , z);

    EXPECT_EQ(3, p.length());
    EXPECT_EQ(2, p.strict_partial_order().size());

    PartialString::EventPairs::const_iterator citer;
    citer = p.strict_partial_order().cbegin();

    EXPECT_EQ(0, citer->first);
    EXPECT_EQ(2, citer->second);

    ++citer;
    EXPECT_EQ(1, citer->first);
    EXPECT_EQ(2, citer->second);

    ++citer;
    EXPECT_EQ(p.strict_partial_order().cend(), citer);
  }

  {
    p = (x , (y | z));

    EXPECT_EQ(3, p.length());
    EXPECT_EQ(2, p.strict_partial_order().size());

    PartialString::EventPairs::const_iterator citer;
    citer = p.strict_partial_order().cbegin();

    EXPECT_EQ(0, citer->first);
    EXPECT_EQ(1, citer->second);

    ++citer;
    EXPECT_EQ(0, citer->first);
    EXPECT_EQ(2, citer->second);

    ++citer;
    EXPECT_EQ(p.strict_partial_order().cend(), citer);
  }

  {
    p = ((x , y) | z);

    EXPECT_EQ(3, p.length());
    EXPECT_EQ(1, p.strict_partial_order().size());
    EXPECT_EQ(0, p.strict_partial_order().front().first);
    EXPECT_EQ(1, p.strict_partial_order().front().second);
  }

  {
    p = (x | (y , z));

    EXPECT_EQ(3, p.length());
    EXPECT_EQ(1, p.strict_partial_order().size());
    EXPECT_EQ(1, p.strict_partial_order().front().first);
    EXPECT_EQ(2, p.strict_partial_order().front().second);
  }

  {
    p = ((x , y) , z);

    EXPECT_EQ(3, p.length());
    EXPECT_EQ(2, p.strict_partial_order().size());

    PartialString::EventPairs::const_iterator citer;
    citer = p.strict_partial_order().cbegin();

    EXPECT_EQ(0, citer->first);
    EXPECT_EQ(1, citer->second);

    ++citer;
    EXPECT_EQ(1, citer->first);
    EXPECT_EQ(2, citer->second);

    ++citer;
    EXPECT_EQ(p.strict_partial_order().cend(), citer);
  }

  {
    p = (x , (y , z));

    EXPECT_EQ(3, p.length());
    EXPECT_EQ(2, p.strict_partial_order().size());

    PartialString::EventPairs::const_iterator citer;
    citer = p.strict_partial_order().cbegin();

    EXPECT_EQ(1, citer->first);
    EXPECT_EQ(2, citer->second);

    ++citer;
    EXPECT_EQ(0, citer->first);
    EXPECT_EQ(1, citer->second);

    ++citer;
    EXPECT_EQ(p.strict_partial_order().cend(), citer);
  }
}

TEST(CkaTest, PartialStringAssociativity)
{
  PartialString x{'x'};
  PartialString y{'y'};
  PartialString z{'z'};

  EXPECT_TRUE(((x | y) | z) <= (x | (y | z)));
  EXPECT_TRUE((x | (y | z)) <= ((x | y) | z));

  EXPECT_TRUE(((x , y) , z) <= (x , (y , z)));
  EXPECT_TRUE((x , (y , z)) <= ((x , y) , z));
}

TEST(CkaTest, PartialStringConcurrentCommutativity)
{
  PartialString x{'x'};
  PartialString y{'y'};

  EXPECT_TRUE((x | y) <= (y | x));
  EXPECT_TRUE((y | x) <= (x | y));
}

TEST(CkaTest, PartialStringExchangeLaw)
{
  PartialString u{'u'};
  PartialString v{'v'};
  PartialString x{'x'};
  PartialString y{'y'};

  PartialString p{((u | v) , (x | y))};
  PartialString q{((u , x) | (v , y))};

  EXPECT_TRUE(p <= q);
  EXPECT_FALSE(q <= p);
}

TEST(CkaTest, PartialStringRefineConcurrentAndSequential)
{
  PartialString x{'x'};
  PartialString y{'y'};
  PartialString z{'z'};

  EXPECT_FALSE(x <= (x , x));
  EXPECT_FALSE(x <= (x | x));

  EXPECT_FALSE((x | y) <= (x , y));
  EXPECT_TRUE((x , y) <= (x | y));

  EXPECT_FALSE((x | y | z) <= ((x , y) | z));
  EXPECT_TRUE(((x , y) | z) <= (x | y | z));

  EXPECT_FALSE(((x | y) , z) <= (x , y , z));
  EXPECT_TRUE((x , y , z) <= ((x | y) , z));
}

TEST(CkaTest, PartialStringComposite)
{
  PartialString x{'x'};
  PartialString y{'y'};
  PartialString z{'z'};

  PartialString p{(x | y)};
  PartialString q{(x , y)};

  EXPECT_TRUE((p , q) <= (p | q));
  EXPECT_TRUE((p , q) <= (q | p));
  EXPECT_TRUE((q , p) <= (p | q));
  EXPECT_TRUE((q , p) <= (q | p));

  EXPECT_FALSE((p | q) <= (p , q));
  EXPECT_FALSE((p | q) <= (q , p));
  EXPECT_FALSE((q | p) <= (p , q));
  EXPECT_FALSE((q | p) <= (q , p));
}

typedef std::vector<std::pair<PartialString, PartialString>> PartialStringTests;

TEST(CkaTest, PartialStringTransitiveReduction)
{
  PartialString x{'x'};
  PartialString y{'y'};
  PartialString z{'z'};

  EXPECT_TRUE((x , y , z) <= ((x , z) | y));
  EXPECT_TRUE((x , z , y) <= ((x , z) | y));
  EXPECT_TRUE(((x | y) , z) <= ((x , z) | y));
}

TEST(CkaTest, PartialStringYes)
{
  PartialString u{'u'};
  PartialString v{'v'};
  PartialString x{'x'};
  PartialString y{'y'};

  PartialStringTests tests = {
    {{ u }, { u }},
    {{ v }, { v }},
    {{ (v | v) }, { (v | v) }},
    {{ (v , v) | x }, { (v | v) | x }},
    {{ ((v , v) , x) }, { ((v | v) , x) }},
    {{ ((v , v) , x) }, { ((v | v) | x) }},
  };

  for (std::size_t n = 0; n < tests.size(); ++n)
    EXPECT_TRUE(tests[n].first <= tests[n].second);
}

TEST(CkaTest, PartialStringNo)
{
  PartialString u{'u'};
  PartialString v{'v'};
  PartialString x{'x'};
  PartialString y{'y'};

  PartialStringTests tests = {
    {{ (v | v) }, { (v , v) }},
    {{ ((v | v) | x) }, { ((v , v) | x) }},
    {{ ((v | v) , x) }, { (x | (v , v)) }},
  };

  for (std::size_t n = 0; n < tests.size(); ++n)
    EXPECT_FALSE(tests[n].first <= tests[n].second);
}

TEST(CkaTest, IncomparableMinimals)
{
  PartialString u{'u'};
  PartialString v{'v'};
  PartialString x{'x'};
  PartialString y{'y'};
  
  PartialString q{((u , x) | (v , y))};

  PartialString a{((x | q) , (x | y))};
  PartialString b{((x , x) | (q , y))};

  EXPECT_TRUE(a <= b);

  // "v ; x" in "a" but not in "b"
  EXPECT_FALSE(b <= a);
}

TEST(CkaTest, IncomparableMaximals)
{
  PartialString p{'p'};
  PartialString q{'q'};
  PartialString x{'x'};
  PartialString y{'y'};
  PartialString z{'z'};
  
  // "p | q" on LHS but "p ; q" on RHS
  EXPECT_FALSE(((x, p) | (y , z , q)) <= (x | (y , z , p , q)));
}

TEST(CkaTest, IncomparableSymmetric)
{
  PartialString x{'x'};
  PartialString y{'y'};
  PartialString p{((x | x) , y)};
  PartialString q{(y | (x , x))};

  EXPECT_FALSE(p <= q);
  EXPECT_FALSE(q <= p);
}

TEST(CkaTest, Equality)
{
  PartialString a{'x'};
  PartialString b{'x'};
  EXPECT_TRUE(a == b);

  PartialString c{(a , b)};
  PartialString d{(a , b)};
  EXPECT_TRUE(c == d);

  PartialString e{(a | b)};
  PartialString f{(a | b)};
  EXPECT_TRUE(e == f);
}

TEST(CkaTest, UintPower)
{
  EXPECT_EQ(5, internal::uint_pow(5, 1));
  EXPECT_EQ(25, internal::uint_pow(5, 2));
  EXPECT_EQ(125, internal::uint_pow(5, 3));
  EXPECT_EQ(625, internal::uint_pow(5, 4));
  EXPECT_EQ(3125, internal::uint_pow(5, 5));
}

TEST(CkaTest, ConvertPartialStringToProgram)
{
  PartialString x{'x'};
  PartialString y{'y'};
  PartialString p{((x | x) , y)};
  Program P{p};

  EXPECT_EQ(1, P.size());
  EXPECT_TRUE(p == P.partial_strings().front());
}

TEST(CkaTest, MovesPartialStringIntoProgram)
{
  PartialString x{'x'};
  PartialString y{'y'};
  Program P{((x | x) , y)};

  EXPECT_EQ(1, P.size());
  EXPECT_TRUE(((x | x) , y) == P.partial_strings().front());
}

TEST(CkaTest, ZeroProgram)
{
  EXPECT_EQ(0, Program::zero().size());
}

TEST(CkaTest, InitLazyProgram)
{
  Program X{'x'};
  Program Y{'y'};
  Program Z{'z'};

  EXPECT_EQ(1, X.size());
  EXPECT_EQ(1, Y.size());
  EXPECT_EQ(1, Z.size());

  PartialString x{'x'};
  PartialString y{'y'};
  PartialString z{'z'};

  // sanity check on `X`
  EXPECT_TRUE(x == X.partial_strings().front());

  Program P{X + (Y , Z)};
  EXPECT_EQ(2, P.size());

  internal::LazyProgram<','> Q{P};
  EXPECT_EQ(2, Q.size());

  internal::PartialStringIterator<','> iter{Q.partial_string_iterator()};
  EXPECT_TRUE(iter.has_next_partial_string());
  {
    PartialString p{iter.next_partial_string()};
    EXPECT_TRUE(x == p);
  }

  EXPECT_TRUE(iter.has_next_partial_string());
  {
    PartialString p{iter.next_partial_string()};
    EXPECT_TRUE(p == (y , z));
  }

  EXPECT_FALSE(iter.has_next_partial_string());

  // modify reference in `Q`
  P = P + (X | Z);
  EXPECT_EQ(3, P.size());
  EXPECT_EQ(3, Q.size());
}

TEST(CkaTest, BinaryLazyProgram)
{
  Program X{'x'};
  Program Y{'y'};
  Program Z{'z'};

  EXPECT_EQ(1, X.size());
  EXPECT_EQ(1, Y.size());
  EXPECT_EQ(1, Z.size());

  PartialString x{'x'};
  PartialString y{'y'};
  PartialString z{'z'};

  Program P{X + (Y , Z)};
  EXPECT_EQ(2, P.size());

  internal::LazyProgram<','> Q{P};
  Q.extend();

  EXPECT_EQ(4, Q.size());

  internal::PartialStringIterator<','> iter{Q.partial_string_iterator()};

  // 1
  EXPECT_TRUE(iter.has_next_partial_string());
  {
    PartialString p{iter.next_partial_string()};
    EXPECT_TRUE((x , x) == p);
  }

  // 2
  EXPECT_TRUE(iter.has_next_partial_string());
  {
    PartialString p{iter.next_partial_string()};
    EXPECT_TRUE(((y , z) , x) == p);
  }

  // 3
  EXPECT_TRUE(iter.has_next_partial_string());
  {
    PartialString p{iter.next_partial_string()};
    EXPECT_TRUE((x , (y , z)) == p);
  }

  // 4
  EXPECT_TRUE(iter.has_next_partial_string());
  {
    PartialString p{iter.next_partial_string()};
    EXPECT_TRUE(((y , z) , (y , z)) == p);
  }

  EXPECT_FALSE(iter.has_next_partial_string());
}

TEST(CkaTest, LazyProgramThree)
{
  Program X{'x'};
  Program Y{'y'};
  Program Z{'z'};

  EXPECT_EQ(1, X.size());
  EXPECT_EQ(1, Y.size());
  EXPECT_EQ(1, Z.size());

  PartialString x{'x'};
  PartialString y{'y'};
  PartialString z{'z'};

  Program P{X + (Y , Z)};
  EXPECT_EQ(2, P.size());

  internal::LazyProgram<','> Q{P};
  Q.extend();
  Q.extend();

  EXPECT_EQ(8, Q.size());

  internal::PartialStringIterator<','> iter{Q.partial_string_iterator()};

  // 1
  EXPECT_TRUE(iter.has_next_partial_string());
  {
    PartialString p{iter.next_partial_string()};
    EXPECT_TRUE(((x , x) , x) == p);
  }

  // 2
  EXPECT_TRUE(iter.has_next_partial_string());
  {
    PartialString p{iter.next_partial_string()};
    EXPECT_TRUE((((y , z) , x) , x) == p);
  }

  // 3
  EXPECT_TRUE(iter.has_next_partial_string());
  {
    PartialString p{iter.next_partial_string()};
    EXPECT_TRUE(((x , (y , z)) , x) == p);
  }

  // 4
  EXPECT_TRUE(iter.has_next_partial_string());
  {
    PartialString p{iter.next_partial_string()};
    EXPECT_TRUE((((y , z) , (y , z)) , x) == p);
  }

  // 5
  EXPECT_TRUE(iter.has_next_partial_string());
  {
    PartialString p{iter.next_partial_string()};
    EXPECT_TRUE(((x , x) , (y , z)) == p);
  }

  // 6
  EXPECT_TRUE(iter.has_next_partial_string());
  {
    PartialString p{iter.next_partial_string()};
    EXPECT_TRUE((((y , z) , x) , (y , z)) == p);
  }

  // 7
  EXPECT_TRUE(iter.has_next_partial_string());
  {
    PartialString p{iter.next_partial_string()};
    EXPECT_TRUE(((x , (y , z)) , (y , z)) == p);
  }

  // 8
  EXPECT_TRUE(iter.has_next_partial_string());
  {
    PartialString p{iter.next_partial_string()};
    EXPECT_TRUE((((y , z) , (y , z)) , (y , z)) == p);
  }

  EXPECT_FALSE(iter.has_next_partial_string());
}

TEST(CkaTest, LazyProgramSymbolic)
{
  Program X{'x'};
  Program Y{'y'};
  Program Z{'z'};

  Program P{X + (Y | Z) + (Z , X)};
  Program K{P};

  // Eager "P , P , P"
  K = (K , P);
  K = (K , P);

  // size of `P` (i.e. 3) cubed
  EXPECT_EQ(27, K.size());

  // Lazy "P , P , P"
  internal::LazyProgram<','> Q{P};
  Q.extend();
  Q.extend();

  EXPECT_EQ(K.size(), Q.size());

  Program R{Program::zero()};
  internal::PartialStringIterator<','> iter{Q.partial_string_iterator()};

  // `R` is the union of all partial strings in `Q`
  while (iter.has_next_partial_string())
    R = R + Program(iter.next_partial_string());

  EXPECT_EQ(K.size(), R.size());
  EXPECT_TRUE(K <= R);
  EXPECT_TRUE(R <= K);
}

TEST(CkaTest, ProgramAssociativity)
{
  Program X{'x'};
  Program Y{'y'};
  Program Z{'z'};

  EXPECT_TRUE(((X | Y) | Z) <= (X | (Y | Z)));
  EXPECT_TRUE((X | (Y | Z)) <= ((X | Y) | Z));

  EXPECT_TRUE(((X , Y) , Z) <= (X , (Y , Z)));
  EXPECT_TRUE((X , (Y , Z)) <= ((X , Y) , Z));

  EXPECT_TRUE(((X + Y) + Z) <= (X + (Y + Z)));
  EXPECT_TRUE((X + (Y + Z)) <= ((X + Y) + Z));
}

TEST(CkaTest, ProgramNondeterministicChoiceIdempotence)
{
  Program X{'x'};

  EXPECT_TRUE((X + X) <= X);
  EXPECT_TRUE(X <= (X + X));
}

TEST(CkaTest, ProgramNondeterministicChoiceCommutativity)
{
  Program X{'x'};
  Program Y{'y'};

  EXPECT_TRUE((X + Y) <= (Y + X));
  EXPECT_TRUE((Y + X) <= (X + Y));
}

TEST(CkaTest, ProgramNondeterministicChoiceIdentity)
{
  Program X{'x'};

  EXPECT_TRUE((X + Program::zero()) <= X);
  EXPECT_TRUE(X <= (X + Program::zero()));
}

TEST(CkaTest, ProgramSequentialAnnihilator)
{
  Program X{'x'};

  EXPECT_TRUE((X , Program::zero()) <= Program::zero());
  EXPECT_TRUE(Program::zero() <= (X , Program::zero()));
}

TEST(CkaTest, ProgramConcurrentCommutativity)
{
  Program X{'x'};
  Program Y{'y'};

  EXPECT_TRUE((X | Y) <= (Y | X));
  EXPECT_TRUE((Y | X) <= (X | Y));
}

TEST(CkaTest, ProgramExchangeLaw)
{
  Program U{'u'};
  Program V{'v'};
  Program X{'x'};
  Program Y{'y'};
  
  Program P{((U | V) , (X | Y))};
  Program Q{((U , X) | (V , Y))};

  EXPECT_TRUE(P <= Q);
  EXPECT_FALSE(Q <= P);

  // composites to test more throughly the encoder
  Program S{(X | Y)};
  Program T{(X , Y)};

  Program A{((P | Q) , (S | T))};
  Program B{((P , S) | (Q , T))};

  EXPECT_TRUE(A <= B);
  EXPECT_FALSE(B <= A);
}

TEST(CkaTest, WeakSequentialConsistency)
{
  Program X{'x'};
  Program Y{'y'};

  EXPECT_TRUE(((X , Y) + (Y , X)) <= (X | Y));
  EXPECT_FALSE((X | Y) <= ((X , Y) + (Y , X)));
}

TEST(CkaTest, LfpProgram)
{
  Program X{'x'};

  LfpProgram<'|'> P{lfp<'|'>(X)};
  LfpProgram<','> Q{lfp<','>(X)};
}

TEST(CkaTest, Reductions)
{
  Program X{'x'};
  Program Y{'y'};

  LfpProgram<','> lfpX{lfp<','>(X)};
  LfpProgram<','> lfpXX{lfp<','>((X , X))};
  LfpProgram<','> lfpXXX{lfp<','>((X , X , X))};
  LfpProgram<','> lfpXXXX{lfp<','>((X , X , X , X))};

  EXPECT_TRUE(lfpXX <= lfpX);
  EXPECT_TRUE(lfpXXX <= lfpX);
  EXPECT_TRUE(lfpXXXX <= lfpXX);
  EXPECT_FALSE(lfpX <= lfpXX);
  EXPECT_FALSE(lfpX <= lfpXXX);
  EXPECT_FALSE(lfpXX <= lfpXXX);
  EXPECT_FALSE(lfpX <= lfpXXX);
  EXPECT_FALSE(lfpX <= lfpXXXX);
  EXPECT_FALSE(lfpXX <= lfpXXXX);

  // `lfpXXX` contains "x ; x ; x" but `lfpXX`
  // contains only even number of "x".
  EXPECT_FALSE(lfpXXX <= lfpXX);

  // `lfpXX` contains "x ; x" but `lfpXXX` contains
  // "x" only in multiple of threes.
  EXPECT_FALSE(lfpXX <= lfpXXX);

  Program U{'u'};
  Program V{'v'};
  
  Program P{((U | V) , (X | Y))};
  Program Q{((U , X) | (V , Y))};

  EXPECT_TRUE(lfp<','>(P) <= lfp<','>(Q));
  EXPECT_TRUE(lfp<'|'>(P) <= lfp<'|'>(Q));
  EXPECT_FALSE(lfp<','>((P , P)) <= lfp<','>((Q , Q  , Q , Q)));
  EXPECT_TRUE(lfp<','>((P , P , P , P)) <= lfp<','>((Q , Q)));
}

TEST(CkaTest, ProgramSequentialLeftDistributivity)
{
  Program X{'x'};
  Program Y{'y'};
  Program Z{'z'};

  Program P{((X + Y) , Z)};
  Program Q{((X , Z) + (Y , Z))};

  EXPECT_TRUE(P <= Q);
  EXPECT_TRUE(Q <= P);
}

TEST(CkaTest, ProgramSequentialRightDistributivity)
{
  Program X{'x'};
  Program Y{'y'};
  Program Z{'z'};

  Program P{(Z , (X + Y))};
  Program Q{((Z , X) + (Z , Y))};

  EXPECT_TRUE(P <= Q);
  EXPECT_TRUE(Q <= P);
}

TEST(CkaTest, ProgramConcurrentLeftDistributivity)
{
  Program X{'x'};
  Program Y{'y'};
  Program Z{'z'};

  Program P{((X + Y) | Z)};
  Program Q{((X | Z) + (Y | Z))};
  Program R{((Z | X) + (Z | Y))};

  EXPECT_TRUE(P <= Q);
  EXPECT_TRUE(Q <= P);

  EXPECT_TRUE(P <= R);
  EXPECT_TRUE(R <= P);
}

TEST(CkaTest, ProgramConcurrentRightDistributivity)
{
  Program X{'x'};
  Program Y{'y'};
  Program Z{'z'};

  Program P{(Z | (X + Y))};
  Program Q{((X | Z) + (Y | Z))};
  Program R{((Z | X) + (Z | Y))};

  EXPECT_TRUE(P <= Q);
  EXPECT_TRUE(Q <= P);

  EXPECT_TRUE(P <= R);
  EXPECT_TRUE(R <= P);
}

TEST(CkaTest, ProgramSequentialNondistributivity)
{
  Program X{'x'};
  Program Y{'y'};
  Program Z{'z'};

  Program P{((X , Y) + Z)};
  Program Q{((X + Z) , (Y + Z))};

  // `P` contains "z" but `Q` contains only partial strings
  // whose length is at most two.
  EXPECT_FALSE(P <= Q);

  // `Q` contains "x , z" (among others) but `P` does not,
  // even partial strings such as "x | z".
  EXPECT_FALSE(Q <= P);
}

TEST(CkaTest, ProgramConcurentNondistributivity)
{
  Program X{'x'};
  Program Y{'y'};
  Program Z{'z'};

  Program P{((X | Y) + Z)};
  Program Q{((X + Z) | (Y + Z))};

  // `P` contains "z" but `Q` contains only partial strings
  // whose length is at most two.
  EXPECT_FALSE(P <= Q);

  // `Q` contains "x | z" (among others) but `P` does not.
  EXPECT_FALSE(Q <= P);
}

/*
 * For illustrative purposes, we also used Seed to randomly
 * generate tests according to the context-free grammar shown
 * in "test/CKA-benchmark.xml".
 *
 * This tool can be downloaded from the following URL:
 *
 *   http://igm.univ-mlv.fr/~nicaud/seed/
 *
 * To generate a random CKA expression of length `N`, run
 * the following command:
 *
 *   java -jar seed.jar test/CKA-benchmark.xml N -text
 *
 * The accompanying tool paper is published in ICST'2011:
 *
 *   Heam, P.C.; Nicaud, C., "Seed: An Easy-to-Use Random Generator
 *   of Recursive Data Structures for Testing," Software Testing,
 *   2011 IEEE Fourth International Conference on Verification and
 *   Validation (ICST), pp.60,69, 21-25 March 2011
 *
 * Benchmarks can be generated by running "generate_cka_benchmarks.sh".
 */

TEST(CkaTest, Random)
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

  EXPECT_FALSE((lfp<'|'>((U | Z)) <= lfp<'|'>(((E | (Q + W)) | (E | (W , (I + (M + X))))))));
  EXPECT_FALSE((lfp<','>((L , (G | ((A , D) | (P | ((L , J) + (Y | Q))))))) <= lfp<','>(W)));
  EXPECT_FALSE((lfp<','>(Q) <= lfp<','>((Z , ((H , (I , A)) | (D | (D + (V + (S | U)))))))));
  EXPECT_FALSE((lfp<'|'>((Y + (R + (J , (A , I))))) <= lfp<'|'>(((Z , P) | (J , (T + Y))))));
  EXPECT_FALSE((lfp<'|'>((W + (F | T))) <= lfp<'|'>((W , (C + (F , (G | (X + (Z | O)))))))));

  EXPECT_FALSE((lfp<'|'>(L) <= lfp<'|'>(((Z , (N | V)) | (Q | (J , (M + (S + (A | ((W | M) , (E , (N , (Y + L)))))))))))));
  EXPECT_FALSE((lfp<','>((A + ((C , (C | S)) | ((Q , (Z + (U , B))) + (A | ((Y | V) , (O , Z))))))) <= lfp<','>((S | R))));
  EXPECT_FALSE((lfp<'|'>(((G | A) + (W , (B | (G + (D + (C + ((W | (L + J)) + (V , (K + (D | S))))))))))) <= lfp<'|'>(H)));
  EXPECT_FALSE((lfp<','>(((O + V) + (G , H))) <= lfp<','>((A | (W , ((V | N) , ((B + C) , (J , (W , (F + (S | Q)))))))))));
  EXPECT_FALSE((lfp<'|'>(((D , (G , D)) , (V + ((Z | (W | O)) , (Q | (H + (Z , P))))))) <= lfp<'|'>((T + (P , (C | O))))));
}
