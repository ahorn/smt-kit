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

/// `PartialString::empty()::min_label()` is undefined
TEST(CkaTest, EmptyPartialAndExtremalLabel)
{
  PartialString x{'x'};
  PartialString y{(PartialString::empty() | x)};
  PartialString z{(x | PartialString::empty())};

  EXPECT_EQ('x', y.min_label());
  EXPECT_EQ('x', y.max_label());

  EXPECT_EQ('x', z.min_label());
  EXPECT_EQ('x', z.max_label());
}

TEST(CkaTest, PartialStringNumberOfEventsWithLabel)
{
  PartialString x{'x'};
  PartialString y{'y'};
  PartialString z{'z'};

  EXPECT_EQ(1, x.number_of_events_with_label('x'));
  EXPECT_EQ(0, x.number_of_events_with_label('y'));
  EXPECT_EQ(0, x.number_of_events_with_label('z'));

  EXPECT_EQ(0, y.number_of_events_with_label('x'));
  EXPECT_EQ(1, y.number_of_events_with_label('y'));
  EXPECT_EQ(0, y.number_of_events_with_label('z'));

  EXPECT_EQ(0, z.number_of_events_with_label('x'));
  EXPECT_EQ(0, z.number_of_events_with_label('y'));
  EXPECT_EQ(1, z.number_of_events_with_label('z'));

  PartialString u{(x | z)};
  {
    EXPECT_EQ(0, u.number_of_events_with_label('x' - '\1'));
    EXPECT_EQ(1, u.number_of_events_with_label('x'));
    EXPECT_EQ(0, u.number_of_events_with_label('y'));
    EXPECT_EQ(1, u.number_of_events_with_label('z'));
    EXPECT_EQ(0, u.number_of_events_with_label('z' + '\1'));
  }

  PartialString v{(u , y)};
  {
    EXPECT_EQ(0, v.number_of_events_with_label('x' - '\1'));
    EXPECT_EQ(1, v.number_of_events_with_label('x'));
    EXPECT_EQ(1, v.number_of_events_with_label('y'));
    EXPECT_EQ(1, v.number_of_events_with_label('z'));
    EXPECT_EQ(0, v.number_of_events_with_label('z' + '\1'));
  }

  PartialString v_prime{(v , y)};
  {
    EXPECT_EQ(0, v_prime.number_of_events_with_label('x' - '\1'));
    EXPECT_EQ(1, v_prime.number_of_events_with_label('x'));
    EXPECT_EQ(2, v_prime.number_of_events_with_label('y'));
    EXPECT_EQ(1, v_prime.number_of_events_with_label('z'));
    EXPECT_EQ(0, v_prime.number_of_events_with_label('z' + '\1'));
  }
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

  EXPECT_FALSE((y , z , x) <= ((x , y) | z));
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
 * Consider the following program consistent of two threads T1 and T2:
 * "[a] := 0; [b] := 0; (T1 || T2)" where 'a' and 'b' are shared memory
 * addresses, T1 = "[a] := 1; r1 := [b]" and T2 = "[b] := 1; r2 := [a]".
 *
 * Let P0 = "[a] := 0",
 *     P1 = "[b] := 0",
 *     P2 = "[a] := 1",
 *     P3 = "r1 := [b]",
 *     P4 = "[b] := 1",
 *     P5 = "r2 := [a]".
 *
 * In this test we ignore that "P2" is sequenced-before "P3",
 * and "P4" is sequenced-before "P5". In that case, we aim to
 * explicitly consider the potential executions of the system.
 */
TEST(CkaTest, HandwrittenProgramIgnorePerThreadOrdering)
{
  Program P0{'\0'};
  Program P1{'\1'};
  Program P2{'\2'};
  Program P3{'\3'};
  Program P4{'\4'};
  Program P5{'\5'};

  Program A{(P0 , P5 , P2) + (P0 , P2 , P5) + (P2 , P5 , P0) + (P2 , P0 , P5)};
  Program B{(P1 , P3 , P4) + (P1 , P4 , P3) + (P4 , P3 , P1) + (P4 , P1 , P3)};

  Program R0{((P0 , P1 ) , ((P2 , P3) | (P4 , P5)))};
  Program R1{(P0 | P1 | ((P2 , P3) | (P4 , P5)))};
  Program R2{(P0 | P1 | P2 | P3 | P4 | P5)};

  // For example, "P2" and "P3" are ordered in "R0" and "R1", but not in "A | B".
  EXPECT_FALSE((A | B) <= R0);
  EXPECT_FALSE((A | B) <= R1);

  EXPECT_TRUE((A | B) <= R2);

  // Since "P0" and "P2", as well as "P1" and "P4" can commute,
  // let's simplify "A" and "B (note that this would violate
  // the write serialization axiom which stipulates that all
  // writes to the same memory address are totally ordered).
  Program C{(P0 , P5 , P2) + ((P0 | P2) , P5) + (P2 , P5 , P0)};
  Program D{(P1 , P3 , P4) + ((P1 | P4) , P3) + (P4 , P3 , P1)};

  // For example, "P2" and "P3" are ordered in "R0" and "R1", but not in "C | D".
  EXPECT_FALSE((C | D) <= R0);
  EXPECT_FALSE((C | D) <= R1);

  EXPECT_TRUE((C | D) <= R2);
}

/*
 * Consider the following program consistent of two threads T1 and T2:
 * "[a] := 0; [b] := 0; (T1 || T2)" where 'a' and 'b' are shared memory
 * addresses, T1 = "[a] := 1; r1 := [b]" and T2 = "[b] := 1; r2 := [a]".
 *
 * Let P0 = "[a] := 0",
 *     P1 = "[b] := 0",
 *     P2 = "[a] := 1",
 *     P3 = "r1 := [b]",
 *     P4 = "[b] := 1",
 *     P5 = "r2 := [a]".
 *
 * Sequential consistency can be achieved by requiring that
 * "P2" is sequenced-before "P3", and "P4" is sequenced-before "P5".
 */
TEST(CkaTest, HandwrittenProgramSequentialConsistency)
{
  Program P0{'\0'};
  Program P1{'\1'};
  Program P2{'\2'};
  Program P3{'\3'};
  Program P4{'\4'};
  Program P5{'\5'};

  Program A{((P2 | P4) , (P3 | P5))};
  Program B{(P4 , P5 , P2 , P3)};
  Program C{(P2 , P3 , P4 , P5)};

  Program P{((P0 | P1) , (A + B + C))};
  Program Q{((P0 , P1) , (A + B + C))};

  Program R0{((P0 , P1 ) , ((P2 , P3) | (P4 , P5)))};
  Program R1{(P0 | P1 | ((P2 , P3) | (P4 , P5)))};
  Program R2{(P0 | P1 | P2 | P3 | P4 | P5)};

  // Both "P0" and "P1" are unsequenced in "P", but sequenced in "R0"
  EXPECT_FALSE(P <= R0);

  EXPECT_TRUE(P <= R1);
  EXPECT_TRUE(P <= R2);

  EXPECT_TRUE(Q <= R0);
  EXPECT_TRUE(Q <= R1);
  EXPECT_TRUE(Q <= R2);
}

TEST(CkaTest, ForAllThereExists)
{
  Program P{'\1'};
  Program Q{'\2'};

  EXPECT_TRUE(P <= (P + Q));
}

// Since we only keep the transitive reduction of a strict partial
// ordering, it would be wrong to optimize refinement checks based
// on the number of partial order constraints.
TEST(CkaTest, NumberOfStrictPartialOrderConstraints)
{
  PartialString u{'\0'};
  PartialString v{'\1'};
  PartialString x{'\2'};
  PartialString y{'\3'};

  // size of strict partial ordering on the LHS: 3
  // size of strict partial ordering on the RHS: 4
  EXPECT_TRUE((v , y , x , u) <= (v , (x | y) , u));
}

TEST(CkaTest, LfpWithNondeterministicChoice)
{
  Program P{'\1'};
  Program Q{'\2'};

  EXPECT_TRUE(lfp<','>(P) <= lfp<','>(P + Q));
  EXPECT_TRUE(lfp<','>(Q) <= lfp<','>(P + Q));
}

TEST(CkaTest, ResetPartialStringIterator)
{
  Program A{'\0'};
  Program B{'\1'};
  Program C{'\2'};
  Program D{'\3'};
  Program E{'\6'};
  Program F{'\7'};

  Program G{(((E | F), (C | D)) + (E, B, F, C) + (F, A, E, D) +
              (E, (C | B), F) + (A, (E | F), D) + ((A | B), (E | F)))};

  Program H{(F, E, C, D)};
  Program I{(E, B, C, F)};
  Program J{(F, E, C, D)};

  EXPECT_TRUE(lfp<','>(H + I + J) <= lfp<','>(G));
}

TEST(CkaTest, Statistics)
{
  Program P{'\0'};
  Program Q{'\1'};

  Refinement r;

  EXPECT_EQ(0, r.number_of_checks());
  EXPECT_EQ(0, r.number_of_shortcuts());
  EXPECT_EQ(0, r.number_of_solver_calls());

  EXPECT_FALSE(r.check(P, (P , Q)));

  EXPECT_EQ(1, r.number_of_checks());
  EXPECT_EQ(1, r.number_of_shortcuts());
  EXPECT_EQ(0, r.number_of_solver_calls());

  EXPECT_TRUE(r.check((P | Q), (Q | P)));

  EXPECT_EQ(2, r.number_of_checks());
  EXPECT_EQ(1, r.number_of_shortcuts());
  EXPECT_EQ(1, r.number_of_solver_calls());
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

TEST(CkaTest, MemoryLabels)
{
  constexpr memory::Address a = 0U;
  constexpr memory::Address b = 1U;

  EXPECT_EQ(0U, memory::relaxed_store_label(a));
  EXPECT_EQ(1U, memory::relaxed_load_label(a));
  EXPECT_EQ(43U, memory::assert_eq_label(a, '\5'));
  EXPECT_EQ(47U, memory::assert_neq_label(a, '\5'));

  EXPECT_TRUE(std::numeric_limits<memory::Byte>::max() < memory::relaxed_store_label(b));
  EXPECT_TRUE(std::numeric_limits<memory::Byte>::max() < memory::relaxed_store_label(b, '\1'));
  EXPECT_TRUE(std::numeric_limits<memory::Byte>::max() < memory::relaxed_load_label(b));
  EXPECT_TRUE(std::numeric_limits<memory::Byte>::max() < memory::assert_eq_label(b, '\5'));
  EXPECT_TRUE(std::numeric_limits<memory::Byte>::max() < memory::assert_neq_label(b, '\5'));
}

TEST(CkaTest, MemoryStoreAddressMonotonicity)
{
  constexpr memory::Address a = 0U;
  constexpr memory::Address b = 1U;
  constexpr memory::Address c = 2U;

  EXPECT_TRUE(memory::relaxed_store_label(a, '\0') < memory::relaxed_store_label(b));
  EXPECT_TRUE(memory::relaxed_store_label(a, '\1') < memory::relaxed_store_label(b));
  EXPECT_TRUE(memory::relaxed_store_label(a, '\2') < memory::relaxed_store_label(b));
  EXPECT_TRUE(memory::relaxed_store_label(a, '\3') < memory::relaxed_store_label(b));

  EXPECT_TRUE(memory::relaxed_store_label(b, '\0') < memory::relaxed_store_label(c));
  EXPECT_TRUE(memory::relaxed_store_label(b, '\1') < memory::relaxed_store_label(c));
  EXPECT_TRUE(memory::relaxed_store_label(b, '\2') < memory::relaxed_store_label(c));
  EXPECT_TRUE(memory::relaxed_store_label(b, '\3') < memory::relaxed_store_label(c));
}

TEST(CkaTest, IsShared)
{
  EXPECT_TRUE(memory::is_shared(memory::relaxed_store_label(0U), memory::relaxed_load_label(0U)));
  EXPECT_TRUE(memory::is_shared(memory::relaxed_store_label(1U), memory::relaxed_load_label(1U)));
  EXPECT_TRUE(memory::is_shared(memory::relaxed_store_label(2U), memory::relaxed_load_label(2U)));

  EXPECT_FALSE(memory::is_shared(memory::relaxed_store_label(0U), memory::relaxed_load_label(1U)));
  EXPECT_FALSE(memory::is_shared(memory::relaxed_store_label(1U), memory::relaxed_load_label(3U)));
  EXPECT_FALSE(memory::is_shared(memory::relaxed_store_label(2U), memory::relaxed_load_label(4U)));
  EXPECT_FALSE(memory::is_shared(memory::relaxed_store_label(3U), memory::relaxed_load_label(4U)));
  EXPECT_FALSE(memory::is_shared(memory::relaxed_store_label(4U), memory::relaxed_load_label(5U)));
}

TEST(CkaTest, IsStore)
{
  constexpr memory::Address a = 0U;
  constexpr memory::Address b = 1U;
  constexpr memory::Address c = 2U;

  EXPECT_TRUE(memory::is_relaxed_store(memory::relaxed_store_label(a)));
  EXPECT_TRUE(memory::is_relaxed_store(memory::relaxed_store_label(b)));
  EXPECT_TRUE(memory::is_relaxed_store(memory::relaxed_store_label(c)));

  EXPECT_FALSE(memory::is_relaxed_store(memory::relaxed_load_label(a)));
  EXPECT_FALSE(memory::is_relaxed_store(memory::relaxed_load_label(b)));
  EXPECT_FALSE(memory::is_relaxed_store(memory::relaxed_load_label(c)));
}

TEST(CkaTest, IsLoad)
{
  constexpr memory::Address a = 0U;
  constexpr memory::Address b = 1U;
  constexpr memory::Address c = 2U;

  EXPECT_TRUE(memory::is_relaxed_load(memory::relaxed_load_label(a)));
  EXPECT_TRUE(memory::is_relaxed_load(memory::relaxed_load_label(b)));
  EXPECT_TRUE(memory::is_relaxed_load(memory::relaxed_load_label(c)));

  EXPECT_FALSE(memory::is_relaxed_load(memory::relaxed_store_label(a)));
  EXPECT_FALSE(memory::is_relaxed_load(memory::relaxed_store_label(b)));
  EXPECT_FALSE(memory::is_relaxed_load(memory::relaxed_store_label(c)));
}

TEST(CkaTest, IsAssert)
{
  constexpr memory::Address a = 0U;
  constexpr memory::Address b = 1U;
  constexpr memory::Address c = 2U;

  EXPECT_TRUE(memory::is_assert(memory::assert_eq_label(a, '\0')));
  EXPECT_TRUE(memory::is_assert(memory::assert_eq_label(b, '\0')));
  EXPECT_TRUE(memory::is_assert(memory::assert_eq_label(c, '\0')));

  EXPECT_TRUE(memory::is_assert(memory::assert_eq_label(a, '\1')));
  EXPECT_TRUE(memory::is_assert(memory::assert_eq_label(b, '\1')));
  EXPECT_TRUE(memory::is_assert(memory::assert_eq_label(c, '\1')));

  EXPECT_TRUE(memory::is_assert(memory::assert_eq_label(a, '\2')));
  EXPECT_TRUE(memory::is_assert(memory::assert_eq_label(b, '\2')));
  EXPECT_TRUE(memory::is_assert(memory::assert_eq_label(c, '\2')));

  EXPECT_TRUE(memory::is_assert(memory::assert_eq_label(a, '\3')));
  EXPECT_TRUE(memory::is_assert(memory::assert_eq_label(b, '\3')));
  EXPECT_TRUE(memory::is_assert(memory::assert_eq_label(c, '\3')));

  EXPECT_TRUE(memory::is_assert(memory::assert_eq_label(a, '\4')));
  EXPECT_TRUE(memory::is_assert(memory::assert_eq_label(b, '\4')));
  EXPECT_TRUE(memory::is_assert(memory::assert_eq_label(c, '\4')));

  EXPECT_TRUE(memory::is_assert(memory::assert_eq_label(a, '\5')));
  EXPECT_TRUE(memory::is_assert(memory::assert_eq_label(b, '\5')));
  EXPECT_TRUE(memory::is_assert(memory::assert_eq_label(c, '\5')));

  EXPECT_TRUE(memory::is_assert_eq(memory::assert_eq_label(a, '\0')));
  EXPECT_TRUE(memory::is_assert_eq(memory::assert_eq_label(b, '\0')));
  EXPECT_TRUE(memory::is_assert_eq(memory::assert_eq_label(c, '\0')));

  EXPECT_TRUE(memory::is_assert_eq(memory::assert_eq_label(a, '\1')));
  EXPECT_TRUE(memory::is_assert_eq(memory::assert_eq_label(b, '\1')));
  EXPECT_TRUE(memory::is_assert_eq(memory::assert_eq_label(c, '\1')));

  EXPECT_TRUE(memory::is_assert_eq(memory::assert_eq_label(a, '\2')));
  EXPECT_TRUE(memory::is_assert_eq(memory::assert_eq_label(b, '\2')));
  EXPECT_TRUE(memory::is_assert_eq(memory::assert_eq_label(c, '\2')));

  EXPECT_TRUE(memory::is_assert_eq(memory::assert_eq_label(a, '\3')));
  EXPECT_TRUE(memory::is_assert_eq(memory::assert_eq_label(b, '\3')));
  EXPECT_TRUE(memory::is_assert_eq(memory::assert_eq_label(c, '\3')));

  EXPECT_TRUE(memory::is_assert_eq(memory::assert_eq_label(a, '\4')));
  EXPECT_TRUE(memory::is_assert_eq(memory::assert_eq_label(b, '\4')));
  EXPECT_TRUE(memory::is_assert_eq(memory::assert_eq_label(c, '\4')));

  EXPECT_TRUE(memory::is_assert_eq(memory::assert_eq_label(a, '\5')));
  EXPECT_TRUE(memory::is_assert_eq(memory::assert_eq_label(b, '\5')));
  EXPECT_TRUE(memory::is_assert_eq(memory::assert_eq_label(c, '\5')));

  // negation
  EXPECT_TRUE(memory::is_assert(memory::assert_neq_label(a, '\0')));
  EXPECT_TRUE(memory::is_assert(memory::assert_neq_label(b, '\0')));
  EXPECT_TRUE(memory::is_assert(memory::assert_neq_label(c, '\0')));

  EXPECT_TRUE(memory::is_assert(memory::assert_neq_label(a, '\1')));
  EXPECT_TRUE(memory::is_assert(memory::assert_neq_label(b, '\1')));
  EXPECT_TRUE(memory::is_assert(memory::assert_neq_label(c, '\1')));

  EXPECT_TRUE(memory::is_assert(memory::assert_neq_label(a, '\2')));
  EXPECT_TRUE(memory::is_assert(memory::assert_neq_label(b, '\2')));
  EXPECT_TRUE(memory::is_assert(memory::assert_neq_label(c, '\2')));

  EXPECT_TRUE(memory::is_assert(memory::assert_neq_label(a, '\3')));
  EXPECT_TRUE(memory::is_assert(memory::assert_neq_label(b, '\3')));
  EXPECT_TRUE(memory::is_assert(memory::assert_neq_label(c, '\3')));

  EXPECT_TRUE(memory::is_assert(memory::assert_neq_label(a, '\4')));
  EXPECT_TRUE(memory::is_assert(memory::assert_neq_label(b, '\4')));
  EXPECT_TRUE(memory::is_assert(memory::assert_neq_label(c, '\4')));

  EXPECT_TRUE(memory::is_assert(memory::assert_neq_label(a, '\5')));
  EXPECT_TRUE(memory::is_assert(memory::assert_neq_label(b, '\5')));
  EXPECT_TRUE(memory::is_assert(memory::assert_neq_label(c, '\5')));

  EXPECT_TRUE(memory::is_assert_neq(memory::assert_neq_label(a, '\0')));
  EXPECT_TRUE(memory::is_assert_neq(memory::assert_neq_label(b, '\0')));
  EXPECT_TRUE(memory::is_assert_neq(memory::assert_neq_label(c, '\0')));

  EXPECT_TRUE(memory::is_assert_neq(memory::assert_neq_label(a, '\1')));
  EXPECT_TRUE(memory::is_assert_neq(memory::assert_neq_label(b, '\1')));
  EXPECT_TRUE(memory::is_assert_neq(memory::assert_neq_label(c, '\1')));

  EXPECT_TRUE(memory::is_assert_neq(memory::assert_neq_label(a, '\2')));
  EXPECT_TRUE(memory::is_assert_neq(memory::assert_neq_label(b, '\2')));
  EXPECT_TRUE(memory::is_assert_neq(memory::assert_neq_label(c, '\2')));

  EXPECT_TRUE(memory::is_assert_neq(memory::assert_neq_label(a, '\3')));
  EXPECT_TRUE(memory::is_assert_neq(memory::assert_neq_label(b, '\3')));
  EXPECT_TRUE(memory::is_assert_neq(memory::assert_neq_label(c, '\3')));

  EXPECT_TRUE(memory::is_assert_neq(memory::assert_neq_label(a, '\4')));
  EXPECT_TRUE(memory::is_assert_neq(memory::assert_neq_label(b, '\4')));
  EXPECT_TRUE(memory::is_assert_neq(memory::assert_neq_label(c, '\4')));

  EXPECT_TRUE(memory::is_assert_neq(memory::assert_neq_label(a, '\5')));
  EXPECT_TRUE(memory::is_assert_neq(memory::assert_neq_label(b, '\5')));
  EXPECT_TRUE(memory::is_assert_neq(memory::assert_neq_label(c, '\5')));
}

TEST(CkaTest, StoredByte)
{
  constexpr memory::Address a = 0U;
  constexpr memory::Address b = 1U;
  constexpr memory::Address c = 2U;

  EXPECT_EQ('\1', memory::byte(memory::relaxed_store_label(a, '\1')));
  EXPECT_EQ('\2', memory::byte(memory::relaxed_store_label(a, '\2')));
  EXPECT_EQ('\3', memory::byte(memory::relaxed_store_label(a, '\3')));
  EXPECT_EQ('\4', memory::byte(memory::relaxed_store_label(a, '\4')));
  EXPECT_EQ('\5', memory::byte(memory::relaxed_store_label(a, '\5')));

  EXPECT_EQ('\1', memory::byte(memory::relaxed_store_label(b, '\1')));
  EXPECT_EQ('\2', memory::byte(memory::relaxed_store_label(b, '\2')));
  EXPECT_EQ('\3', memory::byte(memory::relaxed_store_label(b, '\3')));
  EXPECT_EQ('\4', memory::byte(memory::relaxed_store_label(b, '\4')));
  EXPECT_EQ('\5', memory::byte(memory::relaxed_store_label(b, '\5')));

  EXPECT_EQ('\1', memory::byte(memory::relaxed_store_label(c, '\1')));
  EXPECT_EQ('\2', memory::byte(memory::relaxed_store_label(c, '\2')));
  EXPECT_EQ('\3', memory::byte(memory::relaxed_store_label(c, '\3')));
  EXPECT_EQ('\4', memory::byte(memory::relaxed_store_label(c, '\4')));
  EXPECT_EQ('\5', memory::byte(memory::relaxed_store_label(c, '\5')));
}

TEST(CkaTest, AssertedEqualByte)
{
  constexpr memory::Address a = 0U;
  constexpr memory::Address b = 1U;
  constexpr memory::Address c = 2U;

  EXPECT_EQ('\1', memory::byte(memory::assert_eq_label(a, '\1')));
  EXPECT_EQ('\2', memory::byte(memory::assert_eq_label(a, '\2')));
  EXPECT_EQ('\3', memory::byte(memory::assert_eq_label(a, '\3')));
  EXPECT_EQ('\4', memory::byte(memory::assert_eq_label(a, '\4')));
  EXPECT_EQ('\5', memory::byte(memory::assert_eq_label(a, '\5')));

  EXPECT_EQ('\1', memory::byte(memory::assert_eq_label(b, '\1')));
  EXPECT_EQ('\2', memory::byte(memory::assert_eq_label(b, '\2')));
  EXPECT_EQ('\3', memory::byte(memory::assert_eq_label(b, '\3')));
  EXPECT_EQ('\4', memory::byte(memory::assert_eq_label(b, '\4')));
  EXPECT_EQ('\5', memory::byte(memory::assert_eq_label(b, '\5')));

  EXPECT_EQ('\1', memory::byte(memory::assert_eq_label(c, '\1')));
  EXPECT_EQ('\2', memory::byte(memory::assert_eq_label(c, '\2')));
  EXPECT_EQ('\3', memory::byte(memory::assert_eq_label(c, '\3')));
  EXPECT_EQ('\4', memory::byte(memory::assert_eq_label(c, '\4')));
  EXPECT_EQ('\5', memory::byte(memory::assert_eq_label(c, '\5')));
}

TEST(CkaTest, AssertedNotEqualByte)
{
  constexpr memory::Address a = 0U;
  constexpr memory::Address b = 1U;
  constexpr memory::Address c = 2U;

  EXPECT_EQ('\1', memory::byte(memory::assert_neq_label(a, '\1')));
  EXPECT_EQ('\2', memory::byte(memory::assert_neq_label(a, '\2')));
  EXPECT_EQ('\3', memory::byte(memory::assert_neq_label(a, '\3')));
  EXPECT_EQ('\4', memory::byte(memory::assert_neq_label(a, '\4')));
  EXPECT_EQ('\5', memory::byte(memory::assert_neq_label(a, '\5')));

  EXPECT_EQ('\1', memory::byte(memory::assert_neq_label(b, '\1')));
  EXPECT_EQ('\2', memory::byte(memory::assert_neq_label(b, '\2')));
  EXPECT_EQ('\3', memory::byte(memory::assert_neq_label(b, '\3')));
  EXPECT_EQ('\4', memory::byte(memory::assert_neq_label(b, '\4')));
  EXPECT_EQ('\5', memory::byte(memory::assert_neq_label(b, '\5')));

  EXPECT_EQ('\1', memory::byte(memory::assert_neq_label(c, '\1')));
  EXPECT_EQ('\2', memory::byte(memory::assert_neq_label(c, '\2')));
  EXPECT_EQ('\3', memory::byte(memory::assert_neq_label(c, '\3')));
  EXPECT_EQ('\4', memory::byte(memory::assert_neq_label(c, '\4')));
  EXPECT_EQ('\5', memory::byte(memory::assert_neq_label(c, '\5')));
}

TEST(CkaTest, MemoryAddress)
{
  constexpr memory::Address a = 0U;
  constexpr memory::Address b = 1U;
  constexpr memory::Address c = 2U;
  constexpr memory::Address d = 3U;

  EXPECT_EQ(0U, memory::address(memory::relaxed_load_label(a)));
  EXPECT_EQ(1U, memory::address(memory::relaxed_load_label(b)));
  EXPECT_EQ(2U, memory::address(memory::relaxed_load_label(c)));
  EXPECT_EQ(3U, memory::address(memory::relaxed_load_label(d)));

  EXPECT_EQ(0U, memory::address(memory::relaxed_store_label(a)));
  EXPECT_EQ(1U, memory::address(memory::relaxed_store_label(b)));
  EXPECT_EQ(2U, memory::address(memory::relaxed_store_label(c)));
  EXPECT_EQ(3U, memory::address(memory::relaxed_store_label(d)));
}

TEST(CkaTest, MemoryRefinementReadFromSameAddress)
{
  constexpr memory::Address a = 0U;

  memory::Refinement r;

  PartialString x{memory::relaxed_store_label(a, '\1')};
  PartialString y{memory::relaxed_store_label(a, '\2')};
  PartialString z{memory::relaxed_load_label(a)};

  PartialString p{((x , y) | z)};

  EXPECT_TRUE(r.check((x , z , y), p));
  EXPECT_TRUE(r.check((x , y , z), p));

  // LHS violates the sequenced-before ordering in "p"
  EXPECT_FALSE(r.check((y , x , z), p));

  // since "x" and "y" have different labels, LHS violates
  // the sequenced-before order of "x" and "y" in "p".
  EXPECT_FALSE(r.check((y , z , x), p));

  // But `alike_y` and `y` have the same label so the reordering is allowed.
  PartialString alike_y{memory::relaxed_store_label(a, '\2')};
  EXPECT_TRUE(r.check((y , z , alike_y), ((alike_y , y) | z)));

  // Our memory model rules out that a relaxed load happens-before
  // all relaxed stores on the same memory address.
  EXPECT_FALSE(r.check((z , y , x), p));
  EXPECT_FALSE(r.check((z , x , y), p));
  EXPECT_FALSE(r.check((z , (x | y)), p));
}

TEST(CkaTest, MemoryRefinementReadFromDifferentAddress)
{
  constexpr memory::Address a = 0U;
  constexpr memory::Address b = 1U;

  memory::Refinement r;

  PartialString x{memory::relaxed_store_label(a)};
  PartialString y{memory::relaxed_store_label(b)};
  PartialString z{memory::relaxed_load_label(a)};

  PartialString p{((x , y) | z)};

  EXPECT_TRUE(r.check((x , z , y), p));
  EXPECT_TRUE(r.check((x , y , z), p));

  // LHS violates the sequenced-before ordering in "p"
  EXPECT_FALSE(r.check((y , x , z), p));
  EXPECT_FALSE(r.check((y , z , x), p));

  // "y" writes a different memory address from "x"
  // and both are unsequenced in RHS
  EXPECT_TRUE(r.check((y , x , z), (x | y | z)));
  EXPECT_FALSE(r.check((y , z , x), (x | y | z)));

  EXPECT_FALSE(r.check((z , y , x), p));
  EXPECT_FALSE(r.check((z , x , y), p));
  EXPECT_FALSE(r.check((z , (x | y)), p));
}

TEST(CkaTest, MemoryRefinementModificationOrderSameAddress)
{
  constexpr memory::Address a = 0U;

  memory::Refinement r;

  PartialString x{memory::relaxed_store_label(a)};
  PartialString y{memory::relaxed_store_label(a)};

  PartialString p{(x | y)};

  EXPECT_TRUE(r.check((x , y), p));
  EXPECT_TRUE(r.check((y , x), p));

  // Our memory model rules out that two relaxed stores
  // on the same memory address happen concurrently even
  // when there are no relaxed loads reading from these.
  EXPECT_FALSE(r.check((x | y), p));
}

TEST(CkaTest, MemoryRefinementModificationOrderDifferentAddress)
{
  constexpr memory::Address a = 0U;
  constexpr memory::Address b = 1U;

  memory::Refinement r;

  PartialString x{memory::relaxed_store_label(a)};
  PartialString y{memory::relaxed_store_label(b)};

  PartialString p{(x | y)};

  EXPECT_TRUE(r.check((x , y), p));
  EXPECT_TRUE(r.check((y , x), p));
  EXPECT_TRUE(r.check((x | y), p));
}

TEST(CkaTest, MemoryRefinementRelaxedPartialString)
{
  constexpr memory::Address a = 0U;

  memory::Refinement r;

  PartialString u{memory::relaxed_store_label(a, 1)};
  PartialString v{memory::relaxed_store_label(a, 2)};
  PartialString x{memory::relaxed_load_label(a)};
  PartialString y{memory::relaxed_load_label(a)};

  PartialString p{((u , v) | (x , y))};

  EXPECT_FALSE(r.check(p, p));
}

TEST(CkaTest, MemoryRefinementRelaxedProgram)
{
  constexpr memory::Address a = 0U;

  memory::Refinement r;

  Program U{memory::relaxed_store_label(a, 1)};
  Program V{memory::relaxed_store_label(a, 2)};
  Program X{memory::relaxed_load_label(a)};
  Program Y{memory::relaxed_load_label(a)};

  Program P{((U , V) | (X , Y))};

  EXPECT_TRUE(r.check((U , X , Y , V), P));
  EXPECT_TRUE(r.check((U ,  X , V , Y), P));
  EXPECT_TRUE(r.check((U , V , X , Y), P));

  // since "Y" and "X" have the same label, they can be reordered
  EXPECT_TRUE(r.check((U , V , Y , X), P));
  EXPECT_TRUE(r.check((U , Y , X , V), P));

  EXPECT_FALSE(r.check(P, P));
  EXPECT_FALSE(r.check((V , X , Y , V), P));
  EXPECT_FALSE(r.check((U , X , Y , U), P));
  EXPECT_FALSE(r.check((V , X , Y , U), P));
  EXPECT_FALSE(r.check(((U | V) , X , Y), P));
  EXPECT_FALSE(r.check((U , V , (X | Y)), P));
  EXPECT_FALSE(r.check((X , U , Y , V), P));
  EXPECT_FALSE(r.check((X , Y , U , V), P));
  EXPECT_FALSE(r.check((X , U , V, Y), P));
  EXPECT_FALSE(r.check((Y , U , V, X), P));
  EXPECT_FALSE(r.check((Y , U , X , V), P));
  EXPECT_FALSE(r.check((Y , X , U , V), P));
}

/*
 * Consider the following program consistent of two threads T1 and T2:
 * "[a] := 0; [b] := 0; (T1 || T2)" where 'a' and 'b' are shared memory
 * addresses, T1 = "[a] := 1; r1 := [b]" and T2 = "[b] := 1; r2 := [a]".
 *
 * Let p0 = "[a] := 0",
 *     p1 = "[b] := 0",
 *     p2 = "[a] := 1",
 *     p3 = "r1 := [b]",
 *     p4 = "[b] := 1",
 *     p5 = "r2 := [a]".
 *
 * Sequential consistency can be achieved by requiring that
 * "p2" is sequenced-before "p3", and "p4" is sequenced-before "p5".
 */
TEST(CkaTest, MemoryHandwrittenPartialStringSequentialConsistency)
{
  constexpr memory::Address a = 0U;
  constexpr memory::Address b = 1U;

  memory::Refinement r;

  PartialString p0{memory::relaxed_store_label(a, '\0')};
  PartialString p1{memory::relaxed_store_label(b, '\0')};
  PartialString p2{memory::relaxed_store_label(a, '\1')};
  PartialString p3{memory::relaxed_load_label(b)};
  PartialString p4{memory::relaxed_store_label(b, '\1')};
  PartialString p5{memory::relaxed_load_label(a)};

  PartialString v0{((p2 | p4) , (p3 | p5))};
  PartialString v1{(p4 , p5 , p2 , p3)};
  PartialString v2{(p2 , p3 , p4 , p5)};

  PartialString x0{((p0 | p1) , v0)};
  PartialString x1{((p0 | p1) , v1)};
  PartialString x2{((p0 | p1) , v2)};

  PartialString y0{((p0 , p1) , v0)};
  PartialString y1{((p0 , p1) , v1)};
  PartialString y2{((p0 , p1) , v2)};

  PartialString r0{((p0 , p1 ) , ((p2 , p3) | (p4 , p5)))};
  PartialString r1{(p0 | p1 | ((p2 , p3) | (p4 , p5)))};
  PartialString r2{(p0 | p1 | p2 | p3 | p4 | p5)};

  // Both "p0" and "p1" are unsequenced in "p", but sequenced in "r0"
  EXPECT_FALSE(r.check(x0, r0));
  EXPECT_FALSE(r.check(x1, r0));
  EXPECT_FALSE(r.check(x2, r0));

  EXPECT_TRUE(r.check(x0, r1));
  EXPECT_TRUE(r.check(x1, r1));
  EXPECT_TRUE(r.check(x2, r1));

  EXPECT_TRUE(r.check(x0, r2));
  EXPECT_TRUE(r.check(x1, r2));
  EXPECT_TRUE(r.check(x2, r2));

  EXPECT_TRUE(r.check(y0, r0));
  EXPECT_TRUE(r.check(y1, r0));
  EXPECT_TRUE(r.check(y2, r0));

  EXPECT_TRUE(r.check(y0, r1));
  EXPECT_TRUE(r.check(y1, r0));
  EXPECT_TRUE(r.check(y2, r0));

  EXPECT_TRUE(r.check(y0, r2));
  EXPECT_TRUE(r.check(y1, r2));
  EXPECT_TRUE(r.check(y2, r2));
}

/*
 * Consider the following program consistent of two threads T1 and T2:
 * "[a] := 0; [b] := 0; (T1 || T2)" where 'a' and 'b' are shared memory
 * addresses, T1 = "[a] := 1; r1 := [b]" and T2 = "[b] := 1; r2 := [a]".
 *
 * Let P0 = "[a] := 0",
 *     P1 = "[b] := 0",
 *     P2 = "[a] := 1",
 *     P3 = "r1 := [b]",
 *     P4 = "[b] := 1",
 *     P5 = "r2 := [a]".
 *
 * Sequential consistency can be achieved by requiring that
 * "P2" is sequenced-before "P3", and "P4" is sequenced-before "P5".
 */
TEST(CkaTest, MemoryHandwrittenProgramSequentialConsistency)
{
  constexpr memory::Address a = 0U;
  constexpr memory::Address b = 1U;

  memory::Refinement r;

  Program P0{memory::relaxed_store_label(a, '\0')};
  Program P1{memory::relaxed_store_label(b, '\0')};
  Program P2{memory::relaxed_store_label(a, '\1')};
  Program P3{memory::relaxed_load_label(b)};
  Program P4{memory::relaxed_store_label(b, '\1')};
  Program P5{memory::relaxed_load_label(a)};

  Program A{((P2 | P4) , (P3 | P5))};
  Program B{(P4 , P5 , P2 , P3)};
  Program C{(P2 , P3 , P4 , P5)};

  Program P{((P0 | P1) , (A + B + C))};
  Program Q{((P0 , P1) , (A + B + C))};

  Program R0{((P0 , P1 ) , ((P2 , P3) | (P4 , P5)))};
  Program R1{(P0 | P1 | ((P2 , P3) | (P4 , P5)))};
  Program R2{(P0 | P1 | P2 | P3 | P4 | P5)};

  // Both "P0" and "P1" are unsequenced in "P", but sequenced in "R0"
  EXPECT_FALSE(r.check(P, R0));

  EXPECT_TRUE(r.check(P, R1));
  EXPECT_TRUE(r.check(P, R2));

  EXPECT_TRUE(r.check(Q, R0));
  EXPECT_TRUE(r.check(Q, R1));
  EXPECT_TRUE(r.check(Q, R2));
}

/// Consider the following concurrent program "P":
///
///   [x] := 0 ; [y] := 0 ; (r0 := [x] | r1 := [y] | [y] := 2 | [x] := 1)
///
/// By reflexivity, "P <= P" for the program refinement relation without
/// memory axioms.
///
/// As we know, if we add the memory axioms, then "P" on the RHS is made
/// more precise. Recall that this increase in precision has to be matched
/// on the LHS for the refinement relation to hold. After all, that's the
/// purpose of the memory axioms!
///
/// It is important to understand the ramifications of this. To illustrate
/// potential pitfalls, let's look at the effects of the From-Read axioms.
///
/// If we apply the memory axioms on the RHS without the From-Read axiom,
/// then "r.check(P, P)" holds because there exists a Read-From relation
/// in the RHS that is compatible with the LHS, namely that both registers
/// are set to zero by having both loads read-from the initial stores.
///
/// However, if we do add the From-Read axiom to the memory axiom encoding,
/// then "r.check(P, P)" fails because the From-Read axiom induces on the
/// previous Read-From relation the following happens-before orderings:
///
///   "[x] := 0" happens-before "r0 := [x]" happens-before "[x] := 1"
///
/// Similarly, for the "y" memory location.
///
/// Since this happens-before ordering is not compatible with the LHS,
/// the refinement fails, as desired.
TEST(CkaTest, MemoryAxiomWithFromReadAndMultipleWrites)
{
  constexpr memory::Address x = 0U;
  constexpr memory::Address y = 1U;

  Program initx{memory::relaxed_store_label(x, '\0')};
  Program inity{memory::relaxed_store_label(y, '\0')};

  Program w1y{memory::relaxed_store_label(y, '\2')};
  Program w1x{memory::relaxed_store_label(x, '\1')};

  Program r2x{memory::relaxed_load_label(x)};
  Program r2y{memory::relaxed_load_label(y)};

  Program P{(initx , inity, (r2x | r2y | w1y | w1x))};

  EXPECT_TRUE(P <= P);

  memory::Refinement r;
  EXPECT_FALSE(r.check(P, P));
}

TEST(CkaTest, MemoryAxiomWithFailingAssertion)
{
  constexpr memory::Address x = 0U;

  Program Wx{memory::relaxed_store_label(x, '\0')};
  Program AnZx{memory::assert_neq_label(x, '\0')};
  Program AZx{memory::assert_eq_label(x, '\0')};

  Program P{(Wx , AnZx)};
  Program Q{(Wx , AZx)};

  EXPECT_TRUE(P <= P);
  EXPECT_TRUE(Q <= Q);

  EXPECT_FALSE(P <= Q);
  EXPECT_FALSE(Q <= P);

  memory::Refinement r;

  EXPECT_FALSE(r.check(P, P));
  EXPECT_FALSE(r.check(P, Q));
  EXPECT_FALSE(r.check(Q, P));

  EXPECT_TRUE(r.check(Q, Q));
}

TEST(CkaTest, MemoryAxiomWithAssertionsAndUnsequencedWrites)
{
  constexpr memory::Address x = 0U;

  Program W1x{memory::relaxed_store_label(x, '\1')};
  Program W2x{memory::relaxed_store_label(x, '\2')};

  Program A1x{memory::assert_eq_label(x, '\1')};
  Program A2x{memory::assert_eq_label(x, '\2')};

  Program U{((W1x | W2x) , (A1x + A2x))};
  Program V{(W2x , W1x , A1x)};
  Program X{(W2x , W1x , A2x)};
  Program Y{(W1x , W2x , A1x)};
  Program Z{(W1x , W2x , A2x)};

  EXPECT_TRUE(V <= U);
  EXPECT_TRUE(X <= U);
  EXPECT_TRUE(Y <= U);

  memory::Refinement r;

  EXPECT_TRUE(r.check(V, U));
  EXPECT_TRUE(r.check(Z, U));

  EXPECT_FALSE(r.check(X, U));
  EXPECT_FALSE(r.check(Y, U));
}

TEST(CkaTest, MemoryAxiomWithAssertionsAndSequencedWrites)
{
  constexpr memory::Address x = 0U;

  Program W1x{memory::relaxed_store_label(x, '\1')};
  Program W2x{memory::relaxed_store_label(x, '\2')};

  Program A1x{memory::assert_eq_label(x, '\1')};
  Program A2x{memory::assert_neq_label(x, '\1')};

  Program X{(W1x , (A1x + A2x) , W2x)};
  Program Y{(W1x , A1x , W2x)};
  Program Z{(W1x , A2x , W2x)};

  EXPECT_TRUE(Y <= X);
  EXPECT_TRUE(Z <= X);

  memory::Refinement r;

  EXPECT_TRUE(r.check(Y, X));
  EXPECT_FALSE(r.check(Z, X));
}
