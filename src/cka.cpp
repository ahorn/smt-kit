#include "cka.h"

namespace cka
{

namespace internal
{
  unsigned uint_pow(unsigned base, unsigned exp)
  {
    // exponentiation by squaring, see Wikipedia
    unsigned result = 1U;

    // is exponent positive?
    while (exp)
    {
      // is exponent odd?
      if (exp & 1U)
        result *= base;

      // halve exponent
      exp >>= 1;

      // square
      base *= base;
    }

    return result;
  }
}

PartialString operator|(const PartialString& x, const PartialString& y)
{
  PartialString z{x, y};
  z.recompute_extremals();

  const Length x_len{x.length()}, z_len{z.length()};

  // new pair-wise incomparable events
  for (Event e_x = 0; e_x < x_len; ++e_x)
    for (Event e_y = x_len; e_y < z_len; ++e_y)
      z.m_incomparables.emplace_back(e_x, e_y);

  return z;
}

PartialString operator,(const PartialString& x, const PartialString& y)
{
  PartialString z{x, y};

  const Length x_len{x.length()};
  const Events x_maximals{x.maximals()}, y_minimals{y.minimals()};

  for (Event maximal : x_maximals)
    for (Event minimal : y_minimals)
      z.m_strict_partial_order.emplace_back(maximal, x_len + minimal);

  z.recompute_extremals();
  return z;
}

Program operator|(const Program& X, const Program& Y)
{
  Program::PartialStrings partial_strings;
  partial_strings.reserve(X.size() * Y.size());

  for (const PartialString& x : X.partial_strings())
    for (const PartialString& y : Y.partial_strings())
      partial_strings.push_back((x | y));

  return {std::move(partial_strings)};
}

Program operator,(const Program& X, const Program& Y)
{
  Program::PartialStrings partial_strings;
  partial_strings.reserve(X.size() * Y.size());

  for (const PartialString& x : X.partial_strings())
    for (const PartialString& y : Y.partial_strings())
      partial_strings.push_back((x , y));

  return {std::move(partial_strings)};
}

Program operator+(const Program& X, const Program& Y)
{
  Program::PartialStrings partial_strings;
  partial_strings.reserve(X.size() + Y.size());

  // union of `X` and `Y`
  for (const PartialString& x : X.partial_strings())
    partial_strings.push_back(x);

  for (const PartialString& y : Y.partial_strings())
    partial_strings.push_back(y);

  return {std::move(partial_strings)};
}

bool operator<=(const PartialString& x, const PartialString& y)
{
  static Refinement s_refinement;
  return s_refinement.check(x, y);
}

bool operator<=(const Program& X, const Program& Y)
{
  static Refinement s_refinement;
  return s_refinement.check(X, Y);
}

}
