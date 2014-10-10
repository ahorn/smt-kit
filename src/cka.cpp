#include "cka.h"
#include <cstddef>

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

namespace memory
{

static constexpr std::size_t shift_address = 1 + sizeof(Byte) * 8;

Label relaxed_store_label(Address address, Byte byte)
{
  return (address << shift_address) | (byte << 1);
}

Label relaxed_load_label(Address address)
{
  // it's okay to lose a single byte here,
  // we get simpler address handling in turn
  return relaxed_store_label(address) | 1U;
}

bool is_relaxed_store(Label op)
{
  return (op & 1U) == 0U;
}

bool is_relaxed_load(Label op)
{
  return (op & 1U) == 1U;
}

Address address(Label op)
{
  // smaller return type acts as bitmask
  return op >> shift_address;
}

bool is_shared(Label store, Label load)
{
  assert(is_relaxed_store(store));
  assert(is_relaxed_load(load));

  return address(store) == address(load);
}

bool is_shared(const PartialString& x, Event store, Event load)
{
  assert(store <= x.label_function().size());
  assert(load <= x.label_function().size());

  Label store_label{x.label_function().at(store)};
  Label load_label{x.label_function().at(load)};

  return is_shared(store_label, load_label);
}

}

}
