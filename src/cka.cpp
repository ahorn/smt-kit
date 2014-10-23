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

#ifdef _CKA_SORT_PARTIAL_STRINGS_
struct {
  bool operator()(const PartialString& x, const PartialString& y)
  {
    return x.length() < y.length();
  }
} LengthComparison;
#endif

Program operator|(const Program& X, const Program& Y)
{
  Program::PartialStrings partial_strings;
  partial_strings.reserve(X.size() * Y.size());

  for (const PartialString& x : X.partial_strings())
    for (const PartialString& y : Y.partial_strings())
      partial_strings.push_back((x | y));

#ifdef _CKA_SORT_PARTIAL_STRINGS_
  std::sort(partial_strings.begin(), partial_strings.end(), LengthComparison);
#endif

  return {std::move(partial_strings)};
}

Program operator,(const Program& X, const Program& Y)
{
  Program::PartialStrings partial_strings;
  partial_strings.reserve(X.size() * Y.size());

  for (const PartialString& x : X.partial_strings())
    for (const PartialString& y : Y.partial_strings())
      partial_strings.push_back((x , y));

#ifdef _CKA_SORT_PARTIAL_STRINGS_
  std::sort(partial_strings.begin(), partial_strings.end(), LengthComparison);
#endif

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

#ifdef _CKA_SORT_PARTIAL_STRINGS_
  std::sort(partial_strings.begin(), partial_strings.end(), LengthComparison);
#endif

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

/// Bit mask:
///
///     Bit 3 (2^3)       Bit 2 (2^2)        Bit 1 (2^1)      Bit 0 (2^0)
/// +-----------------+-----------------+-----------------+-----------------+
/// |      equal      |      assert     | release-acquire |      load       |
/// +-----------------+-----------------+-----------------+-----------------+
static constexpr std::size_t shift_byte = 4;
static constexpr std::size_t shift_address = shift_byte + sizeof(Byte) * 8;

Label none_store_label(Address address, Byte byte)
{
  return (address << shift_address) | (byte << shift_byte);
}

Label none_load_label(Address address)
{
  return none_store_label(address) | 1U;
}

Label release_store_label(Address address, Byte byte)
{
  return none_store_label(address, byte) | 2U;
}

Label acquire_load_label(Address address)
{
  return release_store_label(address) | 1U;
}

Label assert_neq_label(Address address, Byte byte)
{
  return acquire_load_label(address) | (byte << shift_byte) | 4U;
}

Label assert_eq_label(Address address, Byte byte)
{
  return assert_neq_label(address, byte) | 8U;
}

bool is_none_store(Label op)
{
  return (op & 0x3U) == 0x0U;
}

bool is_none_load(Label op)
{
  return (op & 0x3U) == 0x1U;
}

bool is_release_store(Label op)
{
  return (op & 0x3U) == 0x2U;
}

bool is_acquire_load(Label op)
{
  return (op & 0x3U) == 0x3U;
}

bool is_store(Label op)
{
  return is_none_store(op) or is_release_store(op);
}

bool is_load(Label op)
{
  return is_none_load(op) or is_acquire_load(op);
}

bool is_assert(Label op)
{
  return (op & 0x4U) == 0x4U;
}

bool is_assert_eq(Label op)
{
  return (op & 0xCU) == 0xCU;
}

bool is_assert_neq(Label op)
{
  return (op & 0xCU) == 0x4U;
}

Byte byte(Label op)
{
  assert(is_store(op) or is_assert(op));

  // smaller return type acts as bitmask
  return op >> shift_byte;
}

Address address(Label op)
{
  assert(is_store(op) or is_load(op));

  // smaller return type acts as bitmask
  return op >> shift_address;
}

bool is_shared(Label store, Label load)
{
  assert(is_release_store(store));
  assert(is_acquire_load(load));

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
