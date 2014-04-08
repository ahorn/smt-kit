#include "crv.h"

namespace crv
{

const std::string Tracer::s_value_prefix = "v!";

const std::string Encoder::s_time_prefix = "t!";
#ifdef _SUP_READ_FROM_
const std::string Encoder::s_sup_time_prefix = "s!";
#endif

const std::string Encoder::s_rf_prefix = "rf!";
const std::string Encoder::s_pf_prefix = "pf!";
const std::string Encoder::s_ldf_prefix = "ldf!";

Tracer& tracer() {
  static Tracer s_tracer;
  return s_tracer;
}

void Tracer::add_assertion(Internal<bool>&& assertion)
{
  if (assertion.is_literal())
    assert(assertion.literal());

  m_assertions.push_back(Internal<bool>::term(std::move(assertion)));
}

void Tracer::add_error(Internal<bool>&& error)
{
  if (error.is_literal())
    assert(!error.literal());

  m_errors.push_back(guard() and Internal<bool>::term(std::move(error)));
}

void Tracer::append_channel_send_event(
  const Address address,
  const smt::Sort& sort,
  const smt::UnsafeTerm& term)
{
  assert(!term.is_null());
  append_event<CHANNEL_SEND_EVENT>(m_event_id_cnt++, address, sort, term);
}

void Tracer::append_message_send_event(
  const Address address,
  const smt::Sort& sort,
  const smt::UnsafeTerm& term)
{
  assert(!term.is_null());
  append_event<MESSAGE_SEND_EVENT>(m_event_id_cnt++, address, sort, term);
}

bool Tracer::decide_flip(
  const Internal<bool>& g,
  bool direction)
{
  assert(!m_scope_stack.empty());

  if (g.is_literal())
    return g.literal();

  if (m_flip_iter == m_flips.cend())
  {
    m_flips.emplace_back(direction);
    assert(m_flips.back().direction == direction);
  }
  else
  {
    direction = m_flip_iter->direction;
    m_flip_iter++;
  }

  if (direction)
    m_guard = m_guard and Internal<bool>::term(g);
  else
    m_guard = m_guard and not Internal<bool>::term(g);

  m_scope_stack.top().guard = m_guard;

  return direction;
}

void Tracer::scope_then(const Internal<bool>& g)
{
  assert(!g.is_literal());
  assert(m_block_id_cnt < std::numeric_limits<BlockIdentifier>::max());
  assert(!m_scope_stack.empty());
  assert(m_scope_stack.top().level < std::numeric_limits<
    ScopeLevel>::max());

  m_block_id_cnt++;
  m_scope_stack.emplace(guard(), Internal<bool>::term(g),
    m_scope_stack.top().level + 1);
  m_guard = m_guard and Internal<bool>::term(g);
}

void Tracer::scope_else()
{
  assert(m_block_id_cnt < std::numeric_limits<BlockIdentifier>::max());
  assert(!m_scope_stack.empty());

  m_block_id_cnt++;
  ThreadLocalScope& scope = m_scope_stack.top();
  scope.guard_prime = not scope.guard_prime;
  m_guard = scope.guard and scope.guard_prime;
}

void Tracer::scope_end()
{
  assert(!m_scope_stack.empty());

  m_guard = m_scope_stack.top().guard;
  m_scope_stack.pop();
}

namespace ThisThread
{
  ThreadIdentifier thread_id()
  {
    return tracer().current_thread_id();
  }
};

}
