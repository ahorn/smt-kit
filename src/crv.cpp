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

Tracer& tracer()
{
  static Tracer s_tracer;
  return s_tracer;
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

smt::Bool Tracer::scope_then(const Internal<bool>& g)
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
  return m_guard;
}

smt::Bool Tracer::scope_else()
{
  assert(m_block_id_cnt < std::numeric_limits<BlockIdentifier>::max());
  assert(!m_scope_stack.empty());

  m_block_id_cnt++;
  ThreadLocalScope& scope = m_scope_stack.top();
  scope.guard_prime = not scope.guard_prime;
  m_guard = scope.guard and scope.guard_prime;
  return m_guard;
}

smt::Bool Tracer::scope_end()
{
  assert(!m_scope_stack.empty());

  m_guard = m_scope_stack.top().guard;
  m_scope_stack.pop();
  return m_guard;
}

void Tracer::add_guard(smt::Bool&& g)
{
  assert(!m_scope_stack.empty());

  m_guard = m_guard and std::move(g);
  m_scope_stack.top().guard = m_guard;
}

void Tracer::add_guard(const smt::Bool& g)
{
  assert(!m_scope_stack.empty());

  m_guard = m_guard and g;
  m_scope_stack.top().guard = m_guard;
}

DfsChecker& dfs_checker()
{
  static DfsChecker s_dfs_checker;
  return s_dfs_checker;
}

bool DfsChecker::branch(const Internal<bool>& g, const bool direction_hint)
{
  if (g.is_literal())
    return g.literal();

  bool direction = direction_hint;
  if (m_dfs.has_next())
    direction = m_dfs.next();
  else
    m_dfs.append_flip(direction_hint);

  force_branch(g, direction);
  return direction;
}

namespace ThisThread
{
  ThreadIdentifier thread_id()
  {
    return tracer().current_thread_id();
  }
};

}
