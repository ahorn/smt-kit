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

void Checker::add_assertion(Internal<bool>&& assertion)
{
  if (assertion.is_literal())
    assert(assertion.literal());

  if (m_assertions.is_null())
    m_assertions = Internal<bool>::term(std::move(assertion));
  else
    m_assertions = m_assertions and Internal<bool>::term(std::move(assertion));
}

void Checker::add_error(Internal<bool>&& error)
{
  if (error.is_literal())
  {
    if (error.literal())
    {
      if (m_errors.is_null())
        m_errors = tracer().guard();
      else
        m_errors = m_errors or tracer().guard();
    }
    else
    {
      if (m_errors.is_null())
        m_errors = smt::literal<smt::Bool>(false);
    }
  }
  else
  {
    if (m_errors.is_null())
      m_errors = tracer().guard() and Internal<bool>::term(std::move(error));
    else
      m_errors = m_errors or (tracer().guard() and Internal<bool>::term(std::move(error)));
  }
}

bool DfsChecker::branch(const Internal<bool>& g, const bool direction_hint)
{
  if (g.is_literal())
    return g.literal();

  bool direction = direction_hint;
  if (m_dfs.is_end())
    m_dfs.append_flip(direction_hint);
  else
    direction = m_dfs.next();

  force_branch(g, direction);
  return direction;
}

DfsPruneChecker& dfs_prune_checker()
{
  static DfsPruneChecker s_dfs_prune_checker;
  return s_dfs_prune_checker;
}

bool DfsPruneChecker::branch(const Internal<bool>& g, const bool direction_hint)
{
  if (g.is_literal())
    return g.literal();

  if (!m_dfs.is_end())
  {
    assert(m_is_feasible);

    const bool direction = m_dfs.next();
    DfsChecker::force_branch(g, direction);
    return direction;
  }

  if (!m_is_feasible)
    // exactly like NO_BRANCH
    return false;

  assert(!g.is_literal() && m_dfs.is_end() && m_is_feasible);

  const smt::Bool g_term = Internal<bool>::term(g);
  if (direction_hint)
    goto THEN_BRANCH;
  else
    goto ELSE_BRANCH;

THEN_BRANCH:
  if (smt::sat == check(tracer().guard() and g_term))
  {
    tracer().add_guard(g_term);
    m_dfs.append_flip(true, !direction_hint);

    assert(m_dfs.last_flip().direction);
    return true;
  }

  // neither THEN_BRANCH nor ELSE_BRANCH is feasible
  if (!direction_hint)
    goto NO_BRANCH;

// fall through THEN_BRANCH to try ELSE_BRANCH
ELSE_BRANCH:
  if (smt::sat == check(tracer().guard() and not g_term))
  {
    tracer().add_guard(not g_term);
    m_dfs.append_flip(false, direction_hint);

    assert(!m_dfs.last_flip().direction);
    return false;
  }

  if (!direction_hint)
    // try the other branch
    goto THEN_BRANCH;

NO_BRANCH:
  // both THEN_BRANCH and ELSE_BRANCH are infeasible
  m_is_feasible = false;

  // favour "else" branch, hoping for shorter infeasible path
  return false;
}

namespace ThisThread
{
  ThreadIdentifier thread_id()
  {
    return tracer().current_thread_id();
  }
};

}
