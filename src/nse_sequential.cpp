#include "nse_sequential.h"

namespace crv
{

constexpr char internal::Inputs::s_prefix[];
internal::Inputs::Counter internal::Inputs::s_counter = 0;

void Checker::add_assertion(Internal<bool>&& assertion)
{
  if (assertion.is_literal())
    assert(assertion.literal());

  smt::Bool assertion_term = Internal<bool>::term(std::move(assertion));
  if (m_assertions.is_null())
    m_assertions = assertion_term;
  else
    m_assertions = m_assertions and assertion_term;

  // so we can prune more branches
  add_guard(assertion_term);
}

void Checker::add_error(Internal<bool>&& error)
{
  if (error.is_literal())
  {
    if (error.literal())
    {
      if (m_errors.is_null())
        m_errors = guard();
      else
        m_errors = m_errors or guard();
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
      m_errors = guard() and Internal<bool>::term(std::move(error));
    else
      m_errors = m_errors or (guard() and Internal<bool>::term(std::move(error)));
  }
}

SequentialDfsChecker& sequential_dfs_checker()
{
  static SequentialDfsChecker s_sequential_dfs_checker;
  return s_sequential_dfs_checker;
}

// maintainer note: recall Dfs::find_next_path(). If the newly alternated
// flip F causes the conjunction of guards to be unsatisfiable, then this
// will be detected here as soon as another branch condition is conjoined.
// In the case there is no such other branch condition, progress is still
// guaranteed because F is frozen and therefore will be popped by Dfs.
bool SequentialDfsChecker::branch(const Internal<bool>& g, const bool direction_hint)
{
  if (g.is_literal())
    return g.literal();

  if (!m_is_feasible)
    // exactly like NO_BRANCH
    return false;

  const smt::Bool g_term = Internal<bool>::term(g);
  if (m_dfs.has_next())
  {
    const bool direction = m_dfs.next();
    if (direction)
      Checker::add_guard(g_term);
    else
      Checker::add_guard(not g_term);

    return direction;
  }

  if (direction_hint)
    goto THEN_BRANCH;
  else
    goto ELSE_BRANCH;

THEN_BRANCH:
  if (smt::sat == check(Checker::guard() and g_term))
  {
    Checker::add_guard(g_term);
    m_dfs.append_flip(true, !direction_hint);
    return true;
  }

  // neither THEN_BRANCH nor ELSE_BRANCH is feasible
  if (!direction_hint)
    goto NO_BRANCH;

// fall through THEN_BRANCH to try ELSE_BRANCH
ELSE_BRANCH:
  if (smt::sat == check(Checker::guard() and not g_term))
  {
    Checker::add_guard(not g_term);
    m_dfs.append_flip(false, direction_hint);
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

}
