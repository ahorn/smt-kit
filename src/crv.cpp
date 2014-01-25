#include "crv.h"

namespace crv
{

const std::string Tracer::s_value_prefix = "v!";
const std::string Encoder::s_time_prefix = "t!";
const std::string Encoder::s_rf_prefix = "rf!";
const std::string Encoder::s_pf_prefix = "pf!";
const std::string Encoder::s_ldf_prefix = "ldf!";

Tracer& tracer() {
  static Tracer s_tracer;
  return s_tracer;
}

void Tracer::add_assertion(Internal<bool>&& assertion)
{
  m_assertions.push_back(std::move(assertion.term));
}

void Tracer::add_error(Internal<bool>&& error)
{
  m_errors.push_back(guard() and std::move(error.term));
}

bool Tracer::decide_flip(
  const Internal<bool>& g,
  bool direction)
{
  assert(!m_scope_stack.empty());

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
    m_guard = m_guard and g.term;
  else
    m_guard = m_guard and not g.term;

  m_scope_stack.top().guard = m_guard;

  return direction;
}

void Tracer::scope_then(const Internal<bool>& g)
{
  assert(!m_scope_stack.empty());
  assert(m_scope_stack.top().level < std::numeric_limits<
    ScopeLevel>::max());

  m_scope_stack.emplace(guard(), g.term,
    m_scope_stack.top().level + 1);
  m_guard = m_guard and g.term;
}

void Tracer::scope_else()
{
  assert(!m_scope_stack.empty());

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

EventMap Encoder::immediate_dominator_map(const Tracer& tracer)
{
  EventMap map;
  const PerThreadMap& per_thread_map = tracer.per_thread_map();

  EventIters::const_reverse_iterator criter;
  std::vector<EventIter> worklist;
  EventIter e_iter, e_prime_iter;
  ScopeLevel scope_level;

  for (const PerThreadMap::value_type& pair : per_thread_map)
  {
    const EventIters& events = pair.second;

    if (events.size() < 2)
      continue;

    assert(worklist.empty());
    worklist.reserve(events.size());

    criter = events.crbegin();
    e_iter = *criter++;
    for (; criter != events.crend(); criter++)
    {
      e_prime_iter = *criter;
      scope_level = e_prime_iter->scope_level;
      assert(std::next(e_prime_iter) == e_iter);

      if (scope_level > e_iter->scope_level)
      {
        // save event for later
        worklist.push_back(e_iter);
      }
      else if (scope_level == e_iter->scope_level)
      {
        // TODO: support Tracer::decide_flip() inside scopes
        if (e_iter->guard.addr() == e_prime_iter->guard.addr())
        {
          // both events are in the same branch, i.e. e_prime_iter
          // is the direct predecessor of e_iter in the unrolled CFG
          map.emplace(e_iter, e_prime_iter);
        }
        else
        {
          // crossing over to another branch or even a different
          // "if-then-else" block, e.g. if (*) { a } if (*) { b }
          worklist.push_back(e_iter);
        }
      }
      else
      {
        // note: scope level may have decreased by more than one,
        // e.g. if (*) { if (*) { a } }
        while (!worklist.empty() &&
          scope_level <= worklist.back()->scope_level)
        {
          map.emplace(worklist.back(), e_prime_iter);
          worklist.pop_back();
        }

        // process first event in "then" branch
        map.emplace(e_iter, e_prime_iter);
      }

      e_iter = e_prime_iter;
    }
  }
  return map;
}

namespace ThisThread
{
  ThreadIdentifier thread_id()
  {
    return tracer().current_thread_id();
  }
};

}
