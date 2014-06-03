// Copyright 2014, Alex Horn. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

#include <iostream>
#include <chrono>
#include <smt>

#ifndef _NSE_REPORT_H_
#define _NSE_REPORT_H_

namespace crv
{

/// Print statistics to standard output
template<typename CheckerStats, typename Duration>
void report_statistics(
  const smt::Solver::Stats& solver_stats,
  CheckerStats checker_stats,
  Duration total_time)
{
  const std::chrono::seconds total_seconds =
    std::chrono::duration_cast<std::chrono::seconds>(total_time);

  const smt::Solver::ElapsedTime check_elapsed_time = solver_stats.check_elapsed_time;
  const smt::Solver::ElapsedTime encode_elapsed_time = solver_stats.encode_elapsed_time;

  const std::chrono::seconds check_elapsed_seconds =
    std::chrono::duration_cast<std::chrono::seconds>(check_elapsed_time);

  const std::chrono::seconds encode_elapsed_seconds =
    std::chrono::duration_cast<std::chrono::seconds>(encode_elapsed_time);

  const std::chrono::seconds branch_seconds =
    std::chrono::duration_cast<std::chrono::seconds>(checker_stats.branch_time);

  const std::chrono::seconds replay_seconds =
    std::chrono::duration_cast<std::chrono::seconds>(checker_stats.replay_time);

  std::cout << "-----------------------:" << std::endl;
  std::cout << "Number of paths explored: " <<  checker_stats.number_of_paths << std::endl;
  std::cout << "Number of solver calls: " <<  checker_stats.number_of_checks << std::endl;

  if (checker_stats.branch_cnt == 0)
    std::cout << "Literal branch percentage: 'undefined'" << std::endl;
  else
    std::cout << "Literal branch percentage: " <<
      ((checker_stats.branch_literal_cnt * 100) /
        checker_stats.branch_cnt)  << "\%" << std::endl;

  std::cout << "Total runtime (s): " << total_seconds.count() << std::endl;
  std::cout << "Encoder time (s): " << encode_elapsed_seconds.count() << std::endl;
  std::cout << "Solver time (s): " << check_elapsed_seconds.count() << std::endl;
  std::cout << "Branch time (s): " << branch_seconds.count() << std::endl;
  std::cout << "Replay time (s): " << replay_seconds.count() << std::endl;

  if (total_time == Duration::zero())
  {
    std::cout << "Solver percentage: 'undefined'" << std::endl;
    std::cout << "Branch percentage: 'undefined'" << std::endl;
    std::cout << "Replay percentage: 'undefined'" << std::endl;
  }
  else
  {
    std::cout << "Solver percentage: " << ((check_elapsed_time * 100) / total_time) << "\%" << std::endl;
    std::cout << "Branch percentage: " << ((checker_stats.branch_time * 100) / total_time) << "\%" << std::endl;
    std::cout << "Replay percentage: " << ((checker_stats.replay_time * 100) / total_time) << "\%" << std::endl;
  }
}

}

#endif
