// Author(s): Wieger Wesselink
// Copyright: see the accompanying file COPYING or copy at
// https://github.com/mCRL2org/mCRL2/blob/master/COPYING
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)
//
/// \file mcrl2/lps/lpsreach.h
/// \brief add your file description here.

#ifndef MCRL2_LPS_LPSREACH_H
#define MCRL2_LPS_LPSREACH_H

#include <chrono>
#include <iomanip>
#include <boost/dynamic_bitset.hpp>
#include <sylvan_ldd.hpp>
#include "mcrl2/lps/specification.h"
#include "mcrl2/utilities/detail/container_utility.h"
#include "mcrl2/data/consistency.h"
#include "mcrl2/data/enumerator.h"
#include "mcrl2/data/substitution_utility.h"
#include "mcrl2/lps/detail/instantiate_global_variables.h"
#include "mcrl2/lps/io.h"
#include "mcrl2/lps/one_point_rule_rewrite.h"
#include "mcrl2/lps/order_summand_variables.h"
#include "mcrl2/lps/replace_constants_by_variables.h"
#include "mcrl2/lps/resolve_name_clashes.h"
#include "mcrl2/lps/symbolic_reachability.h"
#include "mcrl2/utilities/parse_numbers.h"
#include "mcrl2/utilities/stack_array.h"

namespace mcrl2 {

namespace lps {

inline
std::pair<std::set<data::variable>, std::set<data::variable>> read_write_parameters(const lps::action_summand& summand, const std::set<data::variable>& process_parameters)
{
  using utilities::detail::set_union;
  using utilities::detail::set_intersection;

  std::set<data::variable> read_parameters = set_union(data::find_free_variables(summand.condition()), lps::find_free_variables(summand.multi_action()));
  std::set<data::variable> write_parameters;

  for (const auto& assignment: summand.assignments())
  {
    if (assignment.lhs() != assignment.rhs())
    {
      write_parameters.insert(assignment.lhs());
      data::find_free_variables(assignment.rhs(), std::inserter(read_parameters, read_parameters.end()));
    }
  }

  return { set_intersection(read_parameters, process_parameters), set_intersection(write_parameters, process_parameters) };
}

inline
std::map<data::variable, std::size_t> process_parameter_index(const lps::specification& lpsspec)
{
  std::map<data::variable, std::size_t> result;
  std::size_t i = 0;
  for (const data::variable& v: lpsspec.process().process_parameters())
  {
    result[v] = i++;
  }
  return result;
}

inline
std::vector<boost::dynamic_bitset<>> compute_read_write_patterns(const lps::specification& lpsspec)
{
  using utilities::detail::as_set;

  std::vector<boost::dynamic_bitset<>> result;

  auto process_parameters = as_set(lpsspec.process().process_parameters());
  std::size_t n = process_parameters.size();
  std::map<data::variable, std::size_t> index = process_parameter_index(lpsspec);

  for (const auto& summand: lpsspec.process().action_summands())
  {
    auto [read_parameters, write_parameters] = read_write_parameters(summand, process_parameters);
    auto read = lps::parameter_indices(read_parameters, index);
    auto write = lps::parameter_indices(write_parameters, index);
    boost::dynamic_bitset<> rw(2*n);
    for (std::size_t j: read)
    {
      rw[2*j] = true;
    }
    for (std::size_t j: write)
    {
      rw[2*j + 1] = true;
    }
    result.push_back(rw);
  }

  return result;
}

struct lps_summand_group: public lps::summand_group
{
  lps_summand_group(
    const lps::specification& lpsspec,
    const data::variable_list& process_parameters, // the reordered process parameters
    const std::set<std::size_t>& group_indices,
    const boost::dynamic_bitset<>& group_pattern,
    const std::vector<boost::dynamic_bitset<>>& read_write_patterns,
    const std::vector<std::size_t> variable_order // a permutation of [0 .. |process_parameters| - 1]
  )
    : lps::summand_group(process_parameters, group_pattern)
  {
    using lps::project;
    using utilities::detail::as_vector;
    using utilities::detail::as_set;
    using utilities::detail::set_union;

    std::set<std::size_t> used;
    for (std::size_t j: read)
    {
      used.insert(2*j);
    }
    for (std::size_t j: write)
    {
      used.insert(2*j + 1);
    }

    const auto& lps_summands = lpsspec.process().action_summands();
    for (std::size_t i: group_indices)
    {
      std::vector<int> copy;
      for (std::size_t j: used)
      {
        bool b = read_write_patterns[i][j];
        copy.push_back(b ? 0 : 1);
      }
      const auto& smd = lps_summands[i];
      summands.emplace_back(smd.condition(), smd.summation_variables(), project(as_vector(permute_copy(smd.next_state(lpsspec.process().process_parameters()), variable_order)), write), copy);
    }
  }
};

class lpsreach_algorithm
{
    using ldd = sylvan::ldds::ldd;
    using enumerator_element = data::enumerator_list_element_with_substitution<>;

    template <typename Context>
    friend void lps::learn_successors_callback(WorkerP*, Task*, std::uint32_t* v, std::size_t n, void* context);

  protected:
    const lps::symbolic_reachability_options& m_options;
    data::rewriter m_rewr;
    data::mutable_indexed_substitution<> m_sigma;
    data::enumerator_identifier_generator m_id_generator;
    data::enumerator_algorithm<> m_enumerator;
    data::variable_list m_process_parameters;
    std::size_t m_n;
    std::vector<lps::data_expression_index> m_data_index;
    std::vector<lps_summand_group> m_summand_groups;
    data::data_expression_list m_initial_state;
    std::vector<boost::dynamic_bitset<>> m_summand_patterns;
    std::vector<boost::dynamic_bitset<>> m_group_patterns;
    std::vector<std::size_t> m_variable_order;

    ldd state2ldd(const data::data_expression_list& x)
    {
      MCRL2_DECLARE_STACK_ARRAY(v, std::uint32_t, x.size());

      auto vi = v.begin();
      auto di = m_data_index.begin();
      auto xi = x.begin();
      for (; di != m_data_index.end(); ++vi, ++di, ++xi)
      {
        *vi = di->index(*xi);
      }

      return sylvan::ldds::cube(v.data(), x.size());
    };

    // R.L := R.L U {(x,y) in R | x in X}
    void learn_successors(std::size_t i, summand_group& R, const ldd& X)
    {
      mCRL2log(log::debug) << "learn successors of summand group " << i << " for X = " << print_states(m_data_index, X, R.read) << std::endl;

      using namespace sylvan::ldds;
      std::pair<lpsreach_algorithm&, summand_group&> context{*this, R};
      sat_all_nopar(X, lps::learn_successors_callback<std::pair<lpsreach_algorithm&, summand_group&>>, &context);
    }

    template <typename Specification>
    Specification preprocess(const Specification& lpsspec)
    {
      Specification result = lpsspec;
      lps::detail::instantiate_global_variables(result);
      lps::order_summand_variables(result);
      resolve_summand_variable_name_clashes(result); // N.B. This is a required preprocessing step.
      if (m_options.one_point_rule_rewrite)
      {
        one_point_rule_rewrite(result);
      }
      if (m_options.replace_constants_by_variables)
      {
        replace_constants_by_variables(result, m_rewr, m_sigma);
      }
      return result;
    }

  public:
    lpsreach_algorithm(const lps::specification& lpsspec, const lps::symbolic_reachability_options& options_)
      : m_options(options_),
        m_rewr(lps::construct_rewriter(lpsspec.data(), m_options.rewrite_strategy, lps::find_function_symbols(lpsspec), m_options.remove_unused_rewrite_rules)),
        m_enumerator(m_rewr, lpsspec.data(), m_rewr, m_id_generator, false)
    {
      using utilities::detail::as_vector;

      lps::specification lpsspec_ = preprocess(lpsspec);
      m_process_parameters = lpsspec_.process().process_parameters();
      m_n = m_process_parameters.size();
      m_initial_state = lpsspec_.initial_process().expressions();

      m_summand_patterns = compute_read_write_patterns(lpsspec_);
      lps::adjust_read_write_patterns(m_summand_patterns, m_options);

      m_variable_order = lps::compute_variable_order(m_options.variable_order, m_summand_patterns);
      mCRL2log(log::debug) << "variable order = " << core::detail::print_list(m_variable_order) << std::endl;
      m_summand_patterns = lps::reorder_read_write_patterns(m_summand_patterns, m_variable_order);
      mCRL2log(log::debug) << lps::print_read_write_patterns(m_summand_patterns);

      m_process_parameters = permute_copy(m_process_parameters, m_variable_order);
      m_initial_state = permute_copy(m_initial_state, m_variable_order);
      mCRL2log(log::debug) << "process parameters = " << core::detail::print_list(m_process_parameters) << std::endl;
      mCRL2log(log::debug) << "initial state = " << core::detail::print_list(m_initial_state) << std::endl;

      for (const data::variable& param: m_process_parameters)
      {
        m_data_index.push_back(lps::data_expression_index(param.sort()));
      }

      std::vector<std::set<std::size_t>> groups = lps::compute_summand_groups(m_options.summand_groups, m_summand_patterns);
      for (const auto& group: groups)
      {
        mCRL2log(log::debug) << "group " << core::detail::print_set(group) << std::endl;
      }
      m_group_patterns = lps::compute_summand_group_patterns(m_summand_patterns, groups);
      for (std::size_t j = 0; j < m_group_patterns.size(); j++)
      {
        m_summand_groups.emplace_back(lpsspec_, m_process_parameters, groups[j], m_group_patterns[j], m_summand_patterns, m_variable_order);
      }

      for (std::size_t i = 0; i < m_summand_groups.size(); i++)
      {
        mCRL2log(log::debug) << "=== summand group " << i << " ===\n" << m_summand_groups[i] << std::endl;
      }
    }

    ldd run()
    {
      using namespace sylvan::ldds;
      auto& R = m_summand_groups;
      std::size_t iteration_count = 0;

      mCRL2log(log::debug) << "initial state = " << core::detail::print_list(m_initial_state) << std::endl;

      auto start = std::chrono::steady_clock::now();
      ldd x = state2ldd(m_initial_state);
      std::chrono::duration<double> elapsed_seconds = std::chrono::steady_clock::now() - start;
      ldd visited = x;
      ldd todo = x;
      mCRL2log(log::verbose) << "found " << std::setw(12) << satcount(visited) << " states after " << std::setw(3) << iteration_count << " iterations (time = " << std::setprecision(2) << std::fixed << elapsed_seconds.count() << "s)" << std::endl;

      while (todo != empty_set())
      {
        auto loop_start = std::chrono::steady_clock::now();
        iteration_count++;
        mCRL2log(log::debug) << "--- iteration " << iteration_count << " ---" << std::endl;
        mCRL2log(log::debug) << "todo = " << print_states(m_data_index, todo) << std::endl;
        for (std::size_t i = 0; i < R.size(); i++)
        {
          learn_successors(i, R[i], minus(project(todo, R[i].Ip), R[i].Ldomain));
          mCRL2log(log::debug) << "L =\n" << print_relation(m_data_index, R[i].L, R[i].read, R[i].write) << std::endl;
        }
        ldd todo1 = empty_set();
        for (std::size_t i = 0; i < R.size(); i++)
        {
          if (m_options.no_relprod)
          {
            ldd z = lps::alternative_relprod(todo, R[i]);
            mCRL2log(log::debug) << "relprod(" << i << ", todo) = " << print_states(m_data_index, z) << std::endl;
            todo1 = union_(z, todo1);
          }
          else
          {
            mCRL2log(log::debug) << "relprod(" << i << ", todo) = " << print_states(m_data_index, relprod(todo, R[i].L, R[i].Ir)) << std::endl;
            todo1 = relprod_union(todo, R[i].L, R[i].Ir, todo1);
          }
        }
        todo = minus(todo1, visited);
        visited = union_(visited, todo);
        elapsed_seconds = std::chrono::steady_clock::now() - loop_start;
        mCRL2log(log::verbose) << "found " << std::setw(12) << satcount(visited) << " states after " << std::setw(3) << iteration_count << " iterations (time = " << std::setprecision(2) << std::fixed << elapsed_seconds.count() << "s)" << std::endl;
      }

      elapsed_seconds = std::chrono::steady_clock::now() - start;
      std::cout << "number of states = " << satcount(visited) << " (time = " << std::setprecision(2) << std::fixed << elapsed_seconds.count() << "s)" << std::endl;
      mCRL2log(log::verbose) << "LDD size = " << nodecount(visited) << std::endl;
      mCRL2log(log::verbose) << "used variable order = " << core::detail::print_list(m_variable_order) << std::endl;

      return visited;
    }

    const std::vector<boost::dynamic_bitset<>>& read_write_patterns() const
    {
      return m_summand_patterns;
    }

    const std::vector<boost::dynamic_bitset<>>& read_write_group_patterns() const
    {
      return m_group_patterns;
    }
};

} // namespace lps

} // namespace mcrl2

#endif // MCRL2_LPS_LPSREACH_H