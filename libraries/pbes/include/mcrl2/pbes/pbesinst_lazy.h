// Author(s): Wieger Wesselink 2017-2019
// Copyright: see the accompanying file COPYING or copy at
// https://github.com/mCRL2org/mCRL2/blob/master/COPYING
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)
//
/// \file mcrl2/pbes/pbesinst_lazy_algorithm.h
/// \brief A lazy algorithm for instantiating a PBES, ported from bes_deprecated.h.

#include <thread>

#include "mcrl2/data/substitution_utility.h"
#include "mcrl2/pbes/detail/bes_equation_limit.h"
#include "mcrl2/pbes/detail/instantiate_global_variables.h"
#include "mcrl2/pbes/pbes_equation_index.h"
#include "mcrl2/pbes/pbessolve_options.h"
#include "mcrl2/pbes/remove_equations.h"
#include "mcrl2/pbes/replace_constants_by_variables.h"
#include "mcrl2/pbes/rewriters/enumerate_quantifiers_rewriter.h"
#include "mcrl2/pbes/rewriters/one_point_rule_rewriter.h"
#include "mcrl2/pbes/rewriters/simplify_quantifiers_rewriter.h"
#include "mcrl2/pbes/transformation_strategy.h"
#include "mcrl2/pbes/transformations.h"

#ifndef MCRL2_PBES_PBESINST_LAZY_H
#define MCRL2_PBES_PBESINST_LAZY_H

namespace mcrl2
{

namespace pbes_system
{

// This todo set maintains elements that were removed by the reset procedure.
class pbesinst_lazy_todo
{
  protected:
    std::unordered_set<propositional_variable_instantiation> irrelevant;
    std::deque<propositional_variable_instantiation> todo;

    // checks some invariants on the internal state
    bool check_invariants() const
    {
      using utilities::detail::contains;
      for (const auto& X: irrelevant)
      {
        if (contains(todo, X))
        {
          return false;
        }
      }
      std::unordered_set<propositional_variable_instantiation> tmp(todo.begin(), todo.end());
      return tmp.size() == todo.size();
    }

  public:
    const propositional_variable_instantiation& front() const
    {
      return todo.front();
    }

    const propositional_variable_instantiation& back() const
    {
      return todo.back();
    }

    bool empty() const
    {
      return todo.empty() && irrelevant.empty();
    }

    std::size_t size() const
    {
      return todo.size();
    }

    const std::deque<propositional_variable_instantiation>& elements() const
    {
      return todo;
    }

    const std::unordered_set<propositional_variable_instantiation>& irrelevant_elements() const
    {
      return irrelevant;
    }

    std::unordered_set<propositional_variable_instantiation>& irrelevant_elements()
    {
      return irrelevant;
    }

    std::vector<propositional_variable_instantiation> all_elements() const
    {
      std::vector<propositional_variable_instantiation> result;
      result.insert(result.end(), todo.begin(), todo.end());
      result.insert(result.end(), irrelevant.begin(), irrelevant.end());
      return result;
    }

    void pop_front()
    {
      todo.pop_front();
    }

    void pop_back()
    {
      todo.pop_back();
    }

    void insert(const propositional_variable_instantiation& x)
    {
      irrelevant.erase(x);
      todo.push_back(x);
    }

    template <typename FwdIter>
    void insert(FwdIter first, FwdIter last, const std::unordered_set<propositional_variable_instantiation>& discovered)
    {
      using utilities::detail::contains;

      for (FwdIter i = first; i != last; ++i)
      {
        auto j = irrelevant.find(*i);
        if (j != irrelevant.end())
        {
          todo.push_back(*j);
          irrelevant.erase(j);
        }
        else if (!contains(discovered, *i))
        {
          todo.push_back(*i);
        }
      }
    }

    void set_todo(std::deque<propositional_variable_instantiation>& new_todo)
    {
      using utilities::detail::contains;
      std::size_t size_before = todo.size() + irrelevant.size();

      std::unordered_set<propositional_variable_instantiation> new_irrelevant;
      for (const propositional_variable_instantiation& x: all_elements())
      {
        if (!contains(new_todo, x))
        {
          new_irrelevant.insert(x);
        }
      }
      std::swap(todo, new_todo);
      std::swap(irrelevant, new_irrelevant);

      std::size_t size_after = todo.size() + irrelevant.size();
      if (size_before != size_after)
      {
        throw mcrl2::runtime_error("sizes do not match in pbesinst_lazy_todo::set_todo");
      }
      assert(check_invariants());
    }
};

inline
std::ostream& operator<<(std::ostream& out, const pbesinst_lazy_todo& todo)
{
  return out << "todo = " << core::detail::print_list(todo.elements()) << " irrelevant = " << core::detail::print_list(todo.irrelevant_elements()) << std::endl;
}

/// \brief A PBES instantiation algorithm that uses a lazy strategy
class pbesinst_lazy_algorithm
{
  protected:
    /// \brief Algorithm options.
    const pbessolve_options& m_options;

    /// \brief Data rewriter.
    data::rewriter datar;

    /// \brief A PBES.
    pbes m_pbes;

    /// \brief A lookup map for PBES equations.
    pbes_equation_index m_equation_index;

    /// \brief The propositional variable instantiations that need to be handled.
    pbesinst_lazy_todo todo;

    /// \brief The propositional variable instantiations that have been discovered (not necessarily handled).
    std::unordered_set<propositional_variable_instantiation> discovered;

    /// \brief The initial value (after rewriting).
    propositional_variable_instantiation init;

    // \brief The number of iterations
    std::size_t m_iteration_count = 0;

    // The data structures that must be separate per thread.
    mutable data::mutable_indexed_substitution<> m_global_sigma;
    /// \brief The rewriter.
    enumerate_quantifiers_rewriter m_global_R;

    // Mutexes
    std::mutex m_exclusive_todo_access;
    std::mutex m_exclusive_graph_access;

    volatile bool m_must_abort = false;

    // \brief Returns a status message about the progress
    virtual std::string status_message(std::size_t equation_count)
    {
      if (equation_count > 0 && equation_count % 1000 == 0)
      {
        std::ostringstream out;
        out << "Generated " << equation_count << " BES equations" << std::endl;
        return out.str();
      }
      return "";
    }

    // instantiates global variables
    // simplifies the pbes
    pbes preprocess(const pbes& x) const
    {
      pbes p = x;
      pbes_system::detail::instantiate_global_variables(p);
      pbes_system::one_point_rule_rewriter one_point_rule_rewriter;
      pbes_system::simplify_quantifiers_data_rewriter<mcrl2::data::rewriter> simplify_rewriter(datar);
      for (pbes_equation& eqn: p.equations())
      {
        eqn.formula() = order_quantified_variables(one_point_rule_rewriter(simplify_rewriter(eqn.formula())), p.data());
      }
      return p;
    }

    static void rewrite_true_false(
        pbes_expression& result,
        const fixpoint_symbol& symbol,
        const propositional_variable_instantiation& X,
        const pbes_expression& psi
      )
    {
      bool changed = false;
      pbes_expression value;
      if (symbol.is_mu())
      {
        value = false_();
      }
      else
      {
        value = true_();
      }

      auto simplify = [&](pbes_expression& result, pbes_expression exp) -> void {
        if (changed) {
          simplify_rewriter simplify;
          result = simplify(exp);
          return;
        }
        result = exp;
      };

      simplify(
        result,
        replace_propositional_variables(
          psi,
          [&](const propositional_variable_instantiation& Y) -> pbes_expression {
              if (Y == X)
              {
                changed = true;
                return value;
              }
              return Y;
          }
        )
      );
    }

    data::rewriter construct_rewriter(const pbes& pbesspec)
    {
      if (m_options.remove_unused_rewrite_rules)
      {
        return data::rewriter(pbesspec.data(),
                              data::used_data_equation_selector(pbesspec.data(), pbes_system::find_function_symbols(pbesspec), pbesspec.global_variables()),
                              m_options.rewrite_strategy);
      }
      else
      {
        return data::rewriter(pbesspec.data(), m_options.rewrite_strategy);
      }
    }

  public:

    /// \brief Constructor.
    /// \param p The pbes used in the exploration algorithm.
    /// \param rewrite_strategy A strategy for the data rewriter.
    /// \param search_strategy The search strategy used to explore the pbes, typically depth or breadth first.
    /// \param optimization An indication of the optimisation level.
    explicit pbesinst_lazy_algorithm(
      const pbessolve_options& options,
      const pbes& p
    )
     : m_options(options),
       datar(construct_rewriter(p)),
       m_pbes(preprocess(p)),
       m_equation_index(p),
       m_global_R(datar, p.data())
    { }

    virtual ~pbesinst_lazy_algorithm() = default;

    /// \brief Reports BES equations that are produced by the algorithm.
    /// This function is called for every BES equation X = psi with rank k that is produced. By default it does nothing.
    virtual void on_report_equation(const propositional_variable_instantiation& /* X */, const pbes_expression& /* psi */, std::size_t /* k */)
    { }

    /// \brief This function is called when new elements are added to discovered.
    virtual void on_discovered_elements(const std::set<propositional_variable_instantiation>& /* elements */)
    { }

    /// \brief This function is called right after the while loop is finished.
    virtual void on_end_while_loop()
    { }

    void next_todo(propositional_variable_instantiation& result)
    {
      if (m_options.exploration_strategy == breadth_first)
      {
        result = todo.front();
        todo.pop_front();
      }
      else
      {
        result = todo.back();
        todo.pop_back();
      }
    }

    const fixpoint_symbol& symbol(std::size_t i) const
    {
      return m_pbes.equations()[i].symbol();
    }

    // rewrite the right hand side of the equation X = psi
    virtual void rewrite_psi(
      pbes_expression& result,
      const fixpoint_symbol& symbol,
      const propositional_variable_instantiation& X,
      const pbes_expression& psi
    )
    {
      if (m_options.optimization >= 1)
      {
        rewrite_true_false(result, symbol, X, psi);
      }
      else
      {
        result = psi;
      }
    }

    virtual bool solution_found(const propositional_variable_instantiation& /* init */) const
    {
      return false;
    }

    virtual void run_thread(
      pbesinst_lazy_todo* todo,
      const std::size_t process_number,
      std::atomic<std::size_t>& number_of_active_processes,
      data::mutable_indexed_substitution<> sigma,
      enumerate_quantifiers_rewriter R
    )
    {
      mCRL2log(log::verbose) << "Start thread " << process_number << ".\n";
      R.thread_initialise();

      // Local variables to store results, to prevent unneccessary assignments of aterms
      propositional_variable_instantiation X_e;
      pbes_expression psi_e;

      while (number_of_active_processes > 0) {
        if (m_options.number_of_threads>0) m_exclusive_todo_access.lock();
        while (!todo->elements().empty() && !m_must_abort)
        {
          ++m_iteration_count;
          mCRL2log(log::status) << status_message(m_iteration_count);
          detail::check_bes_equation_limit(m_iteration_count);

          next_todo(X_e);

          if (m_options.number_of_threads>0) m_exclusive_todo_access.unlock();

          std::size_t index = m_equation_index.index(X_e.name());
          const pbes_equation& eqn = m_pbes.equations()[index];
          const auto& phi = eqn.formula();
          data::add_assignments(sigma, eqn.variable().parameters(), X_e.parameters());

          rewrite_psi(psi_e, eqn.symbol(), X_e, R(phi, sigma));
          R.clear_identifier_generator();
          data::remove_assignments(sigma, eqn.variable().parameters());

          // report the generated equation
          std::size_t k = m_equation_index.rank(X_e.name());
          mCRL2log(log::debug) << "generated equation " << X_e << " = " << psi_e << " with rank " << k << std::endl;

          if (m_options.number_of_threads>0) m_exclusive_graph_access.lock();
          on_report_equation(X_e, psi_e, k);
          if (m_options.number_of_threads>0) m_exclusive_graph_access.unlock();

          std::set<propositional_variable_instantiation> occ = find_propositional_variable_instantiations(psi_e);

          if (m_options.number_of_threads>0) m_exclusive_todo_access.lock();

          todo->insert(occ.begin(), occ.end(), discovered);
          discovered.insert(occ.begin(), occ.end());
          on_discovered_elements(occ);

          if (solution_found(init))
          {
            m_must_abort = true;
          }
        }
        if (m_options.number_of_threads>0) m_exclusive_todo_access.unlock();

        // Check whether all processes are ready. If so the number_of_active_processes becomes 0.
        // Otherwise, this thread becomes active again, and tries to see whether the todo buffer is
        // not empty, to take up more work.
        number_of_active_processes--;
        std::this_thread::sleep_for(std::chrono::milliseconds(100));
        if (number_of_active_processes>0)
        {
          number_of_active_processes++;
        }
      }
      mCRL2log(log::verbose) << "Stop thread " << process_number << ".\n";
    }

    /// \brief Runs the algorithm. The result is obtained by calling the function \p get_result.
    virtual void run()
    {
      using utilities::detail::contains;

      std::atomic<size_t> m_iteration_count(0);

      if (m_options.replace_constants_by_variables)
      {
        pbes_system::replace_constants_by_variables(m_pbes, datar, m_global_sigma);
      }

      init = atermpp::down_cast<propositional_variable_instantiation>(m_global_R(m_pbes.initial_state(), m_global_sigma));
      todo.insert(init);
      discovered.insert(init);
      const std::size_t number_of_threads=m_options.number_of_threads;
      std::vector<std::thread> threads;
      std::atomic<std::size_t> number_of_active_processes=number_of_threads;

      threads.reserve(number_of_threads);

      for(std::size_t i=0; i<number_of_threads; ++i)
      {
        std::thread tr([&, i](){
          run_thread(
            &todo,
            i,
            number_of_active_processes,
            m_global_sigma,
            m_global_R.clone()
          );
        });
        threads.push_back(std::move(tr));
      }

      for(std::size_t i=0; i<number_of_threads; ++i)
      {
        threads[i].join();
      }

      on_end_while_loop();
    }

    const pbes_equation_index& equation_index() const
    {
      return m_equation_index;
    }

    enumerate_quantifiers_rewriter& rewriter()
    {
      return m_global_R;
    }
};

} // namespace pbes_system

} // namespace mcrl2

#endif // MCRL2_PBES_PBESINST_LAZY_H
