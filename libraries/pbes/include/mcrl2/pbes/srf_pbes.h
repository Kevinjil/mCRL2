// Author(s): Wieger Wesselink
// Copyright: see the accompanying file COPYING or copy at
// https://github.com/mCRL2org/mCRL2/blob/master/COPYING
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)
//
/// \file mcrl2/pbes/srf_pbes.h
/// \brief add your file description here.

#ifndef MCRL2_PBES_SRF_PBES_H
#define MCRL2_PBES_SRF_PBES_H

#include "mcrl2/core/detail/print_utility.h"
#include "mcrl2/data/set_identifier_generator.h"
#include "mcrl2/pbes/find.h"
#include "mcrl2/pbes/join.h"
#include "mcrl2/pbes/pbes.h"
#include "mcrl2/pbes/pbes_functions.h"

namespace mcrl2 {

namespace pbes_system {

class srf_summand
{
  protected:
    data::variable_list m_parameters;
    pbes_expression m_condition;
    propositional_variable_instantiation m_X;

  public:
    srf_summand(
      data::variable_list parameters,
      pbes_expression condition,
      propositional_variable_instantiation X
    )
     : m_parameters(std::move(parameters)), m_condition(std::move(condition)), m_X(std::move(X))
    {}

    const data::variable_list& parameters() const
    {
      return m_parameters;
    }

    data::variable_list& parameters()
    {
      return m_parameters;
    }

    const pbes_expression& condition() const
    {
      return m_condition;
    }

    pbes_expression& condition()
    {
      return m_condition;
    }

    const propositional_variable_instantiation& variable() const
    {
      return m_X;
    }

    propositional_variable_instantiation& variable()
    {
      return m_X;
    }

    void add_variables(const data::variable_list& variables)
    {
      m_parameters = variables + m_parameters;
    }

    void add_condition(const pbes_expression& f)
    {
      m_condition = and_(f, m_condition);
    }

    pbes_expression to_pbes(bool conjunctive) const
    {
      if (conjunctive)
      {
        return make_forall(m_parameters, imp(m_condition, m_X));
      }
      else
      {
        return make_exists(m_parameters, and_(m_condition, m_X));
      }
    }
};

inline
std::ostream& operator<<(std::ostream& out, const srf_summand& summand)
{
  return out << "variables = " << core::detail::print_list(summand.parameters()) << " f = " << summand.condition() << " X = " << summand.variable();
}

class srf_equation
{
  protected:
    fixpoint_symbol m_sigma;
    propositional_variable m_variable;
    std::vector<srf_summand> m_summands;
    bool m_conjunctive;

  public:
    explicit srf_equation(const fixpoint_symbol& sigma, const propositional_variable& variable, std::vector<srf_summand> summands, bool conjunctive)
      : m_sigma(sigma), m_variable(variable), m_summands(std::move(summands)), m_conjunctive(conjunctive)
    {}

    const fixpoint_symbol& symbol() const
    {
      return m_sigma;
    }

    fixpoint_symbol& symbol()
    {
      return m_sigma;
    }

    const propositional_variable& variable() const
    {
      return m_variable;
    }

    propositional_variable& variable()
    {
      return m_variable;
    }

    const std::vector<srf_summand>& summands() const
    {
      return m_summands;
    }

    std::vector<srf_summand>& summands()
    {
      return m_summands;
    }

    bool is_conjunctive() const
    {
      return m_conjunctive;
    }

    pbes_equation to_pbes() const
    {
      std::vector<pbes_expression> v;
      for (const srf_summand& summand: m_summands)
      {
        v.push_back(summand.to_pbes(m_conjunctive));
      }
      pbes_expression rhs = m_conjunctive ? join_and(v.begin(), v.end()) : join_or(v.begin(), v.end());
      return pbes_equation(m_sigma, m_variable, rhs);
    }
};

inline
std::ostream& operator<<(std::ostream& out, const srf_equation& eqn)
{
  out << "srf equation" << std::endl;
  for (const srf_summand& summand: eqn.summands())
  {
    out << summand << std::endl;
  }
  return out;
}

namespace detail {

std::vector<srf_summand> srf_or(
  const pbes_expression& phi,
  std::deque<pbes_equation>& equations,
  const pbes_equation& eqn,
  const data::variable_list& V,
  data::set_identifier_generator& id_generator,
  const core::identifier_string& X_true,
  const core::identifier_string& X_false,
  std::vector<srf_equation>& result
);

struct srf_or_traverser: public pbes_expression_traverser<srf_or_traverser>
{
  typedef pbes_expression_traverser<srf_or_traverser> super;
  using super::enter;
  using super::leave;
  using super::apply;

  // The remaining PBES equations
  std::deque<pbes_equation>& equations;

  // The current equation
  const pbes_equation& eqn;

  const data::variable_list& V;

  // Used for creating new equations
  data::set_identifier_generator& id_generator;

  // The names of the true and false equations
  const core::identifier_string& X_true;
  const core::identifier_string& X_false;

  // The equations of the resulting srf PBES
  std::vector<srf_equation>& result;

  // The summands of the generated equation
  std::vector<srf_summand> summands;

  srf_or_traverser(
    std::deque<pbes_equation>& equations_,
    const pbes_equation& eqn_,
    const data::variable_list& V_,
    data::set_identifier_generator& id_generator_,
    const core::identifier_string& X_true_,
    const core::identifier_string& X_false_,
    std::vector<srf_equation>& result_
  )
   : equations(equations_), eqn(eqn_), V(V_), id_generator(id_generator_), X_true(X_true_), X_false(X_false_), result(result_)
  {}

  void apply(const and_& x)
  {
    if (is_simple_expression(x.left()))
    {
      std::size_t size = summands.size();
      apply(x.right());
      for (auto i = summands.begin() + size; i != summands.end(); ++i)
      {
        i->add_condition(x.left());
      }
    }
    else if (is_simple_expression(x.right()))
    {
      std::size_t size = summands.size();
      apply(x.left());
      for (auto i = summands.begin() + size; i != summands.end(); ++i)
      {
        i->add_condition(x.right());
      }
    }
    else
    {
      const propositional_variable& X = eqn.variable();
      propositional_variable X1(id_generator(X.name()), V);
      const pbes_expression& f = true_();
      equations.push_front(pbes_equation(eqn.symbol(), X1, x));
      summands.emplace_back(data::variable_list(), f, propositional_variable_instantiation(X1.name(), data::make_data_expression_list(V)));
    }
  }

  void apply(const exists& x)
  {
    std::vector<srf_summand> body_summands = srf_or(x.body(), equations, eqn, V + x.variables(), id_generator, X_true, X_false, result);
    for (srf_summand& summand: body_summands)
    {
      summand.add_variables(x.variables());
    }
    summands.insert(summands.end(), body_summands.begin(), body_summands.end());
  }

  void apply(const forall& x)
  {
    if (is_simple_expression(x.body()))
    {
      const pbes_expression& f = x.body();
      const propositional_variable_instantiation& X = propositional_variable_instantiation(X_true, {});
      summands.emplace_back(x.variables(), f, X);
    }
    else
    {
      const propositional_variable& X = eqn.variable();
      propositional_variable X1(id_generator(X.name()), V);
      const pbes_expression& f = true_();
      equations.push_front(pbes_equation(eqn.symbol(), X1, x));
      summands.emplace_back(data::variable_list(), f, propositional_variable_instantiation(X1.name(), data::make_data_expression_list(V)));
    }
  }

  void apply(const propositional_variable_instantiation& x)
  {
    const pbes_expression& f = true_();
    summands.emplace_back(data::variable_list(), f, x);
  }

  void apply(const pbes_expression& x)
  {
    if (is_simple_expression(x))
    {
      const propositional_variable_instantiation& X = propositional_variable_instantiation(X_true, {});
      const pbes_expression& f = x;
      summands.emplace_back(data::variable_list(), f, X);
    }
    else
    {
      super::apply(x);
    }
  }

  void apply(const not_& /* x */)
  {
    throw mcrl2::runtime_error("unsupported term!");
  }

  void apply(const imp& /* x */)
  {
    throw mcrl2::runtime_error("unsupported term!");
  }
};

inline
std::vector<srf_summand> srf_or(
  const pbes_expression& phi,
  std::deque<pbes_equation>& equations,
  const pbes_equation& eqn,
  const data::variable_list& V,
  data::set_identifier_generator& id_generator,
  const core::identifier_string& X_true,
  const core::identifier_string& X_false,
  std::vector<srf_equation>& result
)
{
  srf_or_traverser f(equations, eqn, V, id_generator, X_true, X_false, result);
  f.apply(phi);
  return std::move(f.summands);
}

std::vector<srf_summand> srf_and(
  const pbes_expression& phi,
  std::deque<pbes_equation>& equations,
  const pbes_equation& eqn,
  const data::variable_list& V,
  data::set_identifier_generator& id_generator,
  const core::identifier_string& X_true,
  const core::identifier_string& X_false,
  std::vector<srf_equation>& result
);

struct srf_and_traverser: public pbes_expression_traverser<srf_and_traverser>
{
  typedef pbes_expression_traverser<srf_and_traverser> super;
  using super::enter;
  using super::leave;
  using super::apply;

  // The remaining PBES equations
  std::deque<pbes_equation>& equations;

  // The current equation
  const pbes_equation& eqn;

  const data::variable_list& V;

  // Used for creating new equations
  data::set_identifier_generator& id_generator;

  // The names of the true and false equations
  const core::identifier_string& X_true;
  const core::identifier_string& X_false;

  // The equations of the resulting srf PBES
  std::vector<srf_equation>& result;

  // The summands of the generated equation
  std::vector<srf_summand> summands;

  srf_and_traverser(
    std::deque<pbes_equation>& equations_,
    const pbes_equation& eqn_,
    const data::variable_list& V_,
    data::set_identifier_generator& id_generator_,
    const core::identifier_string& X_true_,
    const core::identifier_string& X_false_,
    std::vector<srf_equation>& result_
  )
    : equations(equations_), eqn(eqn_), V(V_), id_generator(id_generator_), X_true(X_true_), X_false(X_false_), result(result_)
  {}

  void apply(const or_& x)
  {
    if (is_simple_expression(x.left()))
    {
      std::size_t size = summands.size();
      apply(x.right());
      for (auto i = summands.begin() + size; i != summands.end(); ++i)
      {
        i->add_condition(not_(x.left()));
      }
    }
    else if (is_simple_expression(x.right()))
    {
      std::size_t size = summands.size();
      apply(x.left());
      for (auto i = summands.begin() + size; i != summands.end(); ++i)
      {
        i->add_condition(not_(x.right()));
      }
    }
    else
    {
      const propositional_variable& X = eqn.variable();
      propositional_variable X1(id_generator(X.name()), V);
      const pbes_expression& f = true_();
      equations.push_front(pbes_equation(eqn.symbol(), X1, x));
      summands.emplace_back(data::variable_list(), f, propositional_variable_instantiation(X1.name(), data::make_data_expression_list(V)));
    }
  }

  void apply(const forall& x)
  {
    std::vector<srf_summand> body_summands = srf_and(x.body(), equations, eqn, V + x.variables(), id_generator, X_true, X_false, result);
    for (srf_summand& summand: body_summands)
    {
      summand.add_variables(x.variables());
    }
    summands.insert(summands.end(), body_summands.begin(), body_summands.end());
  }

  void apply(const exists& x)
  {
    if (is_simple_expression(x.body()))
    {
      const pbes_expression& f = x.body();
      const propositional_variable_instantiation& X = propositional_variable_instantiation(X_true, {});
      summands.emplace_back(x.variables(), f, X);
    }
    else
    {
      const propositional_variable& X = eqn.variable();
      propositional_variable X1(id_generator(X.name()), V);
      const pbes_expression& f = true_();
      equations.push_front(pbes_equation(eqn.symbol(), X1, x));
      summands.emplace_back(data::variable_list(), f, propositional_variable_instantiation(X1.name(), data::make_data_expression_list(V)));
    }
  }

  void apply(const propositional_variable_instantiation& x)
  {
    const pbes_expression& f = true_();
    summands.emplace_back(data::variable_list(), f, x);
  }

  void apply(const pbes_expression& x)
  {
    if (is_simple_expression(x))
    {
      const propositional_variable_instantiation& X = propositional_variable_instantiation(X_false, {});
      const pbes_expression& f = x;
      summands.emplace_back(data::variable_list(), not_(f), X);
    }
    else
    {
      super::apply(x);
    }
  }

  void apply(const not_& /* x */)
  {
    throw mcrl2::runtime_error("unsupported term!");
  }

  void apply(const imp& /* x */)
  {
    throw mcrl2::runtime_error("unsupported term!");
  }
};

inline
std::vector<srf_summand> srf_and(
  const pbes_expression& phi,
  std::deque<pbes_equation>& equations,
  const pbes_equation& eqn,
  const data::variable_list& V,
  data::set_identifier_generator& id_generator,
  const core::identifier_string& X_true,
  const core::identifier_string& X_false,
  std::vector<srf_equation>& result
)
{
  srf_and_traverser f(equations, eqn, V, id_generator, X_true, X_false, result);
  f.apply(phi);
  return std::move(f.summands);
}

inline
bool is_conjunctive(const pbes_expression& phi)
{
  if (is_simple_expression(phi))
  {
    return false;
  }
  else if (is_propositional_variable_instantiation(phi))
  {
    return false;
  }
  else if (is_or(phi))
  {
    const auto& phi_ = atermpp::down_cast<or_>(phi);
    return is_simple_expression(phi_.left()) || is_simple_expression(phi_.right());
  }
  else if (is_and(phi))
  {
    const auto& phi_ = atermpp::down_cast<or_>(phi);
    return !is_simple_expression(phi_.left()) && !is_simple_expression(phi_.right());
  }
  else if (is_exists(phi))
  {
    return false;
  }
  else if (is_forall(phi))
  {
    return true;
  }
  throw mcrl2::runtime_error("is_conjunctive: unexpected case " + pbes_system::pp(phi));
}

} // namespace detail

// explicit representation of a pbes in SRF format
class srf_pbes
{
  protected:
    data::data_specification m_dataspec;
    std::vector<srf_equation> m_equations;
    propositional_variable_instantiation m_initial_state;

  public:
    srf_pbes(
      const data::data_specification& dataspec,
      std::vector<srf_equation> equations,
      propositional_variable_instantiation initial_state
    )
      : m_dataspec(dataspec), m_equations(std::move(equations)), m_initial_state(std::move(initial_state))
    {}

    const std::vector<srf_equation>& equations() const
    {
      return m_equations;
    }

    std::vector<srf_equation>& equations()
    {
      return m_equations;
    }

    const propositional_variable_instantiation& initial_state() const
    {
      return m_initial_state;
    }

    propositional_variable_instantiation& initial_state()
    {
      return m_initial_state;
    }

    const data::data_specification& data() const
    {
      return m_dataspec;
    }

    pbes to_pbes() const
    {
      std::vector<pbes_equation> v;
      for (const srf_equation& eqn: equations())
      {
        v.push_back(eqn.to_pbes());
      }
      return pbes(m_dataspec, v, m_initial_state);
    }
};

/// \brief Converts a PBES into standard recursive form
/// \pre The pbes p must be normalized
inline
srf_pbes pbes2srf(const pbes& p)
{
  data::set_identifier_generator id_generator;
  for (const core::identifier_string& id: pbes_system::find_identifiers(p))
  {
    id_generator.add_identifier(id);
  }

  core::identifier_string X_false = id_generator("X_false");
  core::identifier_string X_true = id_generator("X_true");
  pbes_equation eqn_false(fixpoint_symbol::mu(), propositional_variable(X_false, {}), propositional_variable_instantiation(X_false, {}));
  pbes_equation eqn_true(fixpoint_symbol::nu(), propositional_variable(X_true, {}), propositional_variable_instantiation(X_true, {}));

  const auto& p_equations = p.equations();
  std::deque<pbes_equation> equations(p_equations.begin(), p_equations.end());
  equations.emplace_back(eqn_false);
  equations.emplace_back(eqn_true);

  std::vector<srf_equation> srf_equations;
  while (!equations.empty())
  {
    pbes_equation eqn = equations.front();
    equations.pop_front();
    bool is_conjunctive = detail::is_conjunctive(eqn.formula());
    std::vector<srf_summand> summands = is_conjunctive ?
      detail::srf_and(eqn.formula(), equations, eqn, eqn.variable().parameters(), id_generator, X_true, X_false, srf_equations) :
      detail::srf_or(eqn.formula(), equations, eqn, eqn.variable().parameters(), id_generator, X_true, X_false, srf_equations);
    srf_equations.emplace_back(eqn.symbol(), eqn.variable(), summands, is_conjunctive);
  }

  return srf_pbes(p.data(), std::vector<srf_equation>(srf_equations.begin(), srf_equations.end()), p.initial_state());
}

} // namespace pbes_system

} // namespace mcrl2

#endif // MCRL2_PBES_SRF_PBES_H