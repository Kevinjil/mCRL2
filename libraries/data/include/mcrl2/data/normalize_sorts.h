// Author(s): Wieger Wesselink
// Copyright: see the accompanying file COPYING or copy at
// https://github.com/mCRL2org/mCRL2/blob/master/COPYING
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)
//
/// \file mcrl2/data/normalize_sorts.h
/// \brief add your file description here.

#ifndef MCRL2_DATA_NORMALIZE_SORTS_H
#define MCRL2_DATA_NORMALIZE_SORTS_H

#include "mcrl2/atermpp/standard_containers/vector.h"
#include "mcrl2/data/builder.h"
#include "mcrl2/data/sort_specification.h"

namespace mcrl2
{

namespace data
{

namespace detail
{

struct normalize_sorts_function
{
  using argument_type = sort_expression;
  using result_type = sort_expression;

  /* const sort_specification& m_sort_spec; */
  const std::map<sort_expression, sort_expression>& m_normalised_aliases;

  normalize_sorts_function(const sort_specification& sort_spec)
    : m_normalised_aliases(sort_spec.sort_alias_map())
  {
  }

  ///\brief Normalise sorts.
  sort_expression operator()(const sort_expression& e) const
  {
    sort_expression result;
    this->operator()(result, e);
    return result;
  }

  void operator()(sort_expression& result, const sort_expression& e) const
  {
    // This routine takes the map m_normalised_aliases which contains pairs of sort expressions
    // <A,B> and takes all these pairs as rewrite rules, which are applied to e using an innermost
    // strategy. Note that it is assumed that m_normalised_aliases contain rewrite rules <A,B>, such
    // that B is a normal form. This allows to check that if e matches A, then we can return B.

    const std::map<sort_expression, sort_expression>::const_iterator i1=m_normalised_aliases.find(e);
    if (i1 != m_normalised_aliases.end())
    {
      result = i1->second;
      return;
    }

    // Expression `result` will be a placeholder for the sort of which all
    // arguments will be normalised.
    result = e;

    // We do not have to do anything if e is a basic sort, as result=e.
    if (is_function_sort(e))
    {
      data::make_function_sort(result,
          [&](sort_expression_list& result_l){ atermpp::make_term_list<sort_expression>(
              result_l,
              atermpp::down_cast<function_sort>(e).domain().begin(),
              atermpp::down_cast<function_sort>(e).domain().end(),
              [&](sort_expression& result, const sort_expression& x){ this->operator()(result, x); }); },
          [&](sort_expression& result){ this->operator()(result, atermpp::down_cast<function_sort>(e).codomain()); });
    }
    else if (is_container_sort(e))
    {
      // Rewrite the argument of the container sort to normal form.
      data::make_container_sort(result,
        atermpp::down_cast<container_sort>(e).container_name(),
        [&](sort_expression& result){ this->operator()(result, atermpp::down_cast<container_sort>(e).element_sort()); });
    }
    else if (is_structured_sort(e))
    {
      // Rewrite the argument sorts to normal form.
      data::make_structured_sort(result,
          [&](structured_sort_constructor_list& result_l)
          {
            atermpp::make_term_list<structured_sort_constructor>(result_l,
                atermpp::down_cast<structured_sort>(e).constructors().begin(),
                atermpp::down_cast<structured_sort>(e).constructors().end(),
                [&](structured_sort_constructor& result, const structured_sort_constructor& x)
                {
                  make_structured_sort_constructor(
                      result,
                      x.name(),
                      [&](structured_sort_constructor_argument_list& result_l)
                      {
                        atermpp::make_term_list<structured_sort_constructor_argument>(result_l,
                            x.arguments().begin(),
                            x.arguments().end(),
                            [&](structured_sort_constructor_argument& result,
                                const structured_sort_constructor_argument& x)
                            {
                              data::make_structured_sort_constructor_argument(result,
                                  x.name(),
                                  [&](sort_expression& result) { this->operator()(result, x.sort()); });
                            });
                      },
                      x.recogniser());
                });
          });
    }

    // The arguments of `result` are now in normal form.
    // Rewrite it to normal form.
    const std::map<sort_expression, sort_expression>::const_iterator i2=m_normalised_aliases.find(result);
    if (i2 != m_normalised_aliases.end())
    {
      this->operator()(result, i2->second); // rewrite the result until normal form.
    }
    return;
  }

};

} // namespace detail


template <typename T>
void normalize_sorts(T& x,
                     const data::sort_specification& sort_spec,
                     typename std::enable_if< !std::is_base_of<atermpp::aterm, T>::value >::type* = nullptr
                    )
{
  core::make_update_apply_builder<data::sort_expression_builder>
  (data::detail::normalize_sorts_function(sort_spec)).update(x);
} 

template <typename T>
void normalize_sorts(T& result,
                  const T& x,
                  const data::sort_specification& sort_spec,
                  typename std::enable_if< std::is_base_of<atermpp::aterm, T>::value >::type* = nullptr
                 )
{
  core::make_update_apply_builder<data::sort_expression_builder>
         (data::detail::normalize_sorts_function(sort_spec)).apply(result, x);
}

template <typename T>
T normalize_sorts(const T& x,
                  const data::sort_specification& sort_spec,
                  typename std::enable_if< std::is_base_of<atermpp::aterm, T>::value >::type* = nullptr
                 )
{
  T result;
  core::make_update_apply_builder<data::sort_expression_builder>
         (data::detail::normalize_sorts_function(sort_spec)).apply(result, x);
  return result;
}

/* The functions below are defined as the function normalize_sorts
   above does not work on other sorts than sort expressions. 

inline sort_expression normalize_sorts(const basic_sort& x,
                                       const data::sort_specification& sort_spec)
{
  return normalize_sorts(static_cast<sort_expression>(x),sort_spec);
}

inline sort_expression normalize_sorts(const function_sort& x,
                                       const data::sort_specification& sort_spec)
{
  return normalize_sorts(static_cast<sort_expression>(x),sort_spec);
}

inline sort_expression normalize_sorts(const container_sort& x,
                                       const data::sort_specification& sort_spec)
{
  return normalize_sorts(static_cast<sort_expression>(x),sort_spec);
}

inline sort_expression normalize_sorts(const structured_sort& x,
                                       const data::sort_specification& sort_spec)
{
  return normalize_sorts(static_cast<sort_expression>(x),sort_spec);
}
*/

} // namespace data

} // namespace mcrl2

#endif // MCRL2_DATA_NORMALIZE_SORTS_H
