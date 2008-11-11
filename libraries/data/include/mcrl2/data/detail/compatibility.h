// Author(s): Jeroen Keiren
// Copyright: see the accompanying file COPYING or copy at
// https://svn.win.tue.nl/trac/MCRL2/browser/trunk/COPYING
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)
//
/// \file mcrl2/data/detail/compatibility.h
/// \brief Conversion utilities for transforming between terms in the old
//         datatype format and the new format.

#ifndef MCRL2_DATA_DETAIL_COMPATIBILITY_H
#define MCRL2_DATA_DETAIL_COMPATIBILITY_H

#include "mcrl2/atermpp/map.h"
#include "mcrl2/atermpp/aterm_access.h"
#include "mcrl2/core/detail/struct_core.h"
#include "mcrl2/data/sort_expression.h"
#include "mcrl2/data/function_symbol.h"
#include "mcrl2/data/data_equation.h"

namespace mcrl2 {

  namespace data {

    namespace detail {

      /// \brief Convert a sort specification in the old data format before data
      ///        implementation to a list of sort expressions in the new data format.
      /// \param sort_spec A sort specification in the old data format before
      ///                 data implementation.
      /// \ret A list of sort expressions in the new data format, containing
      ///      exactly one equivalent for each sort in sort_spec.
      inline
      sort_expression_list aterm_sort_spec_to_sort_expression_list(const atermpp::aterm_appl& sort_spec)
      {
        assert(core::detail::gsIsSortSpec(sort_spec));

        atermpp::term_list<atermpp::aterm_appl> sl = list_arg1(sort_spec);
        return sort_expression_list(sl.begin(), sl.end());
      }

      /// \brief Convert a constructor specification in the old data format
      ///        before data implementation to a mapping of sort expressions to
      ///        constructor declarations in the new data format.
      /// \param cons_spec A constructor specification in the old data format
      ///        before data implementation.
      /// \ret A mapping of sort expressions to the corresponding constructor
      ///      declarations in the new data format.
      inline
      atermpp::map<sort_expression, function_symbol_list> aterm_cons_spec_to_constructor_map(const atermpp::aterm_appl& cons_spec)
      {
        assert(core::detail::gsIsConsSpec(cons_spec));

        atermpp::map<sort_expression, function_symbol_list> m;
        atermpp::term_list<atermpp::aterm_appl> cl = atermpp::list_arg1(cons_spec);

        for(atermpp::term_list<atermpp::aterm_appl>::iterator i = cl.begin(); i != cl.end(); ++i)
        {
          sort_expression s = function_symbol(*i).sort().target_sort();
          atermpp::map<sort_expression, function_symbol_list>::iterator m_i = m.find(s);
          if(m_i == m.end())
          {
            m[s] = make_vector(function_symbol(*i));
          }
          else
          {
            m_i->second.push_back(function_symbol(*i));
          }
        }

        return m;
      }

      /// \brief Convert a map specification in the old data format before data
      ///        implementation to a list of function symbols in the new data format.
      /// \param map_spec A map specification in the old data format before
      ///                 data implementation.
      /// \ret A list of function declaration in the new data format, containing
      ///      exactly one equivalent for each function in map_spec.
      inline
      function_symbol_list aterm_map_spec_to_function_list(const atermpp::aterm_appl& map_spec)
      {
        assert(core::detail::gsIsMapSpec(map_spec));

        atermpp::term_list<atermpp::aterm_appl> fl = atermpp::list_arg1(map_spec);
        return function_symbol_list(fl.begin(), fl.end());
      }

      /// \brief Convert an equation specification in the old data format before data
      ///        implementation to a list of data equations in the new data format.
      /// \param eqn_spec An equation specification in the old data format before
      ///                 data implementation.
      /// \ret A list of data equations in the new data format, containing
      ///      exactly one equivalent for each equation in eqn_spec.
      inline
      data_equation_list aterm_data_eqn_spec_to_equation_list(const atermpp::aterm_appl& eqn_spec)
      {
        assert(core::detail::gsIsDataEqnSpec(eqn_spec));

        atermpp::term_list<atermpp::aterm_appl> el = atermpp::list_arg1(eqn_spec);
        return data_equation_list(el.begin(), el.end());
      }

      /// \brief Convert a list of sort expressions in the new data format to a sort
      ///        specification in the old data format before data implementation.
      /// \param sl A list of sort expressions.
      /// \ret The sort specification in the old data format equivalent to sl.
      inline
      atermpp::aterm_appl sort_expression_list_to_aterm_sort_spec(const boost::iterator_range<sort_expression_list::const_iterator>& sl)
      {
        return core::detail::gsMakeSortSpec(atermpp::aterm_list(sl.begin(), sl.end()));
      }

      /// \brief Convert a list of function symbols in the new data format to a constructor
      ///        specification in the old data format before data implementation.
      /// \param cl A list of function symbols.
      /// \ret The constructor specification in the old data format equivalent to cl.
      inline
      atermpp::aterm_appl constructor_list_to_aterm_cons_spec(const boost::iterator_range<function_symbol_list::const_iterator>& cl)
      {
        return core::detail::gsMakeConsSpec(atermpp::aterm_list(cl.begin(), cl.end()));
      }

      /// \brief Convert a list of function symbols in the new data format to a map
      ///        specification in the old data format before data implementation.
      /// \param fl A list of function symbols.
      /// \ret The map specification in the old data format equivalent to fl.
      inline
      atermpp::aterm_appl function_list_to_aterm_map_spec(const boost::iterator_range<function_symbol_list::const_iterator>& fl)
      {
        return core::detail::gsMakeMapSpec(atermpp::aterm_list(fl.begin(), fl.end()));
      }

      /// \brief Convert a list of data equations in the new data format to an equation
      ///        specification in the old data format before data implementation.
      /// \param el A list of data equations.
      /// \ret The equation specification in the old data format equivalent to el.
      inline
      atermpp::aterm_appl data_equation_list_to_aterm_eqn_spec(const boost::iterator_range<data_equation_list::const_iterator>& el)
      {
        return core::detail::gsMakeDataEqnSpec(atermpp::aterm_list(el.begin(), el.end()));
      }

    } // namespace detail
    
  } // namespace data

} // namespace mcrl2

#endif //MCRL2_DATA_DETAIL_COMPATIBILITY_H

