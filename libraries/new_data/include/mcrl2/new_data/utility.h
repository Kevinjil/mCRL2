// Author(s): Jeroen Keiren, Jeroen van der Wulp, Wieger Wesselink
// Copyright: see the accompanying file COPYING or copy at
// https://svn.win.tue.nl/trac/MCRL2/browser/trunk/COPYING
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)
//
/// \file mcrl2/new_data/utility.h
/// \brief Provides utilities for working with lists.

#ifndef MCRL2_NEW_DATA_UTILITY_H
#define MCRL2_NEW_DATA_UTILITY_H

#include <algorithm>
#include <functional>
#include <iterator>
#include <set>
#include <string>
#include <utility>
#include <vector>

#include "boost/format.hpp"

#include "mcrl2/new_data/assignment.h"
#include "mcrl2/new_data/detail/data_utility.h"
#include "mcrl2/new_data/data_expression_utility.h"
#include "mcrl2/core/print.h"

namespace mcrl2 {

  namespace new_data {

    template < typename SubstitutionFunction >
    inline data_expression substitute(SubstitutionFunction const& f, data_expression const& c)
    {
      return data_expression(f(c));
    }

    /// \brief Applies the assignment to t and returns the result.
    /// \param c an assignment to apply to the expression
    /// \param e the expression on which to apply the assignment
    /// \return The application of the assignment to the term.
    template < >
    inline data_expression substitute(assignment const& c, data_expression const& e)
    {
      return atermpp::replace(e, atermpp::aterm(c.lhs()), atermpp::aterm(c.rhs()));
    }

    /// \brief Applies a substitution function to all elements of a container
    /// \param[in] f substitution function
    /// \param[in,out] c applies substitution function on elements of container
    template < typename Container, typename SubstitutionFunction >
    Container& substitute(SubstitutionFunction const& f, Container& c)
    {
      for (typename Container::iterator i = c.begin(); i != c.end(); ++i)
      {
        *i = f(*i);
      }

      return c;
    }

    /// \brief Applies a substitution function to all elements of a container
    template < typename Container, typename SubstitutionFunction, typename OutputIterator >
    void substitute(SubstitutionFunction const& f, Container const& c, OutputIterator o)
    {
      for (typename Container::const_iterator i = c.begin(); i != c.end(); ++i, ++o)
      {
        *o = f(*i);
      }
    }

    /// \brief Pretty prints the contents of a container
    template < typename Container >
    inline std::string pp(Container const& c)
    {
      std::string result;

      if (c.begin() != c.end())
      {
        result.append(mcrl2::core::pp(*c.begin()));

        for (typename Container::const_iterator i = ++(c.begin()); i != c.end(); ++i)
        {
          result.append(", ").append(mcrl2::core::pp(*i));
        }
      }

      return result;
    }

    /// \brief Returns a copy of t, but with a common postfix added to each variable name,
    /// and such that the new names do not appear in context.
    /// \param t A sequence of data variables
    /// \param context A set of strings
    /// \param postfix_format A string
    /// \return A sequence of variables with names that do not appear in \p context. The
    /// string \p postfix_format is used to generate new names. It should contain one
    /// occurrence of "%d", that will be replaced with an integer.
    inline
    variable_list fresh_variables(variable_list const& t, const std::set<std::string>& context, std::string postfix_format = "_%02d")
    {
      std::vector<std::string> ids = detail::variable_strings(t);
      std::string postfix;
      for (int i = 0; ; i++)
      {
        postfix = str(boost::format(postfix_format) % i);
        std::vector<std::string>::iterator j = ids.begin();
        for ( ; j != ids.end(); j++)
        {
          if (context.find(*j + postfix) != context.end())
            break;
        }
        if (j == ids.end()) // success!
          break;
      }
      variable_list result;
      for (variable_list::const_iterator k = t.begin(); k != t.end(); ++k)
      {
        core::identifier_string name(std::string(k->name()) + postfix);
        result.push_back(variable(name, k->sort()));
      }
      return result;
    }

    /// \brief Returns an identifier that doesn't appear in the set <tt>context</tt>
    /// \param context A set of strings
    /// \param hint A string
    /// \param id_creator A function that generates identifiers
    /// \return An identifier that doesn't appear in the set <tt>context</tt>
    template <typename IdentifierCreator>
    inline core::identifier_string fresh_identifier(const std::set<core::identifier_string>& context, const std::string& hint, IdentifierCreator id_creator = IdentifierCreator())
    {
      int index = 0;
      core::identifier_string s;
      do
      {
        s = core::identifier_string(id_creator(hint, index++));
      }
      while(context.find(s) != context.end());
      return s;
    }

    /// \brief Returns an identifier that doesn't appear in the term context
    /// \param context A term
    /// \param hint A string
    /// \param id_creator A function that generates identifiers
    /// \return An identifier that doesn't appear in the term context
    template <typename Term, class IdentifierCreator>
    core::identifier_string fresh_identifier(Term context, const std::string& hint, IdentifierCreator id_creator = IdentifierCreator())
    {
      return fresh_identifier(core::find_identifiers(context), hint, id_creator);
    }

    /// \brief Creates an identifier built from name and index.
    struct default_identifier_creator
    {
      /// \brief Constructor.
      /// \param name A string
      /// \param index A positive number.
      /// \return An identifier.
      std::string operator()(const std::string& name, int index) const
      {
        if (index <= 0)
          return name;
        return str(boost::format(name + "%02d") % index++);
      }
    };

    /// \brief Returns an identifier that doesn't appear in the term context
    /// \param context A term
    /// \param hint A string
    /// \return An identifier that doesn't appear in the term context
    template <typename Term>
    core::identifier_string fresh_identifier(const Term& context, const std::string& hint)
    {
      return fresh_identifier(context, hint, default_identifier_creator());
    }

    /// \brief Returns a variable that doesn't appear in context
    /// \param context A term
    /// \param s A sort expression
    /// \param hint A string
    /// \return A variable that doesn't appear in context
    template <typename Term>
    variable fresh_variable(Term context, sort_expression s, std::string hint)
    {
      core::identifier_string id = fresh_identifier(context, hint);
      return variable(id, s);
    }

    /// \brief Combines two variables lists
    /// \param v1 a list of variables
    /// \param v2 a list of variables
    /// \return for all x : x in v1 or x in v2  implies x in result
    template < typename Container >
    inline variable_list merge(Container const& v1, Container const& v2) {
      std::set< typename Container::value_type > variables(v1.begin(), v1.end());

      variables.insert(v2.begin(), v2.end());

      return Container(variables.begin(), variables.end());
    }

  } // namespace new_data

} // namespace mcrl2

#endif //MCRL2_NEW_DATA_UTILITY_H

