// Author(s): Wieger Wesselink
// Copyright: see the accompanying file COPYING or copy at
// https://svn.win.tue.nl/trac/MCRL2/browser/trunk/COPYING
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)
//
/// \file mcrl2/pbes/detail/pbes2bes_variable_map_parser.h
/// \brief add your file description here.

#ifndef MCRL2_PBES_DETAIL_PBES2BES_VARIABLE_MAP_PARSER_H
#define MCRL2_PBES_DETAIL_PBES2BES_VARIABLE_MAP_PARSER_H

#include <iostream>
#include <string>

#include <boost/algorithm/string.hpp>
#include <boost/xpressive/xpressive.hpp>

#include "mcrl2/exception.h"
#include "mcrl2/core/text_utility.h"
#include "mcrl2/core/detail/print_utility.h"
#include "mcrl2/pbes/pbes2bes_finite_algorithm.h"

namespace mcrl2 {

namespace pbes_system {

namespace detail {

/*
    /// \brief Returns true if the declaration text matches with the variable d.
    inline
    bool match_type(const std::string& text, const data::variable& d, const data::data_specification& data_spec)
    {
      
    }

    /// \brief Find parameter declarations that match a given string.
    /// This string can for example be 'a' (match the name 'a'), 'b:Bool' (match the name and the given type),
    /// '*' (match any name) and '*:Bool' (match for any name and the given type)
    inline
    std::set<data::variable> find_matching_parameters(const pbes<>& p, const std::string& name, const std::string& text)
    {
      std::vector<std::string> words = core::split(text, ":");
      if (words.size() > 2)
      {
        throw mcrl2::runtime_error("too many colons in parameter declaration: '" + text + "'");
      }
      std::string left = words[0];
      boost::trim(left);
      std::string right;
      if (words.size() == 2)
      {
        right = words[1];
        boost::trim(right);
      }

      std::set<data::variable> result;
      
      for (atermpp::vector<pbes_equation>::const_iterator i = p.equations().begin(); i != p.equations().end(); ++i)
      {
        propositional_variable X = i->variable();       
        if (name == "*" || (std::string(X.name()) == name))
        {
          data::variable_list v = X.parameters();
          for (data::variable_list::cont_iterator j = v.begin(); j != v.end(); ++j)
          {
          }
        }
      }
      throw mcrl2::runtime_error("could not find parameter matching the declaration '" + name + "(" + parameter + ")'");
      return result;
    }
*/

    /// \brief Parses parameter selection for finite pbes2bes algorithm
    inline
    pbes2bes_variable_map parse_variable_map(const pbes<>& p, const std::string& text)
    {
      using namespace boost::xpressive;
      pbes2bes_variable_map result;

      // maps propositional variable name to the corresponding variable declarations, for example:
      // X(b:Bool,c:C) X(d:*) Y(*:Bool) results in the mapping
      //
      // X -> { "b:Bool", "c:C", "d:*" }
      // Y -> { "*:Bool" }
      typedef std::map<std::string, std::set<std::string> > name_map;
      name_map parameter_declarations;

      std::vector<std::string> lines = core::split(text, ";");
      for (std::vector<std::string>::iterator i = lines.begin(); i != lines.end(); ++i)
      {
        std::string line = boost::trim_copy(*i);
        if (line.empty())
        {
          continue;
        }
        sregex sre = sregex::compile("(\\w*)\\(([:,#\\s\\w]*)\\)\\s*", regex_constants::icase);
        match_results<std::string::const_iterator> what;
        if (!regex_match(line, what, sre))
        {
          std::cerr << "warning: ignoring selection '" << line << "'" << std::endl;
          continue;
        }
        std::string X = what[1];
        boost::trim(X);
        std::string word = what[2];
        boost::trim(word);
        std::vector<std::string> parameters = core::regex_split(word, "\\s*,\\s*");
        for (std::vector<std::string>::iterator j = parameters.begin(); j != parameters.end(); ++j)
        {
          parameter_declarations[X].insert(*j);
        }
      }
      for (name_map::const_iterator k = parameter_declarations.begin(); k != parameter_declarations.end(); ++k)
      {
        std::cout << k->first << " -> " << core::detail::print_set(k->second) << std::endl;
      }
      return result;
    }

} // namespace detail

} // namespace pbes_system

} // namespace mcrl2

#endif // MCRL2_PBES_DETAIL_PBES2BES_VARIABLE_MAP_PARSER_H
