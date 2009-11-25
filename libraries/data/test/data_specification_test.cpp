// Author(s): Jeroen Keiren, Wieger Wesselink
// Copyright: see the accompanying file COPYING or copy at
// https://svn.win.tue.nl/trac/MCRL2/browser/trunk/COPYING
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)
//
/// \file data_specification_test.cpp
/// \brief Basic regression test for data specifications.

#include <iostream>
#include <boost/range/iterator_range.hpp>
#include <boost/test/minimal.hpp>

#include "mcrl2/data/data_specification.h"
#include "mcrl2/data/basic_sort.h"
#include "mcrl2/data/find.h"
#include "mcrl2/data/data_expression.h"
#include "mcrl2/data/sort_expression.h"
#include "mcrl2/data/set.h"
#include "mcrl2/data/bag.h"
#include "mcrl2/data/list.h"
#include "mcrl2/data/structured_sort.h"
#include "mcrl2/data/utility.h"
#include "mcrl2/data/parser.h"
#include "mcrl2/core/garbage_collection.h"
#include "mcrl2/atermpp/aterm_init.h"

using namespace mcrl2;
using namespace mcrl2::data;

bool compare_for_equality(data_specification const& left, data_specification const& right)
{ 
  if (!(left == right)) 
  { BOOST_CHECK(left == right);

    std::clog << "+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++" << std::endl
              << "Specification detailed comparison:" << std::endl;

    if (left.sorts() != right.sorts()) {
      std::clog << "Sorts (left)  " << pp(left.sorts()) << std::endl;
      std::clog << "Sorts (right) " << pp(right.sorts()) << std::endl;
    }
    if (left.constructors() != right.constructors()) {
      std::clog << "Constructors (left)  " << pp(left.constructors()) << std::endl;
      std::clog << "Constructors (right) " << pp(right.constructors()) << std::endl;
    }
    if (left.mappings() != right.mappings()) 
    { std::clog << "Mappings (left)  " << pp(left.mappings()) << std::endl;
      std::clog << "Mappings (right) " << pp(right.mappings()) << std::endl;
    }
    if (left.equations() != right.equations()) {
      std::clog << "Equations (left)  " << pp(left.equations()) << std::endl;
      std::clog << "Equations (right) " << pp(right.equations()) << std::endl;
    }

    std::clog << "+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++" << std::endl;

    return false;
  }

  return true;
}

void test_sorts()
{
  std::clog << "test_sorts" << std::endl;

  basic_sort s("S");
  basic_sort s0("S0");
  alias s1(basic_sort("S1"), s);

  atermpp::set< sort_expression > sl;
  sl.insert(s);
  sl.insert(s0);

  data_specification spec;
  spec.add_sort(s);
  spec.add_sort(s0);
  spec.add_alias(s1);
  data_specification spec1;
  spec1.add_alias(s1);
  spec1.add_sort(s0);
  spec1.add_sort(s);

  BOOST_CHECK(std::equal(sl.begin(), sl.end(), spec.sorts().begin()));
  BOOST_CHECK(std::equal(sl.begin(), sl.end(), spec1.sorts().begin()));
  BOOST_CHECK(compare_for_equality(spec, spec1));

  basic_sort s2("S2");
  sort_expression_vector s2l(make_vector(reinterpret_cast<sort_expression&>(s2)));
  boost::iterator_range<sort_expression_vector::const_iterator> s2l_range(s2l);
  spec.make_complete(s2);
  spec1.make_complete(s2l_range);
  BOOST_CHECK(compare_for_equality(spec, spec1));

  spec.remove_sorts(s2l_range);
  spec1.remove_sort(s2);
  compare_for_equality(spec, spec1);
}

void test_aliases()
{
  std::clog << "test_aliases" << std::endl;

  basic_sort s("S");
  basic_sort t("T");
  alias      s1(basic_sort("S1"), s);
  alias      s2(basic_sort("S2"), s);

  data_specification spec;

  // BOOST_CHECK(boost::distance(spec.aliases()) == 0);

  atermpp::set< sort_expression > sorts;
  sorts.insert(s);
  sorts.insert(t);
  spec.add_sorts(boost::make_iterator_range(sorts));

  /* atermpp::set< sort_expression > aliases;
  aliases.insert(s1);
  aliases.insert(s2);
  spec.add_aliases(boost::make_iterator_range(aliases));

  BOOST_CHECK(boost::distance(spec.aliases(s)) == 2);
  BOOST_CHECK(boost::distance(spec.aliases(t)) == 0);
  BOOST_CHECK(spec.aliases(s) == boost::make_iterator_range(aliases)); */
}

void test_constructors()
{
  std::clog << "test_constructors" << std::endl;

  basic_sort s("S");
  basic_sort s0("S0");
  function_sort s0s(make_vector(sort_expression(s0)),s);
  function_symbol f("f", s);
  function_symbol g("g", s0s);
  function_symbol h("h", s0);
  function_symbol_vector fgl(make_vector(f,g));
  function_symbol_vector hl(make_vector(h));
  function_symbol_vector fghl(make_vector(f,g,h));
  boost::iterator_range<function_symbol_vector::const_iterator> fgl_range(boost::make_iterator_range(fgl));
  boost::iterator_range<function_symbol_vector::const_iterator> hl_range(boost::make_iterator_range(hl));
  boost::iterator_range<function_symbol_vector::const_iterator> fghl_range(boost::make_iterator_range(fghl));

  data_specification spec;
  spec.add_sort(s);
  spec.add_sort(s0);

  spec.add_constructor(f);
  spec.add_constructor(g);
  spec.add_constructor(h);

  data_specification spec1(spec);
  spec1.add_constructors(fghl_range);

  function_symbol_vector constructors(boost::copy_range< function_symbol_vector >(spec.constructors()));
  BOOST_CHECK(spec.constructors(s) == fgl_range);
  std::cerr << "AAA1 " << constructors.size() << "\n";
  std::cerr << "AAA1 " << pp(constructors) << "\n";
  BOOST_CHECK(constructors.size() == 5); // f,g,h, true, false.
  BOOST_CHECK(spec.search_constructor(f));
  BOOST_CHECK(spec.search_constructor(g));
  BOOST_CHECK(spec.search_constructor(h));

  BOOST_CHECK(compare_for_equality(spec, spec1));
  BOOST_CHECK(spec.constructors() == spec1.constructors());
  BOOST_CHECK(spec.constructors(s) == fgl_range);
  BOOST_CHECK(spec.constructors(s0) == hl_range);
  BOOST_CHECK(spec1.constructors(s) == fgl_range);
  BOOST_CHECK(spec1.constructors(s0) == hl_range);
  spec.add_constructor(function_symbol("i", s0));
  function_symbol i("i", s0);
  spec.remove_constructor(i);
  BOOST_CHECK(compare_for_equality(spec, spec1));

  spec.add_constructor(i);
  function_symbol_vector il(make_vector(i));
  boost::iterator_range<function_symbol_vector::const_iterator> il_range(il);
  spec1.add_constructors(il_range);
  BOOST_CHECK(compare_for_equality(spec, spec1));
  /* BOOST_CHECK(spec.is_system_defined(i));
  BOOST_CHECK(!spec.is_system_defined(f));
  BOOST_CHECK(!spec.is_system_defined(g));
  BOOST_CHECK(!spec.is_system_defined(h));
  BOOST_CHECK(spec1.is_system_defined(i));
  BOOST_CHECK(!spec1.is_system_defined(f));
  BOOST_CHECK(!spec1.is_system_defined(g));
  BOOST_CHECK(!spec1.is_system_defined(h)); */

  spec.remove_constructor(i);
  spec1.remove_constructors(il_range);
  BOOST_CHECK(compare_for_equality(spec, spec1));
}

void test_functions()
{
  std::clog << "test_functions" << std::endl;

  basic_sort s("S");
  basic_sort s0("S0");
  function_sort s0s(make_vector(sort_expression(s0)), s);
  function_symbol f("f", s);
  function_symbol g("g", s0s);
  function_symbol h("h", s0);

  function_symbol_vector fgl(make_vector(f,g));
  function_symbol_vector hl(make_vector(h));
  function_symbol_vector fghl(make_vector(f,g,h));
  boost::iterator_range<function_symbol_vector::const_iterator> fgl_range(boost::make_iterator_range(fgl));
  boost::iterator_range<function_symbol_vector::const_iterator> hl_range(boost::make_iterator_range(hl));
  boost::iterator_range<function_symbol_vector::const_iterator> fghl_range(boost::make_iterator_range(fghl));

  data_specification spec;
  spec.add_sort(s);
  spec.add_sort(s0);
  spec.add_mapping(f);
  spec.add_mapping(g);
  spec.add_mapping(h);

  data_specification spec1(spec);
  spec1.add_mappings(fghl_range);

  std::cerr << "BBB " << boost::distance(spec.mappings()) << "\n";
  BOOST_CHECK(boost::distance(spec.mappings()) == 35);
  BOOST_CHECK(spec.search_mapping(f));
  BOOST_CHECK(spec.search_mapping(g));
  BOOST_CHECK(spec.search_mapping(h));

  BOOST_CHECK(compare_for_equality(spec, spec1));
  BOOST_CHECK(boost::distance(spec.mappings(s)) == 3);
  BOOST_CHECK(std::find(spec.mappings(s).begin(), spec.mappings(s).end(), f) != spec.mappings(s).end());
  BOOST_CHECK(std::find(spec.mappings(s).begin(), spec.mappings(s).end(), g) != spec.mappings(s).end());
  BOOST_CHECK(std::find(spec.mappings(s0).begin(), spec.mappings(s0).end(), h) != spec.mappings(s0).end());
  BOOST_CHECK(boost::distance(spec1.mappings(s)) == 3);
  BOOST_CHECK(std::find(spec1.mappings(s).begin(), spec1.mappings(s).end(), f) != spec1.mappings(s).end());
  BOOST_CHECK(std::find(spec1.mappings(s).begin(), spec1.mappings(s).end(), g) != spec1.mappings(s).end());
  BOOST_CHECK(std::find(spec1.mappings(s0).begin(), spec1.mappings(s0).end(), h) != spec1.mappings(s0).end());

  function_symbol i("i", s0);
  spec.add_mapping(i);
  function_symbol_vector il(make_vector(i));
  boost::iterator_range<function_symbol_vector::const_iterator> il_range(il);
  spec1.add_mappings(il_range);
  compare_for_equality(spec, spec1);
  /* BOOST_CHECK(spec.is_system_defined(i));
  BOOST_CHECK(!spec.is_system_defined(f));
  BOOST_CHECK(!spec.is_system_defined(g));
  BOOST_CHECK(!spec.is_system_defined(h));
  BOOST_CHECK(spec1.is_system_defined(i));
  BOOST_CHECK(!spec1.is_system_defined(f));
  BOOST_CHECK(!spec1.is_system_defined(g));
  BOOST_CHECK(!spec1.is_system_defined(h)); */

  spec.remove_mappings(il_range);
  spec1.remove_mapping(i);
  compare_for_equality(spec, spec1);
}

void test_equations()
{
  std::clog << "test_equations" << std::endl;
  basic_sort s("S");
  basic_sort s0("S0");
  function_sort s0s(make_vector(reinterpret_cast<sort_expression&>(s0)), s);
  function_symbol f("f", s0s);
  variable x("x", s0);
  data_expression_vector xel(make_vector(reinterpret_cast<data_expression&>(x)));
  application fx(f, boost::make_iterator_range(xel));
  variable_vector xl(make_vector(x));
  boost::iterator_range<variable_vector::const_iterator> x_range(xl);
  data_equation fxx(x_range, x, fx, x);

  data_specification spec;
  data_specification spec1;
  spec.add_sort(s);
  spec.add_sort(s0);

  spec1 = spec;
  BOOST_CHECK(compare_for_equality(spec, spec1));
  spec.add_equation(fxx);
  data_equation_vector fxxl(make_vector(fxx));
  boost::iterator_range<data_equation_vector::const_iterator> fxxl_range(fxxl);
  spec1.add_equations(fxxl_range);

  BOOST_CHECK(compare_for_equality(spec, spec1));

  data_equation fxf(x_range, x, fx, f);
  data_equation_vector fxfl(make_vector(fxf));
  boost::iterator_range<data_equation_vector::const_iterator> fxfl_range(fxfl);
  spec.add_equation(fxf);
  spec1.add_equations(fxfl_range);

  BOOST_CHECK(compare_for_equality(spec, spec1));
  /* BOOST_CHECK(spec.is_system_defined(fxf));
  BOOST_CHECK(!spec.is_system_defined(fxx));
  BOOST_CHECK(spec1.is_system_defined(fxf));
  BOOST_CHECK(!spec1.is_system_defined(fxx)); */

  data_equation_vector result = find_equations(spec, f);
  BOOST_CHECK(result.size() == 2);
  BOOST_CHECK(std::find(result.begin(), result.end(), fxf) != result.end());
  BOOST_CHECK(std::find(result.begin(), result.end(), fxx) != result.end());
  spec.remove_equations(fxfl_range);
  spec1.remove_equation(fxf);
  BOOST_CHECK(compare_for_equality(spec, spec1));
}

void test_is_certainly_finite()
{
  std::clog << "test_is_certainly_finite" << std::endl;
  basic_sort s("S");
  basic_sort s0("S0");
  function_sort s0s0(make_vector(static_cast<sort_expression&>(s0)), s0);
  function_symbol f("f", s);
  function_symbol g("g", s0s0);
  variable x("x", s0);
  application gx(g, boost::make_iterator_range(make_vector(static_cast<data_expression&>(x))));
  data_specification spec;
  spec.add_sort(s);
  spec.add_sort(s0);
  spec.add_constructor(f);
  spec.add_constructor(g);

  BOOST_CHECK(spec.is_certainly_finite(s));
  BOOST_CHECK(!spec.is_certainly_finite(s0));

  spec.make_complete(sort_real::real_());
  BOOST_CHECK(spec.is_certainly_finite(sort_bool::bool_()));
  BOOST_CHECK(!spec.is_certainly_finite(sort_pos::pos()));
  BOOST_CHECK(!spec.is_certainly_finite(sort_nat::nat()));
  BOOST_CHECK(!spec.is_certainly_finite(sort_int::int_()));
  BOOST_CHECK(!spec.is_certainly_finite(sort_real::real_()));

  basic_sort s1("S1");
  basic_sort s2("S2");
  spec.add_constructor(function_symbol("h", function_sort(s1, s2)));
  spec.add_constructor(function_symbol("i", function_sort(s2, s1)));

  spec.add_alias(alias(basic_sort("a"), s));
  spec.add_alias(alias(basic_sort("a0"), s0));
  spec.add_alias(alias(basic_sort("a1"), s1));

  BOOST_CHECK(spec.is_certainly_finite(spec.normalise_sorts(basic_sort("a"))));
  BOOST_CHECK(!spec.is_certainly_finite(spec.normalise_sorts(basic_sort("a0"))));
  BOOST_CHECK(!spec.is_certainly_finite(spec.normalise_sorts(basic_sort("a1"))));

  using namespace sort_list;

  BOOST_CHECK(!spec.is_certainly_finite(list(s)));
  BOOST_CHECK(!spec.is_certainly_finite(list(s0)));

  using namespace sort_set;

  BOOST_CHECK(spec.is_certainly_finite(set_(s)));
  BOOST_CHECK(!spec.is_certainly_finite(set_(s0)));

  using namespace sort_bag;

  BOOST_CHECK(!spec.is_certainly_finite(bag(s)));
  BOOST_CHECK(!spec.is_certainly_finite(bag(s0)));
  BOOST_CHECK(spec.is_certainly_finite(function_sort(s,s)));
  BOOST_CHECK(!spec.is_certainly_finite(function_sort(s,s0)));
  BOOST_CHECK(!spec.is_certainly_finite(function_sort(s0,s)));

  // structured sort
  atermpp::vector< data::structured_sort_constructor_argument > arguments;

  arguments.push_back(data::structured_sort_constructor_argument(s));
  arguments.push_back(data::structured_sort_constructor_argument(s0));
  arguments.push_back(data::structured_sort_constructor_argument(s1));

  atermpp::vector< data::structured_sort_constructor > constructors;
  constructors.push_back(data::structured_sort_constructor("a",
     boost::make_iterator_range(arguments.begin(), arguments.begin() + 1)));
  constructors.push_back(data::structured_sort_constructor("b",
     boost::make_iterator_range(arguments.begin() + 1, arguments.begin() + 2)));
  constructors.push_back(data::structured_sort_constructor("b",
     boost::make_iterator_range(arguments.begin() + 2, arguments.begin() + 3)));

  BOOST_CHECK(spec.is_certainly_finite(data::structured_sort(boost::make_iterator_range(constructors.begin(), constructors.begin() + 1))));
  BOOST_CHECK(!spec.is_certainly_finite(data::structured_sort(boost::make_iterator_range(constructors.begin() + 1, constructors.begin() + 2))));
  BOOST_CHECK(!spec.is_certainly_finite(data::structured_sort(boost::make_iterator_range(constructors.begin() + 2, constructors.begin() + 3))));
  BOOST_CHECK(!spec.is_certainly_finite(data::structured_sort(boost::make_iterator_range(constructors.begin() + 0, constructors.begin() + 3))));
}

void test_constructor()
{
  std::clog << "test_constructor" << std::endl;
  std::string SPEC =
    "sort                      \n"
    "  D     = struct d1 | d2; \n"
    "  Error = struct e;       \n"
    "                          \n"
    ;
  data_specification data = parse_data_specification(SPEC);
  ATermAppl a = data::detail::data_specification_to_aterm_data_spec(data);
  data_specification spec1(a);
}

template < typename ForwardTraversalIterator, typename Expression >
bool search(boost::iterator_range< ForwardTraversalIterator > const& range, Expression const& expression)
{
  return std::find(range.begin(), range.end(), expression) != range.end();
}

void test_system_defined()
{
  std::clog << "test_system_defined" << std::endl;

  data_specification specification;

  BOOST_CHECK(!specification.constructors(sort_bool::bool_()).empty());

  specification = parse_data_specification(
    "sort S;"
    "map f: Set(S);");

  std::cerr << "SET " << specification.sorts() << "\n";
  BOOST_CHECK(search(specification.sorts(), sort_set::set_(basic_sort("S"))));
  // BOOST_CHECK(search(specification.sorts(), sort_fset::fset(basic_sort("S")))); MUST BE CHECKED ALSO?

  specification = parse_data_specification(
    "sort D = Set(Nat);"
    "sort E = D;"
    "sort F = E;");

  BOOST_CHECK(sort_set::set_generate_constructors_code(sort_nat::nat()) == specification.constructors(basic_sort("D")));
  BOOST_CHECK(specification.constructors(specification.normalise_sorts(basic_sort("D"))) == 
                     specification.constructors(specification.normalise_sorts(basic_sort("E"))));
  BOOST_CHECK(specification.mappings(specification.normalise_sorts(basic_sort("D"))) == 
              specification.mappings(specification.normalise_sorts(basic_sort("E"))));
  BOOST_CHECK(specification.constructors(specification.normalise_sorts(basic_sort("D"))) == 
                     specification.constructors(specification.normalise_sorts(basic_sort("F"))));

  data_specification copy = specification;

  BOOST_CHECK(compare_for_equality(data_specification(detail::data_specification_to_aterm_data_spec(copy)), specification));

  specification = parse_data_specification(
    "sort D = struct d(getBool : Bool)?is_d;"
    "sort E = D;"
    "sort F = E;");

  BOOST_CHECK(specification.is_alias(basic_sort("D")));
  BOOST_CHECK(specification.is_alias(basic_sort("F")));
  std::cerr << "CONSTRUCTORS " << specification.constructors(basic_sort("D")) << "\n";
  BOOST_CHECK(boost::distance(specification.constructors(basic_sort("D"))) == 1);

  BOOST_CHECK(specification.constructors(basic_sort("D")) == specification.constructors(basic_sort("E")));
  BOOST_CHECK(specification.mappings(basic_sort("D")) == specification.mappings(basic_sort("E")));
  BOOST_CHECK(specification.constructors(basic_sort("D")) == specification.constructors(basic_sort("F")));

  copy = specification;

  BOOST_CHECK(compare_for_equality(data_specification(detail::data_specification_to_aterm_data_spec(copy)), specification));

  // Check for the non presence of function sort
  BOOST_CHECK(specification.mappings(function_sort(basic_sort("D"), sort_bool::bool_())).empty());

  specification.add_mapping(function_symbol("f", function_sort(sort_bool::bool_(), sort_bool::bool_(), sort_nat::nat())));

  BOOST_CHECK(!specification.mappings(function_sort(sort_bool::bool_(), sort_bool::bool_(), sort_nat::nat())).empty());

  // Manually structured sort
  atermpp::vector< data::structured_sort_constructor_argument > arguments;

  // sort that references itself by a name
  arguments.push_back(data::structured_sort_constructor_argument(basic_sort("Q")));

  atermpp::vector< data::structured_sort_constructor > constructors;
  constructors.push_back(data::structured_sort_constructor("q",
     boost::make_iterator_range(arguments.begin(), arguments.begin() + 1)));

  specification.add_alias(alias(basic_sort("Q"), data::structured_sort(constructors)));
}

void test_utility_functionality()
{
  data_specification spec;

  basic_sort s("S");
  basic_sort s0("S0");
  basic_sort a("a");
  function_sort s0s(make_vector(sort_expression(s0)), s);
  function_symbol f("f", s);
  BOOST_CHECK(!spec.search_mapping(f));
  function_symbol g("g", s0s);
  BOOST_CHECK(!spec.search_mapping(g));
  function_symbol h("h", s0);
  BOOST_CHECK(!spec.search_sort(s0));
  spec.add_sort(s0);
  BOOST_CHECK(!spec.search_constructor(f));
  BOOST_CHECK(!spec.search_sort(s));
  spec.add_constructor(f);
  spec.add_mapping(g);
  BOOST_CHECK(!spec.search_mapping(h));
  spec.add_mapping(h);

  spec.add_sort(s);
  spec.add_alias(alias(basic_sort("a"), s));
  BOOST_CHECK(spec.search_sort(s));

  BOOST_CHECK(spec.search_sort(a));

  BOOST_CHECK(spec.search_sort(s));
  BOOST_CHECK(spec.search_sort(s));

  BOOST_CHECK(!spec.search_mapping(f));
  BOOST_CHECK(spec.search_constructor(f));

  BOOST_CHECK(!spec.search_constructor(g));
  BOOST_CHECK(spec.search_mapping(g));
  BOOST_CHECK(!spec.search_constructor(g));
  BOOST_CHECK(!spec.search_constructor(h));
  BOOST_CHECK(spec.search_mapping(h));

  BOOST_CHECK(spec.constructors(a) == spec.constructors(s));
  BOOST_CHECK(spec.mappings(a) == spec.mappings(s));
}

void test_normalisation()
{
  using namespace mcrl2::data;
  using namespace mcrl2::data::sort_list;
  using namespace mcrl2::data::sort_set;
  using namespace mcrl2::data::sort_bag;

  data_specification specification;

  basic_sort A("A");

  specification.add_sort(A);

  basic_sort L("L");
  basic_sort S("S");
  basic_sort B("B");

  specification.add_alias(alias(L, list(A)));
  specification.add_alias(alias(S, set_(A)));
  specification.add_alias(alias(B, bag(A)));

  BOOST_CHECK(specification.normalise_sorts(L) == specification.normalise_sorts(list(A)));
  BOOST_CHECK(specification.normalise_sorts(list(L)) == specification.normalise_sorts(list(list(A))));
  BOOST_CHECK(specification.normalise_sorts(S) == specification.normalise_sorts(set_(A)));
  BOOST_CHECK(specification.normalise_sorts(list(S)) == specification.normalise_sorts(list(set_(A))));
  BOOST_CHECK(specification.normalise_sorts(B) == specification.normalise_sorts(bag(A)));
  BOOST_CHECK(specification.normalise_sorts(list(B)) == specification.normalise_sorts(list(bag(A))));

  specification = parse_data_specification(
    "sort A = struct a(B);"
    "sort B = struct b(A);");

  atermpp::vector< structured_sort_constructor_argument > arguments;

  arguments.push_back(structured_sort_constructor_argument(basic_sort("B")));
  arguments.push_back(structured_sort_constructor_argument(basic_sort("A")));

  atermpp::vector< structured_sort_constructor > constructors;

  constructors.push_back(structured_sort_constructor("a", boost::make_iterator_range(arguments.begin(), arguments.begin() + 1)));
  constructors.push_back(structured_sort_constructor("b", boost::make_iterator_range(arguments.begin() + 1, arguments.end())));

  structured_sort sA(data::structured_sort(boost::make_iterator_range(constructors.begin(), constructors.begin() + 1)));
  structured_sort sB(data::structured_sort(boost::make_iterator_range(constructors.begin() + 1, constructors.end())));

  BOOST_CHECK(specification.search_sort(specification.normalise_sorts(sA)));
  BOOST_CHECK(specification.search_sort(specification.normalise_sorts(sB)));

  BOOST_CHECK(specification.normalise_sorts(sA) == specification.normalise_sorts(specification.normalise_sorts(sA)));
  BOOST_CHECK(specification.normalise_sorts(sB) == specification.normalise_sorts(specification.normalise_sorts(sB)));
}

void test_copy()
{
  std::clog << "test_copy" << std::endl;

  data_specification specification = parse_data_specification(
    "sort D = struct d(bla : Bool)?is_d;"
    "sort A = S;"
    "sort S;"
    "map f: Set(S);");

  BOOST_CHECK(specification.search_constructor(sort_bool::true_()));

  data_specification other;
  other = specification;

  BOOST_CHECK(other == specification);

  specification = data_specification();

  core::garbage_collect();

  BOOST_CHECK(other.normalise_sorts(basic_sort("A")) == other.normalise_sorts(basic_sort("S")));
  BOOST_CHECK(!specification.search_sort(basic_sort("A")));
}

int test_main(int argc, char** argv)
{
  MCRL2_ATERMPP_INIT(argc, argv);

  test_sorts();
  core::garbage_collect();

  test_constructors();
  core::garbage_collect();

  test_functions();
  core::garbage_collect();

  test_equations();
  core::garbage_collect();

  test_is_certainly_finite();
  core::garbage_collect();

  test_constructor();
  core::garbage_collect();

  test_system_defined();
  core::garbage_collect();

  test_utility_functionality();
  core::garbage_collect();

  test_normalisation();
  core::garbage_collect();

  test_copy();
  core::garbage_collect();

  return EXIT_SUCCESS;
}


