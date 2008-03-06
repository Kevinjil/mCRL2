
//Aterms
#include <mcrl2/atermpp/algorithm.h>
#include <mcrl2/atermpp/aterm.h>
#include <mcrl2/atermpp/table.h>

//LPS Framework
#include <mcrl2/data/data_operation.h>
#include <mcrl2/lps/linear_process.h>
#include <mcrl2/lps/specification.h>
#include <mcrl2/data/sort_utility.h>
#include "mcrl2/core/messaging.h"
#include "mcrl2/utilities/aterm_ext.h"
#include "mcrl2/data/detail/data_functional.h"

//Enumerator
#include <mcrl2/data/enum/standard.h>
#include <mcrl2/lps/nextstate.h>

#include <mcrl2/lps/decluster.h>

//using namespace std;
// For Aterm library extension functions
#ifdef __cplusplus
using namespace ::mcrl2::utilities;
using namespace mcrl2::core;
#endif
using namespace atermpp;
using namespace mcrl2::data;
using namespace mcrl2::lps;
using namespace mcrl2;

namespace mcrl2 {

namespace lps {

/////////////////////////////////////////////////////////////////
// Helper functions
/////

///\ret variable v occurs in l.
template <typename data_type>
bool occurs_in(data_type l, data_variable v)
{
  return find_if(l, data::detail::compare_data_variable(v)) != aterm_appl();
}


///\ret a list of all data_variables of sort s in vl
data_variable_list get_occurrences(const data_variable_list& vl, const sort_expression& s)
{
  data_variable_list result;
  for (data_variable_list::iterator i = vl.begin(); i != vl.end(); ++i)
  {
    if (i->sort() == s)
    {
      result = push_front(result, *i);
    }
  }
  result = reverse(result);
  return result;
}

///\ret the list of all data_variables in vl, which are unequal to v
data_variable_list filter(const data_variable_list& vl, const data_variable& v)
{
  gsDebugMsg("filter:vl = %s, v = %s\n", vl.to_string().c_str(), v.to_string().c_str());
  data_variable_list result;
  for (data_variable_list::iterator i = vl.begin(); i != vl.end(); ++i)
  {
    if (!(*i == v))
    {
      result = push_front(result, *i);
    }
  }
  gsDebugMsg("filter:result = %s\n", result.to_string().c_str());
  return result;
}

///\ret the list of all date_variables in vl, that are not in rl
data_variable_list filter(const data_variable_list& vl, const data_variable_list& rl)
{
  data_variable_list result;
  for (data_variable_list::iterator i = vl.begin(); i != vl.end(); ++i)
  {
    if (!occurs_in(rl, *i))
    {
      result = push_front(result, *i);
    }
  }

  return result;
}

///\pre fl is a list of constructors
///\ret a list of declusterable sorts in sl
sort_expression_list get_finite_sorts(const data_operation_list& fl, const sort_expression_list& sl)
{
  sort_expression_list result;
  for(sort_expression_list::iterator i = sl.begin(); i != sl.end(); ++i)
  {
    if (is_finite(fl, *i))
    {
      result = push_front(result, *i);
    }
  }
  reverse(result);
  return result;
}

///\ret a list of all variables of a sort that occurs in sl
data_variable_list get_variables(const data_variable_list& vl, const sort_expression_list& sl)
{
  data_variable_list result;
  for (data_variable_list::iterator i = vl.begin(); i != vl.end(); ++i)
  {
    if (occurs_in(sl, i->sort()))
    {
      result = push_front(result, *i);
    }
  }
  result = reverse(result);
  return result;
}


////////////////////////////////////////////////////////////////
// Declustering
/////

///\pre specification is the specification belonging to summand
///\post the declustered version of summand has been appended to result
///\ret none
void decluster_summand(const lps::specification& specification, const lps::summand& summand_, lps::summand_list& result, EnumeratorStandard& enumerator, bool finite_only)
{
  int nr_summands = 0; // Counter for the nummer of new summands, used for verbose output

  gsVerboseMsg("initialization...");

  data_variable_list variables; // The variables we need to consider in declustering
  if (finite_only)
  {
    // Only consider finite variables
    variables = get_variables(summand_.summation_variables(), get_finite_sorts(specification.data().constructors(), specification.data().sorts()));
  }
  else
  {
    variables = summand_.summation_variables();
  }

  gsVerboseMsg("variables: %s\n", variables.to_string().c_str());

  if (aterm_get_length(variables) == 0)
  {
    // Nothing to be done, return original summand
    gsVerboseMsg("No summation variables in this summand\n");
    result = push_front(result, summand_);
  }
  else
  {
    // List of variables with the declustered variables removed (can be done upfront, which is more efficient,
    // because we only need to calculate it once.
    data_variable_list new_vars = filter(summand_.summation_variables(), variables);

    ATermList vars = ATermList(variables);

    ATerm expr = enumerator.getRewriter()->toRewriteFormat(aterm_appl(summand_.condition()));

    // Solutions
    EnumeratorSolutions* sols = enumerator.findSolutions(vars, expr, false);

    gsVerboseMsg("processing...");
    // sol is a solution in internal rewriter format
    ATermList sol;
    bool error = false; // Flag enumerator error to break loop.
    while (sols->next(&sol) && !error)
    {
      if (sols->errorOccurred())
      {
        // If an error occurs in enumerating, remove all summands that
        // have been added to result thus far, and re-add the original.
        // This prevents problems e.g. in case of a sort without constructors.
        gsDebugMsg("An error occurred in enumeration, removing already added summands\n");
        error = true;

        for (int i = 0; i < nr_summands; ++i);
        {
          result = pop_front(result);
        }
        nr_summands = 0;
      }
      else
      {
        data_assignment_list substitutions; 
        // Convenience cast, so that the iterator, and the modifications from the atermpp library can be used
        aterm_list solution = aterm_list(sol);

        // Translate internal rewriter solution to lps data_assignment_list
        for (aterm_list::iterator i = solution.begin(); i != solution.end(); ++i)
        {
          // lefthandside of substitution
          data_variable var = data_variable(ATgetArgument(ATerm(*i), 0));

          // righthandside of substitution in internal rewriter format
          ATerm arg = ATgetArgument(ATerm(*i),1);

          // righthandside of substitution in lps format
          data_expression res = data_expression(aterm_appl(enumerator.getRewriter()->fromRewriteFormat(arg)));

          // Substitution to be performed
          data_assignment substitution = data_assignment(var, res);
          substitutions = push_front(substitutions, substitution);
        }
        gsDebugMsg("substitutions: %s\n", substitutions.to_string().c_str());

        summand s = summand(new_vars,
                                    summand_.condition().substitute(assignment_list_substitution(substitutions)),
                                    summand_.is_delta(),
                                    summand_.actions().substitute(assignment_list_substitution(substitutions)),
                                    summand_.time().substitute(assignment_list_substitution(substitutions)),
                                    summand_.assignments().substitute(assignment_list_substitution(substitutions))
                                    );
        
        result = push_front(result, s);
        ++nr_summands;
      }
    }

    gsVerboseMsg("done...\n");
    if (nr_summands == 0 && sols->errorOccurred())
    {
      gsVerboseMsg("Cannot expand this summand, keeping the original\n");
      result = push_front(result, summand_);
    }
    else if (nr_summands == 0)
    {
      gsVerboseMsg("All valuations for the variables in the condition of this summand reduce to false; removing this summand\n");
    }
    else
    {
      gsVerboseMsg("Replaced with %d summands\n", nr_summands);
    }
  }
}

///Takes the summand list sl, declusters it,
///and returns the declustered summand list
lps::summand_list decluster_summands(const lps::specification& specification,
                                     const lps::summand_list& sl,
                                     EnumeratorStandard& enumerator, 
                                     bool finite_only)
{
  lps::summand_list result;

  // decluster_summand(..) is called only in this function, therefore, it is safe to count the summands here for verbose output.
  lps::summand_list summands = reverse(sl); // This is not absolutely necessary, but it helps in comparing input and output of the decluster algorithm (that is, the relative order is preserved (because decluster_summand plainly appends to result)
  int j = 1;
  for (summand_list::iterator i = summands.begin(); i != summands.end(); ++i, ++j)
  {
    gsVerboseMsg("Summand %d\n", j);
    lps::summand s = *i;
    decluster_summand(specification, s, result, enumerator, finite_only);
  }

  return result;
}

///Takes the specification in specification, declusters it,
///and returns the declustered specification.
lps::specification decluster(const lps::specification& specification, Rewriter& r, bool finite_only)
{
  gsVerboseMsg("Declustering...\n");
  lps::linear_process lps = specification.process();

  gsVerboseMsg("Input: %d summands.\n", lps.summands().size());

  // Some use of internal format because we need it for the rewriter
  EnumeratorStandard enumerator = EnumeratorStandard(specification.data(), &r);

  lps::summand_list sl = decluster_summands(specification, lps.summands(), enumerator, finite_only);
  lps = set_summands(lps, sl);

  gsVerboseMsg("Output: %d summands.\n", lps.summands().size());

  return set_lps(specification, lps);
}

} // namespace lps

} // namespace mcrl2

