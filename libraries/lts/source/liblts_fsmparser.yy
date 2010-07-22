// Author(s): Muck van Weerdenburg
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)
//
/// \file fsmparser.yy

%{
#include <vector>
#include <sstream>
#include <cstring>
#include "mcrl2/lts/lts.h"
#include "liblts_fsmparser.h"
#include "liblts_fsmlexer.h"

// Local variables
std::vector<bool> ignore_par; /* Records which parameters will be ignored */
unsigned int num_pars;        /* Number of parameters */
unsigned int par_index;       /* Index of current parameter */

// Function declarations

//external declarations from fsmlexer.ll
void fsmyyerror(const char *s);
int fsmyylex(void);

char* intToCString(int i);

#define safe_assign(lhs, rhs) { ATbool b; ATindexedSetPut(fsm_lexer_obj->protect_table, (ATerm) rhs, &b); lhs = rhs; }
%}

%union {
  ATermAppl aterm;
  int number;
}

//more verbose and specific error messages
%error-verbose

//set name prefix
%name-prefix="fsmyy"

%start fsm_file

%token EOLN SECSEP LPAR RPAR ARROW HASH QMARK COLON COMMA BAG BAR KWSTRUCT SET LIST
%token <number> NUMBER
%token <aterm> ID QUOTED BOOL POS NAT INT REAL
%type  <aterm> sort_expr sort_expr_arrow domain_no_arrow sort_expr_struct domain_no_arrow_elts_hs struct_constructors_bs struct_constructor recogniser struct_projections_cs struct_projection sort_expr_primary sort_constant sort_constructor domain_no_arrow_elt action

%%

fsm_file :
    {
      num_pars = 0;
      ignore_par.clear();
    }
  params
    {
      fsm_lexer_obj->valueTable = ATreverse( fsm_lexer_obj->valueTable );
    }
  SECSEP EOLN
  states
  SECSEP EOLN transitions
  ;

// --------- Section containing the state vector ----------

params :
  /* empty */
  |
  params param
    {
      ++num_pars;
    }
  EOLN
  ;

param :
  ID
    {
      fsm_lexer_obj->typeId = $1;
    }
  cardinality type_def
  ;

cardinality :
  LPAR NUMBER RPAR
    {
      ignore_par.push_back($2 == 0);
    }
  ;

type_def :
  sort_expr
    {
      if (!ignore_par[num_pars])
      {
        fsm_lexer_obj->typeValues = ATempty;
        fsm_lexer_obj->typeId = ATmakeAppl2(fsm_lexer_obj->const_ATtype,(ATerm) fsm_lexer_obj->typeId,(ATerm) $1);
      }
    }
  type_values
    {
      if (!ignore_par[num_pars])
      {
        fsm_lexer_obj->typeValues = ATreverse( fsm_lexer_obj->typeValues );
        fsm_lexer_obj->valueTable = ATinsert( fsm_lexer_obj->valueTable,
            (ATerm)fsm_lexer_obj->typeValues );
      }
    }
  ;

//Sort expressions
//----------------

//sort expression
sort_expr:
  sort_expr_arrow
    {
      safe_assign($$, $1);
    }
  ;

//arrow sort expression
sort_expr_arrow:
  sort_expr_struct
    {
      safe_assign($$, $1);
    }
  | domain_no_arrow ARROW sort_expr_arrow
    {
      std::string result = static_cast<std::string> ( ATwriteToString( (ATerm)$1 ) )
        + "->" + static_cast<std::string> ( ATwriteToString( (ATerm)$3 ) );
      safe_assign($$, ATmakeAppl0( ATmakeAFun( result.c_str(), 0, ATfalse ) ))
    }
  ;

//domain
domain_no_arrow:
  domain_no_arrow_elts_hs
    {
      safe_assign($$, $1);
    }
  ;

//one or more domain elements, separated by hashes
domain_no_arrow_elts_hs:
  domain_no_arrow_elt
    {
      safe_assign($$, $1);
    }
  | domain_no_arrow_elts_hs HASH domain_no_arrow_elt
    {
      std::string result = static_cast<std::string> ( ATwriteToString( (ATerm)$1 ) )
        + "#" + static_cast<std::string> ( ATwriteToString( (ATerm)$3 ) );
      safe_assign($$, ATmakeAppl0( ATmakeAFun( result.c_str(), 0, ATfalse ) ));
    }
  ;

//domain element
domain_no_arrow_elt:
  sort_expr_struct
    {
      safe_assign($$, $1);
    }
  ;

//structured sort
sort_expr_struct:
  sort_expr_primary
    {
      safe_assign($$, $1);
    }
  | KWSTRUCT struct_constructors_bs
    {
      std::string result = "struct " + static_cast<std::string> ( ATwriteToString( (ATerm)$2 ) );
      safe_assign($$, ATmakeAppl0( ATmakeAFun( result.c_str(), 0, ATfalse ) ));
    }
  ;

//one ore more structured sort constructors, separated by bars
struct_constructors_bs:
  struct_constructor
    {
      safe_assign($$, $1);
    }
  | struct_constructors_bs BAR struct_constructor
    {
      std::string result = static_cast<std::string> ( ATwriteToString( (ATerm)$1 ) )
        + "|" + static_cast<std::string> ( ATwriteToString( (ATerm)$3 ) );
      safe_assign($$, ATmakeAppl0( ATmakeAFun( result.c_str(), 0, ATfalse ) ));
    }
  ;

//structured sort constructor
struct_constructor:
  ID recogniser
    {
      std::string result = static_cast<std::string> ( ATwriteToString( (ATerm)$1 ) )
        + " " + static_cast<std::string> ( ATwriteToString( (ATerm)$2 ) );
      safe_assign($$, ATmakeAppl0( ATmakeAFun( result.c_str(), 0, ATfalse ) ));
    }
  | ID LPAR struct_projections_cs RPAR recogniser
    {
      std::string result = static_cast<std::string> ( ATwriteToString( (ATerm)$1 ) )
        + "(" + static_cast<std::string> ( ATwriteToString( (ATerm)$3 ) ) + ")" +
              static_cast<std::string> ( ATwriteToString( (ATerm)$5 ) );
      safe_assign($$, ATmakeAppl0( ATmakeAFun( result.c_str(), 0, ATfalse ) ));
    }
  ;

//recogniser
recogniser:
  /* empty */
    {
      std::string result = static_cast<std::string> ( "");
      safe_assign($$, ATmakeAppl0( ATmakeAFun( result.c_str(), 0, ATfalse ) ));
    }
  | QMARK ID
    {
      std::string result = "?" + static_cast<std::string> ( ATwriteToString( (ATerm)$2 ) );
      safe_assign($$, ATmakeAppl0( ATmakeAFun( result.c_str(), 0, ATfalse ) ));
    }
  ;

//one or more structured sort projections, separated by comma's
struct_projections_cs:
  struct_projection
    {
      safe_assign($$, $1);
    }
  | struct_projections_cs COMMA struct_projection
    {
      std::string result = static_cast<std::string> ( ATwriteToString( (ATerm)$1 ) )
        + "," + static_cast<std::string> ( ATwriteToString( (ATerm)$3 ) );
      safe_assign($$, ATmakeAppl0( ATmakeAFun( result.c_str(), 0, ATfalse ) ));

    }
  ;

//structured sort projection
struct_projection:
  sort_expr
    {
      safe_assign($$, $1);
    }
  | ID COLON sort_expr
    {
      std::string result = static_cast<std::string> ( ATwriteToString( (ATerm)$1 ) )
        + ":" + static_cast<std::string> ( ATwriteToString( (ATerm)$3 ) );
      safe_assign($$, ATmakeAppl0( ATmakeAFun( result.c_str(), 0, ATfalse ) ));
    }
  ;

//primary sort expression
sort_expr_primary:
  ID
    {
      safe_assign($$, $1);
    }
  | sort_constant
    {
      safe_assign($$, $1);
    }
  | sort_constructor
    {
      safe_assign($$, $1);
    }
  | LPAR sort_expr RPAR
    { 
      std::string result = "(" + static_cast<std::string> ( ATwriteToString( (ATerm)$2 ) ) + ")";
      safe_assign($$, ATmakeAppl0( ATmakeAFun( result.c_str(), 0, ATfalse ) ));
    }
  ;

//sort constant
sort_constant:
  BOOL
    {
      safe_assign($$, ATmakeAppl0( ATmakeAFun( "Bool", 0, ATfalse ) ));
    }
  | POS
    {
      safe_assign($$, ATmakeAppl0( ATmakeAFun( "Pos", 0, ATfalse ) ));
    }
  | NAT
    {
      safe_assign($$, ATmakeAppl0( ATmakeAFun( "Nat", 0, ATfalse ) ));
    }
  | INT
    {
      safe_assign($$, ATmakeAppl0( ATmakeAFun( "Int", 0, ATfalse ) ));
    }
  | REAL
    {
      safe_assign($$, ATmakeAppl0( ATmakeAFun( "Real", 0, ATfalse ) ));
    }
  ;

//sort constructor
sort_constructor:
  LIST LPAR sort_expr RPAR
    {
      std::string result = "List(" + static_cast<std::string> ( ATwriteToString( (ATerm)$3 ) ) + ")";
      safe_assign($$, ATmakeAppl0( ATmakeAFun( result.c_str(), 0, ATfalse ) ));
    }
  | SET LPAR sort_expr RPAR
    {
      std::string result = "Set(" + static_cast<std::string> ( ATwriteToString( (ATerm)$3 ) ) + ")";
      safe_assign($$, ATmakeAppl0( ATmakeAFun( result.c_str(), 0, ATfalse ) ));
    }
  | BAG LPAR sort_expr RPAR
    {
      std::string result = "Bag(" + static_cast<std::string> ( ATwriteToString( (ATerm)$3 ) ) + ")";
      safe_assign($$, ATmakeAppl0( ATmakeAFun( result.c_str(), 0, ATfalse ) ));
    }
  ;

type_values :
  /* empty */
  |
  type_values type_value
  ;

type_value :
  QUOTED
    {
      if (!ignore_par[num_pars])
      {
        fsm_lexer_obj->typeValues = ATinsert( fsm_lexer_obj->typeValues,
            (ATerm)ATmakeAppl2(fsm_lexer_obj->const_ATvalue, (ATerm)$1,
            (ATerm)fsm_lexer_obj->typeId ) );
      }
    }
  ;

// ----------- Section containing the states ---------

states :
  /* empty */
  |
  states
    {
      par_index = 0;
    }
  state
    {
      fsm_lexer_obj->stateVector = ATreverse( fsm_lexer_obj->stateVector );
      unsigned int i = fsm_lexer_obj->fsm_lts->add_state(
          (ATerm) fsm_lexer_obj->stateVector );
      if ( i == 0 )
      {
        fsm_lexer_obj->fsm_lts->set_initial_state( i );
      }
      fsm_lexer_obj->stateVector = ATempty
    }
  EOLN
  ;

state :
  /* empty */
  |
  state NUMBER
    {
      if (!ignore_par[par_index])
      {
        if ( par_index < ATgetLength( fsm_lexer_obj->valueTable ) )
        {
          fsm_lexer_obj->stateVector = ATinsert( fsm_lexer_obj->stateVector,
              ATelementAt( (ATermList)ATelementAt( fsm_lexer_obj->valueTable,
                  par_index ), $2 ) );
        }
      }
      ++par_index;
    }
  ;

// ---------- Section containing the transitions ----------

transitions:
  /* empty */
  |
  transitions transition
  EOLN
  ;

transition:
  NUMBER NUMBER action
    {
      unsigned int frState = $1-1;
      unsigned int toState = $2-1;
      ATerm label = ATtableGet(fsm_lexer_obj->labelTable,(ATerm)$3);
      if ( label == NULL )
      {
        unsigned int i = fsm_lexer_obj->fsm_lts->add_label((ATerm)$3,
            !strcmp("tau",ATgetName(ATgetAFun($3))));
        label = (ATerm) ATmakeInt(i);
        ATtablePut(fsm_lexer_obj->labelTable,(ATerm)$3,label);
      }
      fsm_lexer_obj->fsm_lts->add_transition(mcrl2::lts::transition(frState,
          ATgetInt((ATermInt)label), toState ));
    }
  ;

action :
  /* empty */
    { safe_assign($$, ATmakeAppl0( ATmakeAFun( "", 0, ATfalse ) )) }
  |
  QUOTED
    { safe_assign($$, $1) }
  ;

%%

char* intToCString( int i )
{
    std::ostringstream oss;
    oss << i;
    return (char*)oss.str().c_str();
}
