/* $Id: gsinstantiate.c,v 1.1 2005/05/03 15:44:47 muck Exp $ */
#ifdef __cplusplus
extern "C" {
#endif

#define NAME "gsinstantiate"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <getopt.h>
#include <aterm2.h>
#include "gslowlevel.h"
#include "gsfunc.h"
#include "libgsparse.h"
#include "libgsnextstate.h"
#include "libgsrewrite.h"

static unsigned long num_states;
static unsigned long trans;
static unsigned long level;
static unsigned long max_states;
static bool trace;
static bool monitor;
static FILE *aut;
static unsigned long current_state;
static ATermIndexedSet states;
static ATermTable backpointers;
static bool deadlockstate;
static ATerm *orig_state;

void gsinst_callback(ATermAppl transition, ATerm state)
{
	ATbool new_state;
	unsigned long i;

	deadlockstate = false;

	i = ATindexedSetPut(states, state, &new_state);
	if ( new_state )
	{
		if ( (max_states == 0) || (num_states < max_states) )
		{
			num_states++;
			if ( trace )
			{
				ATtablePut(backpointers, state, *orig_state);
			}
		}
	}

	if ( i < num_states )
	{
		if ( aut != NULL )
		{
			fprintf(aut,"(%lu,\"",current_state);
			gsPrintPart(aut,transition,false,0);
			fprintf(aut,"\",%lu)\n",i);
fflush(aut);
		}
		trans++;
	}
}


void print_help(FILE *f)
{
	fprintf(f,"Usage: %s OPTIONS LPEFILE [OUTFILE]\n",NAME);
	fprintf(f,"Generate state space of LPEFILE and save the result to\n"
	          "OUTFILE (in the aut format). If OUTFILE is not supplied, the\n"
		  "state space is not stored.\n"
	          "\n"
	          "The OPTIONS that can be used are:\n"
	          "-h, --help               Display this help message\n"
		  "-f, --freevar            Do not replace free variables in\n"
		  "                         the LPE with dummy values.\n"
		  "-y, --dummy              Replace free variables in the LPE\n"
		  "                         with dummy values. (default)\n"
	          "-l, --max num            Explore at most num states\n"
	          "    --deadlock           Synonym for --deadlock-detect\n"
	          "-d, --deadlock-detect    Detect deadlocks (i.e. for every\n"
		  "                         deadlock a message is printed)\n"
	          "-e, --deadlock-trace     Write trace to each deadlock state\n"
		  "                         to a file\n"
	          "-m, --monitor            Print status of generation\n"
	          "-R, --rewriter name      Use rewriter 'name' (default inner3)\n"
	       );
}

int main(int argc, char **argv)
{
	FILE *SpecStream;
	ATerm stackbot;
	ATermAppl Spec;
	#define sopts "hfyldemR"
	struct option lopts[] = {
		{ "help", 		no_argument,		NULL,	'h' },
		{ "freevar", 		no_argument,		NULL,	'f' },
		{ "dummy", 		no_argument,		NULL,	'y' },
		{ "max", 		required_argument,	NULL,	'l' },
		{ "deadlock", 		no_argument,		NULL,	'd' },
		{ "deadlock-detect", 	no_argument,		NULL,	'd' },
		{ "deadlock-trace", 	no_argument,		NULL,	'e' },
		{ "monitor", 		no_argument,		NULL,	'm' },
		{ "rewriter", 		required_argument,	NULL,	'R' },
		{ 0, 0, 0, 0 }
	};
	int opt, strat;
	bool usedummies,trace_deadlock,explore;
	char *rw_arg;

	ATinit(argc,argv,&stackbot);

	strat = GS_REWR_INNER3;
	usedummies = true;
	max_states = 0;
	trace = false;
	trace_deadlock = false;
	monitor = false;
	explore = false;
	while ( (opt = getopt_long(argc,argv,sopts,lopts,NULL)) != -1 )
	{
		switch ( opt )
		{
			case 'h':
				print_help(stderr);
				return 0;
			case 'f':
				usedummies = false;
				break;
			case 'y':
				usedummies = true;
				break;
			case 'l':
				if ( optarg == NULL )
				{
					// XXX argument hack
					// argument doesn't seem to work for short options
					if ( (argv[optind][0] >= '0') && (argv[optind][0] <= '9') )
					{
						max_states = strtoul(argv[optind],NULL,0);
						optind++;
					}
				} else {
					if ( (optarg[0] >= '0') && (optarg[0] <= '9') )
					{
						max_states = strtoul(optarg,NULL,0);
					}
				}
				break;
			case 'd':
				explore = true;
				break;
			case 'e':
				trace = true;
				trace_deadlock = true;
				break;
			case 'm':
				monitor = true;
				break;
			case 'R':
				if ( optarg == NULL )
				{
					rw_arg = argv[optind++];
				} else {
					rw_arg = optarg;
				}
				if ( !strcmp(rw_arg,"inner") )
				{
					strat = GS_REWR_INNER;
				} else if ( !strcmp(rw_arg,"inner2") )
				{
					strat = GS_REWR_INNER2;
				} else if ( !strcmp(rw_arg,"inner3") )
				{
					strat = GS_REWR_INNER3;
				} else if ( !strcmp(rw_arg,"innerc") )
				{
					strat = GS_REWR_INNERC;
				} else if ( !strcmp(rw_arg,"innerc2") )
				{
					strat = GS_REWR_INNERC2;
				} else if ( !strcmp(rw_arg,"jitty") )
				{
					strat = GS_REWR_JITTY;
				} else {
					fprintf(stderr,"warning: unknown rewriter '%s', using default\n",rw_arg);
					strat = GS_REWR_INNER3;
				}
				break;
			default:
				break;
		}
	}

	if ( argc-optind < 1 )
	{
		print_help(stderr);
		return 1;
	}

	if ( (SpecStream = fopen(argv[optind],"r")) == NULL )
	{
		perror(NAME);
		return 1;
	}
	if ( argc-optind > 1 )
	{
		if ( (aut = fopen(argv[optind+1],"w")) == NULL )
		{
			perror(NAME);
			return 1;
		}
	} else {
		aut = NULL;
	}

	gsEnableConstructorFunctions();
	Spec = (ATermAppl) ATreadFromFile(SpecStream);
	if ( Spec == NULL )
	{
		return 1;
	}

	states = ATindexedSetCreate(10000,50);
	num_states = 0;
	trans = 0;
	if ( trace )
	{
		backpointers = ATtableCreate(10000,50);
	} else {
		backpointers = NULL;
	}
	
	if ( aut != NULL )
	{
		fprintf(aut,"des (0,0,0)                   \n");
	}

	ATerm state = gsNextStateInit(Spec,!usedummies,strat);

	ATbool new_state;
	current_state = ATindexedSetPut(states,state,&new_state);
	num_states++;

	level = 1;
	unsigned long nextlevelat = 1;
	unsigned long prevtrans = 0;
	unsigned long prevcurrent = 0;
	bool err = false;
	orig_state = &state;
	while ( current_state < num_states )
	{
		state = ATindexedSetGetElem(states,current_state);
		deadlockstate = true;
		gsNextState(state, gsinst_callback); // XXX state may contain Nils instead of free vars
		if ( NextStateError )
		{
			err = true;
			break;
		}
		if ( deadlockstate )
		{
			if ( explore )
			{
				printf("deadlock-detect: Deadlock found.\n");
				fflush(stdout);
			}
			if ( trace_deadlock )
			{
				ATerm s = state;
				ATerm ns;
				ATermList tr = ATmakeList0();

				while ( (ns = ATtableGet(backpointers, s)) != NULL )
				{
					tr = ATinsert(tr, s);
					s = ns;
				}

				for (; !ATisEmpty(tr); tr=ATgetNext(tr))
				{
					ATermList l = gsNextState(s, NULL);
					for (; !ATisEmpty(l); l=ATgetNext(l))
					{
						if ( ATisEqual(ATgetFirst(ATgetNext(ATLgetFirst(l))),ATgetFirst(tr)) )
						{
							gsPrintPart(stdout,ATAgetFirst(ATLgetFirst(l)),false,0);
							printf("\n");
							break;
						}
					}
					s = ATgetFirst(tr);
				}
				fflush(stdout);
			}
		}

		current_state++;
		if ( monitor && ( (current_state%1000) == 0 ) )
		{
			printf("monitor: Currently at level %lu with %lu state%s and %lu transition%s explored and %lu state%s seen.\n",level,current_state,(current_state==1)?"":"s",trans,(trans==1)?"":"s",num_states,(num_states==1)?"":"s");
		}
		if ( current_state == nextlevelat )
		{
			if ( monitor )
			{
				printf("monitor: Level %lu done. (%lu state%s, %lu transition%s)\n",level,current_state-prevcurrent,((current_state-prevcurrent)==1)?"":"s",trans-prevtrans,((trans-prevtrans)==1)?"":"s");
				fflush(stdout);
			}
			level++;
			nextlevelat = num_states;
			prevcurrent = current_state;
			prevtrans = trans;
		}
/*		if ( current_state == nextlevelat )
		{
			if ( monitor )
			{
				printf("monitor: Level %lu done. Currently %lu states visited and %lu states and %lu transitions explored.\n",level,num_states,current_state,trans);
				fflush(stdout);
			}
			level++;
			nextlevelat = num_states;
		}*/
	}

	if ( aut != NULL )
	{
		rewind(aut);
		fprintf(aut,"des (0,%lu,%lu)",trans,num_states);
		fclose(aut);
	}

	if ( !err )
	{
		printf("Done with state space generation (%lu level%s, %lu state%s and %lu transition%s).\n",level-1,(level==2)?"":"s",num_states,(num_states==1)?"":"s",trans,(trans==1)?"":"s");
	}
}

#ifdef __cplusplus
}
#endif
