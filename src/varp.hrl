%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2019, Tony Rogvall
%%% @doc
%%%
%%% @end
%%% Created : 14 Mar 2019 by Tony Rogvall <tony@rogvall.se>

-ifndef(__VARP_HRL__).
-define(__VARP_HRL__, true).

-define(T,  true).
-define(F,  false).

-define(TOP_LEVEL, 0).

-define(DELTA, 0).
-define(GAMMA, 1).
-define(BETA,  2).
-define(ALPHA, 3).

-define(NUM_COUNTERS, 13).
-define(COUNTER_CONFLICT_CLAUSES,   1).
-define(COUNTER_MINIMIZE_COUNT,     2).
-define(COUNTER_COMPRESS_CLAUSES,   3).
-define(COUNTER_CONFLICT_LITERALS,  4).
-define(COUNTER_STUMBLE_COUNT,      5).
-define(COUNTER_OLLE_COUNT,         6).
-define(COUNTER_STUMBLE_OLLE_COUNT, 7).
-define(COUNTER_BJR_BCP_COUNTER,    8).  %% restart counter
-define(COUNTER_REORDER_COUNTER,    9).
-define(COUNTER_ST_BCP_COUNTER,     10). %% cancel/timeout check counter
-define(COUNTER_BT_BCP_COUNTER,     11). %% cancel/timeout check counter
-define(COUNTER_BJT_BCP_COUNTER,    12). %% cancel/timeout check counter
-define(COUNTER_BJR_BOUND0,         13). %% store prvious #bound level=0

%% plugin results
-define(INCONSISTENT, inconsistent).
-define(CONTINUE,     continue).
-define(DONE,         done).
-define(ABORT(X),     {abort,(X)}).
-define(TIMEOUT,      ?ABORT(timeout)).
-define(ITERATIONS,   ?ABORT(iterations)).
-define(NOVAR,        ?ABORT(novar)).
-define(THRESHOLD,    ?ABORT(threshold)).
%% none resumable
-define(CANCEL,       ?ABORT(user)).
-define(ERROR,        ?ABORT(error)).

-define(GETOPT(Key, Map), maps:get((Key),(Map))).
-define(GETOPT_BS(Bs, Key), ?GETOPT((Key),(Bs)#bs.option)).

-define(LOG_LEVEL_NONE, -1).
-define(LOG_LEVEL_EMERGENCY, 0).
-define(LOG_LEVEL_ALERT,     1).
-define(LOG_LEVEL_CRITICAL,  2).
-define(LOG_LEVEL_ERROR,     3).
-define(LOG_LEVEL_WARNING,   4).
-define(LOG_LEVEL_NOTICE,    5).
-define(LOG_LEVEL_INFO,      6).
-define(LOG_LEVEL_DEBUG,     7).

-define(debug(Opt, Fmt, As), ?log(Opt,?LOG_LEVEL_DEBUG,Fmt,As)).
-define(warning(Opt, Fmt, As), ?log(Opt,?LOG_LEVEL_WARNING,Fmt,As)).
-define(info(Opt, Fmt, As), ?log(Opt,?LOG_LEVEL_INFO,Fmt,As)).
	
-define(log(OptMap, Level, Fmt, As),
	case Level =< maps:get(log,OptMap,?LOG_LEVEL_NONE) of
	    true ->
		io:format(Fmt, As);
	    false ->
		ok
	end).

-define(dbg0(F,As), ok).
-define(dbg1(F,A), io:format((F),(A))).
-ifdef(DEBUG).
-define(dbg(F,A), io:format((F),(A))).
-define(dcall(Fun), Fun()).
-else.
-define(dbg(F,A), ok).
-define(dcall(Fun), ok).
-endif.
-define(warn(F,A), io:format((F),(A))).


-type variable() :: varp_nif:variable().
-type literal() :: varp_nif:literal().
-type symbol() :: varp_nif:symbol().
-type varp() :: varp_nif:varp().
-type sort_key() :: varp_nif:sort_key().

-type vtype() :: 'int' | 'uint' | 'bit'.
-type ptype() :: vtype() | 'bool'.
-type psize() :: pos_integer().
-type pbits() :: {vtype(),Size::psize(),[literal()]} | {bool,literal()}.

-type pred()  :: {p,Name::atom(),[index()]}.
-type index() :: integer() | atom() | [integer()|atom()] | func().
-type func()  :: {f,Name::atom(),[index()]}.

-type var() :: pred() |
	       {uint,Size::psize(),pred()} |
	       {int,pred(),Size::psize(),Pos::integer()} |
	       {bit,pred(),Size::psize(),Pos::integer()}.

%% -define(PSYM_ARITY, true).

-type pdecl() ::
	#{ {atom(),arity()} => {ptype(),arity(),psize()}, %% PSYM_ARITY
	   atom()           => {ptype(),arity(),psize()} %% !PSYM_ARITY
	 }.
	   
-type plit() ::
	#{ {atom(),ptype(),psize()} => literal()|[literal()] }.

-record(bs,
	{
	 option = #{} :: map(), %% the options
	 counters :: reference(), %% counters(?NUM_COUNTERS)
	 d1 :: reference(),   %% histogram delta1 counters(1024)
	 d2 :: reference(),   %% histogram delta2 counters(1024)
	 clen :: reference(), %% histogram clause len counters(1024)
	 vs :: map(),         %% map() model variables var <=> Vn
	 vp :: reference(),   %% varc instance
	 t_global :: reference(), %% global timer 
	 t_local :: reference(),  %% local timer
	 main,                 %% main formula variable
	 meta=#{} :: #{ string() => integer() },
	 %% Def = {[v1,..vn],F(v1...vn)}
	 defs=#{} :: #{ pred() => {[atom()],term()}},
	 decls=#{} :: pdecl(),
	 subst=[],             %% var/function substitution(s)
	 literals=#{} :: #{ atom() => true },
	 assert=[],            %% list of assertions [A1,...An]
	 input=[],             %% list of input modules [I1,...In]
	 output=[],            %% list of output modules [I1,...In]
	 proof_fd              %% proof output file
	}).

-type bs() :: #bs{}.

-define(BOOL,
	{"true",true},
	{"false",false},
	{"1",true},
	{"0",false}).

-define(ORDER_UNDEFINED,  16#00).   %% "zero" order
-define(ORDER_IDENTITY,   16#01).   %% "input" order
-define(ORDER_RANDOM,     16#02).   %% "random" order
-define(ORDER_DEGREE,     16#03).   %% order according to occurence
-define(ORDER_RANK,       16#04).   %% 1/n1+...1/nk where ni is size of clause i
%% -define(ORDER_ACTIVITY,  16#05).   %% order according to conflict activity
-define(ORDER_USER,       16#06).   %% order according to user count
-define(ORDER_MASK,       16#3f).

-define(ORDER_ASCEND,     16#00).  %% ascending order
-define(ORDER_DESCEND,    16#80).  %% descending order
-define(ORDER_INTERLEAVE, 16#40).  %% mixed order
-define(ORDER_DIR_MASK,   16#C0).

-define(ORDER,
	{"undefined",  ?ORDER_UNDEFINED},
	{"identity",   ?ORDER_IDENTITY bor ?ORDER_DESCEND},
	{"+identity",  ?ORDER_IDENTITY bor ?ORDER_ASCEND},
	{"-identity",  ?ORDER_IDENTITY bor ?ORDER_DESCEND},
	{"=identity",  ?ORDER_IDENTITY bor ?ORDER_INTERLEAVE},

	{"random",   ?ORDER_RANDOM bor ?ORDER_DESCEND},
	{"+random",  ?ORDER_RANDOM bor ?ORDER_ASCEND},
	{"-random",  ?ORDER_RANDOM bor ?ORDER_DESCEND},
	{"=random",  ?ORDER_RANDOM bor ?ORDER_INTERLEAVE},

	{"degree",   ?ORDER_DEGREE bor ?ORDER_DESCEND},
	{"+degree",  ?ORDER_DEGREE bor ?ORDER_ASCEND},
	{"-degree",  ?ORDER_DEGREE bor ?ORDER_DESCEND},
	{"=degree",  ?ORDER_DEGREE bor ?ORDER_INTERLEAVE},

	{"rank",     ?ORDER_RANK bor ?ORDER_DESCEND},
	{"+rank",    ?ORDER_RANK bor ?ORDER_ASCEND},
	{"-rank",    ?ORDER_RANK bor ?ORDER_DESCEND},
	{"=rank",    ?ORDER_RANK bor ?ORDER_INTERLEAVE},

	{"user",     ?ORDER_USER bor ?ORDER_DESCEND},
	{"+user",    ?ORDER_USER bor ?ORDER_ASCEND},
	{"-user",    ?ORDER_USER bor ?ORDER_DESCEND},
	{"=user",    ?ORDER_USER bor ?ORDER_INTERLEAVE}
       ).

-define(BUMP_RANK,  -4).  %% bump implication clause number of steps
-define(BUMP_LOG10, -3).  %% bump value = log10(<number-of-variables>)
-define(BUMP_LOG2,  -2).  %% bump value = log2(<number-of-variables>)
-define(BUMP_NEXT,  -1).
-define(BUMP_NONE,   0).

-define(BUMP,
	{"none", ?BUMP_NONE},
	{"next", ?BUMP_NEXT},
	{"log2", ?BUMP_LOG2},
	{"log10", ?BUMP_LOG10},
	{"rank", ?BUMP_RANK}
       ).

-ifdef(OTP_RELEASE). %% this implies 21 or higher
-define(EXCEPTION(Class, Reason, Stacktrace), Class:Reason:Stacktrace).
-define(GET_STACK(Stacktrace), Stacktrace).
-else.
-define(EXCEPTION(Class, Reason, _), Class:Reason).
-define(GET_STACK(_), erlang:get_stacktrace()).
-endif.

-endif.
