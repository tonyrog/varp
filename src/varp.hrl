%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2019, Tony Rogvall
%%% @doc
%%%
%%% @end
%%% Created : 14 Mar 2019 by Tony Rogvall <tony@rogvall.se>

-ifndef(__VARP_HRL__).
-define(__VARP_HRL__, true).

-define(T,  t).
-define(F,  f).

-define(dbg0(F,As), ok).
-define(dbg1(F,A), io:format((F),(A))).
-ifdef(DEBUG).
-define(dbg(F,A), io:format((F),(A))).
-define(dcall(Fun), Fun()).
-else.
-define(dbg(F,A), ok).
-define(dcall(Fun), ok).
-endif.

-define(TOP_LEVEL, 0).

-define(DELTA, 0).
-define(GAMMA, 1).
-define(ALPHA, 2).
-define(BETA,  3).

-define(NUM_COUNTERS, 12).
-define(COUNTER_CONFLICT_CLAUSES,   1).
-define(COUNTER_MINIMIZE_COUNT,     2).
-define(COUNTER_COMPRESS_CLAUSES,   3).
-define(COUNTER_CONFLICT_LITERALS,  4).
-define(COUNTER_STUMBLE_COUNT,      5).
-define(COUNTER_OLLE_COUNT,         6).
-define(COUNTER_STUMBLE_OLLE_COUNT, 7).
-define(COUNTER_BJR_EVAL_COUNTER,   8).  %% restart counter
-define(COUNTER_REORDER_COUNTER,    9).
-define(COUNTER_ST_EVAL_COUNTER,    10). %% cancel/timeout check counter
-define(COUNTER_BT_EVAL_COUNTER,    11). %% cancel/timeout check counter
-define(COUNTER_BJT_EVAL_COUNTER,   12). %% cancel/timeout check counter

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

-record(cid,
	{ 
	  line,
	  name
	 }).

-record(cconst,
	{
	  line :: integer(),
	  base :: 2 | 8 | 10 | 16 | char | float | string,
	  value :: string()
	}).
	  
-record(cunary,
	{
	  line :: integer(),
	  op   :: atom(),
	  arg
	 }).

-record(cbinary,
	{
	  line :: integer(),
	  op   :: atom(),
	  arg1,
	  arg2
	 }).

-record(ccall,
	{
	  line :: integer(),
	  func,
	  args
	 }).

%%  cond ? then : else FIXME? GNU:  cond ? then
-record(cifexpr,
	{
	  line :: integer(),
	  test,
	  then,
	  else
	 }).

-record(cassign,
	{
	  line :: integer(),
	  op,
	  lhs,
	  rhs
	 }).

%% special  a..b  range
-record(crange,
	{
	  line :: integer(),
	  from,
	  to
	}).


-record(bs,
	{
	 state  = ok :: ok|cancel|timeout,
	 option = #{} :: map(), %% the options
	 counters :: reference(), %% counters(?NUM_COUNTERS)
	 d1 :: reference(),   %% histogram delta1 counters(1024)
	 d2 :: reference(),   %% histogram delta2 counters(1024)
	 clen :: reference(), %% histogram clause len counters(1024)
	 vs :: map(),         %% map() model variables var <=> Vn
	 vp :: reference(),   %% varc instance
	 t_global :: reference(), %% global timer 
	 t_local :: reference(),  %% local timer
	 main,                %% main formula variable
	 meta=[],            %% meta variable bindings during build
	 defs=[],            %% definitions [{{p,x,[v1,..vn]}, F(v1...vn)}]
	 decls=[],           %% declarations [{int,Sz,Pred},{uint,Sz,Pred}]
	 subst=[],           %% var/function substitution(s)
	 literals=[],        %% declared literals [atom()]
	 assert=[],          %% list of assertions [A1,...An]
	 input=[],           %% list of input modules [I1,...In]
	 output=[],          %% list of output modules [I1,...In]
	 proof_fd            %% proof output file
	}).

-define(BOOL,
	{"true",true},
	{"false",false},
	{"1",true},
	{"0",false}).

-define(ORDER,
	{"undefined", undefined},
	{"identity",  identity},
	{"random",    random},
	{"degree",     '+degree'},
	{"+degree",    '+degree'},
	{"-degree",    '-degree'},
	{"rank",       '+rank'},
	{"+rank",      '+rank'},
	{"-rank",      '-rank'},
	{"activity",   '+activity'},
	{"+activity",  '+activity'},
	{"-activity",  '-activity'}
       ).

-ifdef(OTP_RELEASE). %% this implies 21 or higher
-define(EXCEPTION(Class, Reason, Stacktrace), Class:Reason:Stacktrace).
-define(GET_STACK(Stacktrace), Stacktrace).
-else.
-define(EXCEPTION(Class, Reason, _), Class:Reason).
-define(GET_STACK(_), erlang:get_stacktrace()).
-endif.

-endif.



