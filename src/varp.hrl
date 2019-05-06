%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2019, Tony Rogvall
%%% @doc
%%%
%%% @end
%%% Created : 14 Mar 2019 by Tony Rogvall <tony@rogvall.se>

-ifndef(__VARP_HRL__).
-define(__VARP_HRL__, true).

-define(TRUE,   1).
-define(FALSE, -1).

-define(NUM_COUNTERS, 8).
-define(COUNTER_CONFLICT_CLAUSES,   1).
-define(COUNTER_MINIMIZE_COUNT,     2).
-define(COUNTER_COMPRESS_CLAUSES,   3).
-define(COUNTER_CONFLICT_LITERALS,  4).
-define(COUNTER_STUMBLE_COUNT,      5).
-define(COUNTER_OLLE_COUNT,         6).
-define(COUNTER_STUMBLE_OLLE_COUNT, 7).
-define(COUNTER_EVAL_COUNTER,       8).

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
	 option = #{} :: map(), %% the options
	 counters :: reference(), %% counters(?NUM_COUNTERS)
	 d1 :: reference(), %% counters(1024)
	 d2 :: reference(), %% counters(1042)
	 vs :: map(),         %% map() model variables var <=> Vn
	 vp :: reference(),   %% varc instance
	 meta=[],            %% meta variable bindings during build
	 defs=[],            %% definitions [{{p,x,[v1,..vn]}, F(v1...vn)}]
	 decls=[],           %% declarations [{int,Sz,Pred},{uint,Sz,Pred}]
	 subst=[],           %% var/function substitution(s)
	 literals=[]         %% declared literals [atom()]
	}).

-ifdef(OTP_RELEASE). %% this implies 21 or higher
-define(EXCEPTION(Class, Reason, Stacktrace), Class:Reason:Stacktrace).
-define(GET_STACK(Stacktrace), Stacktrace).
-else.
-define(EXCEPTION(Class, Reason, _), Class:Reason).
-define(GET_STACK(_), erlang:get_stacktrace()).
-endif.

-endif.



