%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2018, Tony Rogvall
%%% @doc
%%%    Implement the main loop with backjump (new multi bcp version)
%%% @end
%%% Created : 23 Apr 2018 by Tony Rogvall <tony@rogvall.se>

-module(varp_backjump).
-behaviour(varp_plugin).

-export([run/2]).
-export([options/0]).

%% -define(DEBUG, true).
-include("varp.hrl").

-define(CHECK_INTERVAL, 1000).  %% 1000ms 

%% -compile(export_all).

-define(SORT(Ord1,Ord2),
	{order,[{sort,[(Ord),(Ord2)]},{seed,0}]}).

-define(REORDER_NONE,
	[
	]).

-define(REORDER_SATURATE, 
	[
	 {0,{saturate,[{level,1},{laps,1}]}}
	]).

-define(REORDER_0,
	[
	 {0,?SORT(degree,random)},
	 {1,?SORT(rank,random)},
	 {2,?SORT(random,random)}
	]).

-define(REORDER_1,
	[
	 {0,?SORT(rank,random)}
	 {1,{saturate,[{level,1},{laps,1}]}}
	]).

-define(REORDER, ?REORDER_NONE).

options() ->
    [#{ long  => "timeout",
	short => "t",
	key   => timeout,
	spec  => {union,[float,{enum,[{"infinity",infinity}]}]},
	default => infinity,
	description => "Max time to run backjump in seconds"
      },

     #{ long => "max",
	short => "n",
	key => max,
	spec => unsigned,
	default => 1,
	description => "Max number of models to count or collect, 0=all."
      },
     
     #{ long => "minimize",
	short => "z",
	key => minimize,
	spec => {enum,
		 [{"0", none},  {"n", none}, {"none",none},
		  {"1", local}, {"l", local}, {"local",local},
		  {"2", global}, {"g", global}, {"global",global},
		  {"3", recursive}, {"r",recursive},{"recursive",recursive}]},
	default => none,
	description => "Use conflict clause minimization."
      },

     #{ long => "stumble",
	key => stumble,
	spec => unsigned,
	default => 0,
	description => "extra backjump level"},

     #{ long => "olle",
	key => olle,
	spec => float,
	default => 0,
	description => "extra backjump factor"},
     
     #{ long => "stumble-olle",
	key => stumble_olle,
	spec =>  {enum,[?BOOL]},
	default => false,
	description => "both backjump and factor"},

     #{ long => "max-conflicts",
	key => max_conflicts,
	spec =>  unsigned,
	default => 1,
	description => "Max number of conflicts to analyse"},

     #{ long => "max-learned",
	key => max_learned,
	spec =>  unsigned,
	default => 0,
	description => "Max number of clauses to generate in learning"},

     #{ long => "max-learned-factor",
	key => max_learned_factor,
	spec =>  float,
	default => 0,
	description => "Factor to calculate number of learned clauses"},

     #{ long => "max-learned-inc",
	key => max_learned_inc,
	spec =>  float,
	default => 0,
	description => "Factor to increase number of learned clauses"},

     #{ long => "keep-factor",
	key => keep_factor,
	spec =>  float01,
	default => 0.5,
	description => "Number of clauses to keep,"
	"in terms of number of learned clauese"},
     
     #{ long => "min-keep-clauses",
	key => min_keep_clauses,
	spec =>  unsigned,
	default => 0,
	description => "Min number of clauses to keep"},

     #{ long => "restart-counter",
	key => restart_counter,
	spec =>  unsigned,
	default => 0,
	description => "Number of (bcp)counts until restart"},

     #{ long => "restart-interval",
	key => restart_interval,
	spec =>  {union,[float,{enum,[{"infinity",infinity}]}]},
	default => infinity,
	description => "Restart interval in seconds"},

     #{ long => "bump",
	key => bump,
	spec => {union,[integer,float01,{enum,[?BUMP]}]},
	default => 1, %% 0.5?
	description => "VSIDS bump value"},

     #{ long => "display",
	short => "d",
	key => display,
	spec => {enum,[{"delta",delta},
		       {"d",delta},
		       {"histogram",histogram},
		       {"h",histogram},
		       ?BOOL]},
	default => false,
	description => "Display statistics."
      },

     %% internal options
     #{ key => reorder,
	spec => {list,
		 {integer,{atom,{list,term}}}},
	default => ?REORDER,
	description => "Internal reorder list"}
    ].
     
-record(m,
	{
	 method,  %% collect or count
	 max,     %% max number to collect/count
	 n  = 0,
	 ms = []
	}).
	 
run(Bs, Param) when is_record(Bs, bs), is_map(Param) ->
    MaxConflicting = maps:get(max_conflicts,Param),
    varp_nif:setopt(Bs#bs.vp, max_conflicting, MaxConflicting),
    varp_nif:setopt(Bs#bs.vp, xref, false), %% not while building clauses
    Timeout = maps:get(timeout, Param, infinity),
    MaxLearned = max_learned(Bs,Param),
    _KeepSize  = keep_size(Bs, Param, MaxLearned),
    set_bcp_counter(Bs, varp_nif:getstat(Bs#bs.vp, bcp_counter)),
    start_restart_timer(Param),
    Bs1 = varp:set_local_timeout(Bs, Timeout),
    M0  = #m { method = varp_nif:getopt(Bs1#bs.vp,method),
	       max = maps:get(max, Param) },
    init(Bs1, Param, MaxLearned, M0).

init(Bs, Param, MaxLearned, MR) ->
    0 = varp_nif:level(Bs#bs.vp),
    timeout_or_cancel(Bs, Param, MaxLearned, MR).

timeout_or_cancel(Bs, Param, MaxLearned, MR) ->
    case varp:check_timeout_or_cancel(Bs,?COUNTER_BJT_BCP_COUNTER,
				      ?CHECK_INTERVAL) of
	false ->
	    main(Bs,Param,MaxLearned,MR);
	{true, What} ->
	    varp_nif:pop(Bs#bs.vp, ?TOP_LEVEL),
	    return(What, MR, Bs)
    end.

main(Bs,Param,MaxLearned,MR) ->
    case varp_nif:nbcp(Bs#bs.vp) of
	false ->  %% contradiction
	    Level = varp_nif:level(Bs#bs.vp),
	    case Level of
		0 when MR#m.n =:= 0 ->
		    varp_formula:proof_output(Bs,$a,[]),
		    display_stat(Bs,Param),
		    return(?INCONSISTENT,MR,Bs);
		0 ->
		    return(?DONE,MR,Bs);
		_ ->
		    conflict(Bs,Param,MaxLearned,MR)
	    end;
	true ->  %% model
	    Level = varp_nif:level(Bs#bs.vp),
	    N = MR#m.n + 1,
	    Model = varp:output_model(Bs,false,N),
	    if N >= MR#m.max, MR#m.max > 0; Level =:= 0 -> %%?
		    display_stat(Bs,Param),
		    R = if Level =:= 0 -> ?DONE; true -> ?CONTINUE end,
		    case MR#m.method of
			collect ->
			    {R,[Model|MR#m.ms],Bs};
			count ->
			    {R,N,Bs}
		    end;
	       true ->
		    Block = varp:block_clause(Bs),
		    %% FIXME: minimize Block clause and find
		    %% a working jump level (maybe just one up?)
		    varp_nif:pop(Bs#bs.vp, ?TOP_LEVEL),
		    %% FIXME: DELTA is maybe not the correct place!?
		    varp_circuit:clause(Bs, Block, ?DELTA),
		    %% we start with simple restart
		    case MR#m.method of
			collect ->
			    MR1 = MR#m { n=N, ms = [Model|MR#m.ms] },
			    init(Bs,Param,MaxLearned,MR1);
			count ->
			    MR1 = MR#m { n=N },
			    init(Bs,Param,MaxLearned,MR1)
		    end
	    end
    end.

conflict(Bs,Param,MaxLearned,MR) ->
    %% LClauseList = [{ClauseLength, ClauseIndex}] 
    %% ClauseLength may be 1 !
    LClauses1 = varp_conflict:analyze(Bs#bs.vp,
				      maps:get(bump,Param),
				      maps:get(minimize,Param)),
    case lists:keysort(1, LClauses1) of
	LClauses2 = [{1,_Count,_}|_] ->
	    %% has unit! jump to top-level and install
	    varp_nif:pop(Bs#bs.vp, ?TOP_LEVEL),
	    move_to_gamma(Bs, LClauses2),
	    main_bcp(Bs,Param,?TOP_LEVEL,MaxLearned,MR);

	[{_Len,Count,Aix}] -> %% one clause only
	    minimize_count(Bs, Count),
	    {ALen,D1,D2,J2,J3,_Clause} = jump_info(Bs#bs.vp, Aix),
	    do_stat(Bs,D1,D2),
	    L = maps:get(stumble,Param),
	    K = maps:get(olle,Param),
	    M = maps:get(stumble_olle,Param),
	    JLevel = do_jump(Bs,L,K,M,D1,D2,J2,J3),
	    varp_nif:pop(Bs#bs.vp, JLevel),
	    move_to_gamma(Bs,ALen,Aix),
	    main_bcp(Bs,Param,JLevel,MaxLearned,MR);

	LClauses2 -> %% no units determine level
	    %% io:format("conflict clauses = ~p\n", [LClauses2]),
	    JClauses1 = 
		[{jump_info(Bs#bs.vp, Aix),Count} ||
		    {_Len,Count,Aix} <- LClauses2],
	    %% io:format("JClauses1 = ~w\n", [JClauses1]),
	    %% jump_info = {L,D1,D2,J2,J3,Aix}
	    JClauses2 =
		lists:sort(fun({{La,D1a,_D2a,_J2a,_J3a,_Clausea},_Counta},
			       {{Lb,D1b,_D2b,_J2b,_J3b,_Clauseb},_Countb}) ->
				   if D1a =:= D1b -> La < Lb;
				      true -> D1a > D1b
				   end
			   end, JClauses1),
	    [JClause|JClauses3] = JClauses2,
	    LClauses4 = [{L,Count,Clause} ||
			    {{L,_D1,_D2,_J2,_J3,Clause},Count} <- JClauses3],
	    LClauses5 = lists:sort(fun({La,_Ca,_},{Lb,_Cb,_}) -> La < Lb end,
				   LClauses4),
	    L = maps:get(stumble,Param),
	    K = maps:get(olle,Param),
	    M = maps:get(stumble_olle,Param),

	    {{ALen,D1,D2,J2,J3,Aix},Count} = JClause,
	    minimize_count(Bs, Count),
	    do_stat(Bs,D1,D2),
	    JLevel = do_jump(Bs,L,K,M,D1,D2,J2,J3),
	    %% FIXME if JLevel = J3 then we SHOULD select
	    %% corresponding literal for -L2/-L3 as next unbound
	    varp_nif:pop(Bs#bs.vp, JLevel),
	    move_to_gamma(Bs, LClauses5),
	    %% install the conflict clause
	    move_to_gamma(Bs,ALen,Aix),
	    main_bcp(Bs,Param,JLevel,MaxLearned,MR)
    end.

minimize_count(_Bs, 0) ->
    ok;
minimize_count(Bs, Count) ->
    %% io:format("Minimize removed ~w literals\n", [Count]),
    counters:add(Bs#bs.counters, ?COUNTER_MINIMIZE_COUNT, Count).

jump_info(V, Cix) ->
    varp_nif:clause_info(V, Cix, jump).

%% Move a list of clauses from alpha to gamma (install them)
move_to_gamma(Bs, [{Len,Count,Aix}|LCs]) ->
    minimize_count(Bs, Count),
    move_to_gamma(Bs, Len, Aix),
    move_to_gamma(Bs, LCs);
move_to_gamma(_Bs, []) ->
    ok.

move_to_gamma(Bs, 1, Aix) ->
    varp_formula:proof_output(Bs,$a,Aix),
    true = varp_nif:move_clause(Bs#bs.vp, Aix, gamma),
    counters:add(Bs#bs.clen, 1, 1);
move_to_gamma(Bs, Len, Aix) ->
    {true,Gix} = varp_nif:move_clause(Bs#bs.vp, Aix, gamma),
    varp_formula:proof_output(Bs,$a,Gix),
    counters:add(Bs#bs.counters, ?COUNTER_CONFLICT_CLAUSES, 1),
    counters:add(Bs#bs.counters, ?COUNTER_CONFLICT_LITERALS, Len),
    if Len >= 1023 ->
	    counters:add(Bs#bs.clen, 1024, 1);
       true ->
	    counters:add(Bs#bs.clen, Len, 1)
    end.

%% after conflict clause generation we need to run bcp and
%% check result.
main_bcp(Bs,Param,Level,MaxLearned,MR) ->
    case varp_nif:bcp(Bs#bs.vp) of
	false ->
	    case Level of
		0 when MR#m.n =:= 0 ->
		    varp_formula:proof_output(Bs,$a,[]),
		    display_stat(Bs,Param),
		    return(?INCONSISTENT,MR,Bs);
		0 ->
		    return(?DONE,MR,Bs);
		_ ->
		    conflict(Bs,Param,MaxLearned,MR)
	    end;
	true ->
	    restart(Bs,Param,MaxLearned,MR)
    end.

restart(Bs,Param,MaxLearned,MR) ->
    RestartByTimeout = restart_by_timeout(Bs, Param), %% also restart!!
    RestartByCount = restart_by_counter(Bs, Param),
    case need_purge(Bs, Param, MaxLearned) of
	true ->
	    varp_nif:pop(Bs#bs.vp, ?TOP_LEVEL),
	    varp_formula:proof_output(Bs,$c,"purge"),
	    ?dbg0("purge\n",[]),
	    varp_formula:del_unused_clauses(Bs),
	    MaxLearned1 = max_learned_inc(Bs, Param, MaxLearned),
	    _KeepSize = keep_size(Bs, Param, MaxLearned1),
	    init(Bs, Param, MaxLearned1, MR);
	false ->
	    if RestartByCount ->
		    varp_formula:proof_output(Bs,$c,"counter limit"),
		    varp_nif:pop(Bs#bs.vp, ?TOP_LEVEL),
		    reorder(Bs, Param),
		    init(Bs, Param, MaxLearned, MR);
	       RestartByTimeout ->
		    varp_formula:proof_output(Bs,$c,"timeout"),
		    varp_nif:pop(Bs#bs.vp, ?TOP_LEVEL),
		    reorder(Bs, Param),
		    init(Bs, Param, MaxLearned, MR);
	       true ->
		    timeout_or_cancel(Bs,Param,MaxLearned,MR)
	    end
    end.

    

reorder(Bs, Param) ->
    N = counters:get(Bs#bs.counters,?COUNTER_REORDER_COUNTER),
    counters:add(Bs#bs.counters,?COUNTER_REORDER_COUNTER, 1),
    reorder_(Bs, N, maps:get(reorder,Param)).

reorder_(_Bs, _N, []) ->
    ok;
reorder_(Bs,  N, Reorder) ->
    ReorderMap = maps:from_list(Reorder),
    case maps:find(N rem maps:size(ReorderMap), ReorderMap) of
	{ok,skip} ->
	    ?dbg0("Skip:\n", []),
	    ok;
	{ok,{order,Opts}} ->
	    ?dbg0("Reorder: ~p\n", [Opts]),
	    Seed = proplists:get_value(seed, Opts, 0),
	    case proplists:get_value(sort, Opts, []) of
		[] -> ok;
		[Key1] ->
		    varp_nif:order_sort(Bs#bs.vp,Key1,Seed);
		[Key1,Key2] ->
		    varp_nif:order_sort(Bs#bs.vp,Key1,Key2,Seed)
	    end;
	{ok,{saturate,Opts}} ->
	    ?dbg0("Saturate: ~p\n", [Opts]),
	    Laps = proplists:get_value(laps,Opts,0),
	    Timeout = proplists:get_value(timeout,Opts,infinity),
	    varp_saturate:saturate(Bs,1,Timeout,Laps,0);
	_ ->
	    Seed = varp_nif:getopt(Bs#bs.vp,seed),
	    varp_nif:order_sort(Bs#bs.vp,random,Seed)
    end.


return(What, MR, Bs) ->
    case MR#m.method of
	collect ->
	    {What,MR#m.ms,Bs};
	count ->
	    {What,MR#m.n,Bs}
    end.

need_purge(Bs, _Param, MaxLearned) ->
    case varp_nif:clauseset_offset(Bs#bs.vp, ?GAMMA) > 0 of
	true ->
	    Learned = varp_nif:clauseset_size(Bs#bs.vp, ?GAMMA),
	    Learned > MaxLearned;
	false ->
	    false
    end.

max_learned_inc(_Bs, Param, MaxLearned) ->
    Inc = maps:get(max_learned_inc,Param),
    MaxLearnedFactorInc = max(1.0,Inc),
    trunc(MaxLearned * MaxLearnedFactorInc).
    
restart_by_timeout(Bs, Param) ->
    receive 
	{timeout,_Timer,restart} ->
	    start_restart_timer(Param),
	    Bound0 = varp_nif:get_number_of_bindings(Bs#bs.vp, 0),
	    PrevBound0 = get_bound0(Bs),
	    set_bound0(Bs, Bound0),
	    PrevBound0 =:= Bound0   %% no units since last restart
    after 0 ->
	    false
    end.

start_restart_timer(Param) ->
    case maps:get(restart_interval,Param) of
	infinity -> undefined;
	IVal when IVal == 0 -> undefined;
	IVal ->
	    IVal1 = max(0.1, IVal),
	    erlang:start_timer(trunc(1000*IVal1), self(), restart)
    end.

get_bound0(Bs) ->
    counters:get(Bs#bs.counters, ?COUNTER_BJR_BOUND0).

set_bound0(Bs, Value) ->
    counters:put(Bs#bs.counters,?COUNTER_BJR_BOUND0, Value).

%% Restart using bcp counter
restart_by_counter(Bs, Param) ->	
    case maps:get(restart_counter,Param) of
	0 -> false;
	RestartCounter ->
	    BcpCounter = varp_nif:getstat(Bs#bs.vp, bcp_counter),
	    PrevCounter = get_bcp_counter(Bs),
	    if (BcpCounter - PrevCounter) >= RestartCounter ->
		    set_bcp_counter(Bs, BcpCounter),
		    true;
	       true ->
		    false
	    end
    end. 

get_bcp_counter(Bs) ->
    counters:get(Bs#bs.counters, ?COUNTER_BJR_BCP_COUNTER).

set_bcp_counter(Bs, Value) ->
    counters:put(Bs#bs.counters,?COUNTER_BJR_BCP_COUNTER, Value).

%% J2 is backjump level, J3 is backstumble level
%% D2 is level to backjump delta, D3 is backjump to two free literal level
%% L min stumble limit, K is factor bwteen D1 and D2
do_jump(Bs,L,K,M,D1,D2,J2,J3) ->
    if  M, L > 0, D2 >= L, K > 0, D2 > 0, D1 >= K*D2 ->
	    counters:add(Bs#bs.counters, ?COUNTER_STUMBLE_OLLE_COUNT, 1),
	    J3;
	L > 0, D2 >= L -> 
	    counters:add(Bs#bs.counters, ?COUNTER_STUMBLE_COUNT, 1),
	    J3;
	K > 0, D2 > 0, D1 >= K*D2 ->
	    counters:add(Bs#bs.counters, ?COUNTER_OLLE_COUNT, 1),
	    J3;
	true -> 
	    J2
    end.

do_stat(Bs, D1, D2) ->
    if D1 >= 1023 ->
	    counters:add(Bs#bs.d1, 1024, 1);
       true ->
	    counters:add(Bs#bs.d1, D1+1, 1)
    end,
    if D2 >= 1023 ->
	    counters:add(Bs#bs.d2, 1024, 1);
       true ->
	    counters:add(Bs#bs.d2, D2+1, 1)
    end.

keep_size(Bs, Param, MaxLearned) ->
    MinKeep = maps:get(min_keep_clauses, Param),
    KeepFactor = maps:get(keep_factor, Param),
    KeepSize = if MaxLearned =:= 0 ->
		       0;
		  KeepFactor > 0, MinKeep > 0 ->
		       max(MinKeep, trunc(KeepFactor*MaxLearned));
		  KeepFactor > 0 ->
		       trunc(KeepFactor*MaxLearned);
		  MinKeep > 0 ->
		       MinKeep;
		  true ->
		       0
	       end,
    varp_nif:clauseset_offset(Bs#bs.vp, ?GAMMA, KeepSize),  %% sets gamma offset
    case maps:get(display, Param) of
	true ->
	    io:format("keep: KeepSize=~w, MaxLearned=~w, KeepFactor=~w, MinKeep=~w\n",
		      [KeepSize, MaxLearned, KeepFactor, MinKeep]);
	_ -> ok
    end,
    KeepSize.

max_learned(Bs,Param) ->
    Permanent = varp_nif:clauseset_size(Bs#bs.vp, ?DELTA),
    MaxLearnedClauses = maps:get(max_learned,Param),
    MaxLearnedFactor = maps:get(max_learned_factor,Param),
    case maps:get(display, Param) of
	true ->    
	    io:format("learned: Permanent=~w,MaxLearnedClause=~w,MaxLearnedFactor=~w\n",
		      [Permanent, MaxLearnedClauses, MaxLearnedFactor]);
	_ ->
	    ok
    end,
    if MaxLearnedFactor > 0, MaxLearnedClauses > 0 ->
	    min(MaxLearnedClauses,trunc(MaxLearnedFactor*Permanent));
       MaxLearnedFactor > 0 ->
	    trunc(MaxLearnedFactor*Permanent);
       MaxLearnedClauses > 0 ->
	    MaxLearnedClauses;
       true ->
	    0
    end.

display_stat(Bs,Param) ->
    case maps:get(display, Param) of
	false ->
	    ok;
	true ->
	    io:format("num conflict clauses added: ~w\n", 
		      [counters:get(Bs#bs.counters,
				    ?COUNTER_CONFLICT_CLAUSES)]),
	    io:format("num conflict ilterals: ~w\n",
		      [counters:get(Bs#bs.counters,
				    ?COUNTER_CONFLICT_LITERALS)]),
	    io:format("num literals removed: ~w\n",
		      [counters:get(Bs#bs.counters,
				    ?COUNTER_MINIMIZE_COUNT)]),
	    io:format("number_of_marks: ~w\n", 
		      [varp_nif:getstat(Bs#bs.vp, mark_counter)]),
	    io:format("number_of_decisions: ~w\n", 
		      [varp_nif:getstat(Bs#bs.vp, decision_counter)]),
	    io:format("number_of_conflicts: ~w\n", 
		      [varp_nif:getstat(Bs#bs.vp, conflict_counter)]),
	    ok;
	delta ->
	    io:format("Backjump deltas used\n", []),
	    lists:foreach(fun(D) ->
				  case {counters:get(Bs#bs.d1, D+1),
					counters:get(Bs#bs.d2, D+1)} of
				      {0,0} -> ok;
				      {N,M} -> 
					  io:format("~w: d1=~w, d2=~w\n", [D,N,M])
				  end
			  end, lists:seq(0,1023));
	histogram ->
	    io:format("Installed clauses lengh histogram\n", []),
	    lists:foreach(fun(L) ->
				  case counters:get(Bs#bs.clen, L) of
				      0 -> ok;
				      N ->
					  if L =:= 1024 ->
						  io:format(">1024: ~w\n", [N]);
					     true ->
						  io:format("~w: ~w\n", [L,N])
					  end
				  end
			  end, lists:seq(1,1024))
    end.
