%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2018, Tony Rogvall
%%% @doc
%%%    Implement the main loop with backjump (new multi bcp version)
%%% @end
%%% Created : 23 Apr 2018 by Tony Rogvall <tony@rogvall.se>

-module(varp_nbackjump).

-export([run/2]).
-export([options/0]).

%% -define(DEBUG, true).
-include("varp.hrl").

-define(ROOT_LEVEL, 1).
-define(CHECK_INTERVAL, 1000).  %% 1000ms 

%% -compile(export_all).

-define(ORDER_OPT(Ord,Ord2),
	{order,[{sort,[(Ord) bor ?ORDER_DESCEND,Ord2]},
		{seed,-1}]}).

-define(REORDER_0,
	[
	 {0,?ORDER_OPT(?ORDER_ACTIVITY,?ORDER_RANDOM)},
	 {1,?ORDER_OPT(?ORDER_DEGREE,?ORDER_RANDOM)},
	 {2,?ORDER_OPT(?ORDER_RANK,?ORDER_RANDOM)},
	 {3,?ORDER_OPT(?ORDER_RANDOM,?ORDER_RANDOM)}
	]).

-define(REORDER_1,
	[
	 {0,?ORDER_OPT(?ORDER_ACTIVITY,?ORDER_UNDEFINED)},
	 {1,?ORDER_OPT(?ORDER_ACTIVITY,?ORDER_UNDEFINED)},
	 {2,?ORDER_OPT(?ORDER_ACTIVITY,?ORDER_UNDEFINED)},
	 {3,?ORDER_OPT(?ORDER_ACTIVITY,?ORDER_UNDEFINED)}
	]).

options() ->
    [#{ long  => "timeout",
	short => "t",
	key   => timeout,
	spec  => {union,[float,{enum,[{"infinity",infinity}]}]},
	default => infinity,
	description => "Max time to run backjump in milliseconds"
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
	spec => {enum,[?BOOL]},
	default => true,
	description => "Use conflict clause minimization."
      },

     #{ long => "iorder",
	key => iorder,
	spec => unsigned,
	default => 0,
	description => "max conflict clause length"},

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
	description => "Number of clauses to keep"},
     
     #{ long => "min-keep-clauses",
	key => min_keep_clauses,
	spec =>  unsigned,
	default => 0,
	description => "Min number of clauses to keep"},

     #{ long => "restart-counter",
	key => restart_counter,
	spec =>  unsigned,
	default => 0,
	description => "Number of counts/bcp until restart"},

     #{ long => "restart-interval",
	key => restart_interval,
	spec =>  {union,[float,{enum,[{"infinity",infinity}]}]},
	default => infinity,
	description => "Restart interval in seconds"},

     #{ long => "decay",
	key => decay,
	spec =>  float,
	default => 0.95,
	description => "Decay factor."},

     #{ long => "bump",
	key => bump,
	spec =>  integer,
	default => 1,
	description => "Bump value."},

     #{ long => "display",
	short => "d",
	key => display,
	spec => {enum,[?BOOL]},
	default => false,
	description => "Display statistics."
      },

     %% internal options
     #{ key => reorder,
	spec => {list,
		 {integer,{atom,{list,term}}}},
	default => ?REORDER_1,
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
    varp_formula:config(Bs, max_conflicting, MaxConflicting),
    Timeout = maps:get(timeout, Param, infinity),
    MaxLearned = max_learned(Bs,Param),
    _KeepSize  = keep_size(Bs, Param, MaxLearned),
    set_bcp_counter(Bs, varp_formula:info(Bs, bcp_counter)),
    start_restart_timer(Param),
    Bs1 = varp:set_local_timeout(Bs, Timeout),
    M0  = #m { method = varp_formula:getopt(Bs1,method),
	       max = maps:get(max, Param) },
    init(Bs1, Param, MaxLearned, M0).

init(Bs, Param, MaxLearned, MR) ->
    varc:set_level(Bs#bs.vp, ?TOP_LEVEL),
    timeout_or_cancel(Bs, Param, MaxLearned, MR).

timeout_or_cancel(Bs, Param, MaxLearned, MR) ->
    case varp:check_timeout_or_cancel(Bs,?COUNTER_BJT_BCP_COUNTER,
				      ?CHECK_INTERVAL) of
	false ->
	    main(Bs,Param,MaxLearned,MR);
	{true, What} ->
	    undo_until(Bs, ?TOP_LEVEL),
	    return(What, MR, Bs)
    end.

main(Bs,Param,MaxLearned,MR) ->
    case varc:nbcp(Bs#bs.vp) of
	false ->  %% contradiction
	    Level = varc:info(Bs#bs.vp, level),
	    case Level of
		0 when MR#m.n =:= 0 ->
		    varp_formula:proof_output(Bs,$a,[]),
		    display_stat(Bs,Param),
		    return(?INCONSISTENT,MR,Bs);
		0 ->
		    return(?DONE,MR,Bs);
		_ ->
		    conflict(Bs,Param,Level,MaxLearned,MR)
	    end;
	true ->  %% model
	    Level = varc:info(Bs#bs.vp, level),
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
		    undo_until(Bs, ?TOP_LEVEL),
		    %% FIXME: DELTA is maybe not the correct place!?
		    varp_formula:add_clause(Bs, Block, ?DELTA),
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

conflict(Bs,Param,Level,MaxLearned,MR) ->
    %% LClauseList = [{ClauseLength, ClauseIndex}] 
    %% ClauseLength may be 1 !
    LClauses1 = varp_conflict:analyze_alpha(Bs,Level,
					    maps:get(bump,Param),
					    maps:get(minimize,Param)),
    %% io:format("LClases1 = ~w\n", [LClauses1]),
    varc:decay(Bs#bs.vp, maps:get(decay,Param)),

    case lists:keysort(1, LClauses1) of
	LClauses2 = [{1,_}|_] -> %% has unit! jump to top-level and install
	    undo_until(Bs, Level, ?TOP_LEVEL),
	    move_to_gamma(Bs, LClauses2),
	    main_bcp(Bs,Param,?TOP_LEVEL,MaxLearned,MR);

	[{_Len,Aix}] -> %% one clause only
	    {ALen,D1,D2,J2,J3,_Clause} = jump_info(Bs#bs.vp, Aix),
	    do_stat(Bs,D1,D2),
	    L = maps:get(stumble,Param),
	    K = maps:get(olle,Param),
	    M = maps:get(stumble_olle,Param),
	    JLevel = do_jump(Bs,L,K,M,D1,D2,J2,J3),
	    undo_until(Bs, Level, JLevel),
	    move_to_gamma(Bs,ALen,Aix),
	    main_bcp(Bs,Param,JLevel,MaxLearned,MR);

	LClauses2 -> %% no units determine level
	    %% io:format("conflict clauses = ~p\n", [LClauses2]),
	    JClauses1 = [jump_info(Bs#bs.vp, Aix) || {_Len,Aix} <- LClauses2],
	    %% io:format("JClauses1 = ~w\n", [JClauses1]),
	    %% jump_info = {L,D1,D2,J2,J3,Aix}
	    JClauses2 =
		lists:sort(fun({La,D1a,_D2a,_J2a,_J3a,_Clausea},
			       {Lb,D1b,_D2b,_J2b,_J3b,_Clauseb}) ->
				   if D1a =:= D1b -> La < Lb;
				      true -> D1a > D1b
				   end
			   end, JClauses1),
	    [JClause|JClauses3] = JClauses2,
	    LClauses4 = [{L,Clause} ||
			    {L,_D1,_D2,_J2,_J3,Clause} <- JClauses3],
	    LClauses5 = lists:sort(fun({La,_},{Lb,_}) -> La < Lb end,
				   LClauses4),
	    L = maps:get(stumble,Param),
	    K = maps:get(olle,Param),
	    M = maps:get(stumble_olle,Param),

	    {ALen,D1,D2,J2,J3,Aix} = JClause,
	    do_stat(Bs,D1,D2),
	    JLevel = do_jump(Bs,L,K,M,D1,D2,J2,J3),
	    %% FIXME if JLevel = J3 then we SHOULD select
	    %% corresponding literal for -L2/-L3 as next unbound
	    undo_until(Bs, Level, JLevel),
	    move_to_gamma(Bs, LClauses5),
	    %% install the conflict clause
	    move_to_gamma(Bs,ALen,Aix),
	    main_bcp(Bs,Param,JLevel,MaxLearned,MR)
    end.


jump_info(V, Cix) ->
    varc:clause_info(V, Cix, jump).

%% Move a list of clauses from alpha to gamma (install them)
move_to_gamma(Bs, [{Len,Aix}|LCs]) ->
    move_to_gamma(Bs, Len, Aix),
    move_to_gamma(Bs, LCs);
move_to_gamma(_Bs, []) ->
    ok.

move_to_gamma(Bs, 1, Aix) ->
    %% io:format("Move UNIT ~w to gamma\n", [varc:get_clause(Bs#bs.vp, Aix)]),
    varp_formula:proof_output(Bs,$a,Aix),
    true = varc:move_clause(Bs#bs.vp, Aix, gamma),
    counters:add(Bs#bs.clen, 1, 1);
move_to_gamma(Bs, Len, Aix) ->
    %% io:format("Move CLAUSE ~w to gamma\n", [varc:get_clause(Bs#bs.vp, Aix)]),
    {true,Gix} = varc:move_clause(Bs#bs.vp, Aix, gamma),
    varp_formula:proof_output(Bs,$a,Gix),
    if Len >= 1023 ->
	    counters:add(Bs#bs.clen, 1024, 1);
       true ->
	    counters:add(Bs#bs.clen, Len, 1)
    end.

%% after conflict clause generation we need to run bcp and
%% check result.
main_bcp(Bs,Param,Level,MaxLearned,MR) ->
    case varc:bcp(Bs#bs.vp) of
	false ->
	    case Level of
		0 when MR#m.n =:= 0 ->
		    varp_formula:proof_output(Bs,$a,[]),
		    display_stat(Bs,Param),
		    return(?INCONSISTENT,MR,Bs);
		0 ->
		    return(?DONE,MR,Bs);
		_ ->
		    conflict(Bs,Param,Level,MaxLearned,MR)
	    end;
	true ->
	    restart(Bs,Param,Level,MaxLearned,MR)
    end.

restart(Bs,Param,Level,MaxLearned,MR) ->
    RestartByTimeout = restart_by_timeout(Bs, Param), %% also restart!!
    RestartByCount = restart_by_counter(Bs, Param),
    case need_purge(Bs, Param, MaxLearned) of
	true ->
	    undo_until(Bs, Level, ?TOP_LEVEL),
	    varp_formula:proof_output(Bs,$c,"purge"),
	    ?dbg1("purge\n",[]),
	    varp_formula:del_unused_clauses(Bs),
	    MaxLearned1 = max_learned_inc(Bs, Param, MaxLearned),
	    _KeepSize = keep_size(Bs, Param, MaxLearned1),
	    init(Bs, Param, MaxLearned1, MR);
	false ->
	    if RestartByCount ->
		    varp_formula:proof_output(Bs,$c,"counter limit"),
		    undo_until(Bs, Level, ?TOP_LEVEL),
		    %% reorder(Bs, Param),
		    init(Bs, Param, MaxLearned, MR);
	       RestartByTimeout ->
		    varp_formula:proof_output(Bs,$c,"timeout"),
		    undo_until(Bs, Level, ?TOP_LEVEL),
		    %% reorder(Bs, Param),
		    init(Bs, Param, MaxLearned, MR);
	       true ->
		    timeout_or_cancel(Bs,Param,MaxLearned,MR)
	    end
    end.

reorder(Bs, Param) ->
    N = counters:get(Bs#bs.counters,?COUNTER_REORDER_COUNTER),
    counters:add(Bs#bs.counters,?COUNTER_REORDER_COUNTER, 1),
    ReorderMap = maps:from_list(maps:get(reorder,Param)),
    case maps:find(N rem maps:size(ReorderMap), ReorderMap) of
	{ok,{order,Opts}} ->
	    ?dbg1("Reorder: ~p\n", [Opts]),
	    Seed = proplists:get_value(seed, Opts, -1),
	    case proplists:get_value(sort, Opts, []) of
		[] -> ok;
		[Key1] ->
		    varp_formula:order_sort(Bs,Key1,?ORDER_UNDEFINED,Seed);
		[Key1,Key2] ->
		    varp_formula:order_sort(Bs,Key1,Key2,Seed)
	    end;
	{ok,{saturate,Opts}} ->
	    Laps = proplists:get_value(laps,Opts,0),
	    Timeout = proplists:get_value(timeout,Opts,infinity),
	    varp_saturate:saturate(Bs,1,Timeout,{{Laps},{Laps}}, 0);
	_ ->
	    Seed = varp_formula:getopt(Bs,seed),
	    varp_formula:order_sort(Bs,?ORDER_RANDOM,?ORDER_UNDEFINED,Seed)
    end.


return(What, MR, Bs) ->
    case MR#m.method of
	collect ->
	    {What,MR#m.ms,Bs};
	count ->
	    {What,MR#m.n,Bs}
    end.

need_purge(Bs, _Param, MaxLearned) ->
    case varc:clauseset_offset(Bs#bs.vp, ?GAMMA) > 0 of
	true ->
	    Learned = varc:clauseset_size(Bs#bs.vp, ?GAMMA),
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
	    Bound0 = varc:get_number_of_bindings(Bs#bs.vp, 0),
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
	    BcpCounter = varp_formula:info(Bs, bcp_counter),
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

%% simulated bcp - test
nbcp(V) ->
    nbcp_(V, varc:info(V, level)).

nbcp_(V, Level) ->
    case varc:bcp(V) of
	true ->
	    case varc:next_unbound(V) of
		false -> true;  %% model
		Xj ->
		    NextLevel = Level+1,
		    varc:set_level(V, NextLevel),
		    varc:decide(V, Xj),
		    nbcp_(V, NextLevel)
	    end;
	false ->
	    false
    end.


undo_until(Bs, NewLevel) ->
    Level = varc:info(Bs#bs.vp, level),
    undo_until(Bs, Level, NewLevel).

undo_until(Bs, Level, NewLevel) when Level > NewLevel ->
    varc:undo_level(Bs#bs.vp, Level),
    undo_until(Bs, Level-1, NewLevel);
undo_until(Bs, Level, Level) ->
    varc:set_level(Bs#bs.vp, Level),
    Bs.

%% J2 is backjump level, J3 is backstumble level
%% D2 is level to backjump delta, D3 is backjump to two free literal level
%% L min stumble limit, K is factor bwteen D1 and D2
do_jump(Bs,L,K,M,D1,D2,J2,J3) ->
    if  M, L > 0, D2 >= L, K > 0, D2 > 0, D1 >= K*D2 ->
	    counters:add(Bs#bs.counters, ?COUNTER_STUMBLE_OLLE_COUNT, 1),
	    J3;

	L > 0, D2 >= L -> 
	    counters:add(Bs#bs.counters, 
			 ?COUNTER_STUMBLE_COUNT, 1),
	    J3;
	K > 0, D2 > 0, D1 >= K*D2 ->
	    counters:add(Bs#bs.counters,
			 ?COUNTER_OLLE_COUNT, 1),
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
    varc:clauseset_offset(Bs#bs.vp, ?GAMMA, KeepSize),  %% sets gamma offset
    case maps:get(display, Param) of
	true ->
	    io:format("keep: KeepSize=~w, MaxLearned=~w, KeepFactor=~w, MinKeep=~w\n",
		      [KeepSize, MaxLearned, KeepFactor, MinKeep]);
	false -> ok
    end,
    KeepSize.

max_learned(Bs,Param) ->
    Permanent = varc:clauseset_size(Bs#bs.vp, ?DELTA),
    MaxLearnedClauses = maps:get(max_learned,Param),
    MaxLearnedFactor = maps:get(max_learned_factor,Param),
    case maps:get(display, Param) of
	true ->    
	    io:format("learned: Permanent=~w,MaxLearnedClause=~w,MaxLearnedFactor=~w\n",
		      [Permanent, MaxLearnedClauses, MaxLearnedFactor]);
	false ->
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
	true ->
	    io:format("num conflict clauses added: ~w\n", 
		      [counters:get(Bs#bs.counters, ?COUNTER_CONFLICT_CLAUSES)]),
	    io:format("num conflict ilterals: ~w\n",
		      [counters:get(Bs#bs.counters, ?COUNTER_CONFLICT_LITERALS)]),
	    io:format("num literals removed: ~w\n",
		      [counters:get(Bs#bs.counters, ?COUNTER_MINIMIZE_COUNT)]),
	    io:format("compression saved bits: ~w\n",
		      [counters:get(Bs#bs.counters, ?COUNTER_COMPRESS_CLAUSES)]),
	    io:format("usage stumble counter: ~w\n",
		      [counters:get(Bs#bs.counters, ?COUNTER_STUMBLE_COUNT)]),
	    io:format("usage olle counter: ~w\n",
		      [counters:get(Bs#bs.counters, ?COUNTER_OLLE_COUNT)]),
	    io:format("number of reorders: ~w\n",
		      [counters:get(Bs#bs.counters, ?COUNTER_REORDER_COUNTER)]),

	    %% delta usage histograms
	    %% back jump distances
	    io:format("Backjump deltas used\n", []),
	    lists:foreach(fun(D) ->
				  case {counters:get(Bs#bs.d1, D+1),
					counters:get(Bs#bs.d2, D+1)} of
				      {0,0} -> ok;
				      {N,M} -> 
					  io:format("~w: d1=~w, d2=~w\n", [D,N,M])
				  end
			  end, lists:seq(0,1023)),
	    io:format("Conflict clauses installed\n", []),
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
			  end, lists:seq(1,1024)),
	    ok;
	false ->
	    ok
    end.
