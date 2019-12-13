%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2018, Tony Rogvall
%%% @doc
%%%    Implement the main loop with backjump (new multi bcp version)
%%% @end
%%% Created : 23 Apr 2018 by Tony Rogvall <tony@rogvall.se>

-module(varp_nbackjump).

-export([run/2]).
-export([options/0]).

-export([minimize/2]).
%% -define(DEBUG, true).
-include("varp.hrl").

-define(CHECK_INTERVAL, 1000).  %% 1000ms 

-compile(export_all).
-import(varp_formula, [format_lit/2, format_lit/3]).
-import(varp_formula, [format_var/2]).
-import(varp_formula, [format_clause/2, format_clause/3]).
-import(varp_formula, [format_literals/2]).

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
	spec =>  float,
	default => 1.0,
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
	default => [],
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
    %% Calculate size of lru cache
    KeepFactor = maps:get(keep_factor, Param),
    MinKeep    = maps:get(min_keep_clauses, Param),
    KeepSize   = if MaxLearned =:= 0 ->
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
    Permanent = varc:clauseset_size(Bs#bs.vp, ?DELTA),
    %% io:format("permanent = |Delta| = ~w\n", [Permanent]),
    %% io:format("keep-size = ~w\n", [KeepSize]),
    %% io:format("max-learned = ~w\n", [MaxLearned]),
    varc:clauseset_offset(Bs#bs.vp, ?GAMMA, KeepSize),  %% sets gamma offset

    case maps:get(display, Param) of
	true ->
	    io:format("Permanent=~w, KeepSize=~w, MaxLearned=~w, KeepFactor=~w, MinKeep=~w\n",
		      [Permanent, KeepSize, MaxLearned, KeepFactor, MinKeep]);
	false -> ok
    end,

    case maps:get(restart_counter,Param) of
	0 -> ok;
	_ ->
	    BcpCounter = varp_formula:info(Bs, bcp_counter),
	    counters:put(Bs#bs.counters,?COUNTER_BJR_BCP_COUNTER, BcpCounter)
    end,
    case maps:get(restart_interval,Param) of
	infinity -> ok;
	RestartInterval ->
	    erlang:start_timer(trunc(1000*RestartInterval), self(), restart)
    end,
    Bs1 = varp:set_local_timeout(Bs, Timeout),
    M0  = #m { method = varp_formula:getopt(Bs1,method),
	       max = maps:get(max, Param) },
    init(Bs1, Param, MaxLearned, M0).

init(Bs, Param, MaxLearned, MR) ->
    varc:set_level(Bs#bs.vp, ?TOP_LEVEL),
    loop(Bs, Param, MaxLearned, MR).

loop(Bs, Param, MaxLearned, MR) ->
    case varp:check_timeout_or_cancel(Bs,?COUNTER_BJT_BCP_COUNTER,
				      ?CHECK_INTERVAL) of
	false ->
	    loop_(Bs, Param, MaxLearned, MR);
	{true, What} ->
	    undo_until(Bs, ?TOP_LEVEL),
	    return(What, MR, Bs)
    end.

loop_(Bs,Param,MaxLearned,MR) ->
    ?dbg("loop_: nbcp\n",[]),
    case varc:nbcp(Bs#bs.vp) of
	false ->  %% contradiction
	    Level = varc:info(Bs#bs.vp, level),
	    case Level of
		0 when MR#m.n =:= 0 ->
		    varp_formula:proof_output(Bs,$a,[]),
		    display_stat(Bs,Param),
		    return(?INCONSISTENT,MR,Bs);
		0 ->
		    return(?CONTINUE,MR,Bs);
		_ ->
		    contradiction(Bs,Param,Level,MaxLearned,MR)
	    end;
	true ->  %% model
	    N = MR#m.n + 1,
	    Model = varp:output_model(Bs, N),
	    Level = varc:info(Bs#bs.vp, level),
	    if N >= MR#m.max, MR#m.max > 0; Level =:= 0 -> %%?
		    display_stat(Bs,Param),
		    case MR#m.method of
			collect ->
			    {?CONTINUE,[Model|MR#m.ms],Bs};
			count ->
			    {?CONTINUE,N,Bs}
		    end;
	       true ->
		    Block = varp:block_clause(Bs),
		    %% FIXME: minimize Block clause and find
		    %% a working jump level (maybe just one up?)
		    undo_until(Bs, ?TOP_LEVEL),
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

return(What, MR, Bs) ->
    case MR#m.method of
	collect ->
	    {What,MR#m.ms,Bs};
	count ->
	    {What,MR#m.n,Bs}
    end.

contradiction(Bs,Param,Level,MaxLearned,MR) ->
    ClauseList0 = varp_conflict:analyze(Bs,Level,maps:get(bump,Param)),
    varc:decay(Bs#bs.vp, maps:get(decay,Param)),
    ClauseList1 = 
	case maps:get(minimize,Param) of
	    true ->
		lists:usort([ minimize(Bs,Clause) || Clause <- ClauseList0]);
	    false ->
		ClauseList0
	end,
    LClauseList1 = [{length(Clause),Clause} || Clause <- ClauseList1],

    LClauseList2 = lists:keysort(1, LClauseList1),
    
    %% 
    {LUnitClauseList, LClauseList3} =
	lists:splitwith(fun({L,_}) -> L =:= 1 end, LClauseList2),

    %% UnitClauses
    UnitClauses = lists:usort([Clause || {_,Clause} <- LUnitClauseList]),

    JClauseList1 =
	lists:map(
	  fun({L,Clause}) ->
		  case lists:sort(fun(A,B) -> A > B end,
				  [varc:implication_level(Bs#bs.vp,Q) ||
				      Q <- Clause]) of
		      [J1,J2,J3|_] ->
			  D1 = J1 - J2,
			  D2 = J2 - J3,
			  {L,D1,D2,J2,J3,Clause};
		      [J1,J2] ->
			  J3 = ?TOP_LEVEL,
			  D1 = J1 - J2,
			  D2 = J2 - J3,
			  {L,D1,D2,J2,J3,Clause}
		  end
	  end, LClauseList3),

    JClauseList2 =
	lists:sort(fun({La,D1a,_D2a,_J2a,_J3a,_Clausea},
		       {Lb,D1b,_D2b,_J2b,_J3b,_Clauseb}) ->
			   if D1a =:= D1b -> La < Lb;
			      true -> D1a > D1b
			   end
		   end, JClauseList1),

    {JClause,LClauseList4} =
	if UnitClauses =:= [] ->
		[JC | JCList3] = JClauseList2,
		{JC,[{L,Clause} || {L,_D1,_D2,_J2,_J3,Clause} <- JCList3]};
	   true ->
		{undefined,
		 [{L,Clause} || {L,_D1,_D2,_J2,_J3,Clause} <- JClauseList2]}
	end,

    LClauseList5 = lists:sort(fun({La,_},{Lb,_}) -> La < Lb end,
			      LClauseList4),

    LClauseList6 = 
	case maps:get(iorder,Param) of
	    0 -> 
		LClauseList5;
	    IOrder ->
		lists:takewhile(fun({La,_}) -> La =< IOrder end, 
				LClauseList5)
	end,

    %% LClauseList7 = case maps:get(max_conflicts,Param) of
    %% 		       0 -> 
    %% 			   LClauseList6;
    %% 		       1 ->
    %% 			   [];
    %% 		       MaxC ->
    %% 			   lists:sublist(LClauseList6, MaxC-1)
    %% 		   end,
    LClauseList7 = LClauseList6,

    L = maps:get(stumble,Param),
    K = maps:get(olle,Param),
    M = maps:get(stumble_olle,Param),

    JLevel =
	case JClause of
	    undefined -> ?TOP_LEVEL;
	    {_L,D1,D2,J2,J3,_} -> 
		do_stat(Bs,D1,D2),
		do_jump(Bs,L,K,M,D1,D2,J2,J3)
	end,

    undo_until(Bs, Level, JLevel),  %% undo until JLevel
    varc:set_level(Bs#bs.vp, JLevel),

    %% install unit clauses
    Bs0 = lists:foldl(
	    fun(Clause,Bsi) ->
		    do_clause_stat(Bsi, 1),
		    add_conflict_clause(Bsi,Clause)
	    end, Bs, UnitClauses),

    %% install length clauses
    Bs1 = lists:foldl(
	    fun({Len,Clause},Bsi) ->
		    do_clause_stat(Bsi, Len),
		    add_conflict_clause(Bsi,Clause)
	    end, Bs0, LClauseList7),
    
    Bs2 = case JClause of
	      undefined ->
		  Bs1;
	      {_Len,_D1,_D2,_J2,_J3,Clause} ->
		  do_clause_stat(Bs1, length(Clause)),
		  add_conflict_clause(Bs1,Clause)
	  end,

    Learned0 = varc:clauseset_size(Bs2#bs.vp, ?GAMMA),
    NewLearnedClauses = length(LClauseList7) +
	if JClause =:= undefined -> 0; true -> 1 end,
    Learned = Learned0 + NewLearnedClauses,
    DoPurge = varc:clauseset_offset(Bs2#bs.vp, ?GAMMA) > 0,

    DoRestartCount =
	case maps:get(restart_counter,Param) of
	    0 -> false;
	    RestartCounter ->
		EvalCounter = varp_formula:info(Bs2, bcp_counter),
		PrevCounter = counters:get(Bs2#bs.counters,
					   ?COUNTER_BJR_BCP_COUNTER),
		if (EvalCounter - PrevCounter) >= RestartCounter ->
			counters:put(Bs2#bs.counters,?COUNTER_BJR_BCP_COUNTER,
				     EvalCounter),
			true;
		   true ->
			false
		end
	end,
    %% FIXME: flush restart timer somewhere to avoid initial re-restart...
    %% FIXME: only run restart if no units has been found during the
    %%        restart_interval time, otherwise keep the order!
    DoRestartTime = 
	receive 
	    {timeout,_Timer,restart} ->
		RestartInterval = maps:get(restart_interval,Param),
		erlang:start_timer(trunc(1000*RestartInterval),self(),restart),
		true
	after 0 ->
		false
	end,

    DoRestart = DoRestartCount orelse DoRestartTime,

    if 
	DoPurge, JLevel =:= ?TOP_LEVEL ->
	    if Learned > MaxLearned ->
		    varp_formula:del_unused_clauses(Bs2),
		    reorder(Bs2, Param);
	       true ->
		    %% but we can re-order literals?
		    ok
	    end,
	    Learned1 = varp_formula:info(Bs2, number_of_learned_clauses),
	    NU = varp_formula:number_of_unbound(Bs2),
	    io:format("UNIT-RESTART Learned=~w,MaxLearned=~w,NewLearned=~w,Unbound=~w!\n", 
		      [Learned, MaxLearned,Learned1,NU]),
	    %%
	    init(Bs,Param,MaxLearned,MR);
       DoPurge, Learned > MaxLearned ->
	    %% restart and purge!

	    undo_until(Bs2, Level, ?TOP_LEVEL),
	    ?dbg("Set LEVEL ~w\n", [?TOP_LEVEL]),
	    varc:set_level(Bs2#bs.vp, ?TOP_LEVEL),
	    ?dbg("del_unused_clauses\n", []),
	    varp_formula:del_unused_clauses(Bs),
	    Learned1 = varp_formula:info(Bs2, number_of_learned_clauses),
	    io:format("RESTART Learned=~w,MaxLearned=~w,NewLearned=~w\n", 
		      [Learned, MaxLearned,Learned1]),
	    reorder(Bs2, Param),
	    init(Bs2,Param,MaxLearned,MR);
       DoRestart ->
	    io:format("RESTART Count=~w, Time=~w\n", 
		      [DoRestartCount, DoRestartTime]),
	    undo_until(Bs2, Level, ?TOP_LEVEL),
	    varc:set_level(Bs2#bs.vp, ?TOP_LEVEL),
	    reorder(Bs2, Param),
	    init(Bs2,Param,MaxLearned,MR);
       true ->
	    loop(Bs2,Param,MaxLearned,MR)
    end.

reorder(Bs, Param) ->
    N = counters:get(Bs#bs.counters,?COUNTER_REORDER_COUNTER),
    counters:add(Bs#bs.counters,?COUNTER_REORDER_COUNTER, 1),
    ReorderMap = maps:from_list(maps:get(reorder,Param)),
    case maps:find(N rem maps:size(ReorderMap), ReorderMap) of
	{ok,{order,Opts}} ->
	    io:format("Reorder: ~p\n", [Opts]),
	    Seed = proplists:get_value(seed, Opts, -1),
	    case proplists:get_value(sort, Opts, []) of
		[] -> ok;
		[Key1] ->
		    varp_formula:order_sort(Bs,Key1,?ORDER_UNDEFINED,Seed);
		[Key1,Key2] ->
		    varp_formula:order_sort(Bs,Key1,Key2,Seed)
	    end;
	{ok,{saturate,Opts}} ->
	    io:format("reorder: Saturate: ~p\n", [Opts]),
	    Laps = proplists:get_value(laps,Opts,0),
	    Timeout = proplists:get_value(timeout,Opts,infinity),
	    varp_saturate:saturate(Bs,1,Timeout,{{Laps},{Laps}}, 0);
	_ ->
	    io:format("reorder: Random\n"),
	    Seed = varp_formula:getopt(Bs,seed),
	    varp_formula:order_sort(Bs,?ORDER_RANDOM,?ORDER_UNDEFINED,Seed)
    end.

undo_until(Bs, NewLevel) ->
    Level = varc:info(Bs#bs.vp, level),
    undo_until(Bs, Level, NewLevel).

undo_until(Bs, Level, NewLevel) when Level > NewLevel ->
    ?dbg("undo: ~w\n", [Level]),
    varc:undo_level(Bs#bs.vp, Level),
    undo_until(Bs, Level-1, NewLevel);
undo_until(Bs, Level, Level) ->
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

do_clause_stat(Bs, Len) ->
    if Len >= 1023 ->
	    counters:add(Bs#bs.clen, 1024, 1);
       true ->
	    counters:add(Bs#bs.clen, Len, 1)
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

max_learned(Bs,Param) ->
    Permanent = varc:clauseset_size(Bs#bs.vp, ?DELTA),
    MaxLearnedClauses = maps:get(max_learned,Param),
    MaxLearnedFactor = maps:get(max_learned_factor,Param),
    case maps:get(display, Param) of
	true ->    
	    io:format("Permanent=~w,MaxLearnedClause=~w,MaxLearnedFactor=~w\n",
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
	    io:format("num ilterals removed: ~w\n",
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

add_conflict_clause(Bs,[]) ->
    Bs;
add_conflict_clause(Bs,Clause=[L]) ->
    ?dbg("conflict clause: ~s\n", [format_clause(Bs, Clause)]),
    true = varc:bind(Bs#bs.vp,L,?TOP_LEVEL),
    varp_formula:proof_output(Bs,$a,Clause),
    Bs;
add_conflict_clause(Bs,Clause) ->
    ?dbg("conflict clause: ~s\n", [format_clause(Bs, Clause)]),
    ClauseIndex = varp_formula:add_clause(Bs, Clause, ?GAMMA),
    counters:add(Bs#bs.counters, ?COUNTER_CONFLICT_CLAUSES,1),
    counters:add(Bs#bs.counters, ?COUNTER_CONFLICT_LITERALS,length(Clause)),
    varp_formula:proof_output(Bs,$a,ClauseIndex),
    Bs.

abs_sort(Clause) ->
    lists:sort(fun(A,B) -> abs(A) < abs(B) end, Clause).

compress(Bs,Param,Clause) ->
    case maps:get(compress,Param) of
	true ->
	    Len = length(Clause),
	    if Len > 2 ->
		    NBits = length(Clause)*32,  %% initial number of bits
		    DeltaCode = compress_(Clause),  %% abs deltas
		    NCompressed = 32 + 
			lists:sum([bit:size(Code)+1||Code<-DeltaCode]),
		    N = NBits - NCompressed,
		    io:format("compress, Clause=~w,delta=~w,NBits=~w,NCompressed=~w,N=~w\n", [Clause, DeltaCode, NBits, NCompressed, N]),
		    if N =< 0 ->
			    ok;
		       true ->
			    counters:add(Bs#bs.counters, ?COUNTER_COMPRESS_CLAUSES,N)
		    end,
		    Clause;
	       true ->
		    Clause
	    end;
	false ->
	    Clause
    end.

compress_([{L1,_}|Ls=[{L2,_}|_]]) -> [abs(L1)-abs(L2) | compress_(Ls)];
compress_([_Ln]) -> [].

minimize(_Bs,[]) -> [];
minimize(_Bs,Clause=[_]) -> Clause;
minimize(Bs,Clause0) ->
    Clause = sort_abs_clause(Clause0),
    %% io:format("minimize: ~p\n", [Clause]),
    case minimize_(Bs, Clause, Clause, [], 0, 0) of
	{0,_,_} -> 
	    %% io:format("  no change\n", []),
	    Clause;
	{NumRemoved,_InputClauseLength,Clause1} ->
	    counters:add(Bs#bs.counters, ?COUNTER_MINIMIZE_COUNT,
			 NumRemoved),
	    %% io:format("minimize: saved ~.2f%\n", [(NumRemoved / _InputClauseLength)*100]),
	    Clause1
    end.

minimize_(Bs, [Li|Ls], Clause, NewClause, Removed, Length) ->
    case varc:implication_clause(Bs#bs.vp, -Li) of
	-1 ->
	    minimize_(Bs, Ls, Clause, [Li|NewClause], Removed, Length+1);
	I ->
	    A = varc:get_clause(Bs#bs.vp,I),
	    %% io:format("implication clause of ~w = ~w, clause=~w\n", 
	    %%    [-Li, A, Clause]),
	    %% if A-{Li} is a subset of Clause then remove Li from clause
	    case is_subclause_abs(A, -Li, Clause) of
		true ->
		    minimize_(Bs, Ls, Clause, NewClause, Removed+1, Length+1);
		false ->
		    minimize_(Bs, Ls, Clause, [Li|NewClause], Removed, Length+1)
	    end
    end;
minimize_(_Bs, [], _Clause, NewClause, Removed, Length) ->
    {Removed,Length,lists:reverse(NewClause)}.

%% check if As is a subset of Bs
is_subclause(As, Li, Bs) ->
    case (As--[Li]) -- Bs of
	[] -> true;
	_ -> false
    end.

sort_abs_clause(Clause) ->
    lists:sort(
      fun(A,A) -> false;
	 (A,B) -> 
	      case abs(A) - abs(B) of
		  0 -> A < 0;
		  R -> R > 0
	      end
      end, Clause).

%% assume clauses are abs sorted in reversed order
is_subclause_abs([Li|As],Li,Bs) ->
    is_subclause_abs(As,Li,Bs);
is_subclause_abs([X|As],Li,[X|Bs]) ->
    is_subclause_abs(As,Li,Bs);
is_subclause_abs(As=[A|_As0],Li,[B|Bs]) ->
    if abs(A) < abs(B) ->
	    is_subclause_abs(As,Li,Bs);
       true ->
	    false
    end;
is_subclause_abs([],_Li,_Bs) ->
    true;
is_subclause_abs(_As,_Li,[]) ->
    false.
