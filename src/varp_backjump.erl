%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2018, Tony Rogvall
%%% @doc
%%%    Implement the main loop with backjump
%%% @end
%%% Created : 23 Apr 2018 by Tony Rogvall <tony@rogvall.se>

-module(varp_backjump).

-export([run/2]).
-export([options/0]).

-export([minimize/2]).
%% -define(DEBUG, true).
-include("varp.hrl").

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
	default => 0,
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
	default => 0,
	description => "max number of conflicts to generate per conflict"},

     #{ long => "num-conflicts",
	key => num_conflicts,
	spec =>  unsigned,
	default => 1,
	description => "number of conflicts to analyse"},

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
	description => "Number of counts/eval until restart"},

     #{ long => "restart-interval",
	key => restart_interval,
	spec =>  unsigned,
	default => 0,
	description => "Restart interval in milliseconds"},

     #{ long => "display",
	short => "d",
	key => display,
	spec => {enum,[?BOOL]},
	default => false,
	description => "Display statistics."
      }
    ].
     

run(Bs, Param) when is_record(Bs, bs), is_map(Param) ->
    varp_formula:config(Bs, max_conflicting, 0),
    varp_formula:config(Bs, permanent, 0),
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
    Permanent = varp_formula:info(Bs, permanent),
    varp_formula:config(Bs, keep, KeepSize),

    case maps:get(display, Param) of
	true ->
	    io:format("Permanent=~w, KeepSize=~w, MaxLearned=~w, KeepFactor=~w, MinKeep=~w\n",
		      [Permanent, KeepSize, MaxLearned, KeepFactor, MinKeep]);
	false -> ok
    end,

    case maps:get(restart_counter,Param) of
	0 -> ok;
	_ ->
	    EvalCounter = varp_formula:info(Bs, eval_counter),
	    counters:put(Bs#bs.counters,?COUNTER_EVAL_COUNTER, EvalCounter)
    end,
    case maps:get(restart_interval,Param) of
	0 -> ok;
	RestartInterval ->
	    erlang:start_timer(RestartInterval, self(), restart)
    end,
    Bs1 = varp:set_local_timeout(Bs, Timeout),
    init(Bs1, Param, MaxLearned).

init(Bs, Param, MaxLearned) ->
    loop(Bs,Param,?TOP_LEVEL,MaxLearned,varp_formula:first_init(Bs),[]).

loop(Bs,Param,Level,MaxLearned,I,Stack) ->
    case varp_formula:eval(Bs) of
	false ->
	    if Level =:= 0 ->
		    varp_formula:proof_output(Bs,$a,[]),
		    display_stat(Bs,Param),
		    {?INCONSISTENT,[],Bs};
	       true ->
		    contradiction(Bs,Param,Level,MaxLearned,I,Stack)
	    end;
	true ->
	    next(Bs,Param,Level,MaxLearned,I,Stack)
    end.

contradiction(Bs,Param,Level,MaxLearned,_I,Stack) ->
    ClauseList0 = conflict_analysis(Bs,Param,Level),
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
				  [implication_level(Bs,Q)||Q <- Clause]) of
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

    LClauseList7 = case maps:get(max_conflicts,Param) of
		       0 -> 
			   LClauseList6;
		       1 ->
			   [];
		       MaxC ->
			   lists:sublist(LClauseList6, MaxC-1)
		   end,

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

    ?dbg(" level=~w, jlevel=~w\n", [Level,JLevel]),

    ?dcall(fun() -> io:format("stack[~w]: ", [Level]),
		    display_stack_ln(Bs, Stack),
		    io:format("\n", [])
	   end),
    ?dbg("undo[~w]: ~w\n", [Level, JLevel+1]),
    undo_until(Bs, Level, JLevel),  %% undo until JLevel
    varp_formula:set_level(Bs, JLevel),
    {INext,Stack1} = pop_until(Bs,Stack,JLevel),
    ?dcall(fun() -> io:format("stack[~w]: ", [JLevel]),
		    display_stack_ln(Bs, Stack1),
		    io:format("\n", [])
	   end),

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

    Learned0 = varp_formula:info(Bs2, number_of_learned_clauses),
    NewLearnedClauses = length(LClauseList7) +
	if JClause =:= undefined -> 0; true -> 1 end,
    Learned = Learned0 + NewLearnedClauses,
    DoPurge = varp_formula:info(Bs2, keep) > 0,

    DoRestartCount =
	case maps:get(restart_counter,Param) of
	    0 -> false;
	    RestartCounter ->
		EvalCounter = varp_formula:info(Bs, eval_counter),
		PrevCounter = counters:get(Bs#bs.counters,
					   ?COUNTER_EVAL_COUNTER),
		if (EvalCounter - PrevCounter) >= RestartCounter ->
			counters:put(Bs#bs.counters,?COUNTER_EVAL_COUNTER,
				     EvalCounter),
			true;
		   true ->
			false
		end
	end,
    DoRestartTime = 
	receive 
	    {timeout,_Timer,restart} ->
		RestartInterval = maps:get(restart_interval,Param),
		erlang:start_timer(RestartInterval, self(), restart),
		true
	after 0 ->
		false
	end,

    DoRestart = DoRestartCount orelse DoRestartTime,

    {DoStop,StopReason} 
	= case varp:is_timeout_or_was_canceled(Bs) of
	      false -> {false, none};
	      YY -> YY
	  end,

    if DoStop ->
	    undo_until(Bs, Level, ?TOP_LEVEL),
	    {StopReason,0,Bs};
       DoPurge, JLevel =:= ?TOP_LEVEL ->
	    if Learned > MaxLearned ->
		    varp_formula:del_unused_clauses(Bs),
		    reorder(Bs);
	       true ->
		    %% but we can re-order literals?
		    ok
	    end,
	    Learned1 = varp_formula:info(Bs2, number_of_learned_clauses),
	    NU = varp_formula:number_of_unbound(Bs2),
	    io:format("UNIT-RESTART Learned=~w,MaxLearned=~w,NewLearned=~w,Unbound=~w!\n", 
		      [Learned, MaxLearned,Learned1,NU]),
	    %%
	    init(Bs,Param,MaxLearned);
       DoPurge, Learned > MaxLearned ->
	    %% restart and purge!

	    undo_until(Bs, Level, ?TOP_LEVEL),
	    varp_formula:set_level(Bs, ?TOP_LEVEL),
	    %% {INext1,[]} = backjump(Bs2,Stack1,?TOP_LEVEL),
	    varp_formula:del_unused_clauses(Bs),
	    Learned1 = varp_formula:info(Bs2, number_of_learned_clauses),
	    io:format("RESTART Learned=~w,MaxLearned=~w,NewLearned=~w\n", 
		      [Learned, MaxLearned,Learned1]),
	    reorder(Bs),
	    init(Bs,Param,MaxLearned);
       DoRestart ->
	    io:format("RESTART Count=~w, Time=~w\n", 
		      [DoRestartCount, DoRestartTime]),
	    undo_until(Bs, Level, ?TOP_LEVEL),
	    varp_formula:set_level(Bs, ?TOP_LEVEL),
	    reorder(Bs),
	    init(Bs,Param, MaxLearned);
       true ->
	    loop(Bs2,Param,JLevel,MaxLearned,INext,Stack1)
    end.

reorder(Bs) ->
    N = counters:get(Bs#bs.counters,?COUNTER_REORDER_COUNTER),
    counters:add(Bs#bs.counters,?COUNTER_REORDER_COUNTER, 1),
    case N rem 2 of
	0 ->
	    io:format("degree\n"),
	    varp_formula:order_sort(Bs,'-degree',undefined,-1);
	1 ->
	    io:format("random\n"),
	    Seed = varp_formula:getopt(Bs,seed),
	    varp_formula:order_sort(Bs,random,undefined,Seed);
	2 ->
	    %% enable when 2-klauses works again
	    io:format("saturate\n"),
	    varp_saturate:saturate(Bs, 1, infinity, {{1},{1}}, 0)
    end.


undo_until(Bs, Level, NewLevel) when Level > NewLevel ->
    ?dbg("undo: ~w\n", [Level]),
    varp_formula:undo_level(Bs, Level),
    undo_until(Bs, Level-1, NewLevel);
undo_until(Bs, Level, Level) ->
    Bs.

pop_until(Bs,[{_,_Xk,Level}|Stack],JLevel) when Level > JLevel ->
    pop_until(Bs,Stack,JLevel);
pop_until(_Bs,Stack=[{K,_Xk,Level}|_],JLevel) when Level =:= JLevel ->
    ?dbg("backjump[~w]: ~s\n", [JLevel, format_lit(_Bs,_Xk)]),
    {K,Stack};
pop_until(Bs,[],_JLevel) ->
    {varp_formula:first_init(Bs), []}.

next(Bs,Param,Level,MaxLearned,I,Stack) ->
    case varp_formula:next_unbound(Bs,I) of
	false ->
	    Model = varp:output_model(Bs, 1),
	    display_stat(Bs,Param),
	    case varp_formula:getopt(Bs,method) of
		collect ->
		    {?CONTINUE,[Model],Bs};
		count ->
		    {?CONTINUE,1,Bs}
	    end;
	{J,Xj} ->
	    NextLevel = Level+1,
	    varp_formula:set_level(Bs,NextLevel),
	    true = varp_formula:bind(Bs,Xj),
	    ?dbg("decision@~w = ~s\n", [NextLevel,format_lit(Bs,Xj)]),
	    loop(Bs,Param,NextLevel,MaxLearned,J,[{J,Xj,NextLevel}|Stack])
    end.

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
    Permanent = varp_formula:info(Bs, permanent),
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
    true = varp_formula:bind(Bs,L,?TOP_LEVEL),
    varp_formula:proof_output(Bs,$a,Clause),
    Bs;
add_conflict_clause(Bs,Clause) ->
    ?dbg("conflict clause: ~s\n", [format_clause(Bs, Clause)]),
    Max = varp_formula:info(Bs, max_clause_length),
    L = length(Clause),
    if L >= Max ->
	    L2 = L div 2,
	    {CL1,CL2} = lists:split(L2, Clause),
	    Vi = varp_formula:add_variable(Bs),
	    Bs1 = varp_formula:set_var({p,'#',[Vi]}, Vi, Bs),
	    Bs2 = add_conflict_clause(Bs1,[Vi|CL1]),
	    add_conflict_clause(Bs2,[-Vi|CL2]);
       true ->
	    ClauseIndex = varp_formula:add_clause(Bs, Clause),
	    counters:add(Bs#bs.counters, ?COUNTER_CONFLICT_CLAUSES,1),
	    counters:add(Bs#bs.counters, ?COUNTER_CONFLICT_LITERALS,
			 length(Clause)),
	    varp_formula:proof_output(Bs,$a,ClauseIndex),
	    Bs
    end.

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
    case implication_clause(Bs, -Li) of
	-1 ->
	    minimize_(Bs, Ls, Clause, [Li|NewClause], Removed, Length+1);
	I ->
	    A = get_clause(Bs,I),
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

conflict_analysis(Bs,Param,Level) ->
    Trail= [P|_] = get_literal_bindings(Bs,Level),
    ?dbg("trail: ~s\n", [format_literals(Bs,Trail)]),
    Seen0 = #{ abs(P) => true }, %% a set of traversed literals
    N = varp_formula:info(Bs, number_of_conflicting_clauses),
    CList = [ {I,varp_formula:conflicting_clause(Bs,I)} || 
		I <- lists:seq(0, N-1)],
    M = maps:get(num_conflicts,Param),
    L = if M =:= 0 -> N;
	   true -> min(M, N)
	end,
    [ begin
	  Ri = conflicting_reason(Bs,-P,I),
	  varp_formula:use_clause(Bs, I),
	  ?dbg("reason[~w] cix=~w: ~s,~s\n", 
	       [I,_Cix,format_lit(Bs,-P),
		format_literals(Bs,Ri)]),
	  conflict_reason(Bs,Ri,Trail,Level,Seen0,1,[])
      end || {I,_Cix} <- lists:sublist(CList, L)].

conflict_reason(Bs,[Q|Qs],Trail,Level,Seen,C,CL) ->
    AbsQ = abs(Q),
    case Seen of
	#{ AbsQ := true } ->
	    conflict_reason(Bs,Qs,Trail,Level,Seen,C,CL);
	_ ->
	    Seen1 = Seen# { AbsQ => true },
	    QLevel = implication_level(Bs,Q),
	    if QLevel =:= Level ->
		    conflict_reason(Bs,Qs,Trail,Level,Seen1,C+1,CL);
	       QLevel =< ?TOP_LEVEL -> %% filter constants
		    conflict_reason(Bs,Qs,Trail,Level,Seen1,C,CL);
	       true ->
		    conflict_reason(Bs,Qs,Trail,Level,Seen1,C,[Q|CL])
	    end
    end;
conflict_reason(Bs,[],Trail,Level,Seen,C,CL) ->
    conflict_seen(Bs,Trail,Level,Seen,C,CL).

conflict_seen(Bs,[P|Trail],Level,Seen,C,CL) ->
    AbsP = abs(P),
    case Seen of
	#{ AbsP := true } ->
	    if  C =< 1, CL =:= [] ->
		    [-P];
		C =< 1 ->
		    [-P|CL];
		true ->
		    conflict_reason(Bs,reason(Bs,P),Trail,Level,Seen,C-1,CL)
	    end;
	_ ->
	    conflict_seen(Bs,Trail,Level,Seen,C,CL)
    end.

reason(Bs,P) ->
    case implication_clause(Bs,P) of
	-1 -> [];
	I -> get_clause(Bs,I) -- [P]
    end.

conflicting_reason(Bs,P,I) ->
    case varp_formula:conflicting_clause(Bs,I) of
	-1 -> [];
	Ci -> get_clause(Bs,Ci) -- [P]
    end.

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

implication_clause(Bs,Li) ->
    {Cix,_,_} = varp_formula:implication_clause(Bs,Li),
    Cix.

implication_level(Bs,Li) ->
    {_,_,Lev} = varp_formula:implication_clause(Bs,Li),
    Lev.

get_clause(Bs, I) ->
    varp_formula:get_clause(Bs,I).

%% -1 - 1 => 0 1
neg01(Val) -> (Val+1) div 2. 
    
val(Xi) when Xi < 0 -> 0;
val(Xi) when Xi > 0 -> 1.

format_bindings(Bs) ->
    format_bindings(Bs,all).

format_bindings(Bs,Level) ->
    Bnd = lists:map(
	    fun(L) ->
		    {Cix,_,ImpLev} = varp_formula:implication_clause(Bs,L),
		    {ImpLev,L,Cix}
	    end, varp_formula:get_bindings(Bs,0)),
    lists:foreach(
      fun(G) ->
	      [{_Lev,_,_}|_] = G,
	      if Level =:= all; Level =:= _Lev ->
		      ?dbg("bindings[~w]: ~s\n",[_Lev,format_group(Bs,G)]);
		 true ->
		      ok
	      end
      end, key_group_list(1,Bnd)).

format_group(Bs,[{_,L,Cix}|G]) ->
    case Cix of
	-1 ->
	    [ [format_binding(Bs,L)," "] | format_group(Bs,G)];
	_ ->
	    [ [format_binding(Bs,L),":",integer_to_list(Cix)," "] |
	      format_group(Bs,G)]
    end;
format_group(_Bs,[]) ->
    [].

%% generate a list of key groups	      
key_group_list(Pos,L) ->
    case lists:keysort(Pos,L) of
	[] -> [];
	[H|T] -> key_group_list(Pos,[H],[],T)
    end.

key_group_list(Pos,Acc=[A|_],Gs,[H|T]) when 
      element(Pos,A) =:= element(Pos,H) ->
    key_group_list(Pos,[H|Acc],Gs,T);
key_group_list(Pos,Acc,Gs,[H|T]) ->
    key_group_list(Pos,[H],[lists:reverse(Acc)|Gs],T);
key_group_list(_Pos,Acc,Gs,[]) ->
    lists:reverse([lists:reverse(Acc)|Gs]).

format_binding(Bs,L) ->
    [format_var(Bs,abs(L)),"=",
     if L < 0 -> "0";
	L > 0 -> "1"
     end].

get_literal_bindings(Bs,Level) ->
    lists:reverse(varp_formula:get_bindings(Bs,Level)).

get_literal_implications(Bs, Level) ->
    case varp_formula:get_bindings(Bs,Level) of
	[] -> [];
	[_|L] -> L
    end.

display_stack_ln(Bs,[{K,Xk,Level}|Stack]) ->
    io:format("~s@~w/~w ", [format_lit(Bs,Xk), Level, K]),
    display_stack_ln(Bs, Stack);
display_stack_ln(_Bs,[]) ->
    ok.
