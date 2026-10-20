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
-export([restart_steps/1]).

%% -define(DEBUG, true).
-include("varp.hrl").

-define(CHECK_INTERVAL, 1000).  %% 1000ms 

%% -compile(export_all).

%% a restart strategy is a chain of plugin steps (see restart_steps)
-define(RESTART_NONE, "").

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

     #{ long => "restart",
	key => restart,
	spec => string,
	default => ?RESTART_NONE,
	description => "Restart strategy: plugin steps with their options, "
		       "separated by |, run at level 0 one per restart in "
		       "turn (skip: a plain restart). "
		       "\"order --sort rank,random | saturate -k 1 -l 1 | skip\""},

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

     %% internal option: the step the first restart takes (a clone in
     %% varp_parallel starts at its own number, so the clones differ)
     #{ key => restart_offset,
	spec => unsigned,
	default => 0,
	description => "First restart step"}
    ].
     
-record(m,
	{
	 method,  %% collect or count
	 max,     %% max number to collect/count
	 n  = 0,
	 ms = []
	}).
	 
run(Bs, Param0) when is_record(Bs, bs), is_map(Param0) ->
    ?dbg0("~w: bj cube=~w\n", [self(), maps:get(assume, Param0, [])]),
    case restart_steps(maps:get(restart, Param0, ?RESTART_NONE)) of
	{error, Reason} ->
	    io:format("backjump: --restart: ~s\n", [Reason]),
	    {?ERROR, [], Bs};
	Steps ->
	    ?dbg0("restart_steps = ~p\n", [Steps]),
	    run_(Bs, Param0#{restart_steps => Steps})
    end.

run_(Bs, Param) ->
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
    case assume(Bs, Param) of
	true -> timeout_or_cancel(Bs, Param, MaxLearned, MR);
	false -> assumptions_failed(Bs, Param, MR)
    end.

%% Assumptions (used by bmc): literals decided on levels of their own
%% before the search proper, and again after every jump below them.
%% A learned clause never depends on them, so the clause database can
%% be reused with other assumptions afterwards.
assume(Bs, Param) ->
    assume_(Bs#bs.vp, maps:get(assume, Param, [])).

assume_(_Vp, []) ->
    true;
assume_(Vp, [L|Ls]) ->
    case varp_nif:value(Vp, L) of
	true -> assume_(Vp, Ls);
	false -> false;
	undefined ->
	    case varp_nif:assume(Vp, L) andalso varp_nif:bcp(Vp) of
		true -> assume_(Vp, Ls);
		false -> false
	    end
    end.

%% no (more) models under the assumptions: the formula itself may
%% have some, so this is DONE, not INCONSISTENT, which is reserved for
%% a contradiction at level 0 (the formula has no models at all; after
%% that the instance is spent, a cube search must not go on in it)
assumptions_failed(Bs, Param, MR) ->
    varp_nif:pop(Bs#bs.vp, ?TOP_LEVEL),
    display_stat(Bs, Param),
    case {MR#m.n, maps:get(assume, Param, [])} of
	{0, []} -> return(?INCONSISTENT, MR, Bs);
	_ -> return(?DONE, MR, Bs)
    end.

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
		    varp_circuit:clause(Bs#bs.vp, Block, ?DELTA),
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
	    move_to_gamma(Bs, Param, LClauses2),
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
	    move_to_gamma(Bs,Param,ALen,Aix),
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
	    move_to_gamma(Bs, Param, LClauses5),
	    %% install the conflict clause
	    move_to_gamma(Bs,Param,ALen,Aix),
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
move_to_gamma(Bs, Param, [{Len,Count,Aix}|LCs]) ->
    minimize_count(Bs, Count),
    move_to_gamma(Bs, Param, Len, Aix),
    move_to_gamma(Bs, Param, LCs);
move_to_gamma(_Bs, _Param, []) ->
    ok.

move_to_gamma(Bs, _Param, 1, Aix) ->
    varp_formula:proof_output(Bs,$a,Aix),
    true = varp_nif:move_clause(Bs#bs.vp, Aix, gamma),
    counters:add(Bs#bs.clen, 1, 1);
move_to_gamma(Bs, Param, Len, Aix) ->
    {true,Gix} = varp_nif:move_clause(Bs#bs.vp, Aix, gamma),
    varp_formula:proof_output(Bs,$a,Gix),
    export_clause(Bs, Param, Len, Gix),
    counters:add(Bs#bs.counters, ?COUNTER_CONFLICT_CLAUSES, 1),
    counters:add(Bs#bs.counters, ?COUNTER_CONFLICT_LITERALS, Len),
    if Len >= 1023 ->
	    counters:add(Bs#bs.clen, 1024, 1);
       true ->
	    counters:add(Bs#bs.clen, Len, 1)
    end.

%% a short learned clause goes to the other instances through the
%% export fun in Param (varp_parallel); a unit is a fact and goes
%% through the facts (bcp reports it at level 0)
export_clause(Bs, Param, Len, Gix) ->
    case maps:get(export, Param, undefined) of
	undefined ->
	    ok;
	Export when Len =< map_get(share_len, Param) ->
	    Export(varp_nif:get_clause(Bs#bs.vp, Gix));
	_ ->
	    ok
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
	    case assume(Bs, Param) of
		true -> restart(Bs,Param,MaxLearned,MR);
		false -> assumptions_failed(Bs, Param, MR)
	    end
    end.

%% facts (permanent bindings) found elsewhere, handed over by an
%% import fun in Param (varp_parallel): they go in at level 0, which
%% is a restart; a fact that is false here means the formula has no
%% models at all
restart(Bs,Param,MaxLearned,MR) ->
    case import(Bs, Param) of
	ok ->
	    restart_(Bs,Param,MaxLearned,MR);
	false ->
	    varp_nif:pop(Bs#bs.vp, ?TOP_LEVEL),
	    display_stat(Bs,Param),
	    case MR#m.n of
		0 -> return(?INCONSISTENT, MR, Bs);
		_ -> return(?DONE, MR, Bs)
	    end
    end.

import(Bs, Param) ->
    case import_facts(Bs, Param) of
	ok -> import_clauses(Bs, Param);
	false -> false
    end.

import_facts(Bs, Param) ->
    case maps:get(import, Param, undefined) of
	undefined -> ok;
	Import ->
	    case Import() of
		[] -> ok;
		Facts ->
		    varp_nif:pop(Bs#bs.vp, ?TOP_LEVEL),
		    varp_formula:proof_output(Bs,$c,"import"),
		    %% literals and substitutions (the latter become
		    %% clauses here, the cross reference is off)
		    case varp:import_facts(Bs#bs.vp, Facts) of
			true -> ok;
			false -> false
		    end
	    end
    end.

%% short clauses learned elsewhere, the same way (varp:import_clauses
%% puts them in gamma, where the purge treats them as the own ones)
import_clauses(Bs, Param) ->
    case maps:get(import_clauses, Param, undefined) of
	undefined -> ok;
	Import ->
	    case Import() of
		[] -> ok;
		Clauses ->
		    varp_nif:pop(Bs#bs.vp, ?TOP_LEVEL),
		    varp_formula:proof_output(Bs,$c,"import clauses"),
		    case varp:import_clauses(Bs#bs.vp, Clauses) of
			true -> ok;
			false -> false
		    end
	    end
    end.

%% a restart (the learned clauses over the limit, the bcp counter or
%% the timer) pops to level 0, and the next step of the restart
%% strategy runs there before the search starts over
restart_(Bs,Param,MaxLearned,MR) ->
    RestartByTimeout = restart_by_timeout(Bs, Param), %% also restart!!
    RestartByCount = restart_by_counter(Bs, Param),
    Purge = need_purge(Bs, Param, MaxLearned),
    if Purge; RestartByCount; RestartByTimeout ->
	    varp_nif:pop(Bs#bs.vp, ?TOP_LEVEL),
	    MaxLearned1 =
		case Purge of
		    true ->
			varp_formula:proof_output(Bs,$c,"purge"),
			?dbg0("purge\n",[]),
			varp_formula:del_unused_clauses(Bs),
			MaxLearned2 = max_learned_inc(Bs, Param, MaxLearned),
			_KeepSize = keep_size(Bs, Param, MaxLearned2),
			MaxLearned2;
		    false when RestartByCount ->
			varp_formula:proof_output(Bs,$c,"counter limit"),
			MaxLearned;
		    false ->
			varp_formula:proof_output(Bs,$c,"timeout"),
			MaxLearned
		end,
	    case restart_step(Bs, Param) of
		ok ->
		    init(Bs, Param, MaxLearned1, MR);
		?INCONSISTENT ->
		    %% the step found the formula contradictory at level 0
		    display_stat(Bs, Param),
		    case MR#m.n of
			0 -> return(?INCONSISTENT, MR, Bs);
			_ -> return(?DONE, MR, Bs)
		    end;
		What ->
		    return(What, MR, Bs)
	    end;
       true ->
	    timeout_or_cancel(Bs,Param,MaxLearned,MR)
    end.

%% --restart "step | step | ...": each step is a plugin with its
%% options, as on the command line, parsed once here. skip is a plain
%% restart. The steps are taken in turn, one per restart.
restart_steps("") ->
    [];
restart_steps(String) ->
    _ = application:load(varp),  %% the plugin list is in the app env
    Plugins = varp:load_plugins(),
    try
	[restart_step_(string:lexemes(Step, " \t"), Plugins)
	 || Step <- string:split(String, "|", all)]
    catch
	throw:{error, _} = Error -> Error
    end.

restart_step_([], _Plugins) ->
    throw({error, "empty step"});
restart_step_(["skip"], _Plugins) ->
    skip;
restart_step_([Name|Args], Plugins) ->
    case maps:get(Name, Plugins, undefined) of
	undefined ->
	    throw({error, "unknown plugin " ++ Name});
	Mod ->
	    OptionInfoList = Mod:options(),
	    OptionSpec = maps:put('$plugin', Mod,
				  varp_option:options_spec(OptionInfoList)),
	    OptMap = varp_option:default_opts(OptionInfoList),
	    case varp_option:process_args(Args, OptionSpec, OptMap, []) of
		{[], StepParam, []} ->
		    {Mod, step_param(Mod, StepParam)};
		{Rest, _, Bound} ->
		    throw({error, "not an option of " ++ Name ++ ": " ++
			       lists:join(" ", Rest ++ [V || {V,_} <- Bound])})
	    end
    end.

%% what a step may not do inside a search: saturate reports no
%% models (the search finds them, and would count them twice) and
%% does not warn about the main variable
step_param(varp_saturate, Param) ->
    Param#{model => false, warn => false};
step_param(_Mod, Param) ->
    Param.

%% run the next step at level 0. The instance is what the step works
%% on; the state record it returns is dropped (a step's own timeout
%% must not become the search's). The cross reference and the
%% conflict limit are the search's own again afterwards. An order
%% step without a seed of its own gets a new one every time, or every
%% random order would be the same.
restart_step(Bs, Param) ->
    case maps:get(restart_steps, Param, []) of
	[] ->
	    ok;
	Steps ->
	    N = counters:get(Bs#bs.counters,?COUNTER_REORDER_COUNTER),
	    counters:add(Bs#bs.counters,?COUNTER_REORDER_COUNTER, 1),
	    I = (N + maps:get(restart_offset, Param, 0)) rem length(Steps),
	    case lists:nth(I+1, Steps) of
		skip ->
		    ok;
		_Step={Mod, StepParam0} ->
		    Vp = Bs#bs.vp,
		    varp_formula:proof_output(Bs,$c,"restart " ++ atom_to_list(Mod)),
		    StepParam = step_seed(Vp, StepParam0, N),
		    Xref = varp_nif:getopt(Vp, xref),
		    MaxConflicting = varp_nif:getopt(Vp, max_conflicting),
		    {Result, _Acc, _Bs1} = Mod:run(Bs, StepParam),
		    varp_nif:setopt(Vp, xref, Xref),
		    varp_nif:setopt(Vp, max_conflicting, MaxConflicting),
		    case Result of
			?INCONSISTENT -> ?INCONSISTENT;
			?CANCEL -> ?CANCEL;
			?TIMEOUT when _Bs1#bs.t_local =:= undefined -> ?TIMEOUT;
			_ -> ok
		    end
	    end
    end.

step_seed(Vp, Param = #{seed := -1}, N) ->
    Param#{seed => varp_nif:getopt(Vp, seed) + N};
step_seed(_Vp, Param, _N) ->
    Param.


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
