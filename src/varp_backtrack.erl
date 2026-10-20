%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2017, Tony Rogvall
%%% @doc
%%%    Backtrack: chronological search, no learning, every model in
%%%    the order of the variables. Under assumptions (a cube) when
%%%    varp_parallel hands them over.
%%% @end
%%% Created : 22 Dec 2017 by Tony Rogvall <tony@rogvall.se>

-module(varp_backtrack).
-behaviour(varp_plugin).

-export([options/0]).
-export([run/2]).

%% -compile(export_all).

%% -define(DEBUG, true).
-include("varp.hrl").

-define(CHECK_INTERVAL, 1000).  %% 1000ms 

options() ->
    [#{ long  => "timeout",
	short => "t",
	key   => timeout,
	spec  => {union,[float,{enum,[{"infinity",infinity}]}]},
	default => infinity,
	description => "Max time to run backtrack in seconds"
      },
     #{ long => "max",
	short => "n",
	key => max,
	spec => unsigned,
	default => 1,
	description => "Max number of models to count or collect, 0=all."
      }
    ].

%% Param may carry assume: literals (a cube, from varp_parallel) that
%% the search runs under, on levels of their own below the decisions;
%% undo never flips them, so the search stays inside the cube
run(Bs, Param) when is_record(Bs, bs), is_map(Param) ->
    ?dbg0("~w: bt cube=~w\n", [self(), maps:get(assume, Param, [])]),
    N = maps:get(max, Param),
    Timeout = maps:get(timeout, Param, infinity),
    Vp = Bs#bs.vp,
    varp_nif:setopt(Vp, max_conflicting, 1),
    Bs1 = varp:set_local_timeout(Bs, Timeout),
    0 = varp_nif:level(Vp),
    put(proof_output, varp_nif:getopt(Vp, proof_output)),
    Method = varp_nif:getopt(Vp, method),
    case assume(Vp, maps:get(assume, Param, [])) of
	false ->
	    %% nothing under the assumptions
	    undo_all(Bs1),
	    case Method of
		collect -> {?DONE, [], Bs1};
		count -> {?DONE, 0, Bs1}
	    end;
	true ->
	    put(base_level, varp_nif:level(Vp)),
	    _ = varp_nif:push(Vp),
	    case Method of
		collect -> collect(Bs1, 0, N, []);
		count   -> count(Bs1, 0, N)
	    end
    end.

assume(_Vp, []) ->
    true;
assume(Vp, [L|Ls]) ->
    case varp_nif:value(Vp, L) of
	true -> assume(Vp, Ls);
	false -> false;
	undefined ->
	    case varp_nif:assume(Vp, L) andalso varp_nif:bcp(Vp) of
		true -> assume(Vp, Ls);
		false -> false
	    end
    end.

%% flip the latest decision, staying above the assumptions
undo(Bs) ->
    varp_nif:undo(Bs#bs.vp, get(base_level)).

%% nothing found at all: the formula has no models, or under
%% assumptions just the cube is empty, which is done, not inconsistent
exhausted(Bs, Acc) ->
    case get(base_level) of
	0 -> {?INCONSISTENT, Acc, Bs};
	_ -> {?DONE, Acc, Bs}
    end.

collect(Bs, Count, N, Acc) ->
    case varp:check_timeout_or_cancel(Bs,?COUNTER_BT_BCP_COUNTER,
				      ?CHECK_INTERVAL) of
	false ->
	    if N =:= 0; Count < N ->
		    collect_(Bs,Count,N,Acc);
	       true ->
		    undo_all(Bs),
		    {?CONTINUE,Acc,Bs}
	    end;
	{true, Why} ->
	    undo_all(Bs),
	    {Why,Acc,Bs}
    end.

collect_(Bs, Count, N, Acc) when N =:= 0; Count < N ->
    case varp_nif:nbcp(Bs#bs.vp) of
	true ->
	    %% io:format("model: ~p\n", [varp:get_all_bindings(Bs#bs.vp)]),
	    Model = varp:output_model(Bs,false,Count+1),
	    case undo(Bs) of
		true ->
		    collect(Bs, Count+1, N, [Model|Acc]);
		false ->
		    {?DONE, [Model|Acc], Bs}
	    end;
	false ->
	    %% io:format("contradiction: ~p\n", [varp_nif:get_all_bindings(Bs#bs.vp)]),
	    proof_output(Bs),
	    case undo(Bs) of
		true ->
		    collect(Bs, Count, N, Acc);
		false ->
		    if Count =:= 0 ->
			    %% proof_end(Bs),
			    exhausted(Bs, []);
		       true ->
			    {?DONE,Acc,Bs}
		    end
	    end
    end.

count(Bs, Count, N) ->
    case varp:check_timeout_or_cancel(Bs,?COUNTER_BT_BCP_COUNTER,
				      ?CHECK_INTERVAL) of
	false ->
	    if N =:= 0; Count < N ->
		    count_(Bs,Count,N);
	       true ->
		    undo_all(Bs),
		    {?CONTINUE,Count,Bs}
	    end;
	{true, Why} ->
	    undo_all(Bs),
	    {Why,Count,Bs}
    end.

count_(Bs, Count, N) when N =:= 0; Count < N ->
    case varp_nif:nbcp(Bs#bs.vp) of
	true ->
	    case varp_nif:getopt(Bs#bs.vp,print) of
		false -> ok;
		_ -> varp:output_model(Bs,false,Count+1)
	    end,
	    case undo(Bs) of
		true ->
		    count(Bs, Count+1, N);
		false ->
		    {?DONE, Count+1, Bs}
	    end;
	false ->
	    proof_output(Bs),
	    case undo(Bs) of
		true ->
		    count(Bs, Count, N);
		false ->
		    if Count =:= 0 ->
			    %% proof_end(Bs),
			    exhausted(Bs, 0);
		       true ->
			    {?DONE,Count,Bs}
		    end
	    end
    end.

%% undo all levels (except 0) and set level = 0
undo_all(Bs) ->
    varp_nif:pop(Bs#bs.vp, 0).


%% Xi is the current decision, that failed, 
%% Stack contains the negated previous decisions
proof_output(Bs) ->
    case get(proof_output) of
	none ->
	    ok;
	_ ->
	    Clause = varp:decision_clause(Bs),
	    varp_formula:proof_output(Bs,$a,Clause)
    end.

%% proof_end(Bs) ->
%%    case get(proof_output) of
%%	none ->
%%	    ok;
%%	_ ->
%%	    varp_formula:proof_output(Bs,$a,[])
%%    end.    
