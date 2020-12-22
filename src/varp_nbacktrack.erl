%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2017, Tony Rogvall
%%% @doc
%%%    Backtrack 
%%% @end
%%% Created : 22 Dec 2017 by Tony Rogvall <tony@rogvall.se>

-module(varp_nbacktrack).
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

run(Bs, Param) when is_record(Bs, bs), is_map(Param) ->
    N = maps:get(max, Param),
    %% Print = varp_formula:getopt(Bs,print),
    Timeout = maps:get(timeout, Param, infinity),
    varp_formula:config(Bs, max_conflicting, 1),
    Bs1 = varp:set_local_timeout(Bs, Timeout),
    0 = varp_nif:push(Bs#bs.vp), %% assert, may be relaxed
    case varp_formula:getopt(Bs1,method) of
	collect -> collect(Bs1, 0, N, []);
	count   -> count(Bs1, 0, N)
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
	    %% io:format("model: ~p\n", [varp_nif:get_all_bindings(Bs#bs.vp)]),
	    Model = varp:output_model(Bs,false,Count+1),
	    case varp_nif:undo(Bs#bs.vp) of
		true ->
		    collect(Bs, Count+1, N, [Model|Acc]);
		false ->
		    {?DONE, [Model|Acc], Bs}
	    end;
	false ->
	    %% io:format("contradiction: ~p\n", [varp_nif:get_all_bindings(Bs#bs.vp)]),
	    proof_output(Bs),
	    case varp_nif:undo(Bs#bs.vp) of
		true ->
		    collect(Bs, Count, N, Acc);
		false ->
		    if Count =:= 0 ->
			    %% proof_end(Bs),
			    {?INCONSISTENT,[],Bs};
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
	    case varp_formula:getopt(Bs,print) of
		false -> ok;
		_ -> varp:output_model(Bs,false,Count+1)
	    end,
	    case varp_nif:undo(Bs#bs.vp) of
		true ->
		    count(Bs, Count+1, N);
		false ->
		    {?DONE, Count+1, Bs}
	    end;
	false ->
	    proof_output(Bs),
	    case varp_nif:undo(Bs#bs.vp) of
		true ->
		    count(Bs, Count, N);
		false ->
		    if Count =:= 0 ->
			    %% proof_end(Bs),
			    {?INCONSISTENT,0,Bs};
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
    case ?GETOPT_BS(Bs, proof_output) of
	none ->
	    ok;
	_ ->
	    Clause = varp:decision_clause(Bs),
	    varp_formula:proof_output(Bs,$a,Clause)
    end.

%% proof_end(Bs) ->
%%    case ?GETOPT_BS(Bs, proof_output) of
%%	none ->
%%	    ok;
%%	_ ->
%%	    varp_formula:proof_output(Bs,$a,[])
%%    end.    
