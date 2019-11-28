%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2017, Tony Rogvall
%%% @doc
%%%    Backtrack 
%%% @end
%%% Created : 22 Dec 2017 by Tony Rogvall <tony@rogvall.se>

-module(varp_nbacktrack).

-export([options/0]).
-export([run/2]).

-compile(export_all).

%% -define(DEBUG, true).
-include("varp.hrl").

-define(LEVEL, 1).
-define(CHECK_INTERVAL, 1000).  %% 1000ms 

options() ->
    [#{ long  => "timeout",
	short => "t",
	key   => timeout,
	spec  => {union,[float,{enum,[{"infinity",infinity}]}]},
	default => infinity,
	description => "Max time to run backtrack in milliseconds"
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
    varc:set_level(Bs#bs.vp, ?LEVEL),
    case varp_formula:getopt(Bs1,method) of
	collect -> collect(Bs1, 0, N, []);
	count   -> count(Bs1, 0, N)
    end.

collect(Bs, Count, N, Acc) ->
    case varp:check_timeout_or_cancel(Bs,?COUNTER_BT_EVAL_COUNTER,
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
    case varc:nbcp(Bs#bs.vp) of
	true ->
	    Model = varp:output_model(Bs,Count+1),
	    case varc:undo(Bs#bs.vp) of
		true ->
		    collect(Bs, Count+1, N, [Model|Acc]);
		false ->
		    {?DONE, [Model|Acc], Bs}
	    end;
	false ->
	    proof_output(Bs),
	    case varc:undo(Bs#bs.vp) of
		true ->
		    collect(Bs, Count, N, Acc);
		false ->
		    if Count =:= 0 ->
			    {?INCONSISTENT,[],Bs};
		       true ->
			    {?DONE,Acc,Bs}
		    end
	    end
    end.

count(Bs, Count, N) ->
    case varp:check_timeout_or_cancel(Bs,?COUNTER_BT_EVAL_COUNTER,
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
    case varc:nbcp(Bs#bs.vp) of
	true ->
	    case varp_formula:getopt(Bs,print) of
		false -> ok;
		_ -> varp:output_model(Bs,Count+1)
	    end,
	    case varc:undo(Bs#bs.vp) of
		true ->
		    count(Bs, Count+1, N);
		false ->
		    {?DONE, Count+1, Bs}
	    end;
	false ->
	    proof_output(Bs),
	    case varc:undo(Bs#bs.vp) of
		true ->
		    count(Bs, Count, N);
		false ->
		    if Count =:= 0 ->
			    {?INCONSISTENT,0,Bs};
		       true ->
			    {?DONE,Count,Bs}
		    end
	    end
    end.

%% undo all levels (except 0) and set level = 0
undo_all(Bs) ->
    Level = varc:info(Bs#bs.vp, level),
    undo_all_levels(Bs, Level).

undo_all_levels(Bs, 0) ->
    varc:set_level(Bs#bs.vp, 0);
undo_all_levels(Bs, I) ->
    varp_formula:undo_level(Bs,I),
    undo_all_levels(Bs, I-1).

decision_clause(Bs) ->
    Level = varc:info(Bs#bs.vp, level),
    decision_clause_(Bs, Level).

decision_clause_(_Bs, 0) ->
    [];
decision_clause_(Bs, Level) ->
    case varc:get_decision(Bs#bs.vp, Level, 3) of    
	f -> decision_clause_(Bs,Level-1);
	Xi -> decision_clause__(Bs,Level-1,[-Xi])
    end.

decision_clause__(_Bs, 0, Clause) ->
    Clause;
decision_clause__(Bs, Level, Clause) ->
    Xi = varc:get_decision(Bs#bs.vp, Level, 4),
    decision_clause__(Bs, Level-1, [-Xi|Clause]).
    
%% Xi is the current decision, that failed, 
%% Stack contains the negated previous decisions
proof_output(Bs) ->
    case ?GETOPT_BS(Bs, proof_output) of
	none ->
	    ok;
	_ ->
	    Clause = decision_clause(Bs),
	    varp_formula:proof_output(Bs,$a,Clause)
    end.
