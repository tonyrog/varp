%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2017, Tony Rogvall
%%% @doc
%%%    Backtrack 
%%% @end
%%% Created : 22 Dec 2017 by Tony Rogvall <tony@rogvall.se>

-module(varp_backtrack).
-behaviour(varp_plugin).

-export([options/0]).
-export([run/2]).

%% -compile(export_all).

%% -define(DEBUG, true).
-include("varp.hrl").

-define(LEVEL, 1).
-define(CHECK_INTERVAL, 1000).  %% 1000ms 

%% stack element
-record(e, 
	{
	 lit = 0 :: literal(),   %% current literal
	 ls      :: [literal()], %% literal list [] | [Xi] | [Xi,-Xi]
	 level   :: integer(), %% backtrack level
	 turbo   :: boolean()  %% true if turbo rule may be used
	}).

options() ->
    [#{ long  => "timeout",
	short => "t",
	key   => timeout,
	spec  => {union,[float,{enum,[{"infinity",infinity}]}]},
	default => infinity,
	description => "Max time to run backtrack in seconds"
      },
     #{ long  => "turbo",
	key   => turbo,
	spec  => {enum,[?BOOL]},
	default => false,
	description => "Use turbo bcp"
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
    Print = varp_formula:getopt(Bs,print),
    Timeout = maps:get(timeout, Param, infinity),
    UseTurbo = maps:get(turbo, Param, false),
    varp_formula:config(Bs, max_conflicting, 1),
    Bs1 = varp:set_local_timeout(Bs, Timeout),
    case varp_formula:getopt(Bs1,method) of
	collect ->
	    bt(Bs1, fun(Count,Acc,Bs2) ->
			    Model = varp:output_model(Bs2,false,Count),
			    Continue = (N =:= 0) orelse (Count < N),
			    {Continue,[Model|Acc]}
		    end, [], UseTurbo);
	count ->
	    bt(Bs1, fun(Count,_Acc,Bs2) ->
			    if Print =:= false -> ok;
			       true -> varp:output_model(Bs2,false,Count)
			    end,
			    if Count rem 1000 =:= 0 ->
				    io:format("~w\n", [Count]); %% option?
			       true -> 
				    ok
			    end,
			    Continue = (N =:= 0) orelse (Count < N),
			    {Continue,Count}
		    end, 0, UseTurbo)
    end.

%%
%% Explicit recursion version, allow timed backtracking
%% mix algorithms etc.
%%
bt(Bs,Func,Acc,UseTurbo) ->
    case init(Bs,UseTurbo) of
	{model,_Stack} ->
	    {_,Acc1} = Func(1,Acc,Bs), 
	    {?DONE, Acc1, Bs};  %% no more models!
	{true,Stack} ->
	    loop(Stack,Func,0,0,Acc,Bs,UseTurbo);
	false ->
	    {?INCONSISTENT, Acc, Bs}
    end.

%% initalise backtrack stack
init(Bs,UseTurbo) ->
    case varc:next_unbound(Bs#bs.vp) of
	false ->
	    {model,[]};
	Xi ->
	    ?dbg("~sinit ~w @~w\n", [indent(?LEVEL),Xi,?LEVEL]),
	    {true,[#e{ls=[Xi,-Xi],level=?LEVEL,turbo=UseTurbo}]}
    end.

next([#e{ls=[]}|Stack1],Bs,UseTurbo) ->
    undo(Bs,Stack1),
    next(Stack1,Bs,UseTurbo);
next([#e{ls=[Xi|Xs],level=Level,turbo=Turbo}|Stack],Bs,UseTurbo) ->
    varc:set_level(Bs#bs.vp,Level),
    case eqv(Bs,Xi,Level,Turbo) of
	false ->
	    Stack1 = [#e{lit=Xi,ls=Xs,level=Level,turbo=Turbo}|Stack],
	    proof_output(Bs, Stack1),
	    undo_level(Bs,Level),
	    next(Stack1,Bs,UseTurbo);
	turbo -> %% turbo can only be used on one side right now
	    io:format("TURBO\n"),
	    Stack1 = [#e{lit=Xi,ls=Xs,level=Level,turbo=false}|Stack],
	    proof_output(Bs, Stack1),
	    undo_level(Bs,Level),
	    next(Stack1,Bs,UseTurbo);
	true ->
	    case varc:next_unbound(Bs#bs.vp) of
		false ->
		    {model,[#e{lit=Xi,ls=Xs,level=Level,turbo=Turbo}|Stack]};
		Xj ->
		    ?dbg("~snext ~w @~w\n", [indent(Level),Xi,Level]),
		    {true,
		     [#e{ls=[Xj,-Xj],level=Level+1,turbo=UseTurbo},
		      #e{lit=Xi,ls=Xs,level=Level,turbo=Turbo}|Stack]}
	    end
    end;
next([],_Bs,_UseTurbo) ->
    false.

loop(Stack,Func,I,Count,Acc,Bs,UseTurbo) ->
    case varp:check_timeout_or_cancel(Bs,?COUNTER_BT_BCP_COUNTER,
				      ?CHECK_INTERVAL) of
	false ->
	    loop_(Stack,Func,I,Count,Acc,Bs,UseTurbo);
	{true, Why} ->
	    undo_all(Bs, Stack), %% make environment useful
	    {Why,Acc,Bs}
    end.

loop_(Stack,Func,I,Count,Acc,Bs,UseTurbo) ->
    case next(Stack,Bs,UseTurbo) of
	{model,Stack1} ->
	    Count1 = Count+1,
	    case Func(Count1,Acc,Bs) of
		{true,Acc1} ->
		    undo(Bs,Stack1),
		    loop(Stack1,Func,I+1,Count1,Acc1,Bs,UseTurbo);
		{false,Acc1} ->
		    {?CONTINUE,Acc1,Bs}
	    end;
	{true,Stack1} ->
	    loop(Stack1,Func,I+1,Count,Acc,Bs,UseTurbo);
	false ->
	    if Count =:= 0 ->
		    {?INCONSISTENT,Acc,Bs};
	       true ->
		    {?DONE,Acc,Bs}
	    end
    end.
	
undo(Bs,[#e{level=Level}|_]) ->
    undo_level(Bs,Level);
undo(_Bs,[]) ->
    ok.

undo_all(Bs,[#e{level=Level}|Stack]) ->
    undo_level(Bs,Level),
    undo_all(Bs, Stack);
undo_all(_Bs, []) ->
    ok.

undo_level(Bs, Level) ->
    ?dbg("~sundo@~w\n", [indent(Level),Level]),
    varc:undo_level(Bs#bs.vp,Level).
    
%% Xi is the current decision, that failed,
%% Stack contains the negated previous decisions
proof_output(Bs, Stack) ->
    case ?GETOPT_BS(Bs, proof_output) of
	none ->
	    ok;
	_ ->
	    Stack1 = lists:dropwhile(fun(#e{ls=Xs}) -> Xs =:= [] end, Stack),
	    Clause = [-(E#e.lit) || E <- Stack1], %% decision clause
	    varp_formula:proof_output(Bs,$a,Clause)
    end.

eqv(Bs,L,_Level,Turbo) ->
    ?dbg("~sdecide+bcp ~s/~w turbo=~w\n",
	 [indent(_Level),varp_formula:format_lit(Bs,L),
	  varc:info(Bs#bs.vp, phase),Turbo]),
    case varc:decide(Bs#bs.vp,L) of
	false -> false;
	true ->
	    if Turbo ->
		    varc:bcp(Bs#bs.vp,[L]);
	       true ->
		    varc:bcp(Bs#bs.vp)
	    end
    end.

-ifdef(DEBUG).
indent(D) -> lists:duplicate(D, $>).
-endif.
