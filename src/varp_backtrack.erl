%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2017, Tony Rogvall
%%% @doc
%%%    Backtrack 
%%% @end
%%% Created : 22 Dec 2017 by Tony Rogvall <tony@rogvall.se>

-module(varp_backtrack).

-export([options/0]).
-export([run/2]).

%% -compile(export_all).

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
    Print = varp_formula:getopt(Bs,print),
    Timeout = maps:get(timeout, Param, infinity),
    varp_formula:config(Bs, max_conflicting, 1),
    Bs1 = varp:set_local_timeout(Bs, Timeout),
    case varp_formula:getopt(Bs1,method) of
	collect ->
	    bt(Bs1, fun(Count,Acc,Bs2) ->
			    Model = varp:output_model(Bs2,false,Count),
			    Continue = (N =:= 0) orelse (Count < N),
			    {Continue,[Model|Acc]}
		    end, []);
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
		    end, 0)
    end.

%%
%% Explicit recursion version, allow timed backtracking
%% mix algorithms etc.
%%
bt(Bs,Func,Acc) ->
    case init(Bs) of
	{model,_Stack} ->
	    {_,Acc1} = Func(1,Acc,Bs), 
	    {?DONE, Acc1, Bs};  %% no more models!
	{true,Stack} ->
	    loop(Stack,Func,0,0,Acc,Bs);
	false ->
	    {?INCONSISTENT, Acc, Bs}
    end.

%% initalise backtrack stack
init(Bs) ->
    case varc:next_unbound(Bs#bs.vp) of
	false ->
	    {model,[]};
	Xi ->
	    {true,[{0,[Xi,-Xi],?LEVEL}]}
    end.

next([{_,[],_}|Stack1],Bs) ->
    undo(Bs,Stack1),
    next(Stack1,Bs);
next([{_,[Xi|Xs],Level}|Stack],Bs) ->
    varc:set_level(Bs#bs.vp,Level),
    ?dbg0("~s~s\n", [indent(Level),varp_formula:format_lit(Bs,Xi)]),
    case eq_eval(Bs,Xi,Level) of
	false ->
	    Stack1 = [{Xi,Xs,Level}|Stack],
	    proof_output(Bs, Stack1),
	    undo_level(Bs,Level),
	    next(Stack1,Bs);
	true ->
	    case varc:next_unbound(Bs#bs.vp) of
		false ->
		    {model,[{Xi,Xs,Level}|Stack]};
		Xj ->
		    {true,[{0,[Xj,-Xj],Level+1},{Xi,Xs,Level}|Stack]}
	    end
    end;
next([],_Bs) ->
    false.

loop(Stack,Func,I,Count,Acc,Bs) ->
    case varp:check_timeout_or_cancel(Bs,?COUNTER_BT_BCP_COUNTER,
				      ?CHECK_INTERVAL) of
	false ->
	    loop_(Stack,Func,I,Count,Acc,Bs);
	{true, Why} ->
	    undo_all(Bs, Stack), %% make environment useful
	    {Why,Acc,Bs}
    end.

loop_(Stack,Func,I,Count,Acc,Bs) ->
    case next(Stack,Bs) of
	{model,Stack1} ->
	    Count1 = Count+1,
	    case Func(Count1,Acc,Bs) of
		{true,Acc1} ->
		    undo(Bs,Stack1),
		    loop(Stack1,Func,I+1,Count1,Acc1,Bs);
		{false,Acc1} ->
		    {?CONTINUE,Acc1,Bs}
	    end;
	{true,Stack1} ->
	    loop(Stack1,Func,I+1,Count,Acc,Bs);
	false ->
	    if Count =:= 0 ->
		    {?INCONSISTENT,Acc,Bs};
	       true ->
		    {?DONE,Acc,Bs}
	    end
    end.
	
undo(Bs,[{_,_,Level}|_]) ->
    undo_level(Bs,Level);
undo(_Bs,[]) ->
    ok.

undo_all(Bs,[{_,_,Level}|Stack]) ->
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
	    Stack1 = lists:dropwhile(fun({_,Xs,_}) -> Xs =:= [] end, Stack),
	    Clause = [-Xj || {Xj,_,_} <- Stack1], %% decision clause
	    varp_formula:proof_output(Bs,$a,Clause)
    end.

eq_eval(Bs,L,_D) ->
    ?dbg("~seq_eval@~w: ~w ~s", 
	 [indent(_D),_D, L, varp_formula:fmt_var(Bs,L)]),
    Res = eqv(Bs,L),
    ?dbg(" = ~w\n", [Res]),
    Res.

eqv(Bs,L) ->
    varc:bind(Bs#bs.vp,L) andalso varc:bcp(Bs#bs.vp).

indent(D) -> lists:duplicate(D, $>).
