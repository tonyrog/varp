%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2017, Tony Rogvall
%%% @doc
%%%    Run saturation
%%% @end
%%% Created : 19 Dec 2017 by Tony Rogvall <tony@rogvall.se>

-module(varp_saturate).

-export([run/2]).
-export([options/0]).
-export([saturate/5]).

-compile(export_all).
-import(varp_formula, [format_lit/2, format_var/2]).

%% -define(DEBUG, true).
-include("varp.hrl").

-define(CHECK_INTERVAL, 1000).

options() ->
    [#{ long  => "timeout",
	short => "t",
	key   => timeout,
	spec  => {union,[float,{enum,[{"infinity",infinity}]}]},
	default => infinity,
	description => "Max time to in seconds."
      },
     #{ long => "level",
	short => "k",
	key => level,
	spec => unsigned, 
	default => 1,
	description => "Saturation level."
      },
     #{ long => "pair",
	key => pair,
	spec => {enum,[?BOOL]},
	default => false,
	description => "Add extra variable in saturation."
      },
     #{ long => "threshold",
	key => threshold,
	spec => unsigned,
	default => 0,
	description => "Threshold for bound variables in saturation round."
      },
     #{ long  => "laps",
	short => "l",
	key   => laps,
	spec  => unsigned,
	default => 0,
	description => "Max saturation lap count"
      }
     ].


run(Bs, Param) when is_record(Bs, bs), is_map(Param) ->
    varp_formula:config(Bs, max_conflicting, 1),
    K = maps:get(level, Param, 1),
    _Pair = maps:get(pair, Param, false),
    Order = maps:get(order, Param, undefined),
    Timeout = maps:get(timeout, Param, infinity),
    Threshold = maps:get(threshold, Param, 0),
    Laps = maps:get(laps, Param, infinity),
    MaxLaps = max_laps(K, Laps),
    if Order =:= undefined -> ok;
       true -> varp_formula:order_sort(Bs, Order)
    end,
    saturate(Bs,K,Timeout,MaxLaps,Threshold).

saturate(Bs,K,Timeout,MaxLaps,Threshold) ->
    Bs1 = varp:set_local_timeout(Bs, Timeout),
    case saturate_(Bs1,K,MaxLaps,Threshold) of
	false ->
	    {?INCONSISTENT,[],Bs1};
	{Reason,Bs1} -> 
	    %% io:format("level = ~w\n", [varp_formula:info(Bs, level)]),
	    ?dbg("saturate limit ~w\n", [_Reason]),
	    {Reason,[],Bs1#bs{ t_local = undefined }}
    end.

saturate_(Bs,_K,0,_Threshold) ->
    {?ITERATIONS,Bs};
saturate_(Bs,K,Laps,Threshold) ->
    Level = ?TOP_LEVEL,
    N = varp_formula:number_of_bound(Bs),
    if  K =:= 1 ->
	    init_1(Bs,N,Level,Laps,Threshold);
	K > 0 -> 
	    init_k(Bs,K,N,Level,Laps,Threshold)
    end.

init_k(Bs,K,N,Level,Laps,Threshold) ->
    case varp_formula:first_unbound(Bs) of
	false ->
	    {?NOVAR,Bs};
	{I,X} ->
	    loop_k(Bs,I,X,K,N,Level,Laps,Threshold)
    end.

loop_k(Bs,I,X,K,N,Level,Laps,Threshold) ->
    case push2_eq_eval(Bs,-X,Level) of
	false ->
	    ?dbg("~scontradiction, undo ~w\n", [indent(Level+1),Level+1]),
	    pop2(Bs, Level),
	    case eq_eval(Bs,X,Level) of
		false ->
		    ?dbg("~scontradiction\n", [indent(Level)]),
		    false;
		true  -> 
		    loop_k_next(Bs,I,X,K,N,Level,Laps,Threshold)
	    end;
	true ->
	    N1 = varp_formula:number_of_bound(Bs),
	    case loop_k_next(Bs,I,X,K-1,N1,Level+2,Laps,Threshold) of
		false ->
		    ?dbg("~scontradiction, undo ~w\n", [indent(Level+1),Level+1]),
		    pop2(Bs, Level),
		    case eq_eval(Bs,X,Level) of
			false ->
			    ?dbg("~scontradiction\n", [indent(Level)]),
			    false;
			true  -> 
			    loop_k_next(Bs,I,X,K,N,Level,Laps,Threshold)
		    end;
		{_Reason,Bs1} ->
		    %% io:format("stop reason = ~w\n", [Reason]),
		    Ls = varp_formula:get_bindings(Bs1,Level+2),
		    ?dbg("~s~s/0: => {~s}\n", 
			 [indent(Level),
			  varp_formula:fmt_var(Bs1,X),
			  varp_formula:format_literals(Bs1,Ls)]),
		    pop2(Bs, Level),
		    case push2_eq_eval(Bs1,X,Level) of
			false ->
			    ?dbg("~scontradiction, undo ~w\n", 
				 [indent(Level+1),Level+1]),
			    pop2(Bs, Level),
			    eq_eval(Bs1,-X,Level),
			    loop_k_next(Bs1,I,X,K,N,Level,Laps,Threshold);
			true ->
			    N2 = varp_formula:number_of_bound(Bs),
			    case loop_k_next(Bs1,I,X,K-1,N2,Level+2,Laps,Threshold) of
				false ->
				    ?dbg("~scontradiction, undo ~w\n", 
					 [indent(Level),Level]),
				    pop2(Bs, Level),
				    eq_eval(Bs1,-X,Level),
				    loop_k_next(Bs1,I,X,K,N,Level,Laps,Threshold);
				{_Reason1,Bs2} ->
				    io:format("stop reason = ~w\n", [_Reason1]),
				    ?dbg("~s~s/1: => {~s}\n",
					 [indent(Level),varp_formula:fmt_var(Bs2,X),
					  varp_formula:fmt_literals(
					    Bs2,
					    varp_formula:get_bindings(Bs2,Level+1))]),
				    Ys = varp_formula:intersect_bindings(Bs2,X,Ls),
				    ?dbg("~sintersect = {~s}\n", 
					 [indent(Level),
					  varp_formula:fmt_bind_list(Bs2,Ys)]),
				    pop2(Bs2, Level),
				    varp_formula:install_bindings(Bs,Level,Ys),
				    true = varp_formula:eval(Bs2),
				    loop_k_next(Bs2,I,X,K,N,Level,Laps,Threshold)
			    end
		    end
	    end
    end.

loop_k_next(Bs,I,_X,K,N,Level,Laps,Threshold) ->
    case varp:check_timeout_or_cancel(Bs,?COUNTER_ST_EVAL_COUNTER,
				      ?CHECK_INTERVAL) of
	{true,What} ->
	    {What,Bs};
	false ->
	    case varp_formula:next_unbound(Bs,I) of
		false ->
		    N1 = varp_formula:number_of_bound(Bs),
		    if N1 - N =< Threshold ->
			    {threshold,Bs};
		       true ->
			    case dec(K,Laps) of
				stop ->
				    {laps,Bs};
				Laps1 ->
				    init_k(Bs,K,N1,Level,Laps1,Threshold)
			    end
		    end;
		{I1,X1} when K>1   -> loop_k(Bs,I1,X1,K,N,Level,Laps,Threshold);
		{I1,X1} when K=:=1 -> loop_1(Bs,I1,X1,N,Level,Laps,Threshold)
	    end
    end.

init_1(Bs,N,Level,Laps,Threshold) ->
    case varp_formula:first_unbound(Bs) of
	false -> 
	    loop_1_done(?NOVAR,Laps,Bs);
	{I,X} -> 
	    loop_1(Bs,I,X,N,Level,Laps,Threshold)
    end.

loop_1(Bs,I,X,N,Level,Laps,Threshold) ->
    case push_eq_eval(Bs,-X,Level) of
	false ->
	    ?dbg("~scontradiction, undo ~w\n", [indent(Level),Level]),
	    pop(Bs, Level),
	    case eq_eval(Bs,X,Level+1) of
		false ->
		    varp_formula:proof_output(Bs,$a,[X]),
		    varp_formula:proof_output(Bs,$a,[]),
		    %% L+1 ?  keep bindings?
		    ?dbg("~scontradiction\n", [indent(Level)]),
		    false;
		true ->
		    varp_formula:proof_output(Bs,$a,[X]),
		    Ls = varp_formula:get_bindings(Bs, Level+1),
		    varp_formula:move_level(Bs, Level+1, Level),
		    varp_formula:log_bindings(Bs, X, ?T, Ls),
		    varp_formula:set_level(Bs,Level),
		    loop_1_next(Bs,I,X,N,Level,Laps,Threshold)
	    end;
	true ->
	    Ls = varp_formula:get_bindings(Bs,Level+1),
	    pop(Bs,Level),
	    case push_eq_eval(Bs,X,Level) of
		false ->
		    varp_formula:proof_output(Bs,$a,[-X]),
		    ?dbg("~scontradiction, undo ~w\n", 
			 [indent(Level),Level]),
		    pop(Bs,Level),
		    eq_eval(Bs,-X,Level),
		    varp_formula:log_bindings(Bs, X, ?F, Ls),
		    loop_1_next(Bs,I,X,N,Level,Laps,Threshold);
		true ->
		    ?dbg("~s~s/1: => [~s]\n",
			 [indent(Level),varp_formula:fmt_var(Bs,X),
			  varp_formula:fmt_bind_list(
			    Bs, tl(varp_formula:get_bindings(Bs,Level+1)))]),
		    %% FIXME: if tl(Ys) = [] then do nothig...
		    Ys = varp_formula:intersect_bindings(Bs, X, tl(Ls)),
		    lists:foreach(
		      fun({A,B}) ->
			      %% A -> B, B -> A  (-A,B), (-B,A)
			      varp_formula:proof_output(Bs,$a,[-A,B]),
			      varp_formula:proof_output(Bs,$a,[-B,A]);
			 (A) ->
			      %% X -> A, ~X -> A  (-X,A) (X, A)
			      varp_formula:proof_output(Bs,$a,[-X,A]),
			      varp_formula:proof_output(Bs,$a,[ X,A]),
			      varp_formula:proof_output(Bs,$a,[A])
		      end, Ys),
		    pop(Bs,Level),
		    varp_formula:set_level(Bs,Level),
		    %% io:format("Ys = ~w\n", [Ys]),
		    %% fixme no need to install+eval when Ys=[]!
		    varp_formula:install_bindings(Bs,Level,Ys),
		    true = varp_formula:eval(Bs),
		    varp_formula:log_bindings(Bs, X, undefined, Ys),
		    loop_1_next(Bs,I,X,N,Level,Laps,Threshold)
	    end
    end.

loop_1_next(Bs,I,_X,N,Level,Laps,Threshold) ->
    case varp:check_timeout_or_cancel(Bs,?COUNTER_ST_EVAL_COUNTER,
				      ?CHECK_INTERVAL) of
	{true,What} ->
	    ?dbg("terminate reaon=~w\n", [What]),
	    loop_1_done(What,Laps,Bs);
	false ->
	    case varp_formula:next_unbound(Bs,I) of
		false ->
		    N1 = varp_formula:number_of_bound(Bs),
		    if N1 - N =< Threshold ->
			    loop_1_done(?THRESHOLD,Laps,Bs);
		       true ->
			    case dec(1,Laps) of
				stop ->
				    loop_1_done(?ITERATIONS,Laps,Bs);
				Laps1 ->
				    init_1(Bs,N1,Level,Laps1,Threshold)
			    end
		    end;
		{I1,X1} -> loop_1(Bs,I1,X1,N,Level,Laps,Threshold)
	    end
    end.

loop_1_done(Reason, _Laps={_Ls,_Ms}, Bs) ->
    %% L = element(1,Ls),
    %% M = element(1,Ms),
    %% io:format("lap count=~w (~w)\n", [(M-L)+1, Laps]),
    {Reason,Bs}.

%% push level, set (unbound) variable and eval
push_eq_eval(Bs,X,Level) ->
    ?dbg("~spush_eq_eval: ~s\n", 
	 [indent(Level+1), varp_formula:format_lit(Bs,X)]),
    varp_formula:set_level(Bs,Level+1),
    true = varp_formula:bind(Bs,X),  %% this call should never fail!
    varp_formula:eval(Bs).   %% but this call may return false

pop(Bs, Level) ->
    varp_formula:undo_level(Bs,Level+1).

%% set on one level eval on next level
push2_eq_eval(Bs,X,Level) ->
    ?dbg("~spush2_eq_eval: ~s\n", 
	 [indent(Level+1),varp_formula:fmt_lit(Bs,X)]),
    varp_formula:set_level(Bs,Level+1),
    true = varp_formula:bind(Bs,X),  %% this call should never fail!
    varp_formula:set_level(Bs,Level+2),
    varp_formula:eval(Bs).   %% but this call may return false

pop2(Bs, Level) ->
    varp_formula:undo_level(Bs,Level+2),
    varp_formula:undo_level(Bs,Level+1).

eq_eval(Bs,X,Level) ->
    ?dbg("~seq_eval: ~s\n", 
	 [indent(Level), varp_formula:format_lit(Bs,X)]),
    varp_formula:set_level(Bs,Level),
    true = varp_formula:bind(Bs,X),
    varp_formula:eval(Bs).

indent(D) -> lists:duplicate(D, $\s).

max_laps(1, L) when is_integer(L) -> {{L},{L}};
max_laps(1, [L]) -> {{L},{L}};
max_laps(2, L) when is_integer(L) -> {{L,L},{L,L}};
max_laps(2, [L]) -> {{L,L},{L,L}};
max_laps(2, [L2,L1]) -> {{L1,L2},{L1,L2}};
max_laps(3, L) when is_integer(L) -> {{L,L,L},{L,L,L}};
max_laps(3, [L]) -> {{L,L,L},{L,L,L}};
max_laps(3, [L2,L1]) -> {{L1,L2,L2},{L1,L2,L2}};
max_laps(3, [L3,L2,L1]) -> {{L1,L2,L3},{L1,L2,L3}}.

dec(K, {Ls,Ms}) ->
    case element(K, Ls) of
	1 when K =:= 1 -> stop;
	E -> {setelement(K, Ls, E-1), Ms}
    end.
