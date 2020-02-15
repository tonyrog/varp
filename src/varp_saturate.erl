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

%% -define(DEBUG, true).
%% -compile(export_all).

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
    Timeout = maps:get(timeout, Param, infinity),
    Threshold = maps:get(threshold, Param, 0),
    Laps = maps:get(laps, Param, infinity),
    MaxLaps = max_laps(K, Laps),
    saturate(Bs,K,Timeout,MaxLaps,Threshold).

saturate(Bs,K,Timeout,MaxLaps,Threshold) ->
    varc:config(Bs#bs.vp, xref, true),
    Bs1 = varp:set_local_timeout(Bs, Timeout),
    case saturate_(Bs1,K,MaxLaps,Threshold) of
	false ->
	    {?INCONSISTENT,[],Bs1};
	{Reason,Bs1} -> 
	    varc:config(Bs#bs.vp, xref, false),
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
    case varc:next_unbound(Bs#bs.vp) of
	false ->
	    {?NOVAR,Bs};
	X ->
	    loop_k(Bs,X,K,N,Level,Laps,Threshold)
    end.

loop_k(Bs,Xi,K,N,Level,Laps,Threshold) ->
    case push2_eq_eval(Bs,-Xi,Level) of
	false ->
	    ?dbg("~scontradiction, undo ~w\n", [indent(Level+1),Level+1]),
	    pop2(Bs, Level),
	    case eq_eval(Bs,Xi,Level) of
		false ->
		    ?dbg("~scontradiction\n", [indent(Level)]),
		    false;
		true  -> 
		    loop_k_next(Bs,Xi,K,N,Level,Laps,Threshold)
	    end;
	true ->
	    N1 = varp_formula:number_of_bound(Bs),
	    case loop_k_next(Bs,Xi,K-1,N1,Level+2,Laps,Threshold) of
		false ->
		    ?dbg("~scontradiction, undo ~w\n", [indent(Level+1),Level+1]),
		    pop2(Bs, Level),
		    case eq_eval(Bs,Xi,Level) of
			false ->
			    ?dbg("~scontradiction\n", [indent(Level)]),
			    false;
			true  -> 
			    loop_k_next(Bs,Xi,K,N,Level,Laps,Threshold)
		    end;
		{_Reason,Bs1} ->
		    %% io:format("stop reason = ~w\n", [Reason]),
		    Ls = varp_formula:get_bindings(Bs1,Level+2),
		    ?dbg("~s~s/0: => {~s}\n", 
			 [indent(Level),
			  varp_formula:fmt_var(Bs1,Xi),
			  varp_formula:format_literals(Bs1,Ls)]),
		    pop2(Bs, Level),
		    case push2_eq_eval(Bs1,Xi,Level) of
			false ->
			    ?dbg("~scontradiction, undo ~w\n", 
				 [indent(Level+1),Level+1]),
			    pop2(Bs, Level),
			    eq_eval(Bs1,-Xi,Level),
			    loop_k_next(Bs1,Xi,K,N,Level,Laps,Threshold);
			true ->
			    N2 = varp_formula:number_of_bound(Bs),
			    case loop_k_next(Bs1,Xi,K-1,N2,Level+2,Laps,Threshold) of
				false ->
				    ?dbg("~scontradiction, undo ~w\n", 
					 [indent(Level),Level]),
				    pop2(Bs, Level),
				    eq_eval(Bs1,-Xi,Level),
				    loop_k_next(Bs1,Xi,K,N,Level,Laps,Threshold);
				{_Reason1,Bs2} ->
				    %% io:format("stop reason = ~w\n", [_Reason1]),
				    ?dbg("~s~s/1: => {~s}\n",
					 [indent(Level),varp_formula:fmt_var(Bs2,X),
					  varp_formula:fmt_literals(
					    Bs2,
					    varp_formula:get_bindings(Bs2,Level+1))]),
				    Ys = varp_formula:intersect_bindings(Bs2,Xi,Ls),
				    ?dbg("~sintersect = {~s}\n", 
					 [indent(Level),
					  varp_formula:fmt_bind_list(Bs2,Ys)]),
				    pop2(Bs2, Level),
				    varp_formula:install_bindings(Bs,Level,Ys),
				    true = varc:bcp(Bs2#bs.vp),
				    loop_k_next(Bs2,Xi,K,N,Level,Laps,Threshold)
			    end
		    end
	    end
    end.

loop_k_next(Bs,Xi,K,N,Level,Laps,Threshold) ->
    case varp:check_timeout_or_cancel(Bs,?COUNTER_ST_BCP_COUNTER,
				      ?CHECK_INTERVAL) of
	{true,What} ->
	    {What,Bs};
	false ->
	    case varc:next_unbound(Bs#bs.vp,Xi) of
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
		Xj when K>1   -> loop_k(Bs,Xj,K,N,Level,Laps,Threshold);
		Xj when K=:=1 -> loop_1(Bs,Xj,N,Level,Laps,Threshold)
	    end
    end.

init_1(Bs,N,Level,Laps,Threshold) ->
    case varc:next_unbound(Bs#bs.vp) of
	false ->
	    loop_1_done(?NOVAR,Laps,Bs);
	Xi ->
	    varp_formula:clear_user_count(Bs),
	    loop_1(Bs,Xi,N,Level,Laps,Threshold)
    end.

loop_1(Bs,Xi,N,Level,Laps,Threshold) ->
    case push_eq_eval(Bs,-Xi,Level) of
	false ->
	    ?dbg("~scontradiction, undo ~w\n", [indent(Level),Level]),
	    pop(Bs, Level),
	    case eq_eval(Bs,Xi,Level+1) of
		false ->
		    varp_formula:proof_output(Bs,$a,[Xi]),
		    varp_formula:proof_output(Bs,$a,[]),
		    %% L+1 ?  keep bindings?
		    ?dbg("~scontradiction\n", [indent(Level)]),
		    false;
		true ->
		    varp_formula:proof_output(Bs,$a,[Xi]),
		    %% Ls = varp_formula:get_bindings(Bs, Level+1),
		    varc:move_level(Bs#bs.vp, Level+1, Level),
		    varc:set_level(Bs#bs.vp,Level),
		    loop_1_next(Bs,Xi,N,Level,Laps,Threshold)
	    end;
	true ->
	    Ls = varp_formula:get_bindings(Bs,Level+1),
	    set_user_count(Bs, -Xi, Level+1),
	    pop(Bs,Level),
	    case push_eq_eval(Bs,Xi,Level) of
		false ->
		    varp_formula:proof_output(Bs,$a,[-Xi]),
		    ?dbg("~scontradiction, undo ~w\n", 
			 [indent(Level),Level]),
		    pop(Bs,Level),
		    eq_eval(Bs,-Xi,Level),  %% or install Ls?
		    loop_1_next(Bs,Xi,N,Level,Laps,Threshold);
		true ->
		    ?dbg("~s~s/1: => [~s]\n",
			 [indent(Level),varp_formula:fmt_var(Bs,Xi),
			  varp_formula:fmt_bind_list(
			    Bs, tl(varp_formula:get_bindings(Bs,Level+1)))]),
		    set_user_count(Bs, Xi, Level+1),
		    Ys = varp_formula:intersect_bindings(Bs, Xi, tl(Ls)),
		    %% FIXME: check if proof_output is active!
		    case varp_formula:want_proof_output(Bs) of
			false ->
			    ok;
			_ ->
			    lists:foreach(
			      fun({A,B}) ->
				      %% A -> B, B -> A  (-A,B), (-B,A)
				      varp_formula:proof_output(Bs,$a,[-A,B]),
				      varp_formula:proof_output(Bs,$a,[-B,A]);
				 (A) ->
				      %% Xi -> A, ~Xi -> A  (-Xi,A) (Xi, A)
				      varp_formula:proof_output(Bs,$a,[-Xi,A]),
				      varp_formula:proof_output(Bs,$a,[ Xi,A]),
				      varp_formula:proof_output(Bs,$a,[A])
			      end, Ys)
		    end,
		    pop(Bs,Level),
		    varc:set_level(Bs#bs.vp,Level),
		    if Ys =:= [] ->
			    ok;
		       true ->
			    varp_formula:install_bindings(Bs,Level,Ys),
			    true = varc:bcp(Bs#bs.vp)
		    end,
		    loop_1_next(Bs,Xi,N,Level,Laps,Threshold)
	    end
    end.

loop_1_next(Bs,Xi,N,Level,Laps,Threshold) ->
    case varp:check_timeout_or_cancel(Bs,?COUNTER_ST_BCP_COUNTER,
				      ?CHECK_INTERVAL) of
	{true,What} ->
	    ?dbg("terminate reaon=~w\n", [What]),
	    loop_1_done(What,Laps,Bs);
	false ->
	    case varc:next_unbound(Bs#bs.vp,Xi) of
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
		Xj -> loop_1(Bs,Xj,N,Level,Laps,Threshold)
	    end
    end.

loop_1_done(Reason, _Laps={_Ls,_Ms}, Bs) ->
    %% L = element(1,Ls),
    %% M = element(1,Ms),
    %% io:format("lap count=~w (~w)\n", [(M-L)+1, Laps]),
    {Reason,Bs}.

%% Fixme check flag - we may want to store other stuff as user count!
set_user_count(Bs, X, Level) ->
    Vp = Bs#bs.vp,
    N = varc:get_number_of_bindings(Vp, Level),
    ?dbg0("set_user_count: ~w = ~w\n", [X, N]),
    varc:set_user_count(Vp, X, N).

%% push level, set (unbound) variable and eval
push_eq_eval(Bs,X,Level) ->
    ?dbg("~spush_eq_eval: ~s\n", 
	 [indent(Level+1), varp_formula:format_lit(Bs,X)]),
    varc:set_level(Bs#bs.vp,Level+1),
    true = varc:bind(Bs#bs.vp,X),  %% this call should never fail!
    varc:bcp(Bs#bs.vp).   %% but this call may return false

pop(Bs, Level) ->
    varc:undo_level(Bs#bs.vp,Level+1).

%% set on one level eval on next level
push2_eq_eval(Bs,X,Level) ->
    ?dbg("~spush2_eq_eval: ~s\n", 
	 [indent(Level+1),varp_formula:fmt_lit(Bs,X)]),
    varc:set_level(Bs#bs.vp,Level+1),
    true = varc:bind(Bs#bs.vp,X),  %% this call should never fail!
    varc:set_level(Bs#bs.vp,Level+2),
    varc:bcp(Bs#bs.vp).   %% but this call may return false

pop2(Bs, Level) ->
    varc:undo_level(Bs#bs.vp,Level+2),
    varc:undo_level(Bs#bs.vp,Level+1).

eq_eval(Bs,X,Level) ->
    ?dbg("~seq_eval: ~s\n", 
	 [indent(Level), varp_formula:format_lit(Bs,X)]),
    varc:set_level(Bs#bs.vp,Level),
    true = varc:bind(Bs#bs.vp,X),
    varc:bcp(Bs#bs.vp).

max_laps(1, L) when is_integer(L) -> {{L},{L}};
max_laps(1, [L]) -> {{L},{L}};
max_laps(2, L) when is_integer(L) -> {{L,L},{L,L}};
max_laps(2, [L]) -> {{L,L},{L,L}};
max_laps(2, [L2,L1]) -> {{L1,L2},{L1,L2}};
max_laps(3, L) when is_integer(L) -> {{L,L,L},{L,L,L}};
max_laps(3, [L]) -> {{L,L,L},{L,L,L}};
max_laps(3, [L2,L1]) -> {{L1,L2,L2},{L1,L2,L2}};
max_laps(3, [L3,L2,L1]) -> {{L1,L2,L3},{L1,L2,L3}}.

%% FIXME!
dec(K, {Ls,Ms}) ->
    case element(K, Ls) of
	1 when K =:= 1 -> stop;
	E -> {setelement(K, Ls, E-1), Ms}
    end.

%% read "vector" of unbound variables starting from Var (must be unbound)
vec(Vp, Var, N) ->
    vec_(Vp, Var, N-1, [Var]).

vec_(Vp, _Var, 0, Vs) -> 
    Vs;
vec_(Vp, Var, I, Vs) ->
    case varc:next_unbound(Vp, Var) of
	false ->
	    Var0 = varc:next_unbound(Vp),
	    vec_(Vp, Var0, I-1, [Var0|Vs]);
	Var1 ->
	    vec_(Vp, Var1, I-1, [Var1|Vs])
    end.
	    
step(Vp, [V|Vec]) ->
    case varc:next_unbound(Vp, V) of
	false ->
	    Vec1 = [V1|_] = step(Vp, Vec),
	    case varc:next_unbound(Vp, V1) of
		false -> Vec1;
		V2 -> [V2|Vec1]
	    end;
	V1 ->
	    [V1|Vec]
    end.

-ifdef(DEBUG).
indent(D) -> lists:duplicate(D, $>).
-endif.

