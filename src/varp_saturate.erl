%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2017, Tony Rogvall
%%% @doc
%%%    Run saturation
%%% @end
%%% Created : 19 Dec 2017 by Tony Rogvall <tony@rogvall.se>

-module(varp_saturate).

-export([saturate/2]).
-export([saturate/5]).

-compile(export_all).
-import(varp_formula, [format_lit/2, format_var/2]).

-include("varp.hrl").

%% -define(DEBUG, true).

-define(dbg0(F,As), ok).
-ifdef(DEBUG).
-define(dbg(F,A), io:format((F),(A))).
-define(dcall(Fun), Fun()).
-else.
-define(dbg(F,A), ok).
-define(dcall(Fun), ok).
-endif.

-type bs()::term().

-spec saturate(Bs::bs(), K::non_neg_integer()) -> false | bs().

saturate(Bs, Params) ->
    varp_formula:config(Bs, max_conflicting, 1),
    K = maps:get(saturate, Params, 1),
    _Pair = maps:get(pair, Params, false),
    Order = maps:get(order, Params, undefined),
    MaxTime = maps:get(time, Params, infinity),
    Threshold = maps:get(threshold, Params, 0),
    Laps = maps:get(laps, Params, infinity),
    MaxLaps = max_laps(K, Laps),
    if Order =:= undefined -> ok;
       true -> varp_formula:order_sort(Bs, Order)
    end,
    saturate(Bs, K, MaxTime, MaxLaps, Threshold).

saturate(Bs, K, MaxTime, MaxLaps, Threshold) ->
    TRef = if is_number(MaxTime), MaxTime > 0 ->
		   erlang:start_timer(trunc(1000*MaxTime), undefined, ok);
	      MaxTime =:= infinity ->
		   undefined
	   end,
    case saturate_(Bs,K,TRef,MaxLaps,Threshold) of
	false -> false;
	{_Reason,Bs} -> 
	    io:format("saturate limit ~w\n", [_Reason]),
	    Bs
    end.

saturate_(Bs,_K,_TRef,0,_Threshold) ->
    {laps,Bs};
saturate_(Bs,K,TRef,Laps,Threshold) ->
    Level = ?TOP_LEVEL,
    N = varp_formula:number_of_bound(Bs),
    if  K =:= 1 ->
	    init_1(Bs,N,Level,TRef,Laps,Threshold);
	K > 0 -> 
	    init_k(Bs,K,N,Level,TRef,Laps,Threshold)
    end.

init_k(Bs,K,N,Level,TRef,Laps,Threshold) ->
    case varp_formula:first_unbound(Bs) of
	false ->
	    {novar,Bs};
	{I,X} -> 
	    loop_k(Bs,I,X,K,N,Level,TRef,Laps,Threshold)
    end.    

loop_k(Bs,I,X,K,N,Level,TRef,Laps,Threshold) ->
    case push2_eq_eval(Bs,X,?FALSE,Level) of
	false ->
	    ?dbg("~scontradiction, undo ~w\n", [indent(Level+1),Level+1]),
	    pop2(Bs, Level),
	    case eq_eval(Bs,X,?TRUE,Level) of
		false ->
		    ?dbg("~scontradiction\n", [indent(Level)]),
		    false;
		true  -> 
		    loop_k_next(Bs,I,X,K,N,Level,TRef,Laps,Threshold)
	    end;
	true ->
	    N1 = varp_formula:number_of_bound(Bs),
	    case loop_k_next(Bs,I,X,K-1,N1,Level+2,TRef,Laps,Threshold) of
		false ->
		    ?dbg("~scontradiction, undo ~w\n", [indent(Level+1),Level+1]),
		    pop2(Bs, Level),
		    case eq_eval(Bs,X,?TRUE,Level) of
			false ->
			    ?dbg("~scontradiction\n", [indent(Level)]),
			    false;
			true  -> 
			    loop_k_next(Bs,I,X,K,N,Level,TRef,Laps,Threshold)
		    end;
		{_Reason,Bs1} ->
		    %% io:format("stop reason = ~w\n", [Reason]),
		    Xs = varp_formula:get_bindings(Bs1,Level+2),
		    ?dbg("~s~s/0: => {~s}\n", 
			 [indent(Level),
			  varp_formula:fmt_var(Bs1,X),
			  varp_formula:fmt_bind_list(Bs1,Xs)]),
		    pop2(Bs, Level),
		    case push2_eq_eval(Bs1,X,?TRUE,Level) of
			false ->
			    ?dbg("~scontradiction, undo ~w\n", 
				 [indent(Level+1),Level+1]),
			    pop2(Bs, Level),
			    eq_eval(Bs1,X,?FALSE,Level),
			    loop_k_next(Bs1,I,X,K,N,Level,TRef,Laps,Threshold);
			true ->
			    N2 = varp_formula:number_of_bound(Bs),
			    case loop_k_next(Bs1,I,X,K-1,N2,Level+2,TRef,Laps,Threshold) of
				false ->
				    ?dbg("~scontradiction, undo ~w\n", 
					 [indent(Level),Level]),
				    pop2(Bs, Level),
				    eq_eval(Bs1,X,?FALSE,Level),
				    loop_k_next(Bs1,I,X,K,N,Level,TRef,Laps,Threshold);
				{_Reason1,Bs2} ->
				    io:format("stop reason = ~w\n", [_Reason1]),
				    ?dbg("~s~s/1: => {~s}\n",
					 [indent(Level),varp_formula:fmt_var(Bs2,X),
					  varp_formula:fmt_bind_list(
					    Bs2,
					    varp_formula:get_bindings(Bs2,Level+1))]),
				    Ys = varp_formula:intersect(Bs2, X, Xs),
				    ?dbg("~sintersect = {~s}\n", 
					 [indent(Level),
					  varp_formula:fmt_bind_list(Bs2,Ys)]),
				    pop2(Bs2, Level),
				    install_bindings(Bs,Level,X,Ys),
				    true = varp_formula:eval(Bs2),
				    loop_k_next(Bs2,I,X,K,N,Level,TRef,Laps,Threshold)
			    end
		    end
	    end
    end.

loop_k_next(Bs,I,_X,K,N,Level,TRef,Laps,Threshold) ->
    case varp_formula:next_unbound(Bs,I) of
	false ->
	    TimeRemain = read_timer(TRef),
	    if TimeRemain =:= 0 -> 
		    {timeout,Bs};
	       true ->
		    N1 = varp_formula:number_of_bound(Bs),
		    if N1 - N =< Threshold ->
			    {threshold,Bs};
		       true ->
			    case dec(K,Laps) of
				stop ->
				    {laps,Bs};
				Laps1 ->
				    io:format("Laps1 = ~w\n", [Laps]),
				    init_k(Bs,K,N1,Level,TRef,Laps1,Threshold)
			    end
		    end
	    end;
	{I1,X1} when K>1   -> loop_k(Bs,I1,X1,K,N,Level,TRef,Laps,Threshold);
	{I1,X1} when K=:=1 -> loop_1(Bs,I1,X1,N,Level,TRef,Laps,Threshold)
    end.

init_1(Bs,N,Level,TRef,Laps,Threshold) ->
    case varp_formula:first_unbound(Bs) of
	false -> 
	    {novar,Bs};
	{I,X} -> 
	    loop_1(Bs,I,X,N,Level,TRef,Laps,Threshold)
    end.

loop_1(Bs,I,X,N,Level,TRef,Laps,Threshold) ->
    case push_eq_eval(Bs,X,?FALSE,Level) of
	false ->
	    ?dbg("~scontradiction, undo ~w\n", [indent(Level),Level]),
	    pop(Bs,Level),
	    case eq_eval(Bs,X,?TRUE,Level) of
		false ->
		    ?dbg("~scontradiction\n", [indent(Level)]),
		    false;
		true -> 
		    loop_1_next(Bs,I,X,N,Level,TRef,Laps,Threshold)
	    end;
	true ->
	    Xs = tl(varp_formula:get_bindings(Bs,Level+1)),
	    ?dbg("~s~s/0: => [~s]\n", 
		 [indent(Level), varp_formula:fmt_var(Bs,X),
		  varp_formula:fmt_bind_list(Bs,Xs)]),
	    pop(Bs,Level),
	    case push_eq_eval(Bs,X,?TRUE,Level) of
		false ->
		    ?dbg("~scontradiction, undo ~w\n", 
			 [indent(Level),Level]),
		    pop(Bs,Level),
		    eq_eval(Bs,X,?FALSE,Level),
		    loop_1_next(Bs,I,X,N,Level,TRef,Laps,Threshold);
		true ->
		    ?dbg("~s~s/1: => [~s]\n",
			 [indent(Level),varp_formula:fmt_var(Bs,X),
			  varp_formula:fmt_bind_list(
			    Bs, tl(varp_formula:get_bindings(Bs,Level+1)))]),
		    Ys = varp_formula:intersect(Bs, X, Xs),
		    ?dbg("~sintersect = [~s]\n", 
			 [indent(Level),
			  varp_formula:fmt_bind_list(Bs,Ys)]),
		    pop(Bs,Level),
		    install_bindings(Bs,Level,X,Ys),
		    true = varp_formula:eval(Bs),
		    loop_1_next(Bs,I,X,N,Level,TRef,Laps,Threshold)
	    end
    end.

loop_1_next(Bs,I,_X,N,Level,TRef,Laps,Threshold) ->
    case varp_formula:next_unbound(Bs,I) of
	false ->
	    %% fixme: check timeout more often
	    TimeRemain = read_timer(TRef),
	    if TimeRemain =:= 0 -> 
		    ?dbg("timer terminated\n", []),
		    {timeout,Bs};
	       true ->
		    N1 = varp_formula:number_of_bound(Bs),
		    if N1 - N =< Threshold ->
			    ?dbg("threshold limit\n", []),
			    {threshold,Bs};
		       true -> 
			    case dec(1,Laps) of
				stop ->
				    {laps,Bs};
				Laps1 ->
				    init_1(Bs,N1,Level,TRef,Laps1,Threshold)
			    end
		    end
	    end;
	{I1,X1} -> loop_1(Bs,I1,X1,N,Level,TRef,Laps,Threshold)
    end.

install_bindings(_Bs,_Level,_Var,[]) ->
    ok;
install_bindings(Bs,Level,_Var,Bnds) ->
    varp_formula:set_level(Bs,Level),
    Bcp = varp_option:getopt(bcp,Bs#bs.option),
    install_bindings_(Bs,Level,Bcp,Bnds).


install_bindings_(Bs,Level,Bcp,[{X,X}|Xs]) ->
    install_bindings_(Bs,Level,Bcp,Xs);

install_bindings_(Bs,Level,Bcp,[{X,Y}|Xs]) when abs(Y) =:= ?TRUE ->
    io:format("put ~s = ~s\n", [format_lit(Bs,X),format_lit(Bs,Y)]),
    varp_formula:equal(Bs,X,Y),
    install_bindings_(Bs,Level,Bcp,Xs);

install_bindings_(Bs,Level,Bcp=false,[{X,Y}|Xs]) ->
    varp_formula:equal(Bs,X,Y),
    install_bindings_(Bs,Level,Bcp,Xs);
install_bindings_(Bs,Level,Bcp=true,[{X,Y}|Xs]) ->
    if Level =:= ?TOP_LEVEL ->
	    io:format("substitue [~s/~s]\n",
		      [format_lit(Bs,X),format_lit(Bs,Y)]),
	    varp_formula:substitute(Bs, X, Y),
%%	    io:format("install clause {~s,~s}\n", [format_lit(Bs,Y),format_lit(Bs,-X)]),
%%	    io:format("install clause {~s,~s}\n", [format_lit(Bs,-Y),format_lit(Bs,X)]),
%%	    varp_formula:add_clause(Bs, 'or', [?TRUE,X,-Y]),
%%	    varp_formula:add_clause(Bs, 'or', [?TRUE,-X,Y]),
%%	    varp_formula:equal(Bs,X,Y),
	    ok;
       true -> 
	    ok
    end,
    install_bindings_(Bs,Level,Bcp,Xs);

install_bindings_(Bs,_Level,_Bcp,[]) ->
    Bs.

%% push level, set (unbound) variable and eval
push_eq_eval(Bs,V,Value,Level) ->
    ?dbg("~spush_eq_eval: ~s/~s\n", 
	 [indent(Level+1),
	  varp_formula:fmt_var(Bs,V),
	  varp_formula:format_lit(Bs,Value)]),
    varp_formula:set_level(Bs,Level+1),
    true = varp_formula:equal(Bs,V,Value),  %% this call should never fail!
    varp_formula:eval(Bs).   %% but this call may return false

pop(Bs, Level) ->
    varp_formula:undo_level(Bs,Level+1).

%% set on one level eval on next level
push2_eq_eval(Bs,V,Value,Level) ->
    ?dbg("~spush2_eq_eval: ~s/~s\n", 
	 [indent(Level+1),
	  varp_formula:fmt_var(Bs,V),
	  varp_formula:format_lit(Bs,Value)]),
    varp_formula:set_level(Bs,Level+1),
    true = varp_formula:equal(Bs,V,Value),  %% this call should never fail!
    varp_formula:set_level(Bs,Level+2),
    varp_formula:eval(Bs).   %% but this call may return false

pop2(Bs, Level) ->
    varp_formula:undo_level(Bs,Level+2),
    varp_formula:undo_level(Bs,Level+1).

eq_eval(Bs,V,Value,_D) ->
    ?dbg("~seq_eval: ~s/~s\n", 
	 [indent(_D),
	  varp_formula:fmt_var(Bs,V),
	  varp_formula:format_lit(Bs,Value)]),
    true = varp_formula:equal(Bs,V,Value),
    varp_formula:eval(Bs).

indent(D) -> lists:duplicate(D, $\s).

max_laps(1, L) when is_integer(L); L =:= infinity -> {{L},{L}};
max_laps(1, [L]) -> {{L},{L}};
max_laps(2, L) when is_integer(L); L =:= infinity -> {{L,L},{L,L}};
max_laps(2, [L]) -> {{L,L},{L,L}};
max_laps(2, [L2,L1]) -> {{L1,L2},{L1,L2}};
max_laps(3, L) when is_integer(L); L =:= infinity -> {{L,L,L},{L,L,L}};
max_laps(3, [L]) -> {{L,L,L},{L,L,L}};
max_laps(3, [L2,L1]) -> {{L1,L2,L2},{L1,L2,L2}};
max_laps(3, [L3,L2,L1]) -> {{L1,L2,L3},{L1,L2,L3}}.

dec(K, Laps={Ls,Ms}) ->
    case element(K, Ls) of
	1 when K =:= 1 -> stop;
	infinity -> Laps;
	E -> {setelement(K, Ls, E-1), Ms}
    end.

read_timer(undefined) -> 
    infinity;
read_timer(TRef) when is_reference(TRef) ->
    case erlang:read_timer(TRef) of
	false -> 0;
	Remain -> Remain
    end.
