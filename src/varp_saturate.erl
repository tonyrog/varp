%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2017, Tony Rogvall
%%% @doc
%%%    Run saturation
%%% @end
%%% Created : 19 Dec 2017 by Tony Rogvall <tony@rogvall.se>

-module(varp_saturate).

-compile(export_all).
-import(varp_formula, [format_literal/2]).

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

-define(TOP_LEVEL, 0).
-define(RUN_LEVEL, 1).

-spec saturate(Bs::bs(), K::non_neg_integer()) -> false | bs().

saturate(Bs, Params) ->
    K = maps:get(saturate, Params, 1),
    _Pair = maps:get(pair, Params, false),
    Order = maps:get(order, Params, undefined),
    Time = maps:get(time, Params, infinity),
    Threshold = maps:get(threshold, Params, 0),
    if Order =:= undefined -> ok;
       true -> varp_formula:order_sort(Bs, Order)
    end,
    TRef = if is_integer(Time) ->
		   erlang:start_timer(Time, undefined, ok);
	      Time =:= infinity ->
		   infinity
	   end,
    saturate_(Bs,K,TRef,Threshold).
	    
saturate_(Bs,1,TRef,Threshold) ->
    case varp_formula:first_unbound(Bs) of
	false -> Bs;
	{I,X} ->
	    loop_1(Bs,I,X,
		   varp_formula:number_of_bound(Bs),
		   ?RUN_LEVEL,TRef,Threshold)
    end;
saturate_(Bs,K,TRef,Threshold) when is_integer(K), K >= 1 ->
    case varp_formula:first_unbound(Bs) of
	false -> Bs;
	{I,X} -> loop_k(Bs,I,X,K,
			varp_formula:number_of_bound(Bs),			
			?RUN_LEVEL,TRef,Threshold)
    end.

loop_k(Bs,I,X,K,N,Level,TRef,Threshold) ->
    case mark_eq_eval(Bs,X,?FALSE,Level) of
	false ->
	    ?dbg("~scontradiction, undo ~w\n", [indent(Level),Level]),
	    varp_formula:undo(Bs,Level),
	    case eq_eval(Bs,X,?TRUE,Level) of
		false ->
		    ?dbg("~scontradiction\n", [indent(Level)]),
		    false;
		true  -> 
		    loop_k_next(Bs,I,X,K,N,Level,TRef,Threshold)
	    end;
	true ->
	    N1 = varp_formula:number_of_bound(Bs),
	    case loop_k_next(Bs,I,X,K-1,N1,Level+2,TRef,Threshold) of
		false ->
		    ?dbg("~scontradiction, undo ~w\n", [indent(Level),Level]),
		    varp_formula:undo(Bs,Level),
		    case eq_eval(Bs,X,?TRUE,Level) of
			false ->
			    ?dbg("~scontradiction\n", [indent(Level)]),
			    false;
			true  -> 
			    loop_k_next(Bs,I,X,K,N,Level,TRef,Threshold)
		    end;
		Bs1 ->
		    Xs = varp_formula:get_bindings(Bs1,Level+1),
		    ?dbg("~s~s/false: => {~s}\n", 
			 [indent(Level),
			  varp_formula:fmt_var(Bs1,X),
			  varp_formula:fmt_bind_list(Bs1,Xs)]),
		    varp_formula:undo(Bs1,Level), %% (X=false)

		    case mark_eq_eval(Bs1,X,?TRUE,Level) of
			false ->
			    ?dbg("~scontradiction, undo ~w\n", 
				 [indent(Level),Level]),
			    varp_formula:undo(Bs1,Level),  %% (X=true)
			    eq_eval(Bs1,X,false,Level),
			    loop_k_next(Bs1,I,X,K,N,Level,TRef,Threshold);
			true ->
			    N2 = varp_formula:number_of_bound(Bs),
			    case loop_k_next(Bs1,I,X,K-1,N2,Level+2,TRef,Threshold) of
				false ->
				    ?dbg("~scontradiction, undo ~w\n", 
					 [indent(Level),Level]),
				    varp_formula:undo(Bs1,Level),  %% (X=true)
				    eq_eval(Bs1,X,?FALSE,Level),
				    loop_k_next(Bs1,I,X,K,N,Level,TRef,Threshold);
				Bs2 ->
				    ?dbg("~s~s/true: => {~s}\n",
					 [indent(Level),varp_formula:fmt_var(Bs2,X),
					  varp_formula:fmt_bind_list(
					    Bs2,
					    varp_formula:get_bindings(Bs2,Level+1))]),
				    Ys = varp_formula:intersect(Bs2, X, Xs),
				    ?dbg("~sintersect = {~s}\n", 
					 [indent(Level),
					  varp_formula:fmt_bind_list(Bs2,Ys)]),
				    varp_formula:undo(Bs2,Level), %% undo (X=true)
				    install_bindings(Bs,Level,X,Ys),
				    varp_formula:eval(Bs2),
				    loop_k_next(Bs2,I,X,K,N,Level,TRef,Threshold)
			    end
		    end
	    end
    end.


install_bindings(_Bs,_Level,_Var,[]) ->
    ok;
install_bindings(Bs,Level,_Var,Bnds) ->
    Bcp = varp_option:getopt(bcp,Bs#bs.option),
    if Level =:= ?RUN_LEVEL ->
	    varp_formula:mark(Bs,?TOP_LEVEL);
       true ->
	    ok
    end,
    install_bindings_(Bs,Level,Bcp,Bnds).


install_bindings_(Bs,Level,Bcp,[{X,Y}|Xs]) when abs(Y) =:= ?TRUE ->
    varp_formula:equal(Bs,X,Y),
    install_bindings_(Bs,Level,Bcp,Xs);
install_bindings_(Bs,Level,Bcp=false,[{Var,X}|Xs]) ->
    varp_formula:equal(Bs,Var,X),
    install_bindings_(Bs,Level,Bcp,Xs);
install_bindings_(Bs,Level,Bcp=true,[{Var,X}|Xs]) ->
    if Level =:= ?RUN_LEVEL ->
	    varp_formula:add_clause(Bs, 'or', [?TRUE,Var,-X]),
	    varp_formula:add_clause(Bs, 'or', [?TRUE,-Var,X]);
       true -> 
	    ok
    end,
    install_bindings_(Bs,Level,Bcp,Xs);
install_bindings_(Bs,_Level,_Bcp,[]) ->
    Bs.

loop_k_next(Bs,I,_X,K,N,Level,TRef,Threshold) ->
    case varp_formula:next_unbound(Bs,I) of
	false ->
	    case read_timer(TRef) of
		0 -> Bs;
		_ ->
		    N1 = varp_formula:number_of_bound(Bs),
		    if N1 - N =< Threshold -> Bs;
		       true -> saturate_(Bs,K,TRef,Threshold)
		    end
	    end;
	{I1,X1} when K>1   -> loop_k(Bs,I1,X1,K,N,Level,TRef,Threshold);
	{I1,X1} when K=:=1 -> loop_1(Bs,I1,X1,N,Level,TRef,Threshold)
    end.

loop_1(Bs,I,X,N,Level,TRef,Threshold) ->
    case mark_eq_eval(Bs,X,?FALSE,Level) of
	false ->
	    ?dbg("~scontradiction, undo ~w\n", [indent(Level),Level]),
	    varp_formula:undo(Bs,Level),
	    case eq_eval(Bs,X,?TRUE,Level) of
		false ->
		    ?dbg("~scontradiction\n", [indent(Level)]),
		    false;
		true  -> 
		    loop_1_next(Bs,I,X,N,Level,TRef,Threshold)
	    end;
	true ->
	    Xs = varp_formula:get_bindings(Bs,Level+1),
	    ?dbg("~s~s/false: => {~s}\n", 
		 [indent(Level),
		  varp_formula:fmt_var(Bs,X),
		  varp_formula:fmt_bind_list(Bs,Xs)]),
	    varp_formula:undo(Bs,Level), %% (X=false)
		    
	    case mark_eq_eval(Bs,X,?TRUE,Level) of
		false ->
		    ?dbg("~scontradiction, undo ~w\n", 
			 [indent(Level),Level]),
		    varp_formula:undo(Bs,Level),  %% (X=true)
		    eq_eval(Bs,X,?FALSE,Level),
		    loop_1_next(Bs,I,X,N,Level,TRef,Threshold);
		true ->
		    ?dbg("~s~s/true: => {~s}\n",
			 [indent(Level),varp_formula:fmt_var(Bs,X),
			  varp_formula:fmt_bind_list(
			    Bs,
			    varp_formula:get_bindings(Bs,Level+1))]),
		    Ys = varp_formula:intersect(Bs, X, Xs),
		    ?dbg("~sintersect = {~s}\n", 
			 [indent(Level),
			  varp_formula:fmt_bind_list(Bs,Ys)]),
		    varp_formula:undo(Bs,Level),  %% undo (X=true)
		    install_bindings(Bs,Level,X,Ys),
		    varp_formula:eval(Bs),
		    loop_1_next(Bs,I,X,N,Level,TRef,Threshold)
	    end
    end.

loop_1_next(Bs,I,_X,N,Level,TRef,Threshold) ->
    case varp_formula:next_unbound(Bs,I) of
	false ->
	    case read_timer(TRef) of
		0 -> 
		    ?dbg("timer terminated\n", []),
		    Bs;
		_ ->
		    N1 = varp_formula:number_of_bound(Bs),
		    if N1 - N =< Threshold -> Bs;
		       true -> saturate_(Bs,1,TRef,Threshold)
		    end
	    end;
	{I1,X1} -> loop_1(Bs,I1,X1,N,Level,TRef,Threshold)
    end.


%% place mark before and after the decision variable
mark_eq_eval(Bs,V,Value,Level) ->
    ?dbg("~seq_eval: ~s/~s\n", 
	 [indent(Level),
	  varp_formula:fmt_var(Bs,V),
	  varp_formula:fmt_var(Bs,Value)]),
    varp_formula:mark(Bs,Level),
    case varp_formula:equal(Bs,V,Value) of
	true ->
	    varp_formula:mark(Bs,Level+1),
	    varp_formula:eval(Bs);
	false ->
	    false
    end.

eq_eval(Bs,V,Value,_D) ->
    ?dbg("~seq_eval: ~s/~s\n", 
	 [indent(_D),
	  varp_formula:fmt_var(Bs,V),
	  varp_formula:fmt_var(Bs,Value)]),
    varp_formula:equal(Bs,V,Value) andalso varp_formula:eval(Bs).

indent(D) -> lists:duplicate(D, $\s).

read_timer(infinity) -> infinity;
read_timer(TRef) when is_reference(TRef) ->
    case erlang:read_timer(TRef) of
	false -> 0;
	Remain -> Remain
    end.
