%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2017, Tony Rogvall
%%% @doc
%%%    Run saturation
%%% @end
%%% Created : 19 Dec 2017 by Tony Rogvall <tony@rogvall.se>

-module(varp_saturate).

-compile(export_all).

-define(dbg(F,A), ok).
%% -define(dbg(F,A), io:format((F),(A))).

%%-type index()::integer().
%% -type var()::integer().
-type bs()::term().

-define(START_MARK, 2).

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
		   ?START_MARK,TRef,Threshold)
    end;
saturate_(Bs,K,TRef,Threshold) when is_integer(K), K >= 1 ->
    case varp_formula:first_unbound(Bs) of
	false -> Bs;
	{I,X} -> loop_k(Bs,I,X,K,
			varp_formula:number_of_bound(Bs),			
			?START_MARK,TRef,Threshold)
    end.

loop_k(Bs,I,X,K,N,Mark,TRef,Threshold) ->
    case mark_eq_eval(Bs,X,false,Mark) of
	false ->
	    ?dbg("~scontradiction, undo ~w\n", [indent(Mark),Mark]),
	    varp_formula:undo(Bs,Mark),
	    case eq_eval(Bs,X,true,Mark) of
		false ->
		    ?dbg("~scontradiction\n", [indent(Mark)]),
		    false;
		true  -> 
		    loop_k_next(Bs,I,X,K,N,Mark,TRef,Threshold)
	    end;
	true ->
	    N1 = varp_formula:number_of_bound(Bs),
	    case loop_k_next(Bs,I,X,K-1,N1,Mark+2,TRef,Threshold) of
		false ->
		    ?dbg("~scontradiction, undo ~w\n", [indent(Mark),Mark]),
		    varp_formula:undo(Bs,Mark),
		    case eq_eval(Bs,X,true,Mark) of
			false ->
			    ?dbg("~scontradiction\n", [indent(Mark)]),
			    false;
			true  -> 
			    loop_k_next(Bs,I,X,K,N,Mark,TRef,Threshold)
		    end;
		Bs1 ->
		    Xs = varp_formula:get_bindings(Bs1,Mark+1),
		    ?dbg("~s~s/false: => {~s}\n", 
			 [indent(Mark),
			  varp_formula:fmt_var(Bs1,X),
			  varp_formula:fmt_bind_list(Bs1,Xs)]),
		    varp_formula:undo(Bs1,Mark), %% (X=false)

		    case mark_eq_eval(Bs1,X,true,Mark) of
			false ->
			    ?dbg("~scontradiction, undo ~w\n", 
				 [indent(Mark),Mark]),
			    varp_formula:undo(Bs1,Mark),  %% (X=true)
			    eq_eval(Bs1,X,false,Mark),
			    loop_k_next(Bs1,I,X,K,N,Mark,TRef,Threshold);
			true ->
			    N2 = varp_formula:number_of_bound(Bs),
			    case loop_k_next(Bs1,I,X,K-1,N2,Mark+2,TRef,Threshold) of
				false ->
				    ?dbg("~scontradiction, undo ~w\n", 
					 [indent(Mark),Mark]),
				    varp_formula:undo(Bs1,Mark),  %% (X=true)
				    eq_eval(Bs1,X,false,Mark),
				    loop_k_next(Bs1,I,X,K,N,Mark,TRef,Threshold);
				Bs2 ->
				    ?dbg("~s~s/true: => {~s}\n",
					 [indent(Mark),varp_formula:fmt_var(Bs2,X),
					  varp_formula:fmt_bind_list(
					    Bs2,
					    varp_formula:get_bindings(Bs2,Mark+1))]),
				    Ys = varp_formula:intersect(Bs2, X, Xs),
				    ?dbg("~sintersect = {~s}\n", 
					 [indent(Mark),
					  varp_formula:fmt_bind_list(Bs2,Ys)]),
				    varp_formula:undo(Bs2,Mark),  %% undo (X=true)
				    _ = [ varp_formula:equal(Bs2,Y,W) || {Y,W} <- Ys],
				    varp_formula:eval(Bs2),
				    loop_k_next(Bs2,I,X,K,N,Mark,TRef,Threshold)
			    end
		    end
	    end
    end.

loop_k_next(Bs,I,_X,K,N,Mark,TRef,Threshold) ->
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
	{I1,X1} when K>1   -> loop_k(Bs,I1,X1,K,N,Mark,TRef,Threshold);
	{I1,X1} when K=:=1 -> loop_1(Bs,I1,X1,N,Mark,TRef,Threshold)
    end.

loop_1(Bs,I,X,N,Mark,TRef,Threshold) ->
    case mark_eq_eval(Bs,X,false,Mark) of
	false ->
	    ?dbg("~scontradiction, undo ~w\n", [indent(Mark),Mark]),
	    varp_formula:undo(Bs,Mark),
	    case eq_eval(Bs,X,true,Mark) of
		false ->
		    ?dbg("~scontradiction\n", [indent(Mark)]),
		    false;
		true  -> 
		    loop_1_next(Bs,I,X,N,Mark,TRef,Threshold)
	    end;
	true ->
	    Xs = varp_formula:get_bindings(Bs,Mark+1),
	    ?dbg("~s~s/false: => {~s}\n", 
		 [indent(Mark),
		  varp_formula:fmt_var(Bs,X),
		  varp_formula:fmt_bind_list(Bs,Xs)]),
	    varp_formula:undo(Bs,Mark), %% (X=false)
		    
	    case mark_eq_eval(Bs,X,true,Mark) of
		false ->
		    ?dbg("~scontradiction, undo ~w\n", 
			 [indent(Mark),Mark]),
		    varp_formula:undo(Bs,Mark),  %% (X=true)
		    eq_eval(Bs,X,false,Mark),
		    loop_1_next(Bs,I,X,N,Mark,TRef,Threshold);
		true ->
		    ?dbg("~s~s/true: => {~s}\n",
			 [indent(Mark),varp_formula:fmt_var(Bs,X),
			  varp_formula:fmt_bind_list(
			    Bs,
			    varp_formula:get_bindings(Bs,Mark+1))]),
		    Ys = varp_formula:intersect(Bs, X, Xs),
		    ?dbg("~sintersect = {~s}\n", 
			 [indent(Mark),
			  varp_formula:fmt_bind_list(Bs,Ys)]),
		    varp_formula:undo(Bs,Mark),  %% undo (X=true)
		    _ = [ varp_formula:equal(Bs,Y,W) || {Y,W} <- Ys],
		    varp_formula:eval(Bs),
		    loop_1_next(Bs,I,X,N,Mark,TRef,Threshold)
	    end
    end.

loop_1_next(Bs,I,_X,N,Mark,TRef,Threshold) ->
    case varp_formula:next_unbound(Bs,I) of
	false ->
	    case read_timer(TRef) of
		0 -> Bs;
		_ ->
		    N1 = varp_formula:number_of_bound(Bs),
		    if N1 - N =< Threshold -> Bs;
		       true -> saturate_(Bs,1,TRef,Threshold)
		    end
	    end;
	{I1,X1} -> loop_1(Bs,I1,X1,N,Mark,TRef,Threshold)
    end.


%% place mark before and after the decision variable
mark_eq_eval(Bs,V,Value,Mark) ->
    ?dbg("~seq_eval: ~s/~s\n", 
	 [indent(Mark),
	  varp_formula:fmt_var(Bs,V),
	  varp_formula:fmt_var(Bs,Value)]),
    varp_formula:mark(Bs,Mark),
    case varp_formula:equal(Bs,V,Value) of
	true ->
	    varp_formula:mark(Bs,Mark+1),
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
