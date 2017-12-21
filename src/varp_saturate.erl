%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2017, Tony Rogvall
%%% @doc
%%%    Run saturation
%%% @end
%%% Created : 19 Dec 2017 by Tony Rogvall <tony@rogvall.se>

-module(varp_saturate).

-compile(export_all).

-define(dbg(F,A), ok).
%%-define(dbg(F,A), io:format((F),(A))).

%%-type index()::integer().
%% -type var()::integer().
-type bs()::term().

-spec saturate(Bs::bs(), K::non_neg_integer()) -> false | bs().
	    
saturate(Bs, 1) ->
    case varp_formula:first_unbound(Bs) of
	false -> Bs;
	{I,X} -> loop_1(Bs,I,X,1)
    end;
saturate(Bs, K) when is_integer(K), K >= 1 ->
    case varp_formula:first_unbound(Bs) of
	false -> Bs;
	{I,X} -> loop_k(Bs,I,X,K,1)
    end.

loop_k(Bs,I,X,K,Mark) ->
    case mark_eq_eval(Bs,X,false,Mark) of
	false ->
	    ?dbg("~scontradiction, undo ~w\n", [indent(Mark),Mark]),
	    varp_formula:undo(Bs,Mark),
	    case eq_eval(Bs,X,true,Mark) of
		false ->
		    ?dbg("~scontradiction\n", [indent(Mark)]),
		    false;
		true  -> 
		    loop_k_next(Bs,I,X,K,Mark)
	    end;
	true ->
	    case loop_k_next(Bs,I,X,K-1,Mark+2) of
		false ->
		    ?dbg("~scontradiction, undo ~w\n", [indent(Mark),Mark]),
		    varp_formula:undo(Bs,Mark),
		    case eq_eval(Bs,X,true,Mark) of
			false ->
			    ?dbg("~scontradiction\n", [indent(Mark)]),
			    false;
			true  -> 
			    loop_k_next(Bs,I,X,K,Mark)
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
			    loop_k_next(Bs1,I,X,K,Mark);
			true ->
			    case loop_k_next(Bs1,I,X,K-1,Mark+2) of
				false ->
				    ?dbg("~scontradiction, undo ~w\n", 
					 [indent(Mark),Mark]),
				    varp_formula:undo(Bs1,Mark),  %% (X=true)
				    eq_eval(Bs1,X,false,Mark),
				    loop_k_next(Bs1,I,X,K,Mark);
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
				    loop_k_next(Bs2,I,X,K,Mark)
			    end
		    end
	    end
    end.

loop_k_next(Bs,I,_X,K,Mark) ->
    case varp_formula:next_unbound(Bs,I) of
	false -> Bs;
	{I1,X1} when K>1   -> loop_k(Bs,I1,X1,K,Mark);
	{I1,X1} when K=:=1 -> loop_1(Bs,I1,X1,Mark)
    end.

loop_1(Bs, I, X, Mark) ->
    case mark_eq_eval(Bs,X,false,Mark) of
	false ->
	    ?dbg("~scontradiction, undo ~w\n", [indent(Mark),Mark]),
	    varp_formula:undo(Bs,Mark),
	    case eq_eval(Bs,X,true,Mark) of
		false ->
		    ?dbg("~scontradiction\n", [indent(Mark)]),
		    false;
		true  -> 
		    loop_1_next(Bs, I, X, Mark)
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
		    loop_1_next(Bs, I, X, Mark);
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
		    loop_1_next(Bs, I, X, Mark)		    
	    end
    end.

loop_1_next(Bs, I, _X, Mark) ->
    case varp_formula:next_unbound(Bs,I) of
	false -> Bs;
	{I1,X1} -> loop_1(Bs, I1, X1, Mark)
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

    
