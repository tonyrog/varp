%%
%% Saturate with vector
%%

-module(varp_vsaturate).

-compile(export_all).
-import(varp_formula, [format_lit/2]).

-include("varp.hrl").

-define(dbg(F,A), ok).
%% -define(dbg(F,A), io:format((F),(A))).

-define(if1(Cond,Then),
	if Cond -> Then;
	   true -> ok
	end).

-type index()::integer().
-type var()::integer().
-type bs()::term().

-spec saturate(Bs::bs(), K::non_neg_integer()) -> false | bs().

saturate(Bs,K) when is_integer(K), K >= 1 ->
    varp_formula:info(Bs,"saturate-~w: pair:~w\n",
		      [K,varp_formula:getopt(Bs,pair)]),
    ?dbg("bound => ~s\n",
	 [varp_formula:fmt_bind_list(Bs,
				     varp_formula:get_bindings(Bs,0))]),
    erase(last_print),
    erase(last_bound),
    NB = varp_formula:number_of_bound(Bs),
    case loop(Bs,K) of
	false ->
	    varp_formula:info(Bs,"    | contradiction\n", []),
	    false;
	Bs1 ->
	    varp_formula:info(Bs, "    | bound: ~w [~w]\n",
			 [varp_formula:number_of_bound(Bs1) - NB,
			  varp_formula:number_of_unbound(Bs1)]),
	    Bs1
    end.

loop(Bs,K) ->
    case init_vector(Bs,K) of
	[] -> Bs;
	Vec ->
	    NB = varp_formula:number_of_bound(Bs),
	    loop(Bs,Vec,1,K,NB)
    end.

loop(Bs,Vec,I,K,NB) ->
    case saturate_vec(Bs,Vec) of
	false -> false;
	true ->
	    info(Bs,I,K),
	    case next_vector(Bs,Vec) of %% check all elements?
		[] ->
		    NB1 = varp_formula:number_of_bound(Bs),
		    D = varp_formula:getopt(Bs,threshold),
		    if NB1 - NB > D ->
			    loop(Bs,K);
		       true ->
			    Bs
		    end;
		Vec1 ->
		    loop(Bs,Vec1,I+1,K,NB)
	    end
    end.

%% progress info
info(Bs,I,K) ->
    NV = varp_formula:number_of_variables(Bs),
    B = varp_formula:number_of_bound(Bs),
    NU = NV-B,
    N = varp_math:binom(NU, K),
    P = trunc(1000*(I / N)),
    case {get(last_print),get(last_bound)} of
	{P,B} -> ok;
	_ ->
	    put(last_print,P),
	    put(last_bound,B),
	    varp_formula:info(Bs, "~.3f% [~w/~w]   \r",
			      [P/10,B,NV])
    end.

%% update vector with extra var if wanted and
%% check vector
-spec saturate_vec(Bs::bs(),Vec::[{index(),var()}]) -> boolean().

saturate_vec(Bs,Vec) ->
    Vec1 = case varp_formula:getopt(Bs,pair) of
	       true -> expand_vector(Vec,Bs);
	       false -> Vec
	   end,
    ?dbg("vector: {~s}\n", 
	 [varp_formula:fmt_var_list(Bs,[V||{_,V}<-Vec1])]),
    varp_formula:set_level(Bs, 1),
    Res = saturate_vec_(Bs,Vec1,2),
    ?dbg("bound => {~s}\n\n",
	 [varp_formula:fmt_bind_list(Bs,
				     varp_formula:get_bindings(Bs,1))]),
    %% remove mark but keep bindings
    varp_formula:remove_mark(Bs, 1),
    Res.

-spec saturate_vec_(Bs::bs(),Vec::[{index(),var()}],Level::integer()) ->
			   boolean().
saturate_vec_(Bs,[{_,X}|V],Level) ->
    case varp_formula:is_bound(Bs, X) of %% skip already bound variables
	true ->
	    ?dbg("~svar ~s is bound value=~w\n", 
		 [indent(Level),varp_formula:fmt_var(Bs,X),
		  varp_formula:value(Bs, X)]),
	    saturate_vec_(Bs,V,Level);
	false ->
	    saturate_vec__(Bs,X,V,Level)
    end;
saturate_vec_(_Bs,[],_Level) ->
    true.

saturate_vec__(Bs,X,V,Level) ->
    case mark_eq_eval(Bs,X,?FALSE,Level) of
	false ->
	    ?dbg("~scontradiction, undo ~w\n", [indent(Level),Level]),
	    varp_formula:undo_level(Bs,Level),
	    case eq_eval(Bs,X,?TRUE,Level) of
		false ->
		    ?dbg("~scontradiction\n", [indent(Level)]),
		    false;
		true  -> 
		    saturate_vec_(Bs,V,Level+1)
	    end;
	true ->
	    case saturate_vec_(Bs,V,Level+2) of
		false ->
		    ?dbg("~scontradiction, undo ~w\n", [indent(Level),Level]),
		    varp_formula:undo_level(Bs,Level),
		    eq_eval(Bs,X,?TRUE,Level);
		true ->
		    Xs = varp_formula:get_bindings(Bs,Level+1), %% + X=false!
		    ?dbg("~s~s/false: => {~s}\n", 
			 [indent(Level),
			  varp_formula:fmt_var(Bs,X),
			  varp_formula:fmt_bind_list(Bs,Xs)]),
		    varp_formula:undo_level(Bs,Level), %% (X=false)
		    
		    case mark_eq_eval(Bs,X,?TRUE,Level) of
			false ->
			    ?dbg("~scontradiction, undo ~w\n", 
				 [indent(Level),Level]),
			    varp_formula:undo_level(Bs,Level),  %% (X=true)
			    eq_eval(Bs,X,?FALSE,Level);
			true ->
			    ?dbg("~s~s/true: => {~s}\n",
				 [indent(Level),varp_formula:fmt_var(Bs,X),
				  varp_formula:fmt_bind_list(
				    Bs,
				    varp_formula:get_bindings(Bs,Level+1))]),
			    Ys = varp_formula:intersect(Bs, X, Xs),
			    ?if1(Ys =/= [],
				 begin io:format("intersect=~w\n", [Ys]) end),
			    ?dbg("~sintersect = {~s}\n", 
				 [indent(Level),
				  varp_formula:fmt_bind_list(Bs,Ys)]),
			    varp_formula:undo_level(Bs,Level),  %% undo (X=true)
			    install_bindings(Bs, Ys),
			    varp_formula:eval(Bs)
		    end
	    end
    end.

install_bindings(Bs, Bnds) ->
    Bcp = varp_option:getopt(bcp,Bs#bs.option),
    install_bindings(Bs, Bcp, Bnds).

install_bindings(Bs,Bcp,[{Y,W}|Xs]) when abs(W) =:= ?TRUE ->
    varp_formula:equal(Bs,Y,W),
    install_bindings(Bs,Bcp,Xs);
install_bindings(Bs,Bcp=false,[{Y,W}|Xs]) ->
    varp_formula:equal(Bs,Y,W),
    install_bindings(Bs,Bcp,Xs);
install_bindings(Bs,Bcp=true,[{Y,W}|Xs]) ->
    io:format("install clause (~s, ~s)\n", 
	      [format_lit(Bs,Y), format_lit(Bs, W)]),
    install_bindings(Bs,Bcp,Xs);
install_bindings(Bs,_Bcp,[]) ->
    Bs.

%% place mark before and after the decision variable
mark_eq_eval(Bs,V,Value,Level) ->
    ?dbg("~seq_eval: ~s/~s\n", 
	 [indent(Level),
	  varp_formula:fmt_var(Bs,V),
	  varp_formula:fmt_var(Bs,Value)]),
    varp_formula:set_level(Bs,Level),
    case varp_formula:equal(Bs,V,Value) of
	true ->
	    varp_formula:set_level(Bs,Level+1),
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

%%
%% initialize with first K unbound variables  [{Ik,Xk}, ..., {I1,X1}]
%%
init_vector(_Bs,0) ->
    [];
init_vector(Bs,K) ->
    case varp_formula:first_unbound(Bs) of
	false -> [];
	{I1,X1} -> init_vector_(Bs,K-1,I1,[{I1,X1}])
    end.

init_vector_(_Bs,0,_I,Vec) -> 
    Vec;
init_vector_(Bs,K,I0,Vec) ->
    case varp_formula:next_unbound(Bs,I0) of
	false -> Vec;
	{I1,X1} -> init_vector_(Bs,K-1,I1,[{I1,X1}|Vec])
    end.

%%
%% Select next vector return [] when no more vectors
%%
next_vector(Bs,Vec) ->
    next_vector_(Bs,Vec,0).

next_vector_(Bs,[{I,_Xi}|Vec],Max) ->
    case varp_formula:next_unbound(Bs,I) of
	false ->
	    Vec1 = next_vector_(Bs,Vec,I),
	    select_next(Bs,Vec1,Max);
	{J,_Xj} when Max>0, J >= Max ->
	    Vec1 = next_vector_(Bs,Vec,I),
	    select_next(Bs,Vec1,Max);
	Uj ->
	    [Uj|Vec]
    end;
next_vector_(_Bs,[],_MI) ->
    [].

select_next(_Bs,[],_Max) -> [];
select_next(Bs,Vec=[{K,_Xk}|_],Max) ->
    case varp_formula:next_unbound(Bs,K) of
	false -> [];
	{J,_Xj} when Max>0, J >= Max -> [];
	Uj -> [Uj|Vec]
    end.

%% add one extra element to "vector"
expand_vector([], _Bs) -> [];
expand_vector(Vec, Bs) ->
    J = lists:max([I || {I,_} <- Vec]),
    case varp_formula:next_unbound(Bs,J) of
	false -> Vec;
	{K,Xk} -> Vec++[{K,Xk}]
    end.
