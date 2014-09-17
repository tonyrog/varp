%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2010, Tony Rogvall
%%% @doc
%%%
%%% @end
%%% Created : 21 Jul 2010 by Tony Rogvall <tony@rogvall.se>

-module(prover).

-export([run_formula/1,run_formula/2]).
-export([prove_formula/1,prove_formula/2]).
-export([falsify_formula/1,falsify_formula/2,falsify/1,falsify/2]).
-export([satisfy_formula/1,satisfy_formula/2,satisfy/1,satisfy/2]).
-export([eval_formula/1, eval_formula/2]).
-export([saturate_formula/1, saturate_formula/2, saturate_formula/3]).
-export([backtrack_formula/1, backtrack_formula/2, backtrack/1]).

-compile(export_all).
-import(lists, [foldl/3, reverse/1]).

-define(TRUE,   1).
-define(FALSE, -1).
-define(dbg(F,A), ok).
%% -define(dbg(F,A), io:format((F),(A))).

-define(is_non_negative(N), (is_integer((N)) andalso ((N) >= 0))).

apply_opts(F, Bs) ->
    try case formula:getopt(value, Bs) of
	    none -> Bs;
	    true -> formula:equal(F, true, Bs);
	    false -> formula:equal(F, false, Bs)
	end of
	Bs1 ->
	    case formula:getopt(order, Bs) of
		none -> Bs1;
		Order -> formula:order(Order, Bs1)
	    end
    catch
	throw:contradiction ->
	    false
    end.

run_formula(F) ->
    run_formula(F, []).
run_formula(F,Opts) ->
    run(formula:build(F,Opts)).

run({F,Bs}) ->
    run(F, Bs).

run(undefined, Bs) ->
    no_models(Bs);
run({bool,X}, Bs) ->
    method(X,Bs);
run({_Sign,_N,Xs}, Bs) ->
    %% or just a dummy variable?
    {X,Bs1} = formula:vfold_op('or',{bool,?FALSE},Xs,Bs),
    method(X,Bs1).

    
prove_formula(F) ->
    prove_formula(F,[{method,count},{max,1},{order,reverse_depth}]).
prove_formula(F,Opts) ->
    case falsify_formula(F,Opts) of
	{0,_} -> true;
	0     -> true;
	undefined -> undefined;
	_ -> false
    end.

falsify_formula(F) ->
    falsify_formula(F,[{method,collect},{print,true},{order,depth}]).
falsify_formula(F,Opts) ->
    falsify(formula:build(F,Opts)).

falsify({F,Bs}) ->
    falsify(F, Bs).

falsify({bool,X}, Bs) ->
    Bs1 = formula:setopt(value,false,Bs),
    method(X,Bs1).

%%
%% Find one or more models to formula F
%%
satisfy_formula(F) ->
    satisfy_formula(F, [{method,collect},{print,true},{order,depth}]).

satisfy_formula(F,Opts) ->
    satisfy(formula:build(F,Opts)).

satisfy({F,Bs}) ->
    satisfy(F, Bs).

satisfy({bool,X}, Bs) ->
    Bs1 = formula:setopt(value,true,Bs),
    method(X,Bs1).

%%
%% Plain eval (saturate-0)
%%

eval_formula(F) ->
    eval_formula(F, []).

eval_formula(F,Opts) ->
    eval_bs(formula:build(F,Opts)).

eval_bs({F,Bs}) ->
    case apply_opts(F, Bs) of
	false -> false;
	Bs1 -> eval(Bs1)
    end.

%%
%% K saturate a triple set
%% 
saturate_formula(F) ->
    saturate_formula(1,F,[]).

saturate_formula(K,F) when is_integer(K), K>=0 ->
    saturate_formula(K,F,[]).

saturate_formula(K,F,Opts) ->
    {Fv,Bs} = formula:build(F,Opts),
    case apply_opts(Fv, Bs) of
	false -> false;
	Bs1 -> saturate(K,Bs1)
    end.

%% do plain backtrack over formula
backtrack_formula(F) ->
    backtrack_formula(F,[]).

backtrack_formula(F,Opts) ->
    backtrack(formula:build(F,Opts)).

backtrack({F,Bs}) ->
    backtrack(F,Bs).


%% Basic run
method(X,Bs) ->
    case apply_opts(X, Bs) of
	false -> no_models(Bs);
	Bs1 ->
	    case eval(Bs1) of
		false -> no_models(Bs);
		Bs2 ->
		    case one_model(Bs2) of
			false ->
			    case formula:getopt(saturate, Bs2) of
				0 ->
				    backtrack_bs(Bs2);
				K ->
				    case saturate_(K,Bs2) of
					false -> no_models(Bs);
					Bs3 ->
					    case one_model(Bs3) of
						false ->
						    backtrack_bs(Bs3);
						Bs3R-> Bs3R
					    end
				    end
			    end;
			Bs2R -> Bs2R
		    end
	    end
    end.

%% check if there is already a "unique" model
one_model(Bs) ->
    NV = formula:number_of_variables(Bs),
    NB = formula:number_of_bound(Bs),
    if NV =:= NB ->
	    Print = formula:getopt(print, Bs),
	    Mdl = formula:model(Bs),
	    print(Print,1,Mdl),
	    case formula:getopt(method, Bs) of
		collect -> {1,[Mdl]};
		count -> 1
	    end;
       true ->
	    false
    end.

no_models(Bs) ->
    case formula:getopt(partial, Bs) of
	true ->
	    %% print partial model, the variables bound
	    Mdl = formula:model(Bs),
	    io:format("partial: ~s\n",[format_model(Mdl)]);
	false ->
	    ok
    end,
    case formula:getopt(method, Bs) of
	collect -> {0,[]};
	count -> 0
    end.
    

eval_list([],Bs) ->
    eval(Bs);
eval_list([{F,V}|Ps],Bs) ->
    try formula:equal(F, V, Bs) of
	Bs1 -> eval_list(Ps,Bs1)
    catch
	throw:contradiction -> false
    end.

%% eval all triples (push all triples on queue)
eval(Bs) ->
    formula:info(Bs,"Eval:\n", []),
    case eval_(formula:enq_all(Bs)) of
	false ->
	    formula:info(Bs,"    | contradiction\n", []),
	    false;
	Bs1 ->
	    formula:info(Bs,"    | bound: ~w [~w]\n",
			 [formula:number_of_bound(Bs1) -
			      formula:number_of_bound(Bs),
			  formula:number_of_unbound(Bs1)]),
	    Bs1
    end.
	    

eval_list_([],Bs) ->
    eval_(Bs);
eval_list_([{F,V}|Ps],Bs) ->
    try formula:equal(F, V, Bs) of
	Bs1 -> eval_list_(Ps,Bs1)
    catch
	throw:contradiction -> false
    end.

eval_(Bs) ->
    try formula:eval(Bs) of
	Result -> Result
    catch
	throw:contradiction -> false
    end.


backtrack(F,Bs) ->
    formula:info(Bs,"BACKTRACK method=~w\n", [formula:getopt(method, Bs)]),
    case apply_opts(F, Bs) of
	false -> no_models(Bs);
	Bs1 -> backtrack_bs(eval(Bs1))
    end.

backtrack_bs(Bs) ->
    case formula:getopt(backtrack, Bs) of
	false -> 
	    no_models(Bs),
	    undefined;
	true ->
	    N     = formula:getopt(max, Bs),
	    Print = formula:getopt(print, Bs),
	    case formula:getopt(method, Bs) of
		collect ->
		    bt(Bs, fun({Count0,Acc},Bs1) ->
				   Count = Count0+1,
				   Mdl = formula:model(Bs1),
				   print(Print,Count,Mdl),
				   Continue = (N =:= 0) orelse (Count < N),
				   {Continue,{Count,[Mdl|Acc]}}
			   end, {0,[]});
		count ->
		    bt(Bs, fun(Count0,Bs1) -> 
				   Count = Count0+1,
				   if Print =:= false -> ok;
				      true ->
					   Mdl = formula:model(Bs1),
					   print(Print,Count,Mdl)
				   end,
				   if Count rem 1000 =:= 0 ->
					   io:format("~w\n", [Count]);
				      true -> 
					   ok
				   end,
				   Continue = (N =:= 0) orelse (Count < N),
				   {Continue,Count} 
			   end, 0)
	    end
    end.

print(true,I,Bindings) ->
    Bindings1 = filter_bindings(Bindings),
    io:format("~w: ~s\n",
	      [I,concat([ format_binding(Bound) || Bound <- Bindings1 ], ",")]);
print(literal,I,Bindings) ->
    Bindings1 = filter_bindings(Bindings),
    io:format("~w: ~s\n",
	      [I,concat([ format_binding(Bound) || Bound <- Bindings1 ], ",")]);
print(model,I,Bindings) ->
    Bindings1 = filter_bindings(Bindings),
    io:format("~w: ~s\n",
	      [I,concat([ format_binding(Bound) || 
			    Bound <- Bindings1,
			    element(2,Bound) =/= false ], ",")]);
print(umodel,I,Bindings) ->
    io:format("~w: ~s\n",
	      [I,concat([ format_binding(Bound) || 
			    Bound <- Bindings,
			    element(2,Bound) =/= false ], ",")]);
print(erlang,_I,Bindings) ->
    Bindings1 = filter_bindings(Bindings),
    io:format("~w.\n", [Bindings1]);
print(false,_I,_Bindings) ->
    ok.

filter_bindings(Bindings) ->
    [ B || B={{p,V,_},_} <- Bindings, hd(atom_to_list(V)) =/= $_].

format_model(Model) ->
    concat([ format_binding(Bound) || Bound <- Model ], ",").

format_binding({Var,Value}) ->
    VarFmt = format_var(Var),
    if Value =:= true -> VarFmt;
       Value =:= false -> [$~|VarFmt];
       is_integer(Value) -> [VarFmt,"=",integer_to_list(Value)]
    end.

%% format_var(V) when is_atom(V) ->
%%    [atom_to_list(V)];
format_var({p,V,[]}) ->
    [atom_to_list(V)];
format_var({p,V,As}) ->
    [atom_to_list(V),"(", concat([io_lib:format("~w",[X])||X<-As], ","), ")"].

concat([], _) -> [];
concat([H],_) -> [H];
concat([H|T],S) -> [H,S | concat(T,S)].

%%
%% Explicit recursion version, allow times backtracking
%% mix alogorithms etc.
%%
bt(Bs,Func,Acc) ->
    case bt_init(Bs) of
	{model,Bs,_Stack} ->
	    {_,Acc1} = Func(Acc,Bs),
	    Acc1;
	{true,Stack} ->
	    {_,Acc1} = bt_loop(Stack,Func,Acc),
	    Acc1;
	false ->
	    Acc
    end.

bt_loop(Stack,Func,Acc) ->
    case bt_next(Stack) of
	{model,Bs,Stack1} ->
	    case Func(Acc,Bs) of
		{true,Acc1} ->
		    bt_loop(Stack1,Func,Acc1);
		{false,Acc1} ->
		    {false,Acc1}
	    end;
	{true,Stack1} ->
	    bt_loop(Stack1,Func,Acc);
	false ->
	    {false,Acc}
    end.

%%
%% Stack: [ {I,Xi,[true,false],D,Bs} ]
%%
bt_init(Bs) ->
    I0 = formula:first_init(Bs),
    ?dbg("I0=~w N=~w\n", [I0,formula:number_of_variables(Bs)]),
    Next = formula:next_unbound(I0,Bs),
    ?dbg("Next=~p\n",[Next]),
    case Next  of
	false  -> {model,Bs,[]};
	{I,Xi} -> {true,[{I,Xi,[true,false],0,Bs}]}
    end.

bt_next([{_I,_Xi,[],_D,_Bs}|Stack]) ->
    bt_next(Stack);
bt_next([{I,Xi,[V|Vs],D,Bs0} | Stack]) ->
    Bs = formula:set_bt_depth(D, Bs0),
    if D < 9 ->
	    formula:debug(Bs, "~*.. s: ~s\n",
			  [D*2, "", formula:fmt_var(Xi,Bs)]);
       true ->
	    ok
    end,
    ?dbg("bt: ~w = ~w\n", [Xi,V]),
    case equal_eval(Xi,V,Bs) of
	false -> %% hook this?
	    bt_next([{I,Xi,Vs,D,Bs}|Stack]);
	Bs1 ->
	    case formula:next_unbound(I,Bs1) of
		false -> 
		    {model,Bs1,[{I,Xi,Vs,D,Bs}|Stack]};
		{J,Xj} ->
		    {true,[{J,Xj,[true,false],D+1,Bs1},{I,Xi,Vs,D,Bs}|Stack]}
	    end
    end;
bt_next([]) ->
    false.

%%
%% K-saturate:
%%
%% Algorithm:
%%   Initialize with a vector of K unbound variables (if possible) say 3
%%   [ Y3 Y2 Y1 ]
%%   run test-3 over the selected vector:
%%   Selecte a new vector (like next)
%%   [ Y4 Y2 Y1 ]
%%   until Yn then:
%%   [ Y4 Y3 Y1 ]
%%   (and so on)
%%

%%
%% initialize with first K unbound variables  [{Ik,Xk}, ..., {I1,X1}]
%%
init_vector(0, _Bs) ->
    [];
init_vector(K, Bs) ->
    case formula:first_unbound(Bs) of
	false -> [];
	{I1,X1} -> init_vector_(K-1,I1,[{I1,X1}],Bs)
    end.

init_vector_(0,_I,Vec,_Bs) -> 
    Vec;
init_vector_(K,I0,Vec,Bs) ->
    case formula:next_unbound(I0,Bs) of
	false -> Vec;
	{I1,X1} -> init_vector_(K-1,I1,[{I1,X1}|Vec],Bs)
    end.

%%
%% Select next vector return [] when no more vectors
%%
next_vector(Vec, Bs) ->
    Vec1 = next_vector_(Vec, Bs, 0),
    %% io:format("next(~w) = ~w\n", [Vec, Vec1]),
    Vec1.
    
next_vector_([{I,_Xi}|Vec], Bs, D) ->
    case nth_unbound(D,I,Bs) of
	false ->
	    case next_vector_(Vec, Bs, D+1) of
		[] -> [];
		Vec1=[{J,_Xj}|_] ->
		    case formula:next_unbound(J,Bs) of
			false -> [];
			{K,Xk} ->
			    [{K,Xk}|Vec1]
		    end
	    end;
	{J,Xj} -> [{J,Xj}|Vec]
    end;
next_vector_([], _Bs, _) ->
    [].

nth_unbound(0,I,Bs) ->
    formula:next_unbound(I,Bs);
nth_unbound(N,I,Bs) ->
    case formula:next_unbound(I,Bs) of
	false -> false;
	{I1,_X1} -> nth_unbound(N-1,I1,Bs)
    end.


%% add one extra element to "vector"
expand_vector([], _Bs) -> [];
expand_vector(Vec, Bs) ->
    J = lists:max([I || {I,_} <- Vec]),
    case formula:next_unbound(J,Bs) of
	false -> Vec;
	{K,Xk} -> Vec++[{K,Xk}]
    end.

    
saturate(0,Bs) ->
    eval(Bs);
saturate(K,Bs) when is_integer(K), K >= 1 ->
    case eval(Bs) of
	false -> false;
	Bs1 -> saturate_(K, Bs1)
    end.

saturate_(K,Bs) when is_integer(K), K >= 1 ->
    formula:info(Bs,"Saturate-~w: pair:~w\n", 
		 [K,formula:getopt(pair,Bs)]),
    erase(last_print),
    erase(last_bound),
    NB = formula:number_of_bound(Bs),
    case saturate_loop(K,Bs) of
	false ->
	    formula:info(Bs,"    | contradiction\n", []),
	    false;
	Bs1 ->
	    formula:info(Bs, "    | bound: ~w [~w]\n",
			 [formula:number_of_bound(Bs1) - NB,
			  formula:number_of_unbound(Bs1)]),
	    Bs1
    end.

saturate_loop(K, Bs) ->
    case init_vector(K, Bs) of
	[] -> Bs;
	Vec ->
	    NB = formula:number_of_bound(Bs),
	    saturate_loop(Vec,1,K,NB,Bs)
    end.

saturate_loop(Vec,I,K,NB,Bs) ->
    case saturate_vec(Vec, Bs) of
	false -> false;
	Bs1 ->
	    saturate_info(I,K,Bs1),
	    case next_vector(Vec, Bs1) of %% check all elements?
		[] ->
		    NB1 = formula:number_of_bound(Bs1),
		    D = formula:getopt(threshold, Bs1),
		    if NB1 - NB > D ->
			    saturate_loop(K, Bs1);
		       true ->
			    Bs1
		    end;
		Vec1 ->
		    %% Ks = varp_math:factorial(K),
		    Ks = 1,
		    saturate_loop(Vec1,I+Ks,K,NB,Bs1)
	    end
    end.

%% progress info
saturate_info(I,K,Bs) ->
    NV = formula:number_of_variables(Bs),
    B = formula:number_of_bound(Bs),
    NU = NV-B,
    N = varp_math:binom(NU, K),
    P = trunc(10000*(I / N)),
    case {get(last_print),get(last_bound)} of
	{P,B} -> ok;
	_ ->
	    put(last_print,P),
	    put(last_bound,B),
	    formula:info(Bs, "~.3f% [~w/~w]   \r", [P/100,B,NV])
    end.

%% Saturate for all permutations of vector
saturate_perm_vec(Vec, Bs) ->
    VecList = perms(Vec),
    saturate_vec_list(VecList, Bs).

saturate_vec_list([Vec|VecList], Bs) ->
    case saturate_vec(Vec, Bs) of
	false -> false;
	Bs1 -> saturate_vec_list(VecList, Bs1)
    end;
saturate_vec_list([], Bs) ->
    Bs.

perms([]) -> [[]];
perms(L) -> [[H|T] || H <- L, T <- perms(L--[H])].
    

%% update vector with extra var if wanted and
%% check vector
saturate_vec(Vec, Bs) ->
    case formula:getopt(pair,Bs) of
	false ->
	    %% io:format("saturate_vec: ~w\n", [Vec]),
	    formula:debug(Bs, "vector: ~p\n", [Vec]),
	    saturate_vec_(Vec, Bs);
	true ->
	    Vec1 = expand_vector(Vec,Bs),
	    formula:debug(Bs, "vector: ~p\n", [Vec1]),
	    %% io:format("saturate_vec: ~w\n", [Vec1]),
	    saturate_vec_(Vec1, Bs)
    end.

saturate_vec_([{_,X}|V], Bs) ->
    case equal_mark_eval(X,true,Bs) of
	false ->
	    case equal_eval(X,false,Bs) of
		false -> false;
		BsF -> saturate_vec_(V, BsF)
	    end;
	BsT0 ->
	    case saturate_vec_(V, BsT0) of
		false ->
		    equal_eval(X,false,Bs);
		BsT ->
		    case equal_mark_eval(X,false,Bs) of
			false ->
			    BsT;
			BsF0 ->
			    case saturate_vec_(V,BsF0) of
				false -> BsT;
				BsF ->
				    Bound = formula:latest_bound(BsT),
				    Ps = intersect(X,Bound,BsT,BsF),
				    eval_list_(Ps,Bs)
			    end
		    end
	    end
    end;
saturate_vec_([], Bs) ->
    Bs.

%%
%% @doc
%%    Intersect a binding list with variables bound in environment
%%    Bound is a list of bound variables either for X/0 or X/1
%%    BsT is the environement for which X/1
%%    BsF is the environement for which X/0
%% @end
%%
intersect(X, [Y|Bound], BsT, BsF) ->
    VT  = formula:value(Y,BsT),
    VF  = formula:value(Y,BsF),
    if VT =:= VF ->
	    [{Y,VT}|intersect(X,Bound,BsT,BsF)];
       VT =:= ?TRUE,VF =:= ?FALSE ->
	    [{X,Y}|intersect(X,Bound,BsT,BsF)];
       VT =:= ?FALSE,VF =:= ?TRUE ->
	    [{X,-Y}|intersect(X,Bound,BsT,BsF)];
       true ->
	    VT1 = formula:value(VT, BsF),
	    if VF =:= VT1 ->
		    VF1 = formula:value(VF, BsT),
		    if VT =:= VF1 ->
			    %% all matching bindings in class?
			    [{Y,VT}|intersect(X,Bound,BsT,BsF)];
		       true ->
			    intersect(X,Bound,BsT,BsF)
		    end;
	       true ->
		    intersect(X,Bound,BsT,BsF)
	    end
    end;
intersect(_X,[],_BsT,_BsF) ->
    [].

equal_eval(V, Value, Bs) ->
    ?dbg("eval_equal: ~s = ~s\n", 
	 [formula:fmt_var(V,Bs),formula:fmt_var(Value,Bs)]),
    try formula:equal(V, Value, Bs) of
	Bs1 ->
	    try formula:eval(Bs1) of
		Result -> Result
	    catch
		throw:contradiction -> false
	    end
    catch
	throw:contradiction -> false
    end.

equal_mark_eval(V, Value, Bs) ->
    ?dbg("eval_equal: ~s = ~s\n", 
	 [formula:fmt_var(V,Bs),formula:fmt_var(Value,Bs)]),
    try formula:equal(V, Value, Bs) of
	Bs1 ->
	    Bs2 = formula:mark(Bs1),
	    try formula:eval(Bs2) of
		Result -> Result
	    catch
		throw:contradiction -> false
	    end
    catch
	throw:contradiction -> false
    end.
    

