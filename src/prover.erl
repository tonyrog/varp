%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2010, Tony Rogvall
%%% @doc
%%%
%%% @end
%%% Created : 21 Jul 2010 by Tony Rogvall <tony@rogvall.se>

-module(prover).

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

    
prove_formula(F) ->
    case falsify_formula(F,[{method,count},{max,1},{order,reverse_depth}]) of
	0 -> true;
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
	false ->
	    no_models(Bs);
	Bs1 -> 
	    case eval(Bs1) of
		false ->
		    no_models(Bs);
		Bs2 ->
		    case formula:getopt(saturate, Bs2) of
			0 -> 
			    backtrack_bs(Bs2);
			K ->
			    case saturate_(K,Bs2) of
				false -> 
				    no_models(Bs);
				Bs3 ->
				    backtrack_bs(Bs3)
			    end
		    end
	    end
    end.

no_models(Bs) ->
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
	    formula:info(Bs,"    | bound: ~w\n",
			[formula:number_of_bound(Bs1) -
			     formula:number_of_bound(Bs)]),
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
    N     = formula:getopt(max, Bs),
    Print = formula:getopt(print, Bs),
    case formula:getopt(method, Bs) of
	collect ->
	    bt(Bs, fun({Count0,Acc},Bs1) ->
			   Mdl = formula:model(Bs1),
			   Count = Count0+1,
			   if Print -> 
				   io:format("~w: ~w\n", [Count,Mdl]);
			      true -> ok
			   end,
			   Continue = (N =:= 0) orelse (Count < N),
			   {Continue,{Count,[Mdl|Acc]}}
		   end, {0,[]});
	count ->
	    bt(Bs, fun(Count0,_Bs1) -> 
			   Count = Count0+1,
			   if Count rem 1000 =:= 0 ->
				   io:format("~w\n", [Count]);
			      true -> 
				   ok
			   end,
			   Continue = (N =:= 0) orelse (Count < N),
			   {Continue,Count} 
		   end, 0)
    end.

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
next_vector([{I,_Xi}|Vec], Bs) ->
    case formula:next_unbound(I,Bs) of
	false ->
	    case next_vector(Vec, Bs) of
		[] -> [];
		[{J,Xj}|Vec1] ->
		    case formula:next_unbound(J,Bs) of
			false -> [];
			{K,Xk} -> [{K,Xk},{J,Xj}|Vec1]
		    end
	    end;
	{I1,Xi1} -> [{I1,Xi1}|Vec]
    end;
next_vector([], _Bs) ->
    [].

%% add one extra element to "vector"
expand_vector([{J,Xj}],Bs) ->
    case formula:next_unbound(J,Bs) of
	false -> [];
	{K,Xk} -> [{J,Xj},{K,Xk}]
    end;
expand_vector([X|Xs], Bs) ->
    [X | expand_vector(Xs,Bs)];
expand_vector([], _Bs) ->
    [].
    
saturate(0,Bs) ->
    eval(Bs);
saturate(K,Bs) when is_integer(K), K >= 1 ->
    case eval(Bs) of
	false -> false;
	Bs1 -> saturate_(K, Bs1)
    end.

saturate_(K,Bs) when is_integer(K), K >= 1 ->
    formula:info(Bs,"Saturate-~w: pair:~w\n", 
		 [K,formula:getopt(saturate_pair,Bs)]),
    erase(last_print),
    Vec = init_vector(K, Bs),
    NB = formula:number_of_bound(Bs),
    NU = formula:number_of_unbound(Bs),
    N  = imath:binom(NU, length(Vec)),
    case saturate_loop(Vec,1,N,K,NB,Bs) of
	false -> 
	    formula:info(Bs,"    | contradiction\n", []),
	    false;
	Bs1 ->
	    formula:info(Bs, "    | bound: ~w\n",
			 [formula:number_of_bound(Bs1) - NB]),
	    Bs1
    end.


saturate_loop(Vec,I,N,K,NB,Bs) ->
    %% io:format("saturate: V=~p,I=~w,N=~w,K=~w,NB=~w\n", [Vec,I,N,K,NB]),
    case saturate_vec(Vec, Bs) of
	false -> false;
	Bs1 ->
	    P = trunc(1000*(I / N)),
	    case get(last_print) of
		P -> ok;
		_P0 ->
		    put(last_print,P),
		    B = formula:number_of_bound(Bs1),
		    NV = formula:number_of_variables(Bs1),
		    formula:info(Bs, "~.2f% [~w/~w]   \r", [P/10,B,NV])
	    end,
	    case next_vector(Vec, Bs1) of %% check all elements?
		[] ->
		    NB1 = formula:number_of_bound(Bs1),
		    D = formula:getopt(saturate_threshold, Bs1),
		    if NB1 - NB > D ->
			    case init_vector(K, Bs1) of
				[] -> Bs1;
				Vec1 ->
				    NU = formula:number_of_unbound(Bs),
				    N1 = imath:binom(NU, length(Vec1)),
				    saturate_loop(Vec1,1,N1,K,NB1,Bs1)
			    end;
		       true ->
			    Bs1
		    end;
		Vec1 ->
		    saturate_loop(Vec1,I+1,N,K,NB,Bs1)
	    end
    end.

%% update vector with extra var if wanted and
%% check vector
saturate_vec(Vec, Bs) ->
    case formula:getopt(saturate_pair,Bs) of
	false ->
	    saturate_vec_(Vec, Bs);
	true ->
	    Vec1 = expand_vector(Vec,Bs),
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


skolem_perm(F,Const,Ws) ->
    lists:foreach(
      fun(WsOrder) ->
	      {_,Ts,_} = skolem(F,Const,WsOrder),
	      io:format("Order=~w, Length=~w\n", [WsOrder,length(Ts)])
      end, permut:all(Ws)).
		    
%%
%% skolem build of a function
%% method:
%%
%% Formula Y0=F0(x1,...xn)
%%
%% Y1 = F0(x1/TRUE,...xn)
%% F1(x2,....xn) = F0(x1/Y1,...xn)
%%
%% Y2 = F1(x2/TRUE,...xn)
%% F2(x3,....xn) = F1(x2/Y2,...xn)
%% ...
%% Yi = Fi(xi/TRUE,...xn)
%% Fi+1(xi+1,..xn) = Fi(xi/Yi,..xn)
%%
%% SAT (xi/TRUE)  iff Fn is true
%% TAUT (xi/FALSE) iff Fn is false
%%
skolem(F0) ->
    skolem(F0,true).

skolem(F0,Const) -> 
    skolem(F0,Const,[]).

skolem(F0,true,Ws) ->
    skolem_(F0,?TRUE,Ws);
skolem(F0,false,Ws) ->
    skolem_(F0,?FALSE,Ws).

skolem_(F0,Const,Ws) ->
    {{bool,Y0},Bs0} = formula:build(F0,[]),
    {Ts,Bs} = formula:triples(Bs0),
    io:format("skolem: #triples=~w\n", [length(Ts)]),
    {Ts1,Bs1} = reduce_triples(Ts,Bs),
    io:format("skolem: reduced #triples=~w\n", [length(Ts1)]),
    try formula:eval(Ts1, Bs1) of
	{Ts2,Bs2} -> 
	    io:format("skolem: eval #triples=~w\n", [length(Ts2)]),
	    Vs = formula:model_variables(Bs2,Ws),
	    skolem(Y0,Const,Vs,Ts2,Bs2)
    catch
	throw:contradiction -> false
    end.


skolem(Y0,Const,[Xi|Xs],Ts,Bs) ->
    io:format("~s: length = ~w\n", [formula:fmt_var(Xi,Bs), length(Ts)]),
    case formula:value(Xi,Bs) of
	?TRUE  -> skolem(Y0,Const,Xs,Ts,Bs);
	?FALSE -> skolem(Y0,Const,Xs,Ts,Bs);
	Xiv ->
	    {Y1,_Ts1,Bs1} = copy_triples(Y0, Ts, Bs, [{Xi,Const}]),
	    %% Ts++Ts1,
	    case equal_eval(Xiv, Y1,  Bs1) of
		{[],Bs2} ->
		    skolem_return(Y0,[],Bs2);
		{Ts2,Bs2} ->
		    Y01 = formula:value(Y0,Bs2),
		    skolem(Y01,Const,Xs,Ts2,Bs2);
		false ->
		    false
	    end
    end;
skolem(Y0, _Const, [], Ts, Bs) ->
    skolem_return(Y0, Ts, Bs).

skolem_return(Y,Ts,Bs) ->
    V = formula:value(Y,Bs),
    io:format("~s: #triples ~w\n", [formula:fmt_var(V,Bs),length(Ts)]),
    case V of
	?TRUE ->  {true, Ts, Bs};
	?FALSE -> {false, Ts, Bs};
	V -> {V, Ts, Bs}
    end.

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
    
%%
%% Copy triples and find common sub-formulas
%% V = variable value map         V[a] = b
%% W = variable translation table W[x] = y
%%
%%   each triple in T in Ts0 {
%%       x = V[T.x], y = V[t.y], z = V[T.z]
%%       FUNC[y,z]  = x   (may have to bind multiple triples! x's)
%%       W[x]=x, W[y]=y, W[z]=z
%%       COMP[x]=!is_input(x)
%%       COMP[y]=!is_input(y)
%%       COMP[z]=!is_input(z)
%%       Ts1 += {x,y,z}
%%    }
%%
%%   Make the substitution by:
%%     W[xi] = true (or false)
%%     COMP[xi] = false
%%
%%   each triple T in Ts1 {
%%     if (COMP[y] or COMP[z]) { Ts2 += T }
%%     else {
%%       y' = W[y]
%%       z' = W[z]
%%       if (COMP[x]) {
%%          if (exist FUNC[y',z']) {
%%             W[x] = x' = FUNC[y',z']
%%          else {
%%             x' = fresh(),
%%             W[x] = x'
%%             FUNC[y',z'] = x'
%%          }
%%          COMP[x] = false
%%          Qs += {x',y',z'}
%%       }
%%       else {
%%          x' = W[x]
%%          Qs += {x', y', z'}
%%       }
%%     }
%%   }
%%   repeat while Ts2 != {} Ts = Ts2
%%   result Qs
%%   
%%
copy_triples(F, [], Bs, _Sub) ->
    {F,[],Bs};
copy_triples(F, Ts, Bs, Sub) ->
    {Ts1,Bs1,W0,COMP0,FUNC0} = install_triples(Ts, Bs, [],
					       dict:new(), 
					       dict:new(),
					       dict:new()),
    {W1,COMP1} = foldl(fun({Xi,V}, {Wi,COMPi}) -> 
			       {dict:store(Xi,V,Wi),
				dict:store(Xi,false,COMPi)}
		       end, {W0,COMP0}, Sub),
    {Qs,Bs2,W2} = run_triples(Ts1,Bs1,[],W1,COMP1,FUNC0,0),
    F0 = formula:value(F, Bs2),
    F1 = wget(F0, W2),
    {F1, Qs, Bs2}.


run_triples(Ts,Bs,Qs,W,COMP,FUNC,I) ->
    %% io:format("~w ", [length(Ts)]),
    run_triples_(Ts,Bs,[],Qs,W,COMP,FUNC,I).
    
run_triples_([T={Op,X,Y,Z}|Ts],Bs,Ts1,Qs,W,COMP,FUNC,I) ->
    case need_comp(Y,COMP) orelse need_comp(Z,COMP) of
	true ->
	    %% need to compute Y and Z first
	    run_triples_(Ts, Bs, [T|Ts1], Qs, W, COMP, FUNC,I);
	false ->
	    Y1 = wget(Y, W),
	    Z1 = wget(Z, W),
	    case need_comp(X, COMP) of
		true ->
		    case dict:find({Op,Y1,Z1}, FUNC) of
			error ->
			    {X1,Bs1} = formula:fresh_var(Bs),
			    W1       = wset(X, X1, W),
			    {FUNC1,Bs2} = set_func(Op,X1,Y1,Z1,FUNC,Bs1),
			    COMP1    = set_comp(X, false, COMP),
			    run_triples_(Ts, Bs2, Ts1, [{Op,X1,Y1,Z1}|Qs], 
					 W1, COMP1, FUNC1,I);
			{ok,X1} ->
			    W1 = wset(X, X1, W),
			    COMP1 = set_comp(X, false, COMP),
			    run_triples_(Ts, Bs, Ts1, Qs, 
					 W1, COMP1, FUNC,I)
		    end;
		false ->
		    X1 = wget(X, W),
		    run_triples_(Ts, Bs, Ts1, [{Op,X1,Y1,Z1}|Qs], 
				 W, COMP, FUNC,I)
	    end
    end;
run_triples_([],Bs,[],Qs,W,_COMP,_FUNC,_I) ->
    {Qs,Bs,W};
run_triples_([],Bs,Ts1,Qs,W,COMP,FUNC,I) ->
    run_triples(Ts1,Bs,Qs,W,COMP,FUNC,I+1).

install_triples([{Op,X0,Y0,Z0}|Ts], Bs, Acc, W0, COMP0,FUNC0) ->
    X = formula:value(X0, Bs),
    Y = formula:value(Y0, Bs),
    Z = formula:value(Z0, Bs),
    {FUNC1,Bs1} = set_func(Op,X,Y,Z,FUNC0,Bs),
    W1  = wset(X, X, W0),
    W2  = wset(Y, Y, W1),
    W3  = wset(Z, Z, W2),
    COMP1 = set_comp(X, not formula:is_input(X, Bs1), COMP0),
    COMP2 = set_comp(Y, not formula:is_input(Y, Bs1), COMP1),
    COMP3 = set_comp(Z, not formula:is_input(Z, Bs1), COMP2),
    install_triples(Ts, Bs1, [{Op,X,Y,Z}|Acc], W3, COMP3, FUNC1);
install_triples([], Bs, Acc, W0, COMP0, FUNC0) ->
    {Acc,Bs,W0,COMP0,FUNC0}.

%%
%% Given a set of triples reduce triples 
%% computing the same thing   {X1,A,B} {X2,A,B}
%% => {X1, A, B}  (X1=X2)
%%
reduce_triples([], Bs) ->
    {[],Bs};
reduce_triples(Ts, Bs) ->
    %% io:format("R1: ~w\n", [Ts]),
    {Ts1,Bs1} = reduce_triples(Ts, Bs, [], false, dict:new()),
    %% io:format("R2: ~w\n", [Ts1]),    
    {Ts1,Bs1}.

reduce_triples([{Op,X0,Y0,Z0}|Ts],Bs0,Acc,Status,FUNC0) ->
    X1 = formula:value(X0, Bs0),
    Y1 = formula:value(Y0, Bs0),
    Z1 = formula:value(Z0, Bs0),
    case dict:find({Op,Y1,Z1}, FUNC0) of
	error ->
	    %% io:format("install ~w => ~w\n", [{Op,Y1,Z1},X1]),
	    {FUNC1,Bs1} = set_func(Op,X1,Y1,Z1,FUNC0,Bs0),
	    reduce_triples(Ts,Bs1,[{Op,X0,Y0,Z0}|Acc],Status,FUNC1);
	{ok,X2} ->
	    case formula:value(X2,Bs0) of
		X1 ->
		    %% io:format("duplicate ~w\n", [X1]),
		    reduce_triples(Ts,Bs0,Acc,Status,FUNC0);
		X3 ->
		    %% io:format("merge ~w ~w\n", [X1,X3]),
		    Bs1 = formula:equal(X3,X1,Bs0),
		    reduce_triples(Ts,Bs1,Acc,true,FUNC0)
	    end
    end;
reduce_triples([],Bs0,[],_Status,_FUNC0) ->
    {[],Bs0};
reduce_triples([],Bs0,Acc,true,_FUNC0) ->
    reduce_triples(Acc,Bs0,[],false,dict:new());
reduce_triples([],Bs0,Acc,false,_FUNC0) ->
    {Acc,Bs0}.


%% FIXME must lookup {Op,Y,Z} + {equ,Y,Z} == {equ,Z,Y}
%% X1 = {imp,Y,Z}, X2 = {imp,Y,Z} => X1 = X2 
set_func(imp,X,Y,Z,F0,Bs) ->
    error = dict:find(X,F0),
    {dict:store({imp,Y,Z},X, F0), Bs};
set_func(equ,X,Y,Z,F0,Bs) ->
    error = dict:find(X,F0),
    F1 = dict:store({equ,Y,Z},X, F0),
    {dict:store({equ,Z,Y},X,F1),Bs}.

set_comp(X, Bool, Comp) ->
    dict:store(war(X), Bool, Comp).

need_comp(?TRUE, _Comp) -> false;
need_comp(?FALSE, _Comp) -> false;
need_comp(X, Comp) when X < 0 -> dict:fetch(-X, Comp);
need_comp(X, Comp) -> dict:fetch(X, Comp).

war(?TRUE)  -> ?TRUE;
war(?FALSE) -> ?FALSE;
war(X) when X < 0 -> -X;
war(X) -> X.

wset(?TRUE, _, W)  -> W;
wset(?FALSE, _, W) -> W;
wset(A, B, W) when A < 0 ->  dict:store(-A, -B, W);
wset(A, B, W) -> dict:store(A, B, W).

wget(?TRUE, _W)  -> ?TRUE;
wget(?FALSE, _W) -> ?FALSE;
wget(A, W) when A < 0 -> -dict:fetch(-A, W);
wget(A, W) -> dict:fetch(A, W).

