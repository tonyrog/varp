%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2013, Tony Rogvall
%%% @doc
%%%    Skolem function construction
%%% @end
%%% Created :  3 Dec 2013 by Tony Rogvall <tony@rogvall.se>

-module(skolem).

-compile(export_all).

-define(TRUE,   1).
-define(FALSE, -1).

perm(F,Const,Ws) ->
    lists:foreach(
      fun(WsOrder) ->
	      {_,Ts,_} = build(F,Const,WsOrder),
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
build(F0) ->
    build(F0,true).

build(F0,Const) -> 
    build(F0,Const,[]).

build(F0,true,Ws) ->
    build_(F0,?TRUE,Ws);
build(F0,false,Ws) ->
    build_(F0,?FALSE,Ws).

build_(F0,Const,Ws) ->
    {{bool,Y0},Bs0} = formula:build(F0,[]),
    {Ts,Bs} = formula:triples(Bs0),
    io:format("skolem: #triples=~w\n", [length(Ts)]),
    {Ts1,Bs1} = reduce_triples(Ts,Bs),
    io:format("skolem: reduced #triples=~w\n", [length(Ts1)]),
    try formula:eval(Ts1, Bs1) of
	{Ts2,Bs2} -> 
	    io:format("skolem: eval #triples=~w\n", [length(Ts2)]),
	    Vs = formula:model_variables(Bs2,Ws),
	    build(Y0,Const,Vs,Ts2,Bs2)
    catch
	throw:contradiction -> false
    end.


build(Y0,Const,[Xi|Xs],Ts,Bs) ->
    io:format("~s: length = ~w\n", [formula:fmt_var(Xi,Bs), length(Ts)]),
    case formula:value(Xi,Bs) of
	?TRUE  -> build(Y0,Const,Xs,Ts,Bs);
	?FALSE -> build(Y0,Const,Xs,Ts,Bs);
	Xiv ->
	    {Y1,_Ts1,Bs1} = copy_triples(Y0, Ts, Bs, [{Xi,Const}]),
	    %% Ts++Ts1,
	    case prover:equal_eval(Xiv, Y1,  Bs1) of
		{[],Bs2} ->
		    return(Y0,[],Bs2);
		{Ts2,Bs2} ->
		    Y01 = formula:value(Y0,Bs2),
		    build(Y01,Const,Xs,Ts2,Bs2);
		false ->
		    false
	    end
    end;
build(Y0, _Const, [], Ts, Bs) ->
    return(Y0, Ts, Bs).

return(Y,Ts,Bs) ->
    V = formula:value(Y,Bs),
    io:format("~s: #triples ~w\n", [formula:fmt_var(V,Bs),length(Ts)]),
    case V of
	?TRUE ->  {true, Ts, Bs};
	?FALSE -> {false, Ts, Bs};
	V -> {V, Ts, Bs}
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
    {W1,COMP1} = lists:foldl(fun({Xi,V}, {Wi,COMPi}) -> 
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

