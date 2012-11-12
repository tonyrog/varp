%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2012, Tony Rogvall
%%% @doc
%%%    Formula expansion 
%%% @end
%%% Created : 14 Sep 2012 by Tony Rogvall <tony@rogvall.se>

-module(form).

-compile(export_all).
-import(lists, [map/2, foldl/3]).

expand(F) ->
    expand(F, []).

expand(true,_Bs) ->
    true;
expand(false,_Bs) ->
    false;
expand(V, Bs) when is_atom(V) ->
    {var, expand_meta(V, Bs)};
expand({var,V},Bs) ->       {var, expand_meta(V, Bs)};
expand({'&',A,B},Bs) ->     {'&',expand(A,Bs),expand(B,Bs)};
expand({'and',A,B},Bs) ->   {'and',expand(A,Bs),expand(B,Bs)};
expand({'#',A,B},Bs) ->     {'#',expand(A,Bs),expand(B,Bs)};
expand({'|',A,B},Bs) ->     {'|',expand(A,Bs),expand(B,Bs)};
expand({'or',A,B},Bs) ->    {'or',expand(A,Bs),expand(B,Bs)};
expand({'->',A,B},Bs) ->    {'->',expand(A,Bs),expand(B,Bs)};
expand({'imp',A,B},Bs) ->   {'imp',expand(A,Bs),expand(B,Bs)};
expand({'not',A},Bs) ->     {'not',expand(A,Bs)};
expand({'=',A,B},Bs) ->     {'=',expand(A,Bs),expand(B,Bs)};
expand({'<->',A,B},Bs) ->   {'<->',expand(A,Bs),expand(B,Bs)};
expand({'!=',A,B},Bs) ->    {'!=',expand(A,Bs),expand(B,Bs)};
expand({all,F}, Bs)   ->    all(expand_args(F,Bs));
expand({any,F}, Bs)   ->    any(expand_args(F,Bs));
expand({none,F}, Bs)   ->   {none,expand_args(F,Bs)};
expand({eqk,K,F}, Bs) ->    {eqk,K,expand_args(F,Bs)};
expand({neqk,K,F}, Bs) ->   {neqk,K,expand_args(F,Bs)};
expand({gtk,K,F}, Bs) ->    {gtk,K,expand_args(F,Bs)};
expand({gtek,K,F}, Bs) ->   {gtek,K,expand_args(F,Bs)};
expand({ltk,K,F}, Bs) ->    {ltk,K,expand_args(F,Bs)};
expand({ltek,K,F}, Bs) ->   {ltek,K,expand_args(F,Bs)};
expand({suchthat,Expr,F},Bs) ->
    case eval_meta(Expr,Bs) of
	true  -> expand(F,Bs);
	false -> undefined
    end;
expand({subst,Rx,Py,F},Bs) ->
    expand(F, [{Rx,Py}|Bs]);
expand({subst,SList,F},Bs) ->
    expand(F, SList++Bs);

expand({{forall,Xs,D}, F}, Bs) ->
    D1 = eval_domain(D, Bs),
    Ys = expand_quant(F,Xs,D1,Bs),
    all(Ys);
expand({{exists,Xs,D},F}, Bs) ->
    D1 = eval_domain(D, Bs),
    Ys = expand_quant(F,Xs,D1,Bs),
    any(Ys);
expand({{list,Xs,D},F}, Bs) ->
    D1 = eval_domain(D, Bs),
    expand_quant(F,Xs,D1,Bs);
expand({{one,Xs,D},F}, Bs) ->
    D1 = eval_domain(D, Bs),
    Ys = expand_quant(F,Xs,D1,Bs),
    {one,Ys}.

expand_quant(F,Xs=[X],[Y|Ys],Bs) ->
    case expand(F, [{X,Y}|Bs]) of
	undefined -> expand_quant(F,Xs,Ys,Bs);
	Fs when is_list(Fs) -> Fs ++ expand_quant(F,Xs,Ys,Bs);
	F1 -> [F1 | expand_quant(F,Xs,Ys,Bs)]
    end;
expand_quant(F,Xs,[Y|Ys],Bs) ->
    case expand(F, lists:zip(Xs,Y)++Bs) of
	undefined -> expand_quant(F,Xs,Ys,Bs);
	Fs when is_list(Fs) -> Fs ++ expand_quant(F,Xs,Ys,Bs);
	F1 -> [F1 | expand_quant(F,Xs,Ys,Bs)]
    end;
expand_quant(_F,_Xs,[],_BS) ->
    [].

expand_args(Fs,Bs) when is_list(Fs) ->
    expand_args_(Fs,Bs);
expand_args(F,Bs) ->
    case expand(F,Bs) of
	Fs when is_list(Fs) -> expand_args(Fs,Bs)
    end.

expand_args_([F|Fs],Bs) ->
    case expand(F,Bs) of
	undefined -> expand_args_(Fs,Bs);
	F1 -> [F1 | expand_args_(Fs,Bs)]
    end;
expand_args_([],_Bs) ->
    [].

expand_meta(T,Bs) when is_tuple(T), is_atom(element(1,T)) ->
    [R|Rs] = tuple_to_list(T),
    {Rs1,_Bnd1} = bind_meta(Rs,Bs,[],[]),
    %% check for substitution R(x1,..,xn) / P(y1,..,ym)
    case find_subst(R, Bs) of
	false -> 
	    list_to_tuple([R|Rs1]);
	{Rx,Qy} when is_tuple(Qy), tuple_size(Qy) > 1, element(1,Qy) =/= R ->
	    [_U|Us] = tuple_to_list(Rx),
	    Bnd2 = lists:zip(Us,Rs1),
	    io:format("subst: ~w [~w] => ~w\n", [Rx,Bnd2,Qy]),
	    expand_meta(Qy, Bnd2++Bs);
	Q when is_tuple(Q), tuple_size(Q) =:= 1 ->
	    ok;
	Q when is_atom(Q) ->
	    Q
    end;
expand_meta(V,_Bs) -> V.


eval_domain(V, Bs) when is_atom(V) ->
    V1 = eval_meta(V,Bs),
    [V1];
eval_domain(I, _Bs) when is_integer(I) ->
    [I];
eval_domain({range,A,B}, Bs) ->
    A1 = eval_meta(A,Bs),
    B1 = eval_meta(B,Bs),
    lists:seq(A1, B1);
eval_domain({union,A,B}, Bs) ->
    A1 = eval_domain(A,Bs),
    B1 = eval_domain(B,Bs),
    ordsets:union(A1,B1);
eval_domain({subtract,A,B}, Bs) ->
    A1 = eval_domain(A,Bs),
    B1 = eval_domain(B,Bs),
    ordsets:subtract(A1,B1);
eval_domain({intersect,A,B}, Bs) ->
    A1 = eval_domain(A,Bs),
    B1 = eval_domain(B,Bs),
    ordsets:intersection(A1,B1);
eval_domain({product,A,B}, Bs) ->
    A1 = eval_domain(A,Bs),
    B1 = eval_domain(B,Bs),
    [ [Ai,Bi] || Ai <- A1, Bi <- B1 ].


find_subst(R, [{Rx,Qy}|_]) when R =:= element(1,Rx) ->
    {Rx,Qy};
find_subst(R, [_|Bnd]) -> find_subst(R, Bnd);
find_subst(_R ,[]) -> false.

%% bind for substitution of function symbols
bind_meta([V|Vs], Bs, Acc, Bnd) when is_atom(V) ->
    W = eval_meta(V,Bs),
    if W =:= V ->
	    bind_meta(Vs, Bs, [W|Acc], Bnd);
       true ->
	    bind_meta(Vs, Bs, [W|Acc], [{V,W}|Bnd])
    end;
bind_meta([V|Vs], Bs, Acc, Bnd) ->
    W = eval_meta(V,Bs),
    bind_meta(Vs, Bs, [W|Acc], Bnd);
bind_meta([], _Bs, Acc, Bnd) ->
    {lists:reverse(Acc),lists:reverse(Bnd)}.



all([])     -> true;
all([A])    -> A;
all([A|As]) -> {'and',A,all(As)}.

any([])     -> false;
any([A])    -> A;
any([A|As]) -> {'or',A,any(As)}.

%% F[X/Y]  (forall/exist quantifier not allowed)
subst({var,X}, X, Y) -> Y;
subst(F={var,_}, _X, _Y) -> F;
subst(true, _, _) -> true;
subst(false, _, _) -> false;
subst({'and',A,B},X,Y) -> {'and',subst(A,X,Y),subst(B,X,Y)};
subst({'or',A,B},X,Y) -> {'or',subst(A,X,Y),subst(B,X,Y)};
subst({'not',A},X,Y) -> {'not',subst(A,X,Y)}.

%% peval - partial eval 
peval(true) -> true;
peval(false) ->  false;
peval(V={var,_}) -> V;
peval({'and',A,B}) -> 
    case peval(A) of
	false -> false;
	true  -> peval(B);
	A1 ->
	    case peval(B) of
		false -> false;
		true  -> A1;
		A1    -> A1;
		B1 -> {'and',A1,B1}
	    end
    end;
peval({'or',A,B}) -> 
    case peval(A) of
	true -> true;
	false -> peval(B);
	A1 ->
	    case peval(B) of
		true -> true;
		false -> A1;
		A1 -> A1;
		B1 -> {'or',A1,B1}
	    end
    end;
peval({'not',A}) ->
    case peval(A) of
	false -> true;
	true -> false;
	A1 -> {'not', A1}
    end.

%% eval - evaluate 
eval(true,_Bs) -> true;
eval(false,_Bs) ->  false;
eval({var,X},Bs) -> dict:fetch(X, Bs);
eval({'and',A,B},Bs) -> eval(A,Bs) andalso eval(B,Bs);
eval({'or',A,B},Bs) -> eval(A,Bs) orelse eval(B,Bs);
eval({'not',A},Bs) -> not eval(A,Bs).


%% eval function expressions and suchthat expressions
eval_meta(V, _Bs) when is_integer(V) ->
    V;
eval_meta(true, _Bs) ->
    true;
eval_meta(false, _Bs) ->
    false;
eval_meta(V, Bs) when is_atom(V) ->
    case lists:keyfind(V,1,Bs) of
	undefined -> V;
	{_,W} -> W
    end;
eval_meta({call,F,As},Bs) ->
    case {F,eval_meta_list(As,Bs)} of
	{factorial,[N]} -> imath:factorial(N);
	{binom,[A,B]} -> imath:binom(A,B);
	{sqrt,[A]} -> math:sqrt(A);
	{nroot,[A,N]} -> imath:pow(A,(1/N));
	{ln,[A]} -> math:log(A);
	{log,[A,N]} -> math:log(A)/math:log(N);
	{log2,[A]} -> math:log(A)/math:log(2);
	{log10,[A]} -> math:log10(A);
	{pi,[]} -> math:pi();
	{e,[]} -> math:exp(1);
	{pow,[A,B]} -> math:pow(A,B);
	{sin,[A]} -> math:sin(A);
	{cos,[A]} -> math:cos(A);
	{trunc,[A]} -> trunc(A);
	{round,[A]} -> round(A);
	{abs,[A]} -> abs(A);
	{max,[A,B]} -> max(A,B);
	{min,[A,B]} -> min(A,B);
	{plus,[A,B]} -> A+B;
	{minus,[A,B]} -> A-B;
	{times,[A,B]} -> A*B;
	{divide,[A,B]} -> A div B;
	{remainder,[A,B]} -> A rem B;
	{negate,[A]} -> -A
    end;
eval_meta({Op,A,B},Bs) ->
    case {Op,eval_meta(A,Bs),eval_meta(B,Bs)} of
	{'<',A1,B1} -> A1 < B1;
	{'<=', A1, B1} -> A1 =< B1;
	{'>',A1,B1} -> A1 > B1;
	{'>=', A1, B1} -> A1 >= B1;
	{'==', A1, B1} -> A1 == B1;
	{'and',A1,B1} -> A1 and B1;
	{'or',A1,B1} -> A1 or B1;
	{'+',A1,B1} -> A1+B1;
	{'-',A1,B1} -> A1-B1;
	{'*',A1,B1} -> A1*B1;
	{'/',A1,B1} -> A1 div B1;
	{'%',A1,B1} -> A1 rem B1
    end;
eval_meta({sum,As},Bs) ->
    lists:foldl(fun(Ai,Sum) -> eval_meta(Ai,Bs)+Sum end, 0, As);
eval_meta({Op,A},Bs) ->
    case {Op,eval_meta(A,Bs)} of
	{'-',A1} -> -A1;
	{'+',A1} -> +A1;
	{'not',A1} -> not A1
    end.

eval_meta_list(As,Bs) ->
    map(fun(A) -> eval_meta(A,Bs) end, As).

    
print(F) ->
    io:put_chars([fmt(F),"\n"]).

%% format formula.
fmt(true) -> "true";
fmt(false) -> "false";
fmt(X) when is_atom(X) -> fmt_var(X);
fmt({var,X}) -> fmt_var({var,X});
fmt({Op,A,B}) ->
    ["(",fmt(A)," ",atom_to_list(Op)," ",fmt(B),")"];
fmt({Op,As}) when is_list(As) -> 
    [atom_to_list(Op),"(",fmt_list(As),")"];
fmt({Op,A}) ->   [atom_to_list(Op)," ",fmt(A)].

fmt_list([A]) -> [fmt(A)];
fmt_list([A|As]) -> [fmt(A),"," | fmt_list(As)];
fmt_list([]) -> [].


fmtq(X) ->
    fmt_var(X, "\"").

fmt_var(X) ->
    fmt_var(X, "").

fmt_var(true, _Q)  -> "true";
fmt_var(false, _Q) -> "false";
fmt_var(X, Q) when is_atom(X) -> [Q,io_lib:format("~s", [X]),Q];
fmt_var({var,X}, Q) when is_atom(X) -> [Q,io_lib:format("~s", [X]),Q];
fmt_var({var,X}, Q) when is_tuple(X) ->
    [P|Ps] = tuple_to_list(X),
    [Q,atom_to_list(P),"(",
     string:join([if is_integer(T) -> integer_to_list(T);
		     is_atom(T) -> atom_to_list(T)
		  end ||  T <- Ps ], ","), ")", Q].
%%
%% Test case
%% 
%%


ysat_skolem(N) ->
    R0 = expand(formulas:ysat(N)),
    %% generate expanded skolem formula for r(i)/1
    R1 = lists:foldl(
	   fun(I,Fi) ->
		   Fi1 = subst(Fi, {r,I}, true),
		   subst(Fi, {r,I}, Fi1)
	   end, R0, lists:seq(1, N)),
    peval(R1).

test(N) ->
    F = ysat_skolem(N),
    eval_ysat(F, N).


ysat_gunnar(N) ->
    F = expand(formulas:ysat(N)),
    RI  = [{r,I} || I <- lists:seq(1,N)],
    R1 =
	any(map(
	      fun(I) ->
		      Row = [X =:= 1 || <<X:1>> <= <<I:N>>],
		      lists:foldl(
			fun({Ri,Vi}, Fi) ->
				subst(Fi, Ri, Vi)
			end, F, lists:zip(RI, Row))
	      end, lists:seq(0, (1 bsl N)-1))),
    peval(R1).

    
test_gunnar(N) ->
    R2 = ysat_gunnar(N),
    %% evaluate R2 over all p(i,j) and q(i,j)
    %% number of variables = 2*N*N
    eval_ysat(R2, N).

%% evaluate F over all p(i,j) and q(i,j)
%% number of variables = 2*N*N
eval_ysat(F, N) ->
    K = 2*N*N,
    PIJ = [{p,I,J} || I <- lists:seq(1,N), 
		      J <- lists:seq(1,N)],
    QIJ = [{q,I,J} || I <- lists:seq(1,N), 
		      J <- lists:seq(1,N)],
    PIJQIJ = PIJ ++ QIJ,
    map(
      fun(I) ->
	      Row = [X =:= 1 || <<X:1>> <= <<I:K>>],
	      Assign = lists:zip(PIJQIJ, Row),
	      Dict = dict:from_list(Assign),
	      {eval(F, Dict), Assign} 
      end, lists:seq(0, (1 bsl K)-1)).

test_print(N) ->
    G=lists:filter(fun({R,_}) -> not R end, form:test_gunnar(N)),
    lists:foreach(
      fun({_, M}) -> 
	      io:format("~s\n", 
			[lists:map(
			   fun({{L,I,J},false}) -> 
				   io_lib:format("~w~w~w=0 ",[L,I,J]); 
			      ({{L,I,J},true}) -> 
				   io_lib:format("~w~w~w=1 ", [L,I,J]) 
			   end, M)]) end, G).

count_counter_models(F, N) ->
    Is = apply(?MODULE,F,[N]),
    G=lists:filter(fun({R,_}) -> not R end, Is),
    length(G).

count_models(F, N) ->
    Is = apply(?MODULE,F,[N]),
    G=lists:filter(fun({R,_}) -> R end, Is),
    length(G).

count_ysat_models(N) ->
    F = ysat_gunnar(N),
    K = 2*N*N,
    PIJ = [{p,I,J} || I <- lists:seq(1,N), 
		      J <- lists:seq(1,N)],
    QIJ = [{q,I,J} || I <- lists:seq(1,N), 
		      J <- lists:seq(1,N)],
    PIJQIJ = PIJ ++ QIJ,
    foldl(
      fun(I,Count) ->
	      Row = [X =:= 1 || <<X:1>> <= <<I:K>>],
	      Assign = lists:zip(PIJQIJ, Row),
	      Dict = dict:from_list(Assign),
	      case eval(F, Dict) of
		  true -> Count+1;
		  false -> Count
	      end
      end, 0, lists:seq(0, (1 bsl K)-1)).

