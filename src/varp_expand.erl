%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2012, Tony Rogvall
%%% @doc
%%%    Formula expansion 
%%% @end
%%% Created : 14 Sep 2012 by Tony Rogvall <tony@rogvall.se>

-module(varp_expand).

-export([formula/1, formula/2]).
-export([variables/1]).
-export([subst/3, peval/1, eval/2]).
-export([print/1]).

-export([ysat_skolem/1, test/1, ysat_gunnar/1]).
-export([count_ysat_models/1]).
-export([test_gunnar/1, test_print/1]).
-export([count_counter_models/2, count_models/2]).


-include("varp.hrl").

%% expand formula F expanding all use of meta variables, instanciate predicates
formula(F) ->
    formula(F, []).

formula(F,Bs) ->
    form_(F, Bs).

form_(true,_Bs) ->
    true;
form_(false,_Bs) ->
    false;
form_(V, Bs) when is_atom(V) -> 
    expand_meta({p,V,[]}, Bs);
form_({expr,E},Bs) ->
    eval_meta(E,Bs);
form_(_P0={p,P,Vs},Bs) ->
    P1 = {p,P,eval_meta_list(Vs,Bs)},
    %% io:format("expand: ~p => ~p\n", [_P0, P1]),
    expand_meta(P1, Bs);

form_({'&',A,B},Bs) ->     {'&',form_(A,Bs),form_(B,Bs)};
form_({'&&',A,B},Bs) ->    {'&&',form_(A,Bs),form_(B,Bs)};
form_({'and',A,B},Bs) ->   {'and',form_(A,Bs),form_(B,Bs)};
form_({'|',A,B},Bs) ->     {'|',form_(A,Bs),form_(B,Bs)};
form_({'||',A,B},Bs) ->    {'||',form_(A,Bs),form_(B,Bs)};
form_({'or',A,B},Bs) ->    {'or',form_(A,Bs),form_(B,Bs)};
form_({'->',A,B},Bs) ->    {'->',form_(A,Bs),form_(B,Bs)};
form_({'imp',A,B},Bs) ->   {'imp',form_(A,Bs),form_(B,Bs)};
form_({'!',A},Bs) ->       {'!',form_(A,Bs)};
form_({'not',A},Bs) ->     {'not',form_(A,Bs)};
form_({'~',A},Bs) ->       {'~',form_(A,Bs)};
form_({'equ',A,B},Bs) ->   {'equ',form_(A,Bs),form_(B,Bs)};
form_({'=',A,B},Bs) ->     {'=',form_(A,Bs),form_(B,Bs)};
form_({'^',A,B},Bs) ->     {'^',form_(A,Bs),form_(B,Bs)};
form_({'xor',A,B},Bs) ->   {'xor',form_(A,Bs),form_(B,Bs)};
form_({'<->',A,B},Bs) ->   {'<->',form_(A,Bs),form_(B,Bs)};
form_({'!=',A,B},Bs) ->    {'!=',form_(A,Bs),form_(B,Bs)};
form_({subst,Rx,Py,F},Bs) ->  form_(F, [{Rx,Py}|Bs]);
form_({subst,SList,F},Bs) ->  form_(F, SList++Bs);

form_({'ALL',Fs}, Bs) when is_list(Fs) ->
    Ys = expand_args(Fs, Bs),
    all(Ys);
form_({'ANY',Fs}, Bs) when is_list(Fs) ->
    Ys = expand_args(Fs, Bs),
    any(Ys);
form_({'ONE',Fs}, Bs) when is_list(Fs) ->
    Ys = expand_args(Fs, Bs),
    one(Ys);
form_({'NONE',Fs}, Bs) when is_list(Fs) ->
    Ys = expand_args(Fs, Bs),
    none(Ys);

form_({{'ALL',Xs}, F}, Bs) ->
    Ys = expand_quant(F,Xs,Bs),
    all(Ys);
form_({{'ANY',Xs},F}, Bs) ->
    Ys = expand_quant(F,Xs,Bs),
    any(Ys);
form_({{'ONE',Xs},F}, Bs) ->
    Ys = expand_quant(F,Xs,Bs),
    one(Ys);
form_({{'NONE',Xs},F}, Bs) ->
    Ys = expand_quant(F,Xs,Bs),
    none(Ys);

form_({{'EQ',[X1|Xs]},F}, Bs) ->
    N = eval_meta(X1,Bs),
    Ys = expand_quant(F,Xs,Bs),
    if N =:= 1 -> one(Ys);
       true -> {'EQ',N,Ys}
    end;
form_({{'NEQ',[X1|Xs]},F}, Bs) ->
    N = eval_meta(X1,Bs),
    Ys = expand_quant(F,Xs,Bs),
    {'NEQ',N,Ys};
form_({{'GT',[X1|Xs]},F}, Bs) ->
    N = eval_meta(X1,Bs),
    Ys = expand_quant(F,Xs,Bs),
    {'GT',N,Ys};
form_({{'GTE',[X1|Xs]},F}, Bs) ->
    N = eval_meta(X1,Bs),
    Ys = expand_quant(F,Xs,Bs),
    {'GTE',N,Ys};
form_({{'LT',[X1|Xs]},F}, Bs) ->
    N = eval_meta(X1,Bs),
    Ys = expand_quant(F,Xs,Bs),
    {'LT',N,Ys};
form_({{'LTE',[X1|Xs]},F}, Bs) ->
    N = eval_meta(X1,Bs),
    Ys = expand_quant(F,Xs,Bs),
    {'LTE',N,Ys};

form_(F, _Bs) ->
    F.

expand_quant(F,[#cassign{op='=',lhs=#cid{name=V},rhs=D}|Xs], Bs) ->
    Ds = eval_domain(D, Bs),
    expand_quant_domain(F, V, Ds, Xs, Bs);
expand_quant(F, [Expr|Xs], Bs) ->
    case eval_meta(Expr, Bs) of
	false -> [];
	true -> expand_quant(F, Xs, Bs)
    end;
expand_quant(F, [], Bs) ->
    [form_(F,Bs)].

	    
expand_quant_domain(F, V, [Y|Ys], Xs, Bs) ->
    expand_quant(F, Xs, [{V,Y}|Bs]) ++ 
	expand_quant_domain(F, V, Ys, Xs, Bs);
expand_quant_domain(_F, _V, [], _Xs, _Bs) ->
    [].


expand_args(Fs,Bs) when is_list(Fs) ->
    expand_args_(Fs,Bs);
expand_args(F,Bs) ->
    case form_(F,Bs) of
	Fs when is_list(Fs) -> expand_args(Fs,Bs)
    end.

expand_args_([F|Fs],Bs) ->
    case form_(F,Bs) of
	undefined -> expand_args_(Fs,Bs);
	F1 -> [F1 | expand_args_(Fs,Bs)]
    end;
expand_args_([],_Bs) ->
    [].

expand_meta(_Rx={p,P,Rs},Bs) when is_atom(P) ->
    {Rs1,_Bnd1} = bind_meta(Rs,Bs,[],[]),
    %% check for substitution R(x1,..,xn) / P(y1,..,ym)
    %% io:format("expand_meta: ~p in Bs=~p\n", [_Rx, Bs]),
    Found = find_subst(P, Bs),
    %% io:format("subst  = ~w\n", [Found]),
    case Found of
	false ->
	    {p,P,Rs1};
	{{p,Q,[]},{p,_P,_Us}} ->
	    {p,Q,[]};
	{{p,Q,Qs},{p,P,Ps}} when P =/= Q, length(Qs) > 0 ->
	    Bnd2 = lists:zip(Ps,Rs1),
	    %% io:format("subst: ~w [~w] => ~w\n", [{p,P,Ps},Bnd2,{p,Q,Qs}]),
	    expand_meta({p,Q,Qs}, Bnd2++Bs)
    end;
expand_meta(V,_Bs) ->
    %% io:format("expand_meta: ~p in Bs=~p\n", [V, _Bs]),    
    V.

eval_domain(#crange{from=A,to=B}, Bs) ->
    A1 = eval_meta(A,Bs),
    B1 = eval_meta(B,Bs),
    lists:seq(A1, B1);
eval_domain(#ccall{func=#cid{name="union"},args=[A,B]}, Bs) ->
    A1 = eval_domain(A,Bs),
    B1 = eval_domain(B,Bs),
    ordsets:union(A1,B1);
eval_domain(#ccall{func=#cid{name="subtract"},args=[A,B]}, Bs) ->
    A1 = eval_domain(A,Bs),
    B1 = eval_domain(B,Bs),
    ordsets:subtract(A1,B1);
eval_domain(#ccall{func=#cid{name="intersect"},args=[A,B]}, Bs) ->
    A1 = eval_domain(A,Bs),
    B1 = eval_domain(B,Bs),
    ordsets:intersection(A1,B1);
eval_domain(#ccall{func=#cid{name="product"},args=[A,B]}, Bs) ->
    A1 = eval_domain(A,Bs),
    B1 = eval_domain(B,Bs),
    [ [Ai,Bi] || Ai <- A1, Bi <- B1 ];
eval_domain(Expr, Bs) ->
    [eval_meta(Expr,Bs)].

find_subst(P, [E={_Qy,{p,P,_}}|_]) ->
    E;
find_subst(P, [_|Bnd]) -> 
    find_subst(P, Bnd);
find_subst(_P ,[]) -> 
    false.

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

none(As) -> {'not',any(As)}.
    

one([A]) -> A;
one(As) ->
    {'and', {all, [{'not',{'and',A,B}} || {A,B} <- pairs(As)]},
     {any, As}}.

pairs([]) -> [];
pairs([_]) -> [];
pairs([A|As]) -> [{A,Ai} || Ai <- As] ++ pairs(As).

%% F[X/Y]  (forall/exist quantifier not allowed)
subst({var,X}, X, Y) -> Y;
subst(F={var,_}, _X, _Y) -> F;
subst(true, _, _) -> true;
subst(false, _, _) -> false;
subst({'and',A,B},X,Y) -> {'and',subst(A,X,Y),subst(B,X,Y)};
subst({'or',A,B},X,Y)  -> {'or',subst(A,X,Y),subst(B,X,Y)};
subst({'not',A},X,Y)   -> {'not',subst(A,X,Y)}.

%% peval - partial eval 
peval(true) -> true;
peval(false) ->  false;
peval(V={p,_P,_}) -> V;
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
eval(X={p,_S,_Vs},Bs) -> dict:fetch(X, Bs);
eval({'and',A,B},Bs) -> eval(A,Bs) andalso eval(B,Bs);
eval({'or',A,B},Bs) -> eval(A,Bs) orelse eval(B,Bs);
eval({'not',A},Bs) -> not eval(A,Bs).

%% eval function expressions and suchthat expressions
eval_meta(V, _Bs) when is_integer(V) ->  V;
eval_meta(#cconst{base=B,value=V}, _Bs) -> list_to_integer(V,B);
eval_meta(#cid {name="true"}, _Bs)  -> true;
eval_meta(#cid {name="false"}, _Bs) -> false;
%%eval_meta(true, _Bs) ->  true;
%%eval_meta(false, _Bs) -> false;
%%eval_meta(V, Bs) when is_atom(V) ->
eval_meta(#cid {name=Vn}, Bs) ->
    case proplists:lookup(Vn,Bs) of
	none -> 
	    io:format("variable '~s' is not bound\n", [Vn]),
	    error({unbound, Vn});
	{_,W} -> W
    end;
eval_meta(#ccall{func=F,args=As},Bs) ->
    case {F,eval_meta_list(As,Bs)} of
	{#cid{name="factorial"},[N]} -> varp_math:factorial(N);
	{#cid{name="binom"},[A,B]} -> varp_math:binom(A,B);
	{#cid{name="sqrt"},[A]}    -> math:sqrt(A);
	{#cid{name="nroot"},[A,N]} -> varp_math:nroot(A,N);
	{#cid{name="ln"},[A]}      -> math:log(A);
	{#cid{name="log"},[A,N]}   -> math:log(A)/math:log(N);
	{#cid{name="log2"},[A]}    -> math:log(A)/math:log(2);
	{#cid{name="log10"},[A]}   -> math:log10(A);
	{#cid{name="pi"},[]}       -> math:pi();
	{#cid{name="e"},[]}        -> math:exp(1);
	{#cid{name="pow"},[A,B]}   -> 
	    if is_integer(A), is_integer(B) ->
		    varp_math:pow(A,B);
	       true ->
		    math:pow(A,B)
	    end;
	{#cid{name="sin"},[A]}     -> math:sin(A);
	{#cid{name="cos"},[A]}     -> math:cos(A);
	{#cid{name="trunc"},[A]}   -> trunc(A);
	{#cid{name="round"},[A]}   -> round(A);
	{#cid{name="abs"},[A]}     -> abs(A);
	{#cid{name="max"},[A,B]}   -> max(A,B);
	{#cid{name="min"},[A,B]}   -> min(A,B);
	{#cid{name="sum"},As}      ->
	    lists:foldl(fun(Ai,Sum) -> eval_meta(Ai,Bs)+Sum end, 0, As);
	{#cid{name=F},As1} -> {f,F,As1}
    end;
eval_meta(#cbinary{op=Op,arg1=A,arg2=B},Bs) ->
    A1 = eval_meta(A,Bs),
    B1 = eval_meta(B,Bs),
    if is_number(A1), is_number(B1) ->
	    case Op of
		'<' -> A1 < B1;
		'<=' -> A1 =< B1;
		'>' -> A1 > B1;
		'>=' -> A1 >= B1;
		'==' -> A1 == B1;
		'!=' -> A1 =/= B1;
		'&&' -> A1 and B1;
		'||' -> A1 or B1;
		'&' -> A1 band B1;
		'|' -> A1 bor B1;
		'^' -> A1 bxor B1;
		'<<' -> A1 bsl B1;
		'>>' -> A1 bsr B1;
		'+' -> A1+B1;
		'-' -> A1-B1;
		'*' -> A1*B1;
		'/' -> A1 div B1;
		'%' -> A1 rem B1
	    end;
       true ->
	    {Op,A1,B1}
    end;

eval_meta({sum,As},Bs) -> %% used???
    lists:foldl(fun(Ai,Sum) -> eval_meta(Ai,Bs)+Sum end, 0, As);

eval_meta(#cunary{op=Op,arg=A},Bs) ->
    A1 = eval_meta(A,Bs),
    if is_number(A1) ->
	    case Op of
		'-' -> -A1;
		'+' -> +A1;
		'~' ->  bnot A1;
		'!' -> not A1
	    end;
       true ->
	    {Op,A1}
    end.

eval_meta_list(As,Bs) ->
    lists:map(fun(A) -> eval_meta(A,Bs) end, As).
    
print(F) ->
    io:put_chars([fmt(F),"\n"]).

%% format formula.
fmt(true) -> "true";
fmt(false) -> "false";
fmt(X={p,_Nm,_Vs}) -> fmt_var(X);
fmt({Op,A,B}) ->
    ["(",fmt(A)," ",atom_to_list(Op)," ",fmt(B),")"];
fmt({Op,As}) when is_list(As) -> 
    [atom_to_list(Op),"(",fmt_list(As),")"];
fmt({Op,A}) ->   [atom_to_list(Op)," ",fmt(A)].

fmt_list([A]) -> [fmt(A)];
fmt_list([A|As]) -> [fmt(A),"," | fmt_list(As)];
fmt_list([]) -> [].

-ifdef(not_used).
fmt_q(X) ->
    fmt_var(X, "\"").
-endif.

fmt_var(X) ->
    fmt_var(X, "").

fmt_var({p,V,[]}, Q) -> 
    [Q,atom_to_list(V),Q];
fmt_var({p,V,As},Q) ->
    [Q,atom_to_list(V),"(",lists:join(",",[io_lib:format("~w",[X])||X<-As]),")",Q].

%%
%% Extract all variables from F
%%
variables(F) ->
    sets:to_list(vars(F,sets:new())).

vars(true, Set)  -> Set;
vars(false, Set) -> Set;
vars(V={p,_,_}, Set) -> sets:add_element(V, Set);
vars({'imp',F1,F2}, Set) -> vars(F2, vars(F1,Set));
vars({'->',F1,F2}, Set)  -> vars(F2, vars(F1,Set));
vars({'equ',F1,F2}, Set)  -> vars(F2, vars(F1,Set));
vars({'<->',F1,F2}, Set)  -> vars(F2, vars(F1,Set));
vars({'and',F1,F2}, Set) -> vars(F2, vars(F1,Set));
vars({'&&',F1,F2}, Set)  -> vars(F2, vars(F1,Set));
vars({'&',F1,F2}, Set)  -> vars(F2, vars(F1,Set));
vars({'or',F1,F2},  Set)  ->  vars(F2, vars(F1,Set));
vars({'||',F1,F2},  Set)  ->  vars(F2, vars(F1,Set));
vars({'|',F1,F2},  Set)  ->  vars(F2, vars(F1,Set));
vars({'xor',F1,F2}, Set) ->  vars(F2, vars(F1,Set));
vars({'!',F},Set) -> vars(F,Set);
vars({'not',F},Set) -> vars(F,Set);
vars({'~',F},Set) -> vars(F,Set);
%% may be present in some partially expanded forms
vars({all,Fs}, Set) -> vars_list(Fs, Set);
vars({any,Fs}, Set) -> vars_list(Fs, Set);
vars({one,Fs}, Set) -> vars_list(Fs, Set);
vars({none,Fs}, Set) -> vars_list(Fs, Set).

vars_list([F|Fs],Set) -> vars_list(Fs, vars(F,Set));
vars_list([],Set) -> Set.


%%
%% Test case
%% 
%%


ysat_skolem(N) ->
    R0 = formula(formulas:ysat(N)),
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
    F = formula(formulas:ysat(N)),
    RI  = [{r,I} || I <- lists:seq(1,N)],
    R1 =
	any(
	  lists:map(
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
    lists:map(
      fun(I) ->
	      Row = [X =:= 1 || <<X:1>> <= <<I:K>>],
	      Assign = lists:zip(PIJQIJ, Row),
	      Dict = dict:from_list(Assign),
	      {eval(F, Dict), Assign} 
      end, lists:seq(0, (1 bsl K)-1)).

test_print(N) ->
    G=lists:filter(fun({R,_}) -> not R end, test_gunnar(N)),
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
    lists:foldl(
      fun(I,Count) ->
	      Row = [X =:= 1 || <<X:1>> <= <<I:K>>],
	      Assign = lists:zip(PIJQIJ, Row),
	      Dict = dict:from_list(Assign),
	      case eval(F, Dict) of
		  true -> Count+1;
		  false -> Count
	      end
      end, 0, lists:seq(0, (1 bsl K)-1)).

