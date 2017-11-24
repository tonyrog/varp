%%
%% Basic prover in erlang
%%
-module(vare).

-export([new/1]).
-export([fresh_var/1]).
-export([number_of_variables/1]).
-export([number_of_bound/1]).
-export([number_of_unbound/1]).
-export([first_init/1]).
-export([first_unbound/1]).
-export([next_unbound/2]).
-export([latest_bound/1]).
-export([value/2]).
-export([class/2]).
-export([is_bound/2]).
-export([is_unbound/2]).
-export([order/2]).
-export([clause/2]).
-export([get_bindings/1]).
-export([equal/3]).
-export([mark/1]).
-export([eval/1]).
-export([enq_all/1]).

-include("log.hrl").

%% -define(dbg(F,A), io:format((F),(A))).
-define(dbg(F,A), ok).

-define(TRUE,   1).
-define(FALSE, -1).

-define(is_int_type(T),   (((T)=:=int) orelse ((T)=:=uint))).
-define(is_vec_type(T), (((T)=:=int) orelse ((T)=:=uint) orelse ((T)=:=bit))).
-define(pair(A,B),  [(A)|(B)]).

-record(ts,
	{
	  n = 1,   %% next free triple
	  triple,  %% array 1..N of triple (TI -> T)
	  xref,    %% array 1..M of [Ti]   (Var -> [Ti])
	  queue,   %% triple queue
	  qset     %% Ti -> boolean
	}).

-record(vare,
	{
	  n = 2,            %% next free variable
	  vt :: array:array(),    %% variable binding Vn => Wm
	  vc :: array:array(),    %% variable classes
	  order :: array:array(), %% variable order I => V
	  depth :: integer(), %% backtrack/saturate depth
	  bn :: integer(),  %% number of bound variables
	  bl :: list(),     %% list of bound variables
	  ts,               %% ::ts triples during build
	  option :: #option{}  %% options
	}).

new(Opt) ->
    Ts = #ts { triple = array:new(),
	       xref   = array:new([{default, []}]),
	       queue  = queue:new(),
	       qset   = sets:new()
	     },
    #vare {
       vt = array:from_list([0,1], 0),
       vc = array:new([{default,0}]),
       depth = 0,
       bn = 0,
       bl = [], 
       ts = Ts,
       option = Opt }.

fresh_var(Vare) ->
    N  = Vare#vare.n,
    {N, Vare#vare { n = N+1 }}.

number_of_variables(Vare) ->
    Vare#vare.n - 2.

number_of_bound(Vare) ->
    Vare#vare.bn.

number_of_unbound(Vare) ->
    number_of_variables(Vare) - Vare#vare.bn.

first_init(_Vare) ->
    1.

first_unbound(Vare) ->
    next_unbound(first_init(Vare), Vare).

next_unbound(I, Vare) ->
    next_unbound_(I+1, number_of_variables(Vare)+1, Vare).

next_unbound_(I, Max, Vare) when I =< Max ->
    if Vare#vare.order =:= undefined ->
	    case is_unbound(I, Vare) of
		true  -> {I,I};
		false -> next_unbound_(I+1,Max,Vare)
	    end;
       true ->
	    Xi = array:get(I, Vare#vare.order),
	    ?dbg("order[~w] = ~w, vt[~w]=~w\n", 
		 [I, Xi, Xi, array:get(Xi,Vare#vare.vt)]),
	    case is_unbound(Xi, Vare) of
		true  -> {I,Xi};
		false -> next_unbound_(I+1,Max,Vare)
	    end
    end;
next_unbound_(_X, _N, _Vare) ->
    false.

get_bindings(Vare) ->
    Vare#vare.bl.

latest_bound(Vare) ->
    take_until_mark_(Vare#vare.bl).

-ifdef(__UNDEFINED__).
take_skip_mark_([mark|Xs]) -> take_skip_mark_(Xs);
take_skip_mark_([X|Xs]) -> [X|take_skip_mark_(Xs)];
take_skip_mark_([]) -> [].
-endif.

take_until_mark_([mark|_]) -> [];
take_until_mark_([{_,{X,_,_}}|Xs]) -> [X|take_until_mark_(Xs)];
take_until_mark_([]) -> [].

%% 
%% {'and', x0, x1, ... xn-1}   x0 = x1 AND .. xn-1
%% {'or', x0, x1, ... xn-1}    x0 = x1 OR  .. xn-1
%% {'xor', x0, x1, ... xn-1}   x0 = x1 XOR .. xn-1
%%
clause(_T={'and',X0,X1,X2}, Vare) ->
    triple(imp,-X0,X1,-X2,Vare);
clause(_T={'or',X0,X1,X2}, Vare) ->
    triple(imp,X0,-X1,X2,Vare);
clause(_T={'xor',X0,X1,X2}, Vare) ->
    triple(equ,X0,-X1,X2,Vare);
clause(_T={'equ',X0,X1,X2}, Vare) ->
    triple(equ,X0,X1,X2,Vare);
clause(_T={'and',[X0|As]},Vare) ->
    %% io:format("T = ~p\n", [_T]),
    fold_op('and',X0,?TRUE,As,Vare);
clause(_T={'or',[X0|As]},Vare) ->
    %% io:format("T = ~p\n", [_T]),
    fold_op('or',X0,?FALSE,As,Vare);
clause(_T={'xor',[X0|As]},Vare) ->
    %% io:format("T = ~p\n", [_T]),
    fold_op('xor',X0,?FALSE,As,Vare).

fold_op(Op,X0,A0,As,Vare) ->
    case (Vare#vare.option)#option.assoc of
	left ->  foldl_op(Op,X0,A0,As,Vare);
	right -> foldr_op(Op,X0,A0,As,Vare);
	middle -> foldm_op(Op,X0,A0,As,Vare)
    end.

%% 
%%  (( ((x1 AND x2) AND x3) .. xn-2 ) AND x-1)
%%
%%  y1 = x1 AND x2
%%  y2 = y1 AND x3
%%  y3 = y2 AND x4
%%  ...
%%  x0 = yk AND xn-1

foldl_op(Op,X0,A0,[X1],Vare) ->
    clause({Op,X0,X1,A0},Vare);
foldl_op(Op,X0,_A0,[X1,X2],Vare) ->
    clause({Op,X0,X1,X2},Vare);
foldl_op(Op,X0,A0,[X1,X2|Xs],Vare) ->
    {Y1,Vare1} = fresh_var(Vare),
    Vare2 = clause({Op,Y1,X1,X2},Vare1),
    foldl_op(Op,X0,A0,[Y1|Xs],Vare2).

%%
%% (x1 AND (x2 AND (x3 AND ... (xn-2 AND xn-1)))) 
%%
%%  yk    = xn-2 AND xn-1
%%  yk-1  = xn-3 AND yk
%%  ...
%%  y2    = x2 AND y3
%%  x0    = x1 AND y2
%%

foldr_op(Op,X0,A0,[X1],Vare) ->
    clause({Op,X0,X1,A0},Vare);
foldr_op(Op,X0,_A0,[X1,X2],Vare) ->
    clause({Op,X0,X1,X2},Vare);
foldr_op(Op,X0,A0,[X1,X2|Xs],Vare) ->
    {Y2,Vare1} = fresh_var(Vare),
    Vare2 = foldr_op(Op,Y2,A0,[X2|Xs],Vare1),
    clause({Op,X0,X1,Y2},Vare2).

%%  y1 = x1 AND x2
%%  y2 = xn-1 AND xn-2
%%  ...
%%  x0 = yi AND yj

foldm_op(Op,X0,A0,[X1],Vare) ->
    clause({Op,X0,X1,A0},Vare);
foldm_op(Op,X0,_A0,[X1,X2],Vare) ->
    clause({Op,X0,X1,X2},Vare);
foldm_op(Op,X0,A0,Xs,Vare) ->
    case lists:split(length(Xs) div 2, Xs) of
	{[],[X2]} ->
	    clause({Op,X0,A0,X2},Vare);
	{[X1],[X2]} ->
	    clause({Op,X0,X1,X2},Vare);
	{[X1],[X2,X3]} ->
	    {Y1,Vare1} = fresh_var(Vare),
	    Vare2 = clause({Op,Y1,X2,X3},Vare1),
	    clause({Op,X0,X1,Y1},Vare2);
	{Xs1,Xs2} ->
	    {Y1,Vare1} = fresh_var(Vare),
	    {Y2,Vare2} = fresh_var(Vare1),
	    Vare3 = foldm_op(Op,Y1,A0,Xs1,Vare2),
	    Vare4 = foldm_op(Op,Y2,A0,Xs2,Vare3),
	    clause({Op,X0,Y1,Y2},Vare4)
    end.


triple(Op,X,Y,Z,Vare) ->
    ?debug(Vare#vare.option, "Triple: ~w:~w ~w ~w\n", [X,Y,Op,Z]),
    Ts = Vare#vare.ts,
    Ti  = Ts#ts.n,
    Tp = array:set(Ti, {Op,X,Y,Z}, Ts#ts.triple),
    X0 = Ts#ts.xref,
    X1 = append_xref_(X, Ti, X0),
    X2 = append_xref_(Y, Ti, X1),
    X3 = append_xref_(Z, Ti, X2),
    N  = Ti+1,
    Ts1 = Ts#ts { n = N, triple=Tp, xref=X3 },
    if Ti rem 1000 =:= 999 ->
	    ?info(Vare#vare.option, "triples: ~w\n", [N]);
       true -> ok
    end,
    Vare#vare { ts=Ts1 }.

append_xref_(?TRUE, _Ti, Xref) -> Xref;
append_xref_(?FALSE, _Ti, Xref) -> Xref;
append_xref_(V, Ti, Xr) when V < 0 -> append_xref_(-V, Ti, Xr);
append_xref_(V, Ti, Xr) -> array:set(V, [Ti|array:get(V, Xr)], Xr).

class_next(X, Vare) ->
    array:get(X, Vare#vare.vc).

value(?FALSE, _Vare) -> ?FALSE;
value(?TRUE, _Vare)  -> ?TRUE;
value(X, Vare) when X > 0 ->
    case array:get(X, Vare#vare.vt) of
	0 -> X;
	X1 -> value(X1, Vare)
    end;
value(X, Vare) when X < 0 ->
    -value(-X, Vare).

%% get class variable (with out sign!)
class(?FALSE, _Vare) -> ?FALSE;
class(?TRUE, _Vare)  -> ?TRUE;
class(X, Vare) when X > 0 ->
    case array:get(X, Vare#vare.vc) of
	0 -> X;
	X1 -> class(X1,Vare)
    end;
class(X, Vare) when X < 0 ->
    case array:get(-X, Vare#vare.vc) of
	0 -> X;
	X1 -> class(-X1,Vare)
    end.

%% true if Y is in X's bound chain
-ifdef(__UNDEFINED__).
in_chain(X, Y, Vare) when X < 0 ->
    in_chain(-X, Y, Vare);
in_chain(X, Y, Vare) ->
    case array:get(X, Vare#vare.vt) of
	?TRUE  -> false;
	?FALSE -> false;
	X -> false;
	X1 when X1 =:= Y -> true;
	X1 when X1 =:= -Y -> true;
	X1 -> in_chain(X1,Y,Vare)
    end.
-endif.


is_unbound(X, Vare) when X > 1 ->
    array:get(X, Vare#vare.vt) =:= 0.

is_bound(X, Vare) when X > 1 ->
    array:get(X, Vare#vare.vt) =/= 0.

order(What, Vare) ->
    Vx0 = array:from_list([0,1|lists:seq(2,Vare#vare.n-1)]),
    Vx1 = order_(What, Vx0, Vare),
    %% Map = lists:zip(array:to_list(Vx0),array:to_list(Vx1)),
    %% ?dbg("order map=~w\n", [Map]),
    %% ?dbg("order rmap=~w\n", [[{Y,X}||{X,Y} <-lists:keysort(2, Map)]]),
    Vare#vare { order=Vx1 }.

order_([W|Ws], Vx0, Vare) ->
    Vx1 = order__(W, Vx0, Vare),
    order_(Ws, Vx1, Vare);
order_([], Vx0, _Vare) ->
    Vx0;
order_(W, Vx0, Vare) when is_atom(W) ->
    order__(W, Vx0, Vare);
order_(W={uint,_V,_N,_I}, Vx0, Vare) ->
    order__(W, Vx0, Vare);
order_(W={int,_V,_N,_I}, Vx0, Vare) ->
    order__(W, Vx0, Vare);
order_(W={bit,_V,_N,_I}, Vx0, Vare) ->
    order__(W, Vx0, Vare).

order__(identity,Vx0,_Vare) ->
    Vx0;
order__(reverse,Vx0,_Vare) ->
    [_,_|As] = array:to_list(Vx0),
    array:from_list([0,1|lists:reverse(As)]);
order__(depth, _Vx0, Vare) ->
    A = calculate_depth(Vare),
    array:from_list([0,1|
		     lists:sort(
		       fun(X,Y) -> array:get(X,A) < array:get(Y,A) end,
		       lists:seq(2,Vare#vare.n-1))]);
order__(occure, _Vx0, Vare) ->
    A = calculate_occure(Vare),
    array:from_list([0,1|
		     lists:sort(
		       fun(X,Y) -> array:get(X,A) < array:get(Y,A) end,
		       lists:seq(2,Vare#vare.n-1))]);
order__(depth_occure, _Vx0, Vare) ->
    A0 = calculate_depth(Vare),
    A1 = calculate_occure(Vare),
    array:from_list([0,1|
		     lists:sort(
		       fun(X,Y) ->
			       X0 = array:get(X,A0),
			       Y0 = array:get(Y,A0),
			       if X0 =:= Y0 ->
				       array:get(X,A1) < array:get(Y,A1);
				  true ->
				       X0 < Y0
			       end
		       end, lists:seq(2,Vare#vare.n-1))]);
order__(occure_depth, _Vx0, Vare) ->
    A0 = calculate_occure(Vare),
    A1 = calculate_depth(Vare),
    array:from_list([0,1|
		     lists:sort(
		       fun(X,Y) ->
			       X0 = array:get(X,A0),
			       Y0 = array:get(Y,A0),
			       if X0 =:= Y0 ->
				       array:get(X,A1) < array:get(Y,A1);
				  true ->
				       X0 < Y0
			       end
		       end, lists:seq(2,Vare#vare.n-1))]);
order__(Var, Vx0, Vare) when 
      is_integer(Var), Var > 1, Var < Vare#vare.n ->
    order_first(Var, Vx0).

%% put variable X first!
order_first(X, Vx0) ->
    [0,1|List] = array:to_list(Vx0),
    array:from_list([0,1,X|(List -- [X])]).

%%
%% Calculate variable occurence
%%
calculate_occure(Vare) ->
    Ts = Vare#vare.ts,
    array:sparse_foldl(
      fun(_,{_,X,Y,Z},A0) ->
	      A1 = occure(X, A0),
	      A2 = occure(Y, A1),
	      occure(Z, A2)
      end, array:new([{default,0}]), Ts#ts.triple).

occure(X, A) when X < ?FALSE -> occure(-X, A);
occure(X, A) when X > ?TRUE -> array:set(X, array:get(X,A)+1, A);
occure(?TRUE, A) -> A;
occure(?FALSE, A) -> A.

%%
%% create a array with depth for each variable literals are 0
%% triple {X,A,B} variable X depth is calcluated like
%%  depth(X)=max(depth(A),depth(B))+1
%%
%% assume at most one triple defintion variable
%%
%% {X,Y,Z}      ... {Y,A,B} ... {Z,C,D} ...
%% X < Y < Z
%%
%%
calculate_depth(Vare) ->
    Ts = Vare#vare.ts,
    Vs = varp_topsort:triples(Ts),
    calc_depth(Vs,Ts,array:new([{default,0}])).

calc_depth([X|Xs],Ts,A) ->
    case lists:keyfind(X, 1, Ts) of
	false ->
	    case lists:keyfind(-X, 1, Ts) of
		false ->
		    calc_depth(Xs,Ts,A);
		{_,Y,Z} ->
		    Yd = array:get(abs(Y),A),
		    Zd = array:get(abs(Z),A),
		    calc_depth(Xs,Ts,array:set(X, max(Yd,Zd)+1, A))
	    end;
	{_,Y,Z} ->
	    Yd = array:get(abs(Y),A),
	    Zd = array:get(abs(Z),A),
	    calc_depth(Xs,Ts,array:set(X, max(Yd,Zd)+1, A))
    end;
calc_depth([],_Ts,A) ->
    A.

%%
%% eval(Ts, Vare) -> Vare'
%%
eval(Vare) ->
    eval_(Vare#vare.ts,Vare).

eval_(Ts, Vare) ->
    case (Vare#vare.option)#option.bcp of
	true ->
	    eval_bcp(Ts#ts.queue, Ts#ts.qset, Ts, Vare);
	false ->
	    eval_eqv(Ts#ts.queue, Ts#ts.qset, Ts, Vare)
    end.

%%
%% Full eval with equivalence classes
%%

eval_eqv(Q, Qset, Ts, Vare) ->
    case queue:out(Q) of
	{empty, Q1} ->
	    Ts1 = Ts#ts { queue=Q1, qset=sets:new() },
	    Vare#vare { ts=Ts1};
	{{value,Ti},Q1} ->
	    T={Op,Xt,Yt,Zt} = array:get(Ti, Ts#ts.triple),
	    X = value(Xt, Vare),
	    Y = value(Yt, Vare),
	    Z = value(Zt, Vare),
	    ?dbg("EVAL: ~s\n", [fmt_triple(T,Vare)]),
	    As = eval_op(Op,T,X,Y,Z),
	    {XRef,Vare1} = equal_list_(As,[],Vare,Ts),
	    eval_enq_eqv(Q1, sets:del_element(Ti, Qset), XRef, Ts, Vare1)
    end.

eval_enq_eqv(Q, Qset, [Ti|Tis], Ts, Vare) ->
    case sets:is_element(Ti, Qset) of
	false ->
	    Q1 = queue:in(Ti, Q),
	    Qset1 = sets:add_element(Ti, Qset),
	    eval_enq_eqv(Q1, Qset1, Tis, Ts, Vare);
	true ->
	    eval_enq_eqv(Q, Qset, Tis, Ts, Vare)
    end;
eval_enq_eqv(Q, Qset, [], Ts, Vare) ->
    eval_eqv(Q, Qset, Ts, Vare).

%%
%% @doc
%% eval_op:
%%    Generate binding consequence edge from tripple information.
%%    The edge {{X,Xv},{Y,Yv}} means that when X/Xv -> Y/Yv
%% @end
%%
eval_op(imp,T={_,Xt,_Yt,_Zt},?FALSE,Y,Z) -> [{T,{Xt,?FALSE},{Y,?TRUE}},
					     {T,{Xt,?FALSE},{Z,?FALSE}}];
eval_op(imp,T={_,_Xt,Yt,_Zt},X,?TRUE,Z)   -> [{T,{Yt,?TRUE},{X,Z}}];
eval_op(imp,T={_,_Xt,Yt,_Zt},X,?FALSE,_Z) -> [{T,{Yt,?FALSE},{X,?TRUE}}];
eval_op(imp,T={_,_Xt,_Yt,Zt},X,_Y,?TRUE)  -> [{T,{Zt,?TRUE},{X,?TRUE}}];
eval_op(imp,T={_,_Xt,_Yt,Zt},X,Y,?FALSE)  -> [{T,{Zt,?FALSE},{X,-Y}}];
eval_op(imp,T={_,_Xt,_Yt,Zt},X,Y,Y)       -> [{T,{Zt,Y},{X,?TRUE}}];
eval_op(imp,T={_,_Xt,_Yt,Zt},X,Y,Z) when Y =:= -Z -> [{T,{Zt,-Y},{X,Z}}];
eval_op(imp,_T,_X,_Y,_Z) -> [];
eval_op(equ,T={_,Xt,_Yt,_Zt},?TRUE,Y,Z)  -> [{T,{Xt,?TRUE},{Y,Z}}];
eval_op(equ,T={_,Xt,_Yt,_Zt},?FALSE,Y,Z) -> [{T,{Xt,?FALSE},{Y,-Z}}];
eval_op(equ,T={_,_Xt,Yt,_Zt},X,?TRUE,Z)  -> [{T,{Yt,?TRUE},{X,Z}}];
eval_op(equ,T={_,_Xt,Yt,_Zt},X,?FALSE,Z) -> [{T,{Yt,?FALSE},{X,-Z}}];
eval_op(equ,T={_,_Xt,_Yt,Zt},X,Y,?TRUE)  -> [{T,{Zt,?TRUE},{X,Y}}];
eval_op(equ,T={_,_Xt,_Yt,Zt},X,Y,?FALSE) -> [{T,{Zt,?FALSE},{X,-Y}}];
eval_op(equ,T={_,_Xt,_Yt,Zt},X,Y,Y)      -> [{T,{Zt,Y},{X,?TRUE}}];
eval_op(equ,T={_,_Xt,_Yt,Zt},X,Y,Z) when Y =:= -Z -> [{T,{Zt,-Y},{X,?FALSE}}];
eval_op(equ,_T,_X,_Y,_Z) -> [].


%%
%% BCP version
%%

eval_bcp(Q, Qset, Ts, Vare) ->
    case queue:out(Q) of
	{empty, Q1} ->
	    Ts1 = Ts#ts { queue=Q1, qset=sets:new() },
	    Vare#vare { ts=Ts1};
	{{value,Ti},Q1} ->
	    T={Op,Xt,Yt,Zt} = array:get(Ti, Ts#ts.triple),
	    X = value(Xt, Vare),
	    Y = value(Yt, Vare),
	    Z = value(Zt, Vare),
	    ?dbg("EVAL: ~s\n", [fmt_triple(T,Vare)]),
	    As = eval_bcp(Op,T,X,Y,Z),
	    {XRef,Vare1} = equal_list_(As,[],Vare,Ts),
	    eval_enq_bcp(Q1, sets:del_element(Ti, Qset), XRef, Ts, Vare1)
    end.

eval_enq_bcp(Q, Qset, [Ti|Tis], Ts, Vare) ->
    case sets:is_element(Ti, Qset) of
	false ->
	    Q1 = queue:in(Ti, Q),
	    Qset1 = sets:add_element(Ti, Qset),
	    eval_enq_bcp(Q1, Qset1, Tis, Ts, Vare);
	true ->
	    eval_enq_bcp(Q, Qset, Tis, Ts, Vare)
    end;
eval_enq_bcp(Q, Qset, [], Ts, Vare) ->
    eval_bcp(Q, Qset, Ts, Vare).

%% @doc
%% eval_bcp:
%%    Generate binding consequence edge from tripple information.
%%    The edge {{X,Xv},{Y,Yv}} means that when X/Xv -> Y/Yv
%%    No equivalence classes are generated!
%% @end

eval_bcp(imp,T={_,Xt,_Yt,_Zt},?FALSE,Y,Z) -> [{T,{Xt,?FALSE},{Y,?TRUE}},
					      {T,{Xt,?FALSE},{Z,?FALSE}}];
eval_bcp(imp,T={_,_Xt,Yt,_Zt},X,?TRUE,?FALSE) -> [{T,{Yt,?TRUE},{X,?FALSE}}];
eval_bcp(imp,T={_,_Xt,Yt,_Zt},X,?TRUE,?TRUE)  -> [{T,{Yt,?TRUE},{X,?TRUE}}];
eval_bcp(imp,T={_,_Xt,Yt,_Zt},X,?FALSE,_Z) -> [{T,{Yt,?FALSE},{X,?TRUE}}];
eval_bcp(imp,T={_,_Xt,_Yt,Zt},X,_Y,?TRUE)  -> [{T,{Zt,?TRUE},{X,?TRUE}}];
eval_bcp(imp,T={_,_Xt,_Yt,Zt},X,Y,Y)       -> [{T,{Zt,Y},{X,?TRUE}}];
eval_bcp(imp,_T,_X,_Y,_Z) -> [];

%% eval_bcp(equ,T={_,Xt,_Yt,_Zt},?TRUE,Y,Z)  -> [{T,{Xt,?TRUE},{Y,Z}}];
eval_bcp(equ,T={_,Xt,_Yt,_Zt},?TRUE,Y,?TRUE) -> [{T,{Xt,?TRUE},{Y,?TRUE}}];
eval_bcp(equ,T={_,Xt,_Yt,_Zt},?TRUE,Y,?FALSE) -> [{T,{Xt,?TRUE},{Y,?FALSE}}];
eval_bcp(equ,T={_,Xt,_Yt,_Zt},?TRUE,?TRUE,Z) -> [{T,{Xt,?TRUE},{Z,?TRUE}}];
eval_bcp(equ,T={_,Xt,_Yt,_Zt},?TRUE,?FALSE,Z) -> [{T,{Xt,?TRUE},{Z,?FALSE}}];
eval_bcp(equ,T={_,Xt,_Yt,_Zt},?FALSE,Y,?TRUE) -> [{T,{Xt,?FALSE},{Y,?FALSE}}];
eval_bcp(equ,T={_,Xt,_Yt,_Zt},?FALSE,Y,?FALSE) -> [{T,{Xt,?FALSE},{Y,?TRUE}}];
eval_bcp(equ,T={_,Xt,_Yt,_Zt},?FALSE,?TRUE,Z) -> [{T,{Xt,?FALSE},{Z,?FALSE}}];
eval_bcp(equ,T={_,Xt,_Yt,_Zt},?FALSE,?FALSE,Z) -> [{T,{Xt,?FALSE},{Z,?TRUE}}];

eval_bcp(equ,T={_,_Xt,Yt,_Zt},X,?TRUE,?FALSE) -> [{T,{Yt,?TRUE},{X,?FALSE}}];
eval_bcp(equ,T={_,_Xt,Yt,_Zt},X,?TRUE,?TRUE)  -> [{T,{Yt,?TRUE},{X,?TRUE}}];
eval_bcp(equ,T={_,_Xt,Yt,_Zt},X,?FALSE,?TRUE) -> [{T,{Yt,?FALSE},{X,?TRUE}}];
eval_bcp(equ,T={_,_Xt,Yt,_Zt},X,?FALSE,?FALSE) -> [{T,{Yt,?TRUE},{X,?TRUE}}];
eval_bcp(equ,_T,_X,_Y,_Z) -> [].

%% a bit more high level handle {bool,X} already bound values etc.
equal(X,Y,Vare) ->
    ?dbg("equal: ~w = ~w\n", [X, Y]),
    X1 = value(X,Vare),
    Y1 = value(Y,Vare),
    Ts = Vare#vare.ts,
    {XRef,Vare1} = equal__(X1,Y1,decision,Vare,Ts),
    enq(Ts#ts.queue, Ts#ts.qset, XRef, Ts, Vare1).

enq(Q, Qset, [Ti|Tis], Ts, Vare) ->
    case sets:is_element(Ti, Qset) of
	false ->
	    Q1 = queue:in(Ti, Q),
	    Qset1 = sets:add_element(Ti, Qset),
	    enq(Q1, Qset1, Tis, Ts, Vare);
	true ->
	    enq(Q, Qset, Tis, Ts, Vare)
    end;
enq(Q, Qset, [], Ts, Vare) ->
    Ts1 = Ts#ts { queue=Q, qset=Qset },
    Vare#vare {ts=Ts1}.

enq_all(Vare) ->
    Ts = Vare#vare.ts,
    enq_all(Ts#ts.queue, Ts#ts.qset, 1, Ts#ts.n, Ts, Vare).

enq_all(Q, Qset, Ti, N, Ts, Vare) when Ti =< N ->
    case array:get(Ti, Ts#ts.triple) of
	undefined ->
	    enq_all(Q, Qset, Ti+1, N, Ts, Vare);
	_T ->
	    case sets:is_element(Ti, Qset) of
		false ->
		    Q1 = queue:in(Ti, Q),
		    Qset1 = sets:add_element(Ti, Qset),
		    enq_all(Q1, Qset1, Ti+1, N, Ts, Vare);
		true ->
		    enq_all(Q, Qset, Ti+1, N, Ts, Vare)
	    end
    end;
enq_all(Q, Qset, _Ti, _N, Ts, Vare) ->
    Ts1 = Ts#ts { queue=Q, qset=Qset },
    Vare#vare {ts=Ts1}.

    

%% eval a binding list
equal_list_([{_T,P,{X,Y}}|List],XRef,Vare,Ts) ->
    %% ?dbg("~w : ~w => ~w\n", [_T,P,{X,Y}]),
    X1 = value(X,Vare),
    {XRef1,Vare1} = equal__(X1,Y,P,Vare,Ts),
    equal_list_(List,XRef++XRef1,Vare1,Ts);
equal_list_([],XRef,Vare,_Ts) ->
    {XRef,Vare}.

%% equal__ with info about trigger Xp=Yp
%% return:
%%    {[],Vare}     when noop
%%    {[Ti], Vare}  when binding set
%%    throw(contractdition)
%%

equal__(X,Y,_P,_Vare,_Ts) 
  when X =:= -Y -> 
    %% fixme add _P
    %% show_fail(_Vare),
    throw(contradiction);
equal__(X,X,_P,Vare,_Ts) -> 
    {[],Vare};
equal__(?TRUE,Y,P,Vare,Ts) ->
    if Y < 0 -> eq__(-Y,?FALSE,P,Vare,Ts);
       true ->  eq__(Y,?TRUE,P,Vare,Ts)
    end;
equal__(?FALSE,Y,P,Vare,Ts) ->
    if Y < 0 -> eq__(-Y,?TRUE,P,Vare,Ts);
       true ->  eq__(Y,?FALSE,P,Vare,Ts)
    end;
equal__(X,Y,P,Vare,Ts) when X < 1 -> eq__(-X,-Y,P,Vare,Ts);
equal__(X,Y,P,Vare,Ts) when X > 1 -> eq__(X,Y,P,Vare,Ts).

%%
%% X=Y  when P=(Xp,Dp,Yp) 
%%  X must be unbound 
%%  Y should not have X in it's values chain
%%
eq__(X,Y,P,Vare,Ts) ->
    D    = Vare#vare.depth,
    Bl = add_edge(P,{X,D,Y},Vare#vare.bl,Vare),
    case Bl of
	[{{_Xp,_Dp,_Yp},_}|_] ->
	    ?dbg("  _eq: ~s/~s(~w) [when ~s/~s(~w)]\n", 
		 [fmt_var(X,Vare),fmt_var(Y,Vare), D,
		  fmt_var(_Xp,Vare),fmt_var(_Yp,Vare),_Dp]);
	[{decision,_}|_] ->
	    ?dbg("  _eq: ~s/~s(~w)\n",
		 [fmt_var(X,Vare),fmt_var(Y,Vare), D]);
	[{true,_}|_] ->
	    ?dbg("  _eq: ~s/~s(~w)\n",
		 [fmt_var(X,Vare),fmt_var(Y,Vare), D])
    end,
    Vt   = array:set(X, Y, Vare#vare.vt),
    Bn   = Vare#vare.bn+1,
    XRef = get_xref(X,Vare,Ts),
    Vare1 = case class(Y,Vare) of
	      ?TRUE  ->
		  Vare#vare { vt = Vt, bn=Bn, bl=Bl };
	      ?FALSE ->
		  Vare#vare { vt = Vt, bn=Bn, bl=Bl };
	      Yc when Yc < 0 ->
		  Vc = array:set(-Yc, -X, Vare#vare.vc),
		  Vare#vare { vt = Vt, vc = Vc, bn=Bn, bl=Bl };
	      Yc ->
		  Vc = array:set(Yc, X, Vare#vare.vc),
		  Vare#vare { vt = Vt, vc = Vc, bn=Bn, bl=Bl }
	  end,
    {XRef,Vare1}.

add_edge(decision,Q,Bl,_Vare) ->
    [{decision,Q}|Bl];
add_edge(P,Q,Bl,Vare) ->
    %% ?dbg("~w => ~w :BL=~w\n", [P,Q,Bl]),
    case find_edge_start(P,Bl,Vare) of
	true    -> [{true,Q}|Bl]; %% FIXME
	{P1,ok} -> [{P1,Q} | Bl];
	{P1,P2} ->
	    %% ?dbg("ADD EDGE 2\n"),
	    add_edge(P2,Q,[{P1,Q}|Bl],Vare)
    end.

%% find & normalize vertex
find_edge_start({X,Y},Bl,Vare) when X < 0 -> find_edge_start({-X,-Y},Bl,Vare);
find_edge_start({X,X},_Bl,_Vare) -> true;
find_edge_start(P,Bl,Vare) -> find_edge_start_(P,Bl,Vare).

find_edge_start_({X,Y},[{_,{X,D,Y}}|_],_Vare) -> {{X,D,Y},ok};
find_edge_start_({X,Y},[{_,{X,D,Y1}}|_],Vare) ->
    case value(Y1, Vare) of
	Y -> {{X,D,Y},{Y1,Y}}
    end;
find_edge_start_(P,[_|Bl],Vare) -> find_edge_start_(P,Bl,Vare).

%%
%% Mark binding list
%%
mark(Vare) ->
    Bl = [mark | Vare#vare.bl],
    Vare#vare { bl = Bl }.

%% get all triples from all classes for variable X
get_xref(X,Vare,Ts) when X > 0 ->
    array:get(X, Ts#ts.xref) ++ get_xref(class_next(X,Vare),Vare,Ts);
get_xref(X,Vare,Ts) when X < 0 -> get_xref(-X,Vare,Ts);
get_xref(0, _Ts, _Vare) -> [].


fmt_triple({Op,X,Y,Z}, Vare) ->
    [fmt_var(X,Vare),":",fmt_var(Y,Vare),fmtop(Op),fmt_var(Z,Vare)].

fmt_var(?TRUE, _) -> "true";
fmt_var(?FALSE, _) -> "false";
fmt_var(X,_) when X < 0 -> [$~,$$ | integer_to_list(-X)];
fmt_var(X,_) -> [$$ | integer_to_list(X)].

fmtop(imp) -> "->";
fmtop(equ) -> "<->";
fmtop('xor') -> " ^ ";
fmtop('and') -> " & ";
fmtop('or') -> " | ";
fmtop('not') -> "~".
