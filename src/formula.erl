%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2012, Tony Rogvall
%%% @doc
%%%    Building formulas
%%% @end
%%% Created :  2 Sep 2012 by Tony Rogvall <tony@rogvall.se>

-module(formula).

-export([build/1, build/2]).
-export([new/0, new/1]).
-export([fresh_var/1]).
-export([variable/2, alias/3]).
-export([value/2, is_input/2]).
-export([fmt_var/2]).
%% building with operations
-export([operation/4, operation/3]).
-export([all/2, any/2]).
-export([eqk/4, gtk/4]).
-export([set_bt_depth/2]).
-export([get_bt_depth/1]).

-compile(export_all).
-import(lists, [map/2, reverse/1]).

-define(TRUE,   1).
-define(FALSE, -1).

-define(LOG_NONE, -1).
-define(EMERGENCY, 0).
-define(ALERT,     1).
-define(CRITICAL,  2).
-define(ERROR,     3).
-define(WARNING,   4).
-define(NOTICE,    5).
-define(INFO,      6).
-define(DEBUG,     7).

-define(is_int_type(T),   (((T)=:=int) orelse ((T)=:=uint))).
-define(is_vec_type(T), (((T)=:=int) orelse ((T)=:=uint) orelse ((T)=:=bit))).
-define(pair(A,B),  [(A)|(B)]).

%% -define(dbg(F,A), io:format((F),(A))).
-define(dbg(F,A), ok).

-record(ts,
	{
	  n = 1,   %% next free triple
	  triple,  %% array 1..N of triple (TI -> T)
	  xref,    %% array 1..M of [Ti]   (Var -> [Ti])
	  queue,   %% triple queue
	  qset     %% Ti -> boolean
	}).


-record(bs,
	{
	  n = 2,            %% next free variable
	  vs,               %% dict() model variables var <=> Vn
	  vt :: array(),    %% variable binding Vn => Wm
	  vc :: array(),    %% variable classes
	  order :: array(), %% variable order I => V
	  depth :: integer(), %% backtrack/saturate depth
	  bn :: integer(),  %% number of bound variables
	  bl :: list(),     %% list of bound variables
	  options = 
	      [{value,none},           %% formula value true|false|none
	       {order,identity},       %% variable order
	       {print,false},          %% print models when found
	       {log,?LOG_NONE},
	       {max,0},                %% max number of models presented
	       {method,collect},       %% model collect|count
	       {carry,ignore},         %% ignore carry condition
	       {borrow,ignore},        %% ignore borrow condition
	       {divide_by_zero,false}, %% do not accept divide by zero
	       {eval_bcp, false},      %% simple eval
	       {saturate, 0},          %% plain eval
	       {saturate_threshold,0}, %% >i variables changed -> loop again
	       {saturate_pair, true}], %% saturate pair algoritm
	  meta=[],  %% meta variable bindings during build
	  subst=[], %% var/function substitution(s)
	  ts       %% ::ts triples during build
	}).

new() ->
    new([]).

new(Opts) ->
    Ts = 
	#ts { triple = array:new(),
	      xref   = array:new([{default, []}]),
	      queue  = queue:new(),
	      qset   = sets:new()
	    },
    Bs = #bs { vs = dict:from_list([{true,?TRUE},{?TRUE,true},
				    {false,?FALSE},{?FALSE,false}]),
	       vt = array:from_list([0,1], 0),
	       vc = array:new([{default,0}]),
	       depth = 0,
	       bn = 0,
	       bl = [],
	       ts = Ts
	     },
    setopts(Opts, Bs).
    

fresh_var(Bs) ->
    N  = Bs#bs.n,
    {N, Bs#bs { n = N+1 }}.

number_of_variables(Bs) ->
    Bs#bs.n - 2.

number_of_bound(Bs) ->
    Bs#bs.bn.

number_of_unbound(Bs) ->
    number_of_variables(Bs) - Bs#bs.bn.

order(What, Bs) ->
    Vx0 = array:from_list([0,1|lists:seq(2,Bs#bs.n-1)]),
    Vx1 = order_(What, Vx0, Bs),
    %% Map = lists:zip(array:to_list(Vx0),array:to_list(Vx1)),
    %% ?dbg("order map=~w\n", [Map]),
    %% ?dbg("order rmap=~w\n", [[{Y,X}||{X,Y} <-lists:keysort(2, Map)]]),
    Bs#bs { order=Vx1 }.

order_([W|Ws], Vx0, Bs) ->
    Vx1 = order__(W, Vx0, Bs),
    order_(Ws, Vx1, Bs);
order_([], Vx0, _Bs) ->
    Vx0;
order_(W, Vx0, Bs) when is_atom(W) ->
    order__(W, Vx0, Bs);
order_(W={uint,_V,_N,_I}, Vx0, Bs) ->
    order__(W, Vx0, Bs);
order_(W={int,_V,_N,_I}, Vx0, Bs) ->
    order__(W, Vx0, Bs);
order_(W={bit,_V,_N,_I}, Vx0, Bs) ->
    order__(W, Vx0, Bs).

order__(identity,Vx0,_Bs) ->
    Vx0;
order__(reverse,Vx0,_Bs) ->
    [_,_|As] = array:to_list(Vx0),
    array:from_list([0,1|reverse(As)]);
order__(depth, _Vx0, Bs) ->
    A = calculate_depth(Bs),
    array:from_list([0,1|
		     lists:sort(
		       fun(X,Y) -> array:get(X,A) < array:get(Y,A) end,
		       lists:seq(2,Bs#bs.n-1))]);
order__(occure, _Vx0, Bs) ->
    A = calculate_occure(Bs),
    array:from_list([0,1|
		     lists:sort(
		       fun(X,Y) -> array:get(X,A) < array:get(Y,A) end,
		       lists:seq(2,Bs#bs.n-1))]);
order__(depth_occure, _Vx0, Bs) ->
    A0 = calculate_depth(Bs),
    A1 = calculate_occure(Bs),
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
		       end, lists:seq(2,Bs#bs.n-1))]);
order__(occure_depth, _Vx0, Bs) ->
    A0 = calculate_occure(Bs),
    A1 = calculate_depth(Bs),
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
		       end, lists:seq(2,Bs#bs.n-1))]);
order__(Var, Vx0, Bs) ->
    %% vector component put first in search array
    case dict:find(Var, Bs#bs.vs) of
	error -> Vx0;
	{ok,X} when is_integer(X), X > 1 ->
	    ?dbg("order_first: ~w (~s) = ~w\n", 
		 [Var, fmt_var(X,Bs), X]),
	    order_first(X, Vx0)
    end.

%% put variable X first!
order_first(X, Vx0) ->
    [0,1|List] = array:to_list(Vx0),
    array:from_list([0,1,X|(List -- [X])]).

%%
%% Calculate variable occurence
%%
calculate_occure(Bs) ->
    Ts = Bs#bs.ts,
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
calculate_depth(Bs) ->
    Ts = Bs#bs.ts,
    calc_depth(array:to_list(Ts#ts.triple), [], array:new(),0,Bs).
    
calc_depth([T={_,X,Y,Z}|Ts],Ts1,D0,I,Bs) ->
    {Yd,D1} = var_depth(Y,D0,Bs),
    {Zd,D2} = var_depth(Z,D1,Bs),
    if Yd =:= undefined; Zd =:= undefined ->
	    case var_depth(X,D2,Bs) of
		{undefined,D3} ->
		    calc_depth(Ts, [T|Ts1], D3, I, Bs);
		{_Xd,D3} ->
		    calc_depth(Ts, Ts1, D3, I+1, Bs)
	    end;
       true ->
	    Xd = max(Yd,Zd)+1,
	    case var_depth(X,D2,Bs) of
		{undefined,D3} ->
		    D4 = set_var_depth(X,Xd,D3),
		    calc_depth(Ts, Ts1, D4, I+1, Bs);
		{Xd0,D3} ->
		    D4 = set_var_depth(X,max(Xd,Xd0),D3),
		    calc_depth(Ts, Ts1, D4, I+1, Bs)
	    end
    end;
calc_depth([undefined|Ts],Ts1,D,I,Bs) ->
    calc_depth(Ts,Ts1,D,I,Bs);
calc_depth([],[],D,_I,_Bs) ->
    D;
calc_depth([],Ts,D,0,Bs) ->
    %% no depth could be determined, probably recursive defintion
    %% assign max depth to all?
    MaxD = array:sparse_foldr(fun(_I,X,A) -> erlang:max(X,A) end, 0, D)+1,
    assign_depth(Ts,MaxD,D,Bs);
calc_depth([],Ts,D,_I,Bs) ->
    %% take it for an other spin
    calc_depth(Ts,[],D,0,Bs).

assign_depth([{_,X,Y,Z}|Ts],MaxD,D0,Bs) ->
    D1 = case var_depth(Y,D0,Bs) of
	     undefined -> set_var_depth(Y,MaxD,D0);
	     _Yd -> D0
	 end,
    D2 = case var_depth(Z,D1,Bs) of
	     undefined -> set_var_depth(Z,MaxD,D1);
	     _Zd -> D1
	 end,
    D3 = case var_depth(X,D2,Bs) of
	     undefined -> set_var_depth(Z,MaxD,D2);
	     _Xd -> D2
	 end,
    assign_depth(Ts,MaxD,D3,Bs);
assign_depth([],_MaxD,D0,_Bs) ->
    D0.

    

var_depth(X, D, Bs) ->
    case get_var_depth(X, D) of
	undefined ->
	    case is_input(X, Bs) of
		true ->
		    {0,set_var_depth(X, 0, D)};
		false ->
		    {undefined, D}
	    end;
	Depth ->
	    {Depth,D}
    end.
		
set_var_depth(1,_Level,D) -> D;
set_var_depth(-1,_Level,D) -> D;
set_var_depth(X,Level,D) when X < -1 -> array:set(-X,Level,D);
set_var_depth(X,Level,D) when X > 1 -> array:set(X,Level,D).

get_var_depth(1,_D)  -> 0;
get_var_depth(-1,_D) -> 0;
get_var_depth(X,D) when X < -1 ->  array:get(-X, D);
get_var_depth(X,D) when X > 1 -> array:get(X, D).

first_init(_Bs) ->
    1.

first_unbound(Bs) ->
    next_unbound(first_init(Bs), Bs).

next_unbound(I, Bs) ->
    next_unbound_(I+1, number_of_variables(Bs)+1, Bs).

next_unbound_(I, Max, Bs) when I =< Max ->
    if Bs#bs.order =:= undefined ->
	    case is_unbound(I, Bs) of
		true  -> {I,I};
		false -> next_unbound_(I+1,Max,Bs)
	    end;
       true ->
	    Xi = array:get(I, Bs#bs.order),
	    ?dbg("order[~w] = ~w, vt[~w]=~w\n", 
		 [I, Xi, Xi, array:get(Xi,Bs#bs.vt)]),
	    case is_unbound(Xi, Bs) of
		true  -> {I,Xi};
		false -> next_unbound_(I+1,Max,Bs)
	    end
    end;
next_unbound_(_X, _N, _Bs) ->
    false.

all_bound(Bs) ->
    Bs#bs.bl.

take_skip_mark_([mark|Xs]) -> take_skip_mark_(Xs);
take_skip_mark_([X|Xs]) -> [X|take_skip_mark_(Xs)];
take_skip_mark_([]) -> [].
    
latest_bound(Bs) ->
    take_until_mark_(Bs#bs.bl).

take_until_mark_([mark|_]) -> [];
take_until_mark_([{_,{X,_,_}}|Xs]) -> [X|take_until_mark_(Xs)];
take_until_mark_([]) -> [].
    
make_variable(V, Bs) ->
    {N,Bs1} = fresh_var(Bs),
    {N, alias(V, N, Bs1)}.

variable(V, Bs) ->
    W = expand_meta(V, Bs),
    case dict:find(W, Bs#bs.vs) of
	error ->
	    make_variable(W, Bs);
	{ok,N} ->
	    {N,Bs}
    end.

debug(Bs, Fmt, As) ->
    log(Bs, ?DEBUG, Fmt, As).

info(Bs, Fmt, As) ->
    log(Bs, ?INFO, Fmt, As).

log(Bs, Level0, Fmt, As) ->
    Level = level(Level0),
    LogLevel = getopt(log,Bs),
    if LogLevel =/= ?LOG_NONE, Level =< LogLevel ->
	    io:format(Fmt, As);
       true ->
	    ok
    end.
	    

level(debug)   -> ?DEBUG;
level(info)    -> ?INFO;
level(notice)  -> ?NOTICE;
level(warning) -> ?WARNING;
level(error)   -> ?ERROR;
level(critical) -> ?CRITICAL;
level(alert)    -> ?ALERT;
level(emergency) -> ?EMERGENCY;
level(none) -> ?LOG_NONE;
level(Level) when Level >= -1, Level =< 7 -> Level.

set_bt_depth(D, Bs) when is_integer(D), D>=0 ->
    Bs#bs { depth=D }.

get_bt_depth(Bs) -> Bs#bs.depth.

set_carry(Value, Bs) -> setopt(carry, Value, Bs).
set_borrow(Value,Bs) -> setopt(borrow,Value,Bs).
set_divide_by_zero(Value,Bs) -> setopt(divide_by_zero,Value,Bs).
set_saturate_pair(Value,Bs) -> setopt(saturate_pair,Value,Bs).
set_saturate_threshold(Value,Bs) -> setopt(saturate_threshold,Value,Bs).
set_log(Level,Bs) -> setopt(log,Level,Bs).
    

setopts([{Opt,Value}|Opts], Bs) ->
    setopts(Opts, setopt(Opt,Value,Bs));
setopts([Opt|Opts], Bs) when is_atom(Opt) ->
    setopts(Opts, setopt(Opt,true,Bs));
setopts([], Bs) ->
    Bs.

setopt(value,true,Bs)    ->  setopt_(value,true,Bs);
setopt(value,false,Bs)   -> setopt_(value,false,Bs);
setopt(value,none,Bs)    -> setopt_(value,none,Bs);

setopt(print,true,Bs)    -> setopt_(print,true,Bs);
setopt(print,false,Bs)    -> setopt_(print,false,Bs);

setopt(method,collect,Bs) -> setopt_(method,collect,Bs);
setopt(method,count,Bs) -> setopt_(method,count,Bs);

setopt(max,N,Bs) when is_integer(N), N>=0 ->
    setopt_(max,N,Bs);
%% fixme check all order options! (normalize?)
setopt(order,Order,Bs) -> setopt_(order,Order,Bs);

setopt(eval_bcp,Bool,Bs) when is_boolean(Bool) -> setopt_(eval_bcp, Bool, Bs);

setopt(saturate,K,Bs) when is_integer(K),K>=0 ->
    setopt_(saturate,K,Bs);
setopt(saturate_threshold,K,Bs) when is_integer(K),K>=0 ->
    setopt_(saturate_threshold,K,Bs);

setopt(saturate_pair,true,Bs) ->    setopt_(saturate_pair,true,Bs);
setopt(saturate_pair,false,Bs) ->   setopt_(saturate_pair,false,Bs);

setopt(carry,true,Bs)    ->    setopt_(carry,true,Bs);
setopt(carry,false,Bs)   ->   setopt_(carry,false,Bs);
setopt(carry,ignore,Bs)  ->  setopt_(carry,ignore,Bs);

setopt(borrow,true,Bs)   ->   setopt_(borrow,true,Bs);
setopt(borrow,false,Bs)  ->  setopt_(borrow,false,Bs);
setopt(borrow,ignore,Bs) -> setopt_(borrow,ignore,Bs);

setopt(divide_by_zero,true,Bs) ->   setopt_(divide_by_zero,true,Bs);
setopt(divide_by_zero,false,Bs) ->  setopt_(divide_by_zero,false,Bs);
setopt(divide_by_zero,ignore,Bs) -> setopt_(divide_by_zero,ignore,Bs);

setopt(log,debug,Bs) -> setopt_(log,?DEBUG,Bs);
setopt(log,info,Bs)  -> setopt_(log,?INFO, Bs);
setopt(log,notice,Bs) -> setopt_(log,?NOTICE,Bs);
setopt(log,warning,Bs) -> setopt_(log,?WARNING,Bs);
setopt(log,error,Bs) -> setopt_(log,?ERROR,Bs);
setopt(log,critical,Bs) -> setopt_(log,?CRITICAL,Bs);
setopt(log,alert,Bs) -> setopt_(log,?ALERT,Bs);
setopt(log,emergency,Bs) -> setopt_(log,?EMERGENCY,Bs);
setopt(log,none,Bs) -> setopt_(log,?LOG_NONE,Bs);
setopt(log,Level,Bs) when Level >= -1, Level =< 7 -> setopt_(log,Level,Bs).

setopt_(Key, Value, Bs) ->
    Opts = proplists:delete(Key, Bs#bs.options),
    Bs#bs { options = [{Key,Value}|Opts]}.

%%
%% Get options
%%
getopt(value,  Bs) -> getopt_(value, Bs);
getopt(print,  Bs) -> getopt_(print, Bs);
getopt(debug,  Bs) -> getopt_(debug, Bs);
getopt(log,    Bs) -> getopt_(log, Bs);
getopt(method, Bs) -> getopt_(method, Bs);
getopt(max, Bs)             -> getopt_(max, Bs);
getopt(order, Bs)          -> getopt_(order, Bs);
getopt(carry,  Bs)         -> getopt_(carry, Bs);
getopt(borrow, Bs)         -> getopt_(borrow, Bs);
getopt(divide_by_zero, Bs) -> getopt_(divide_by_zero, Bs);
getopt(eval_bcp, Bs)       -> getopt_(eval_bcp, Bs);
getopt(saturate, Bs)       -> getopt_(saturate, Bs);
getopt(saturate_threshold, Bs) -> getopt_(saturate_threshold, Bs);
getopt(saturate_pair, Bs)  -> getopt_(saturate_pair, Bs).

getopt_(Key, Bs) ->
    proplists:get_value(Key, Bs#bs.options).

%%
%%  {r,f1,..fn} => {q,eval(f1),...,eval(fn)}
%%  if f1 is var xi (e.g atom xi) then bind [{xi,eval(fi)}]
%%
%%  {uint,xi,N,i} and {int,xi,N,i} are special for
%%  unsigned/integer variable bits
%%  {bit,xi,N,i} is used for bitvector
%%
expand_meta(W={uint,V,N,I},_Bs) when is_atom(V), is_integer(N), is_integer(I) ->
    W;
expand_meta(W={int,V,N,I},_Bs) when is_atom(V), is_integer(N), is_integer(I) ->
    W;
expand_meta(W={bit,V,N,I},_Bs) when is_atom(V), is_integer(N), is_integer(I) ->
    W;
expand_meta(_Rx={p,P,Rs},Bs) when is_atom(P) ->
    {Rs1,_Bnd} = bind_meta(Rs, Bs, [], []),
    %% check for substitution R(x1,..,xn) / P(y1,..,ym)
    %% io:format("expand_meta: ~p in Bs=~p\n", [_Rx, Bs]),
    Found = find_subst(P, Bs#bs.subst),
    %% io:format("subst  = ~w\n", [Found]),
    case Found of
	false ->
	    {p,P,Rs1};
	{{p,Q,[]},{p,_P,_Us}} ->
	    {p,Q,[]};
	{{p,Q,Qs},{p,P,Ps}} when P =/= Q, length(Qs) > 0 ->
	    Bnd2 = lists:zip(Ps,Rs1),
	    %% io:format("subst: ~w [~w] => ~w\n", [{p,P,Ps},Bnd2,{p,Q,Qs}]),
	    Meta = Bnd2 ++ Bs#bs.meta,
	    expand_meta({p,Q,Qs}, Bs#bs { meta=Meta})
    end;
expand_meta(V,_Bs) ->
    %% io:format("expand_meta: ~p in Bs=~p\n", [V, _Bs]),    
    V.


find_subst(P, [E={_Qy,{p,P,_}}|_]) ->
    E;
find_subst(P, [_|Bnd]) -> 
    find_subst(P, Bnd);
find_subst(_P ,[]) -> 
    false.

bind_meta([V|Vs], Bs, Acc, Bnd) when is_atom(V) ->
    W = eval_meta(V,Bs),
    bind_meta(Vs, Bs, [W|Acc], [{V,W}|Bnd]);
bind_meta([V|Vs], Bs, Acc, Bnd) ->
    W = eval_meta(V,Bs),
    bind_meta(Vs, Bs, [W|Acc], Bnd);
bind_meta([], _Bs, Acc, Bnd) ->
    {lists:reverse(Acc),lists:reverse(Bnd)}.


%% bind a "meta" variable
push_meta(V,I,Bs) ->
    Bs#bs { meta = [{V,I}|Bs#bs.meta]}.

pop_meta(Bs = #bs { meta = [_|Meta]}) ->
    Bs#bs { meta = Meta }.

alias(V, N, Bs) ->
    case dict:find(N, Bs#bs.vs) of
	error ->
	    Vs1 = dict:store(V, N, Bs#bs.vs),
	    Vs2 = dict:store(N, [V], Vs1),
	    Bs#bs { vs=Vs2 };
	{ok,Vs} ->
	    Vs1 = dict:store(V, N, Bs#bs.vs),
	    Vs2 = dict:store(N, [V|Vs], Vs1),
	    Bs#bs { vs=Vs2 }
    end.



%% true if Y is in X's bound chain
in_chain(X, Y, Bs) when X < 0 ->
    in_chain(-X, Y, Bs);
in_chain(X, Y, Bs) ->
    case array:get(X, Bs#bs.vt) of
	?TRUE  -> false;
	?FALSE -> false;
	X -> false;
	X1 when X1 =:= Y -> true;
	X1 when X1 =:= -Y -> true;
	X1 -> in_chain(X1,Y,Bs)
    end.

is_unbound(X, Bs) when X > 1 ->
    array:get(X, Bs#bs.vt) =:= 0.

is_bound(X, Bs) when X > 1 ->
    array:get(X, Bs#bs.vt) =/= 0.
    

is_input(?TRUE, _Bs)  -> true;
is_input(?FALSE, _Bs) -> true;
is_input(X, Bs) when X < 0 -> is_input(-X, Bs);
is_input(X, Bs) ->
    case dict:find(X, Bs#bs.vs) of %% fixme: what about aliases?
	{ok,V} when not is_integer(V) ->    
	    true;
	_ ->
	    false
    end.

literal(X, _Bs) when is_integer(X) -> X;
literal({'not',X}, Bs) -> -literal(X, Bs);
literal({bool,X}, Bs) -> literal(X, Bs);
literal(X, Bs) -> dict:fetch(X, Bs#bs.vs).

%%
%% eval(Ts, Bs) -> Bs'
%%
eval(Bs) ->
    eval_(Bs#bs.ts,Bs).

eval_(Ts, Bs) ->
    case getopt(eval_bcp, Bs) of
	true ->
	    eval_bcp(Ts#ts.queue, Ts#ts.qset, Ts, Bs);
	false ->
	    eval_eqv(Ts#ts.queue, Ts#ts.qset, Ts, Bs)
    end.

%%
%% Full eval with equivalence classes
%%

eval_eqv(Q, Qset, Ts, Bs) ->
    case queue:out(Q) of
	{empty, Q1} ->
	    Ts1 = Ts#ts { queue=Q1, qset=sets:new() },
	    Bs#bs { ts=Ts1};
	{{value,Ti},Q1} ->
	    T={Op,Xt,Yt,Zt} = array:get(Ti, Ts#ts.triple),
	    X = value(Xt, Bs),
	    Y = value(Yt, Bs),
	    Z = value(Zt, Bs),
	    ?dbg("EVAL: ~s\n", [fmt_triple(T,Bs)]),
	    As = eval_op(Op,T,X,Y,Z),
	    {XRef,Bs1} = equal_list_(As,[],Bs,Ts),
	    eval_enq_eqv(Q1, sets:del_element(Ti, Qset), XRef, Ts, Bs1)
    end.

eval_enq_eqv(Q, Qset, [Ti|Tis], Ts, Bs) ->
    case sets:is_element(Ti, Qset) of
	false ->
	    Q1 = queue:in(Ti, Q),
	    Qset1 = sets:add_element(Ti, Qset),
	    eval_enq_eqv(Q1, Qset1, Tis, Ts, Bs);
	true ->
	    eval_enq_eqv(Q, Qset, Tis, Ts, Bs)
    end;
eval_enq_eqv(Q, Qset, [], Ts, Bs) ->
    eval_eqv(Q, Qset, Ts, Bs).

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

eval_bcp(Q, Qset, Ts, Bs) ->
    case queue:out(Q) of
	{empty, Q1} ->
	    Ts1 = Ts#ts { queue=Q1, qset=sets:new() },
	    Bs#bs { ts=Ts1};
	{{value,Ti},Q1} ->
	    T={Op,Xt,Yt,Zt} = array:get(Ti, Ts#ts.triple),
	    X = value(Xt, Bs),
	    Y = value(Yt, Bs),
	    Z = value(Zt, Bs),
	    ?dbg("EVAL: ~s\n", [fmt_triple(T,Bs)]),
	    As = eval_bcp(Op,T,X,Y,Z),
	    {XRef,Bs1} = equal_list_(As,[],Bs,Ts),
	    eval_enq_bcp(Q1, sets:del_element(Ti, Qset), XRef, Ts, Bs1)
    end.

eval_enq_bcp(Q, Qset, [Ti|Tis], Ts, Bs) ->
    case sets:is_element(Ti, Qset) of
	false ->
	    Q1 = queue:in(Ti, Q),
	    Qset1 = sets:add_element(Ti, Qset),
	    eval_enq_bcp(Q1, Qset1, Tis, Ts, Bs);
	true ->
	    eval_enq_bcp(Q, Qset, Tis, Ts, Bs)
    end;
eval_enq_bcp(Q, Qset, [], Ts, Bs) ->
    eval_bcp(Q, Qset, Ts, Bs).

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
equal(X,Y,Bs) ->
    ?dbg("equal: ~w = ~w\n", [X, Y]),
    X0 = literal(X,Bs),
    X1 = value(X0,Bs),
    Y0 = literal(Y,Bs),
    Y1 = value(Y0,Bs),
    Ts = Bs#bs.ts,
    {XRef,Bs1} = equal__(X1,Y1,decision,Bs,Ts),
    enq(Ts#ts.queue, Ts#ts.qset, XRef, Ts, Bs1).

enq(Q, Qset, [Ti|Tis], Ts, Bs) ->
    case sets:is_element(Ti, Qset) of
	false ->
	    Q1 = queue:in(Ti, Q),
	    Qset1 = sets:add_element(Ti, Qset),
	    enq(Q1, Qset1, Tis, Ts, Bs);
	true ->
	    enq(Q, Qset, Tis, Ts, Bs)
    end;
enq(Q, Qset, [], Ts, Bs) ->
    Ts1 = Ts#ts { queue=Q, qset=Qset },
    Bs#bs {ts=Ts1}.

enq_all(Bs) ->
    Ts = Bs#bs.ts,
    enq_all(Ts#ts.queue, Ts#ts.qset, 1, Ts#ts.n, Ts, Bs).

enq_all(Q, Qset, Ti, N, Ts, Bs) when Ti =< N ->
    case array:get(Ti, Ts#ts.triple) of
	undefined ->
	    enq_all(Q, Qset, Ti+1, N, Ts, Bs);
	_T ->
	    case sets:is_element(Ti, Qset) of
		false ->
		    Q1 = queue:in(Ti, Q),
		    Qset1 = sets:add_element(Ti, Qset),
		    enq_all(Q1, Qset1, Ti+1, N, Ts, Bs);
		true ->
		    enq_all(Q, Qset, Ti+1, N, Ts, Bs)
	    end
    end;
enq_all(Q, Qset, _Ti, _N, Ts, Bs) ->
    Ts1 = Ts#ts { queue=Q, qset=Qset },
    Bs#bs {ts=Ts1}.

    

%% eval a binding list
equal_list_([{_T,P,{X,Y}}|List],XRef,Bs,Ts) ->
    %% ?dbg("~w : ~w => ~w\n", [_T,P,{X,Y}]),
    X1 = value(X,Bs),
    {XRef1,Bs1} = equal__(X1,Y,P,Bs,Ts),
    equal_list_(List,XRef++XRef1,Bs1,Ts);
equal_list_([],XRef,Bs,_Ts) ->
    {XRef,Bs}.

%% equal__ with info about trigger Xp=Yp
%% return:
%%    {[],Bs}     when noop
%%    {[Ti], Bs}  when binding set
%%    throw(contractdition)
%%

equal__(X,Y,_P,_Bs,_Ts) 
  when X =:= -Y -> 
    %% fixme add _P
    %% show_fail(_Bs),
    throw(contradiction);
equal__(X,X,_P,Bs,_Ts) -> 
    {[],Bs};
equal__(?TRUE,Y,P,Bs,Ts) ->
    if Y < 0 -> eq__(-Y,?FALSE,P,Bs,Ts);
       true ->  eq__(Y,?TRUE,P,Bs,Ts)
    end;
equal__(?FALSE,Y,P,Bs,Ts) ->
    if Y < 0 -> eq__(-Y,?TRUE,P,Bs,Ts);
       true ->  eq__(Y,?FALSE,P,Bs,Ts)
    end;
equal__(X,Y,P,Bs,Ts) when X < 1 -> eq__(-X,-Y,P,Bs,Ts);
equal__(X,Y,P,Bs,Ts) when X > 1 -> eq__(X,Y,P,Bs,Ts).

%%
%% X=Y  when P=(Xp,Dp,Yp) 
%%  X must be unbound 
%%  Y should not have X in it's values chain
%%
eq__(X,Y,P,Bs,Ts) ->
    D    = Bs#bs.depth,
    Bl = add_edge(P,{X,D,Y},Bs#bs.bl,Bs),
    case Bl of
	[{{_Xp,_Dp,_Yp},_}|_] ->
	    ?dbg("  _eq: ~s/~s(~w) [when ~s/~s(~w)]\n", 
		 [fmt_var(X,Bs),fmt_var(Y,Bs), D,
		  fmt_var(_Xp,Bs),fmt_var(_Yp,Bs),_Dp]);
	[{decision,_}|_] ->
	    ?dbg("  _eq: ~s/~s(~w)\n", 
		 [fmt_var(X,Bs),fmt_var(Y,Bs), D]);
	[{true,_}|_] ->
	    ?dbg("  _eq: ~s/~s(~w)\n", 
		 [fmt_var(X,Bs),fmt_var(Y,Bs), D])
    end,
    Vt   = array:set(X, Y, Bs#bs.vt),
    Bn   = Bs#bs.bn+1,
    XRef = get_xref(X,Bs,Ts),
    Bs1 = case class(Y,Bs) of
	      ?TRUE  -> 
		  Bs#bs { vt = Vt, bn=Bn, bl=Bl };
	      ?FALSE -> 
		  Bs#bs { vt = Vt, bn=Bn, bl=Bl };
	      Yc when Yc < 0 ->
		  Vc = array:set(-Yc, -X, Bs#bs.vc),
		  Bs#bs { vt = Vt, vc = Vc, bn=Bn, bl=Bl };
	      Yc ->
		  Vc = array:set(Yc, X, Bs#bs.vc),
		  Bs#bs { vt = Vt, vc = Vc, bn=Bn, bl=Bl }
	  end,
    {XRef,Bs1}.

add_edge(decision,Q,Bl,_Bs) ->
    [{decision,Q}|Bl];
add_edge(P,Q,Bl,Bs) ->
    %% ?dbg("~w => ~w :BL=~w\n", [P,Q,Bl]),
    case find_edge_start(P,Bl,Bs) of
	true    -> [{true,Q}|Bl]; %% FIXME
	{P1,ok} -> [{P1,Q} | Bl];
	{P1,P2} ->
	    %% ?dbg("ADD EDGE 2\n"),
	    add_edge(P2,Q,[{P1,Q}|Bl],Bs)
    end.

%% find & normalize vertex
find_edge_start({X,Y},Bl,Bs) when X < 0 -> find_edge_start({-X,-Y},Bl,Bs);
find_edge_start({X,X},_Bl,_Bs) -> true;
find_edge_start(P,Bl,Bs) -> find_edge_start_(P,Bl,Bs).

find_edge_start_({X,Y},[{_,{X,D,Y}}|_],_Bs) -> {{X,D,Y},ok};
find_edge_start_({X,Y},[{_,{X,D,Y1}}|_],Bs) ->
    case value(Y1, Bs) of
	Y -> {{X,D,Y},{Y1,Y}}
    end;
find_edge_start_(P,[_|Bl],Bs) -> find_edge_start_(P,Bl,Bs).

%%
%% Mark binding list
%%
mark(Bs) ->
    Bl = [mark | Bs#bs.bl],
    Bs#bs { bl = Bl }.

%% get all triples from all classes for variable X
get_xref(X,Bs,Ts) when X > 0 ->
    array:get(X, Ts#ts.xref) ++ get_xref(class_next(X,Bs),Bs,Ts);
get_xref(X,Bs,Ts) when X < 0 -> get_xref(-X,Bs,Ts);
get_xref(0, _Ts, _Bs) -> [].

%%
%% Generate the variable rules from a formula
%%
build(F) ->
    build(F,[]).

build(F,Opts) ->
    ?dbg("Formula: ~w\n", [F]),
    Bs = new(Opts),
    try build_(F, Bs) of
	{X,Bs1} -> 
	    {X,Bs1}
    catch
	throw:contradiction -> 
	    {{bool,?FALSE},Bs}
    end.

build_(V, Bs) when is_atom(V) ->
    {X,Bs1} = variable(V, Bs),
    {{bool,X},Bs1};
build_(V={p,_P,_Ps}, Bs) ->
    {X,Bs1} = variable(V, Bs),
    {{bool,X},Bs1};
build_({uint,N,V}, Bs) ->
    if is_atom(V)    -> var_vector(uint,V,N,Bs);
       is_integer(V) -> const_vector(uint,V,N,Bs)
    end;
build_({int,N,V}, Bs) ->
    if is_atom(V)    -> var_vector(int,V,N,Bs);
       is_integer(V) -> const_vector(int,V,N,Bs)
    end;
build_({bit,N,V}, Bs) ->
    if is_atom(V)    -> var_vector(bit,V,N,Bs);
       is_integer(V) -> const_vector(bit,V,N,Bs)
    end;
build_({':=', V, F}, Bs) when is_atom(V) ->
    {Y,Bs1} = build_(F, Bs),
    operation(':=', V, Y, Bs1);

build_({'all',Fs}, Bs) ->
    {Xs,Bs1} = args(Fs,Bs),
    all(Xs, Bs1);
build_({'any',Fs}, Bs) ->
    {Xs,Bs1} = args(Fs,Bs),
    any(Xs, Bs1);
build_({'none',Fs}, Bs) ->
    {Xs,Bs1} = args(Fs,Bs),
    none(Xs, Bs1);
build_({eqk,K,Fs}, Bs) when is_integer(K), K >= 0 ->
    {Xs,Bs1} = args(Fs, Bs),
    eqk(K, length(Xs), Xs, Bs1);
build_({neqk,K,Fs}, Bs) when is_integer(K), K >= 0 ->
    {Xs,Bs1} = args(Fs, Bs),
    {X,Bs2} = eqk(K, length(Xs), Xs, Bs1),
    {negate(X),Bs2};
build_({gtk,K,Fs}, Bs) when is_integer(K), K >= 0 ->
    {Xs,Bs1} = args(Fs, Bs),
    gtk(K, length(Xs), Xs, Bs1);
build_({gtek,0,Fs}, Bs) ->
    {Xs,Bs1} = args(Fs, Bs),
    any(Xs,Bs1);
build_({gtek,K,Fs}, Bs) when is_integer(K), K >= 1 ->
    {Xs,Bs1} = args(Fs, Bs),
    gtk(K-1, length(Xs), Xs, Bs1);
build_({ltk,1,Fs}, Bs) ->
    {Xs,Bs1} = args(Fs, Bs),
    none(Xs,Bs1);
build_({ltk,K,Fs}, Bs) when is_integer(K), K > 1 ->
    {Xs,Bs1} = args(Fs, Bs),
    N = length(Xs),
    gtk(N-K, N, map(fun(X) -> negate(X) end, Xs), Bs1);
build_({ltek,0,Fs}, Bs) ->
    {Xs,Bs1} = args(Fs, Bs),
    none(Xs,Bs1);
build_({ltek,K,Fs}, Bs) when is_integer(K), K > 0 ->
    {Xs,Bs1} = args(Fs, Bs),
    N = length(Xs),
    gtk(N-K-1, N, map(fun(X) -> negate(X) end, Xs), Bs1);
build_({ltk,K,Fs}, Bs) when is_integer(K), K > 1 ->
    {Xs,Bs1} = args(Fs, Bs),
    N = length(Xs),
    gtk(N-K, N, map(fun(X) -> negate(X) end, Xs), Bs1);
build_({'-',F}, Bs) ->
    {Y,Bs1} = build_(F, Bs),
    operation('-', Y, Bs1);
build_({'abs',F}, Bs) ->
    {Y,Bs1} = build_(F, Bs),
    operation('abs', Y, Bs1);
build_({'not',A}, Bs) ->
    {Y,Bs1} = build_(A, Bs),
    operation('not', Y, Bs1);
build_({'~',A}, Bs) ->
    {Y,Bs1} = build_(A, Bs),
    operation('~', Y, Bs1);
%% Fixme: implement shift for variable argument
build_({'<<',A,K},Bs) when is_integer(K), K>=0 ->
    {Y,Bs1} = build_(A,Bs),
    operation('<<',Y,K,Bs1);
build_({'<<<',A,K},Bs) when is_integer(K), K>=0 ->
    {Y,Bs1} = build_(A,Bs),
    operation('<<<',Y,K,Bs1);
build_({'>>',A,K},Bs) when is_integer(K), K >= 0 ->
    {Y,Bs1} = build_(A,Bs),
    operation('>>',Y,K,Bs1);
build_({'>>>',A,K},Bs) when is_integer(K), K >= 0 ->
    {Y,Bs1} = build_(A,Bs),
    operation('>>>',Y,K,Bs1);
build_({cnf,{Cs,Ls}},Bs) when is_list(Cs), is_list(Ls) ->
    build_({'and',{all,Ls},cnf_to_formula(Cs)},Bs);
build_({cnf,{_Vars,_Clauses,Cs}},Bs) when is_list(Cs) ->
    build_(cnf_to_formula(Cs),Bs);
build_({cnf,Cs},Bs) ->
    build_(cnf_to_formula(Cs),Bs);
build_({suchthat,Expr,F},Bs) ->
    case eval_meta(Expr,Bs) of
	true -> build_(F,Bs);
	false -> {0,Bs}
    end;
build_({subst,Rx,Py,F},Bs) ->
    Bs1 = Bs#bs { subst = [{Rx,Py}|Bs#bs.subst]},
    build_(F, Bs1);
build_({subst,SList,F},Bs) ->
    Bs1 = Bs#bs { subst = SList++Bs#bs.subst},
    build_(F, Bs1);
build_({Op,A,B}, Bs) ->
    {Y,Bs1} = build_(A, Bs),
    {Z,Bs2} = build_(B, Bs1),
    operation(Op,Y,Z,Bs2);
build_({ite,C,T,E}, Bs) ->
    {Cf,Bs1} = build_(C, Bs),
    {Tf,Bs2} = build_(T, Bs1),
    {Ef,Bs3} = build_(E, Bs2),
    ite(Cf, Tf, Ef, Bs3);
build_({forall,X,{A,B}, F}, Bs) when is_integer(A), is_integer(B), A=<B ->
    {Ys,Bs1} = build_meta(F,X,lists:seq(A,B,1),[],Bs),
    all(Ys,Bs1);
build_({forall,X,{A,B}, F}, Bs) when is_integer(A), is_integer(B), A>B ->
    {Ys,Bs1} = build_meta(F,X,lists:seq(A,B,-1),[],Bs),
    all(Ys,Bs1);
build_({forall,X,Xs,F}, Bs) when is_list(Xs) ->
    {Ys,Bs1} = build_meta(F,X,Xs,[],Bs),
    all(Ys,Bs1);
build_({exists,X,{A,B},F}, Bs) when is_integer(A), is_integer(B), A=<B ->
    {Ys,Bs1} = build_meta(F,X,lists:seq(A,B,1),[],Bs),
    any(Ys,Bs1);
build_({exists,X,{A,B},F}, Bs) when is_integer(A), is_integer(B), A>B ->
    {Ys,Bs1} = build_meta(F,X,lists:seq(A,B,-1),[],Bs),
    any(Ys,Bs1);
build_({exists,X,Xs,F}, Bs) when is_list(Xs) ->
    {Ys,Bs1} = build_meta(F,X,Xs,[],Bs),
    any(Ys,Bs1);

build_({'one',Fs}, Bs) ->
    {Xs,Bs1} = args(Fs, Bs),
    eqk(1, length(Xs), Xs, Bs1);

build_({list,X,{A,B},F}, Bs) when is_integer(A), is_integer(B), A=<B ->
    build_meta(F,X,lists:seq(A,B,1),[],Bs);
build_({list,X,{A,B},F}, Bs) when is_integer(A), is_integer(B), A>B ->
    build_meta(F,X,lists:seq(A,B,-1),[],Bs);
build_({list,X,Xs,F}, Bs) when is_list(Xs) ->
    build_meta(F,X,Xs,[],Bs).

build_meta(F,X,[Xi|Xs],Acc,Bs) ->
    Bs1 = push_meta(X, Xi, Bs),
    case build_(F,Bs1) of
	{0,Bs2} ->
	    Bs3 = pop_meta(Bs2),
	    build_meta(F,X,Xs,Acc,Bs3);
	{Vs,Bs2} when is_list(Vs) ->
	    Bs3 = pop_meta(Bs2),
	    build_meta(F,X,Xs,Vs++Acc,Bs3);
	{V,Bs2} ->
	    Bs3 = pop_meta(Bs2),
	    build_meta(F,X,Xs,[V|Acc],Bs3)
    end;
build_meta(_F,_X,[],Acc,Bs) ->
    {Acc,Bs}.


eval_meta(V, _Bs) when is_integer(V) ->
    V;
eval_meta(true, _Bs) ->
    true;
eval_meta(false, _Bs) ->
    false;
eval_meta(V, Bs) when is_atom(V) ->
    {_,W} = lists:keyfind(V,1,Bs#bs.meta),
    W;
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

uint64(I,Bs) when is_integer(I) ->
    const_vector(uint,I,64,Bs);
uint64(V,Bs) when is_atom(V) ->
    var_vector(uint,V,64,Bs).

uint32(I,Bs) when is_integer(I) ->
    const_vector(uint,I,32,Bs);
uint32(V,Bs) when is_atom(V) ->
    var_vector(uint,V,32,Bs).

uint16(I,Bs) when is_integer(I) ->
    const_vector(uint,I,16,Bs);
uint16(V,Bs) when is_atom(V) ->
    var_vector(uint,V,16,Bs).

uint8(I,Bs) when is_integer(I) ->
    const_vector(uint,I,8,Bs);
uint8(V,Bs) when is_atom(V) ->
    var_vector(uint,V,8,Bs).

%% generate a constant vector
const_vector(Type,Value,N,Bs) when is_integer(Value) ->
    const_vector(N-1,Type,N,[],Value,Bs).

const_vector(-1,Type,N,Cs,_Value,Bs) ->
    {{Type,N,reverse(Cs)},Bs};
const_vector(I,Type,N,Cs,Value,Bs) ->
    if Value band 1 =:= 1 ->
	    const_vector(I-1,Type,N,[?TRUE|Cs],Value bsr 1, Bs);
       true ->
	    const_vector(I-1,Type,N,[?FALSE|Cs],Value bsr 1, Bs)
    end.

%% Install alias vector
alias_vector(T,V,N,Xs,Bs) ->
    alias_vector(0,T,N,Xs,V,Bs).

alias_vector(I,T,N,[X|Xs],V,Bs) ->
    Bs1 = alias({T,V,N,I}, X, Bs),
    alias_vector(I+1,T,N,Xs,V,Bs1);
alias_vector(_I,_T,_N,[],_V,Bs) ->
    Bs.
    
%% generate a variable vector
var_vector(Type,V,N,Bs) ->
    var_vector(N-1,Type,N,[],V,Bs).

var_vector(-1,Type,N,Xs,_V,Bs) -> 
    {{Type,N,Xs},Bs};
var_vector(I,Type,N,Xs,V,Bs) ->
    {Xi,Bs1} = variable({Type,V,N,I},Bs),
    var_vector(I-1,Type,N,[Xi|Xs],V,Bs1).


%% Fold operator Op over a variable vector
vfold_op(_Op,_D,[A],Bs) ->
    {{bool,A},Bs};
vfold_op(Op,D,[Y|As],Bs) ->
    {Z,Bs1} = vfold_op(Op,D,As,Bs),
    operation(Op,{bool,Y},Z,Bs1);
vfold_op(_Op,D,[],Bs) ->
    {D,Bs}.

%% Fold operator Op over a list of bool variables
fold_op(_Op,_D,[A],Bs) ->
    {A,Bs};
fold_op(Op,D,[Y|As],Bs) ->
    {Z,Bs1} = fold_op(Op,D,As,Bs),
    operation(Op,Y,Z,Bs1);
fold_op(_Op,D,[],Bs) ->
    {D,Bs}.

all(As, Bs) -> 
    fold_op('and',{bool,?TRUE},As,Bs).

any(As, Bs) ->
    fold_op('or',{bool,?FALSE},As,Bs).

none(As,Bs) ->
    {A,Bs1} = any(As,Bs),
    operation('not',A,Bs1).


%% Generate a formula where exact K out of N formulas are true.
eqk(0,_N, Xs, Bs) ->
    {A,Bs1} = any(Xs,Bs), {negate(A),Bs1};
eqk(K,N,_Xs,Bs) when K > N -> %% no models
    {{bool,?FALSE}, Bs};
eqk(K,N,Xs,Bs) when K =:= N ->
    all(Xs,Bs);
eqk(K,N,Xs,Bs) ->
    {Xs1,Bs1} = sort(Xs,K,Bs),
    {A,B} = lists:split(N-K, Xs1),
    {A1,Bs2} = any(A,Bs1),
    {B1,Bs3} = all(B,Bs2),
    operation('and', negate(A1), B1, Bs3).

gtk(0,_N, Xs, Bs) ->
    any(Xs,Bs);
gtk(K,N,_Xs,Bs) when K >= N -> %% no models
    {{bool,?FALSE}, Bs};
gtk(K,N,Xs,Bs) ->
    {Xs1,Bs1} = sort(Xs,K,Bs),
    {A,B} = lists:split(N-K, Xs1),
    {A1,Bs2} = any(A,Bs1),
    {B1,Bs3} = all(B,Bs2),
    operation('and', A1, B1, Bs3).

%% negate all input variables
negate({bool,X}) -> {bool,-X}.
     
vnot(Xs) ->
    map(fun(X) -> -X end, Xs).

vextend(int,Xs,N,K) ->
    vset_size(Xs,K,lists:nth(N,Xs));
vextend(uint,Xs,_N,K) ->
    vset_size(Xs,K,?FALSE);
vextend(bit,Xs,_N,K) ->
    vset_size(Xs,K,?FALSE).


%% set vector size to N  extend (with FALSE) at end / cut at end
vset_size(Xs,N) ->
    vset_size(Xs,N,?FALSE).

vset_size(_Xs,0,_D) -> [];
vset_size([],I,D) -> lists:duplicate(I,D);
vset_size([X|Xs],I,D) -> [X|vset_size(Xs,I-1,D)].


args(Fs,Bs) when is_list(Fs) ->
    args(Fs,[],Bs);
args(F,Bs) ->
    case build_(F, Bs) of
	{Fs,Bs1} when is_list(Fs) ->
	    {Fs,Bs1}
    end.

args([F|Fs],Xs,Bs) ->
    {X,Bs1} = build_(F,Bs),
    args(Fs,[X|Xs],Bs1);
args([],Xs,Bs) ->
    {reverse(Xs),Bs}.
%%
%% Unary operator
%%
operation('not',{bool,Y},Bs) ->
    {{bool,-Y},Bs};
operation('-', {Type,N,Ys}, Bs) when ?is_int_type(Type) ->
    %% Fix me.
    Ys1 = vnot(Ys),
    Zs1 = vset_size([?TRUE],N),
    {{bool,_Co},Xs,Bs1} = vadd(Ys1,Zs1,Bs),
    %% ignore carry
    {{Type,N,Xs}, Bs1};
operation('~', {Type,N,Ys}, Bs) when ?is_vec_type(Type) ->
    Ys1 = vnot(Ys),
    {{Type,N,Ys1}, Bs};
operation('abs', {int,N,Ys}, Bs) ->
    Sign = sign_bit({int,N,Ys}),
    {{_,_,Zs},Bs1} = operation('-',{int,N,Ys},Bs),
    {Xs,Bs2} = vite(Sign, Zs, Ys, Bs1),
    {{int,N,Xs},Bs2};
operation('abs', {uint,N,Ys}, Bs) ->
    {{uint,N,Ys},Bs}.
    
%%
%% Binary operator
%%
operation('and',{bool,Y},{bool,Z}, Bs) ->
    {X,Bs1} = fresh_var(Bs),
    {{bool,X},triple(imp,-X,Y,-Z,Bs1)};

operation('or',{bool,Y},{bool,Z}, Bs) ->
    {X,Bs1} = fresh_var(Bs),
    {{bool,X},triple(imp,X,-Y,Z,Bs1)};

operation('imp',{bool,Y},{bool,Z}, Bs) ->
    {X,Bs1} = fresh_var(Bs),
    {{bool,X},triple(imp,X,Y,Z,Bs1)};

operation('equ',{bool,Y},{bool,Z},Bs) ->
    {X,Bs1} = fresh_var(Bs),
    {{bool,X},triple(equ,X,Y,Z,Bs1)};

operation('xor',{bool,Y},{bool,Z},Bs) ->
    {X,Bs1} = fresh_var(Bs),
    {{bool,X},triple(equ,X,-Y,Z,Bs1)};

operation('<',{bool,Y},{bool,Z},Bs) ->  %% Y < Z
    operation('and', negate({bool,Y}),{bool,Z}, Bs);

operation('>',{bool,Y},{bool,Z},Bs) ->  %% Y > Z
    operation('and', {bool,Y}, negate({bool,Z}), Bs);

operation('!=',{bool,Y},{bool,Z},Bs) ->
    operation('xor',{bool,Y},{bool,Z},Bs);

operation('==',{bool,Y},{bool,Z},Bs) ->
    operation('equ',{bool,Y},{bool,Z},Bs);

operation('<->', A, B, Bs) ->
    operation('==', A, B, Bs);

operation('->', A, B, Bs) ->
    operation('imp', A, B, Bs);

operation('&&', A, B, Bs) ->
    operation('and', A, B, Bs);

operation('||', A, B, Bs) ->
    operation('or', A, B, Bs);

%%
%% Alias operation
%%
operation(':=',V,X={T,N,Xs},Bs) when is_atom(V), ?is_vec_type(T) ->
    {X, alias_vector(T,V,N,Xs,Bs)};
operation(':=',V,X={bool,Xb},Bs) when is_atom(V) ->
    {X, alias(V, Xb, Bs)};

%%    
%% comparison over bool-vector 
%%   '=='  '!='
%%   '<' '<=' '>' '>='
%%

operation('==',{Type1,N,Ys},{Type2,M,Zs},Bs) ->
    %% fixme: warn about different sign (uint == int)
    K = erlang:max(N,M),
    Ys1 = vextend(Type1,Ys,N,K),
    Zs1 = vextend(Type2,Zs,M,K),
    veq(Ys1,Zs1,Bs);

operation('!=',Y,Z,Bs) ->
    {C,Bs1} = operation('==', Y, Z, Bs),
    {negate(C),Bs1};

operation('<',{int,N,Ys},{int,M,Zs},Bs) when N>1, M>1 ->
    K = erlang:max(N,M),
    Ys0 = vextend(int,Ys,N,K),
    Zs0 = vextend(int,Zs,M,K),
    {Ys1,[Yk]} = lists:split(K-1,Ys0),
    {Zs1,[Zk]} = lists:split(K-1,Zs0),
    
    %% abs(X) < abs(Y)
    {Q,Bs1} = operation('equ',{bool,Yk},{bool,Zk},Bs),
    {Lt,Bs2} = vless(Ys1,Zs1,Bs1),
    {A1,Bs3} = operation('and',Q,Lt,Bs2),

    %%  Y<0  AND Z>=0
    {L,Bs4} = operation('<',{bool,Zk},{bool,Yk},Bs3),

    any([A1,L],Bs4);

operation('<',{Type1,N,Ys},{Type2,M,Zs},Bs) when 
      ?is_int_type(Type1), ?is_int_type(Type2) ->
    K = erlang:max(N,M),
    Ys1 = vextend(Type1,Ys,N,K),
    Zs1 = vextend(Type2,Zs,M,K),
    vless(Ys1,Zs1,Bs);

operation('<=',Y,Z,Bs) ->
    {C,Bs1} = operation('<', Z, Y, Bs),
    {negate(C),Bs1};

operation('>',Y,Z,Bs) ->
    operation('<', Z, Y, Bs);

operation('>=',Y,Z,Bs) ->
    operation('<=',Z,Y,Bs);

%% bit-vector operations
operation('|',{Type1,N,Ys},{Type2,M,Zs},Bs) ->
    K = erlang:max(N,M),
    Ys1 = vextend(Type1,Ys,N,K),
    Zs1 = vextend(Type2,Zs,M,K),
    {Xs,Bs1} = vmap_op('or',Ys1,Zs1,Bs),
    Type = mix_type(Type1,Type2),
    {{Type,K,Xs},Bs1};

operation('&',{Type1,N,Ys},{Type2,M,Zs},Bs) ->
    K = erlang:max(N,M),
    Ys1 = vextend(Type1,Ys,N,K),
    Zs1 = vextend(Type2,Zs,M,K),
    {Xs,Bs1} = vmap_op('and',Ys1,Zs1,Bs),
    Type = mix_type(Type1,Type2),
    {{Type,K,Xs},Bs1};

operation('^',{Type1,N,Ys},{Type2,M,Zs},Bs) ->
    K = erlang:max(N,M),
    Ys1 = vextend(Type1,Ys,N,K),
    Zs1 = vextend(Type2,Zs,M,K),
    {Xs,Bs1} = vmap_op('xor',Ys1,Zs1,Bs),
    Type = mix_type(Type1,Type2),
    {{Type,K,Xs},Bs1};

operation('<<',{Type,N,Xs},K,Bs) 
  when ?is_vec_type(Type), is_integer(K), K >= 0 ->
    Xs1 = vshift_left(K,N,Xs),
    {{Type,N,Xs1}, Bs};

operation('>>',{uint,N,Xs},K,Bs) when is_integer(K), K >= 0 ->
    Xs1 = vushift_right(K,N,Xs),
    {{uint,N,Xs1}, Bs};
operation('>>',{bit,N,Xs},K,Bs) when is_integer(K), K >= 0 ->
    Xs1 = vushift_right(K,N,Xs),
    {{bit,N,Xs1}, Bs};
operation('>>',{int,N,Xs},K,Bs) when is_integer(K), K >= 0 ->
    Xs1 = vshift_right(K,N,Xs),
    {{int,N,Xs1}, Bs};

%% rotate left
operation('<<<',X={Type,N,_Xs},K,Bs0) when 
      is_integer(N), ?is_vec_type(Type), is_integer(K), K >= 0 ->
    C = K rem N,
    {X1, Bs1} = operation('<<',X,C,Bs0),
    {X2, Bs2} = operation('>>',X,(N-C),Bs1),
    operation('|', X1, X2, Bs2);

%% rotate right
operation('>>>',X={Type,N,_Xs},K,Bs0) when 
      is_integer(N), ?is_vec_type(Type), is_integer(K), K >= 0 ->
    C = K rem N,
    {X1, Bs1} = operation('>>',X,C,Bs0),
    {X2, Bs2} = operation('<<',X,(N-C),Bs1),
    operation('|', X1, X2, Bs2);


%% arithmetic over bool-vector
operation('+',{Type1,N,Ys},{Type2,M,Zs},Bs) ->
    %% integer type?
    K = erlang:max(N,M),
    Ys1 = vextend(Type1,Ys,N,K),
    Zs1 = vextend(Type2,Zs,M,K),
    {Co,Xs,Bs1} = vadd(Ys1,Zs1,Bs),
    Bs2 = set_carry_(Co,getopt(carry,Bs1),Bs1),
    Type = mix_type(Type1,Type2),
    {{Type,K,Xs},Bs2};

operation('-',{Type1,N,Ys},{Type2,M,Zs},Bs) ->
    %% integer type?
    K = erlang:max(N,M),
    Ys1 = vextend(Type1,Ys,N,K),
    Zs1 = vextend(Type2,Zs,M,K),
    {Borrow,Xs,Bs1} = vsub(Ys1,Zs1,Bs),
    Bs2 = set_carry_(Borrow,getopt(borrow,Bs1),Bs1),
    Type = mix_type(Type1,Type2),
    {{Type,K,Xs}, Bs2};

operation('*',{uint,N,Ys},{uint,M,Zs},Bs) ->
    %% integer type?
    K = erlang:max(N,M),
    Ys1 = vextend(uint,Ys,N,K),
    Zs1 = vextend(uint,Zs,M,K),
    {Xs,Bs1} = vmul(Ys1,Zs1,Bs),
    {{uint,K+K,Xs},Bs1};

%% DivZero  coould be used to generate a Exception output
operation('/',{uint,N,Ys},{uint,M,Zs},Bs) ->
    K = erlang:max(N,M),
    Ys1 = vextend(uint,Ys,N,K),
    Zs1 = vextend(uint,Zs,M,K),
    {Qs,_Rs,DivZero,Bs1} = vdivrem(Ys1,Zs1,Bs),
    Bs2 = set_carry_(DivZero,getopt(divide_by_zero,Bs1),Bs1),
    {{uint,K,Qs},Bs2};

%% DivZero  coould be used to generate a Exception output
operation('%',{uint,N,Ys},{uint,M,Zs},Bs) ->
    K = erlang:max(N,M),
    Ys1 = vextend(uint,Ys,N,K),
    Zs1 = vextend(uint,Zs,M,K),
    {_Qs,Rs,DivZero,Bs1} = vdivrem(Ys1,Zs1,Bs), %% fixme vrem! 
    Bs2 = set_carry_(DivZero,getopt(divide_by_zero,Bs1),Bs1),
    {{uint,K,Rs},Bs2};

operation('min',{Type1,N,Ys},{Type2,M,Zs},Bs) ->
    %% integer type?
    K = erlang:max(N,M),
    Ys1 = vextend(Type1,Ys,N,K),
    Zs1 = vextend(Type2,Zs,M,K),
    {Cond,Bs1} = operation('<',{Type1,K,Ys1},{Type2,K,Zs1},Bs),
    {Xs,Bs2} = vite(Cond, Ys1, Zs1, Bs1),
    Type = mix_type(Type1,Type2),
    {{Type,K,Xs},Bs2};

operation('max',{Type1,N,Ys},{Type2,M,Zs},Bs) ->
    %% integer type?
    K = erlang:max(N,M),
    Ys1 = vextend(Type1,Ys,N,K),
    Zs1 = vextend(Type2,Zs,M,K),
    {Cond,Bs1} = operation('>',{Type1,K,Ys1},{Type2,K,Zs1},Bs),
    {Xs,Bs2} = vite(Cond, Ys1, Zs1, Bs1),
    Type = mix_type(Type1,Type2),
    {{Type,K,Xs},Bs2}.
    

%% Handle carry (Is it wise to backtrack over a Carry variable?)

set_carry_({bool,Carry}, false, Bs) ->    %% never overflow
    triple(equ,?TRUE,Carry,?FALSE,Bs);
set_carry_({bool,Carry}, true, Bs) ->     %% only overflow
    triple(equ,?TRUE,Carry,?TRUE,Bs);
set_carry_({bool,_Carry}, ignore, Bs) ->  %% allow carry overflow
    Bs.

%% sign bit as boolean
sign_bit({Type,N,Xs}) when ?is_int_type(Type) ->
    {bool,lists:nth(N,Xs)}.

%% Mix integer type (cast?)

mix_type(int,int)   -> int;
mix_type(bit,bit)   -> bit;
mix_type(uint,uint) -> uint;
mix_type(int,uint)  -> uint;
mix_type(uint,int)  -> uint;
mix_type(uint,bit)  -> uint;
mix_type(bit,uint)  -> uint.

%%
%% Multiplier circuit: Y*Z
%%
%%  Y = (y0 + y1*2^1 + y2*2^2 + ... yk*2^k)
%%  Z = (z0 + z1*2^1 + z2*2^2 + ... zl*2^l)
%% 
%%  Y*Z = y0*Z + y1*2^1*Z + ... yk*2^k*Z
%%
%%  yi*2^i*Z = yi*z0*2^(i+0) + yi*z1*2^(i+1) + yi*zj*2^(i+j)
%%
%% Ex1
%% Y=7:3 [1,1,1] * Z=5:3[1,0,1]
%%
%% 0: Xs=[0,0,0]
%% 1: [0,0,0]     + [1,0,1]     = [1,0,1,0]
%% 2: [1,0,1,0]   + [0,1,0,1]   = [1,1,1,1,0]
%% 3: [1,1,1,1,0] + [0,0,1,0,1] = [1,1,0,0,0,1]
%%
vmul(Ys, Zs, Bs) ->
    Xs = vextend(uint,[],0,length(Ys)),
    vmul(Ys, Zs, Xs, Bs).

vmul([?FALSE|Ys], Zs, Xs, Bs) ->
     vmul(Ys, [?FALSE|Zs], Xs++[?FALSE], Bs);
vmul([?TRUE|Ys], Zs, Xs, Bs) ->
    {{bool,Co},Xs1,Bs1} = vadd(Xs,Zs,Bs),
    vmul(Ys, [?FALSE|Zs], Xs1++[Co], Bs1);
vmul([Y|Ys], Zs, Xs, Bs) ->
    {YZs,Bs1} = vmap_opx('and',Zs,Y,Bs),
    {{bool,Co},Xs1,Bs2} = vadd(Xs,YZs,Bs1),
    vmul(Ys, [?FALSE|Zs], Xs1++[Co], Bs2);
vmul([], _Zs, Xs, Bs) ->
    {Xs, Bs}.

%%
%% Divider/Reminder circuit  (X/Y)
%%   X : N bits
%%   Y : N bits
%%
%%   R = 0
%%   for (i = 0; i < N; i++) {
%%	R <<= 1;
%%	if (HIGHBIT(X))
%%	    R |= 1;
%%	X <<= 1;
%%	if (R < Y)
%%	    X &= ~1; %% clear low bit
%%	else {
%%	    R -= Y;
%%	    X |= 1;
%%	}
%%
vdivrem(X, Y, Bs) ->
    N = length(Y),
    Zs = vextend(uint,[],0,N),  %% R = 0
    {Q,R,Bs1} = vdivrem(X, Y, Zs, N, N, Bs),
    {DivZero,Bs2} = veq(Y, Zs,Bs1),
    {Q,R,DivZero,Bs2}.

vdivrem(X, _Y, R, _N, 0, Bs) ->
    {X, R, Bs};
vdivrem(X, Y, R, N, I, Bs) ->
    %% R << 1
    [R0|Rs] = vshift_left(1, N, R),      
    Xn = lists:last(X),
    %% if (HIGHBIT(X)) R |= 1;
    {{bool,R00},Bs1} = ite({bool,Xn}, {bool,?TRUE}, {bool,R0},Bs),
    R1 = [R00|Rs],
    %% X <<= 1;
    [_X10|X1] = vshift_left(1, N, X),
    %% if (R < Y)  X &= ~1; else X |= 1;
    {{bool,Lt},Bs2} = vless(R1, Y, Bs1),
    X2 = [-Lt|X1],
    %% R = R - Y
    {Borrow,R2,Bs3} = vsub(R1, Y, Bs2),
    Bs4 = set_carry_(Borrow,ignore,Bs3),
    %% if (R < Y) R=R; R = R - Y
    {R3,Bs5} = vite({bool,Lt}, R1, R2, Bs4),
    vdivrem(X2, Y, R3, N, I-1, Bs5).

%%
%% Reminder circuit  (X%Y)
%%   X : N bits
%%   Y : N bits
%%
%%   R = 0
%%   for (i = 0; i < N; i++) {
%%	R <<= 1;
%%	if (HIGHBIT(X))
%%	    R |= 1;
%%	X <<= 1;
%%	if (R >= Y)
%%	    R -= Y;
%%   }
%%
vrem(X, Y, Bs) ->
    N = length(Y),
    Zs = vextend(uint,[],0,N),  %% R = 0
    {R,Bs1} = vrem(X, Y, Zs, N, N, Bs),
    {DivZero,Bs2} = veq(Y, Zs,Bs1),
    {R,DivZero,Bs2}.

vrem(_X, _Y, R, _N, 0, Bs) ->
    {R, Bs};
vrem(X, Y, R, N, I, Bs) ->
    %% R << 1
    [R0|Rs] = vshift_left(1, N, R),      
    Xn = lists:last(X),
    %% if (HIGHBIT(X)) R |= 1;
    {{bool,R00},Bs1} = ite({bool,Xn}, {bool,?TRUE}, {bool,R0},Bs),
    R1 = [R00|Rs],
    {{bool,Lt},Bs2} = vless(R1, Y, Bs1),
    %% R = R - Y
    {Borrow,R2,Bs3} = vsub(R1, Y, Bs2),
    Bs4 = set_carry_(Borrow,ignore,Bs3),
    %% if (R < Y) R=R; R = R - Y
    {R3,Bs5} = vite({bool,Lt}, R1, R2, Bs4),
    vrem(tl(X), Y, R3, N, I-1, Bs5).

%%
%% Subtraction 
%%
vsub(Ys, Zs, Bs) ->    
    Zs1 = vnot(Zs),
    vadd(Ys,Zs1,[],{bool,?TRUE},Bs).

%%
%% Adder circuit
%%
vadd(Ys,Zs,Bs) ->
    vadd(Ys,Zs,[],{bool,?FALSE},Bs).

vadd([?FALSE|Ys],[?FALSE|Zs],Xs,{bool,Ci},Bs) ->
    vadd(Ys,Zs,[Ci|Xs],{bool,?FALSE},Bs);
vadd([?FALSE|Ys],[Z|Zs],Xs,Ci,Bs) ->
    {{bool,X},Co,Bs1} = half_adder({bool,Z},Ci,Bs),
    vadd(Ys,Zs,[X|Xs],Co,Bs1);
vadd([Y|Ys],[?FALSE|Zs],Xs,Ci,Bs) ->
    {{bool,X},Co,Bs1} = half_adder({bool,Y},Ci,Bs),
    vadd(Ys,Zs,[X|Xs],Co,Bs1);
vadd([Y|Ys],[Z|Zs],Xs,Ci,Bs) ->
    {{bool,X},Co,Bs1} = full_adder({bool,Y},{bool,Z},Ci,Bs),
    vadd(Ys,Zs,[X|Xs],Co,Bs1);
vadd([],[],Xs,Ci,Bs) -> 
    {Ci,reverse(Xs),Bs}.

%% Full adder circuit.
full_adder(Y,Z,Ci,Bs) ->
    {X1,Bs1} = operation('xor',Y,Z,Bs),
    {X2,Bs2} = operation('xor',X1,Ci,Bs1),
    {A1,Bs3} = operation('and',X1,Ci,Bs2),
    {A2,Bs4} = operation('and',Y,Z,Bs3),
    {Co,Bs5} = operation('or',A1,A2,Bs4),
    {X2,Co,Bs5}.

half_adder(Y,Z,Bs) ->
    {X1,Bs1} = operation('xor',Y,Z,Bs),
    {Co,Bs2} = operation('and',Y,Z,Bs1),
    {X1,Co,Bs2}.

%%
%% if-then-else circuit
%%  (I & T) | (~I & E)
%%
ite({bool,?TRUE},T,_E, Bs) ->
    {T,Bs};
ite({bool,?FALSE},_T,E, Bs) -> 
    {E,Bs};
ite(_I,X,X, Bs) ->
    {X,Bs};
%% (I & false) | (~I & E) == ~I & E
ite(I,{bool,?FALSE},E, Bs) ->
    operation('and',negate(I),E,Bs);
%% (I & T) | (~I & false) == I & T
ite(I,T,{bool,?FALSE}, Bs) ->
    operation('and',I,T,Bs);
ite(I,T,E, Bs) ->
    {A1,Bs1} = operation('and',I,T,Bs),
    {A2,Bs2} = operation('and',negate(I),E,Bs1),
    operation('or',A1,A2,Bs2).

%% vector version of ite condition control if Ys or Zs is passed
vite(I,Ys,Zs,Bs) ->
    vite_(I,Ys,Zs,[],Bs).
    
vite_(I,[Y|Ys],[Z|Zs],Xs,Bs) ->
    {{bool,X}, Bs1} = ite(I,{bool,Y},{bool,Z},Bs),
    vite_(I,Ys,Zs,[X|Xs],Bs1);
vite_(_I,[],[],Xs,Bs) ->
    {reverse(Xs),Bs}.

%% conditional vector Ys or variable value Z
vitex(I,Ys,Z,Bs) when is_list(Ys), is_integer(Z) ->
    vitex_(I,Ys,Z,[],Bs).
    
vitex_(I,[Y|Ys],Z,Xs,Bs) ->
    {{bool,X}, Bs1} = ite(I,{bool,Y},{bool,Z},Bs),
    vitex_(I,Ys,Z,[X|Xs],Bs1);
vitex_(_I,[],_Z,Xs,Bs) ->
    {reverse(Xs),Bs}.
    
%% 
%% shift_left 2 [X0,X1,X2,X3,X4,X5,X6,X7]  ==
%%              [FALSE,FALSE,X0,X1,X2,X3,X4,X5]
vshift_left(K,N,Xs) when K >= 0 ->
    K1 = erlang:min(K,N),
    lists:duplicate(K1,?FALSE) ++ lists:sublist(Xs,1,N-K1).

%% unsigned shift right (ignoring sign bit) 
%% shift_right 2 [X0,X1,X2,X3,X4,X5,X6,X7]  ==
%%               [X2,X3,X4,X5,X6,X7,FALSE,FALSE]
vushift_right(K,N,Xs) when K >= 0 ->
    K1 = erlang:min(K,N),
    lists:sublist(Xs, K1+1, N) ++ lists:duplicate(K1,?FALSE).

%% signed shift right (shifing in sign bit)
%% shift_right 2 [X0,X1,X2,X3,X4,X5,X6,X7]  ==
%%               [X2,X3,X4,X5,X6,X7,X7,X7]
vshift_right(K,N,Xs) when K >= 0 ->
    K1 = erlang:min(K,N),
    Sign = lists:nth(N, Xs),
    lists:sublist(Xs, K1+1, N) ++ lists:duplicate(K1,Sign).

%% Compare equal
veq(Ys, Zs, Bs) ->
    {Xs,Bs1} = vmap_op('equ',Ys,Zs,Bs),
    vfold_op('and',{bool,?TRUE},Xs,Bs1).
    
%% Compare less
vless([Y],[Z],Bs) ->
    operation('<',{bool,Y},{bool,Z},Bs);
vless([Y|Ys],[Z|Zs],Bs) ->
    {Lv,Ev,Bs1} = vlteq(Ys,Zs,Bs),
    {L1,Bs2} = operation('<',{bool,Y},{bool,Z},Bs1),
    {L2,Bs3} = operation('and',Ev,L1,Bs2),
    operation('or',L2,Lv,Bs3).

vlteq([Y],[Z],Bs) ->
    {Lt,Bs1} = operation('<', {bool,Y},{bool,Z},Bs),
    {Eq,Bs2} = operation('equ',{bool,Y},{bool,Z},Bs1),
    {Lt,Eq,Bs2};
vlteq([Y|Ys],[Z|Zs],Bs) ->
    {Lv,Ev,Bs1} = vlteq(Ys,Zs,Bs),
    {L1,Bs2} = operation('<',{bool,Y},{bool,Z},Bs1),
    {E1,Bs3} = operation('equ',{bool,Y},{bool,Z},Bs2),
    {L2,Bs4} = operation('and',Ev,L1,Bs3),
    {Lv2,Bs5} = operation('or',L2,Lv,Bs4),
    {Ev2,Bs6} = operation('and',Ev,E1,Bs5),
    {Lv2,Ev2,Bs6}.

%% Apply same operator on two vectors
vmap_op(Op,Ys,Zs,Bs) ->
    vmap_op(Op,Ys,Zs,[],Bs).

vmap_op(Op,[Y|Ys],[Z|Zs],Xs,Bs) ->
    {{bool,X},Bs1} = operation(Op,{bool,Y},{bool,Z},Bs),
    vmap_op(Op,Ys,Zs,[X|Xs],Bs1);
vmap_op(_Op,[],[],Xs,Bs) ->
    {reverse(Xs),Bs}.

%% Apply same operator on one vector and one variable
vmap_opx(Op,Ys,Z,Bs) ->
    vmap_opx(Op,Ys,Z,[],Bs).

vmap_opx(Op,[Y|Ys],Z,Xs,Bs) ->
    {{bool,X},Bs1} = operation(Op,{bool,Y},{bool,Z},Bs),
    vmap_opx(Op,Ys,Z,[X|Xs],Bs1);
vmap_opx(_Op,[],_Z,Xs,Bs) ->
    {reverse(Xs),Bs}.
    

%% circuit for Ys < Zs
%% vless([Y|Ys],[Z|Zs],Xs,Bs) ->

sort(Xs,0,Bs) -> 
    {Xs,Bs};
sort(Xs,I,Bs) ->
    {[X|Xs1],Bs1} = minmax(Xs,Bs),
    {Xs2,Bs2} = sort(reverse(Xs1),I-1,Bs1),
    {Xs2++[X],Bs2}.

%% create a single pass minmax circuit over input
%% return the result reversed.
minmax(Xs, Bs) ->
    minmax(Xs,[],Bs).

minmax([X1],_Ys,Bs) ->
    {[X1],Bs};
minmax([X1,X2],Ys,Bs) ->
    {Min,Max,Bs1} = minmax2(X1,X2,Bs),
    {[Max,Min|Ys], Bs1};
minmax([X1,X2|Xs],Ys,Bs) ->
    {Min,Max,Bs1} = minmax2(X1,X2,Bs),
    minmax([Max|Xs],[Min|Ys],Bs1).

%% min/max circuit
minmax2(X1,X2,Bs) ->
    {Max,Bs1} = operation('or',X1,X2,Bs),
    {Min,Bs2} = operation('and',X1,X2,Bs1),
    {Min,Max,Bs2}.

cnf_to_formula(Cs) ->
    {all, map(fun(C) -> {any, C} end, Cs)}.    

triple(Op,X,Y,Z,Bs) ->
    debug(Bs, "Triple: ~w:~w ~w ~w\n", [X,Y,Op,Z]),
    Ts = Bs#bs.ts,
    Ti  = Ts#ts.n,
    Tp = array:set(Ti, {Op,X,Y,Z}, Ts#ts.triple),
    X0 = Ts#ts.xref,
    X1 = append_xref(X, Ti, X0),
    X2 = append_xref(Y, Ti, X1),
    X3 = append_xref(Z, Ti, X2),
    N  = Ti+1,
    Ts1 = Ts#ts { n = N, triple=Tp, xref=X3 },
    if Ti rem 1000 =:= 999 ->
	    info(Bs, "triples: ~w\n", [N]);
       true -> ok
    end,
    Bs#bs { ts=Ts1 }.

append_xref(?TRUE, _Ti, Xref) -> Xref;
append_xref(?FALSE, _Ti, Xref) -> Xref;
append_xref(V, Ti, Xr) when V < 0 -> append_xref(-V, Ti, Xr);
append_xref(V, Ti, Xr) -> array:set(V, [Ti|array:get(V, Xr)], Xr).

class_next(X, Bs) ->
    array:get(X, Bs#bs.vc).

value(?FALSE, _Bs) -> ?FALSE;
value(?TRUE, _Bs)  -> ?TRUE;
value(X, Bs) when X > 0 ->
    case array:get(X, Bs#bs.vt) of
	0 -> X;
	X1 -> value(X1, Bs)
    end;
value(X, Bs) when X < 0 ->
    -value(-X, Bs).
%%  case array:get(-X, Bs#bs.vt) of
%%	0 -> -X;
%%	X1 -> -value(X1, Bs)
%%  end.

%% get class variable (with out sign!)
class(?FALSE, _Bs) -> ?FALSE;
class(?TRUE, _Bs)  -> ?TRUE;
class(X, Bs) when X > 0 ->
    case array:get(X, Bs#bs.vc) of
	0 -> X;
	X1 -> class(X1,Bs)
    end;
class(X, Bs) when X < 0 ->
    case array:get(-X, Bs#bs.vc) of
	0 -> X;
	X1 -> class(-X1,Bs)
    end.

is_equivalent(X, Y, Bs) ->
    class(X,Bs) =:= class(Y,Bs).

%% Return a list of input variables

model_variables(Bs,[]) ->
    lists:sort(
      dict:fold(
	fun('$free',_,Acc) -> Acc;
	   (true,_,Acc) -> Acc;
	   (false,_,Acc) -> Acc;
	   (_X,Y,Acc) when is_integer(Y) ->
		[Y | Acc];
	   (_,_, Acc) -> Acc
	end, [], Bs#bs.vs));
model_variables(Bs,Ws) ->
    lists:map(fun(W) -> dict:fetch(W,Bs#bs.vs) end, Ws).


%%
%% collect the model
%% Boolean:  [{x,true},{y,false}]
%% Integer:  [{a,15},{b,-7},{c,0}]
%%
model(Bs) ->
    lists:keysort(1, collect_model(Bs)).

collect_model(Bs) ->
    dict:fold(
      fun (?TRUE,_,Ms) -> Ms;
	  (?FALSE,_,Ms) -> Ms;
	  (Y,Xs, Ms) when is_integer(Y) ->
	      model_vars(Xs,Y,Bs,Ms);
	  (_, _, Ms) -> Ms
      end, [], Bs#bs.vs).

%% collect all alias variables    
model_vars([{bit,X,N,I}|Xs],Y,Bs,Ms) ->
    case value(Y, Bs) of
	?TRUE ->
	    model_vars(Xs,Y,Bs,model_bitset(X,N,I,1,Ms));
	?FALSE ->
	    model_vars(Xs,Y,Bs,model_bitset(X,N,I,0,Ms))
    end;
model_vars([{uint,X,_N,I}|Xs],Y,Bs,Ms) ->
    case value(Y, Bs) of
	?TRUE ->
	    model_vars(Xs,Y,Bs,model_bor({X,(1 bsl I)}, Ms));
	?FALSE ->
	    model_vars(Xs,Y,Bs,model_bor({X,0}, Ms))
    end;
model_vars([{int,X,N,I}|Xs],Y,Bs,Ms) ->
    case value(Y, Bs) of
	?TRUE ->
	    if I =:= N-1 ->
		    model_vars(Xs,Y,Bs,model_bor({X,(-1 bsl I)}, Ms));
	       true ->
		    model_vars(Xs,Y,Bs,model_bor({X,(1 bsl I)}, Ms))
	    end;
	?FALSE ->
	    model_vars(Xs,Y,Bs,model_bor({X,0}, Ms))
    end;
model_vars([X|Xs],Y,Bs,Ms) when is_integer(Y) ->
    case value(Y, Bs) of
	?TRUE -> 
	    model_vars(Xs,Y,Bs,[{X,true} | Ms]);
	?FALSE ->
	    model_vars(Xs,Y,Bs,[{X,false} | Ms]);
	Z -> %% unbound...
	    model_vars(Xs,Y,Bs,[{X,Z} | Ms])
    end;
model_vars([],_Y,_Bs,Ms) ->
    Ms.

model_bitset(X,N,I,V,Ms) ->
    case lists:keytake(X, 1, Ms) of
	{value,{_,Bits},Ms1} ->
	    <<A:I,_:1,B/bitstring>> = Bits,
	    [{X,<<A:I,V:1,B/bitstring>>} | Ms1];
	false ->
	    J = (N-I)-1,
	    [{X,<<0:I,V:1,0:J>>}, Ms]
    end.    
    
model_bor({X,Bit}, Ms) ->
    case lists:keytake(X, 1, Ms) of
	{value,{_,Bits},Ms1} ->
	    [{X,Bit bor Bits} | Ms1];
	false ->
	    [{X,Bit} | Ms]
    end.

show_fail(Bs) ->
    io:format("FAIL:\n", []),
    Graph = lists:reverse(Bs#bs.bl),
    fmt_fail(Graph, Bs),
    case get(fmt_digraph) of
	done -> ok;
	undefined -> put(fmt_digraph, 1);
	3 ->
	    fmt_digraph("/tmp/dg.gv", Graph, Bs),
	    spawn(fun() -> os:cmd("open -a OmniGraffle\\ 5 /tmp/dg.gv") end),
	    put(fmt_digraph, done);
	I when is_integer(I) -> put(fmt_digraph, I+1)
    end.

fmt_digraph(File, Bl, Bs) ->
    case file:open(File, [write]) of
	{ok,Fd} ->
	    try fmt_digraph_fd(Fd,Bl,Bs) of
		Result -> Result
	    catch
		error:Reason -> 
		    Trace = erlang:get_stacktrace(),
		    io:format("~w\n", [{crash, error, Reason,Trace}]),
		    exit(Reason),
		    {error,Reason}
	    after
		file:close(Fd)
	    end
    end.

fmt_digraph_fd(Fd, Bl, Bs) ->
    io:format(Fd, "digraph G {\n", []),
    io:format(Fd, "node [color=lightblue,style=filled]\n", []),
    %% collect nodes and mark them with colors and labels
    lists:foldl(fun(mark,Set) -> 
			Set;
		   ({decision,N},Set) ->
			fmt_node(Fd,"color=green",N,Bs,Set);
		   ({true,N},Set) ->
			fmt_node(Fd,"color=blue",N,Bs,Set);
		   ({N1,N2},Set) ->
			Set1 = fmt_node(Fd,"color=lightblue",N1,Bs,Set),
			fmt_node(Fd,"color=lightblue",N2,Bs,Set1)
		end, sets:new(), Bl),
    lists:foreach(
      fun
	  (mark) ->
	      ok;
	  ({decision,{_X,_D,_Y}}) ->
	      ok;
	  ({true,{_X,_D,_Y}}) -> %% FIX
	      ok;
	 ({{X1,D1,Y1},{X2,D2,Y2}}) ->
	      io:format(Fd, "\"~s\" -> \"~s\";\n", 
				  [fmt_bind(X1,Y1,D1,Bs),
			 fmt_bind(X2,Y2,D2,Bs)])
      end, Bl),
    io:format(Fd, "}\n", []).

fmt_node(Fd,Attr,N={X,D,Y},Bs,Set) ->
    case sets:is_element(N, Set) of
	true -> 
	    Set;
	false ->
	    Name = fmt_bind(X,Y,D,Bs),
	    io:format(Fd, "\"~s\" [xlabel=\"~s\" ~s];\n",
		      [Name,Name,Attr]),
	    sets:add_element(N, Set)
    end.


fmt_bind(X,Y,D,Bs) ->
    io_lib:format("~s/~s(~w)", [fmt_v(X,Bs),fmt_v(Y,Bs),D]).


fmt_fail([{decision,{X,D,Y}}|Bl], Bs) ->
    io:format("\n<<~s/~s(~w)>> ", [fmt_v(X,Bs),fmt_v(Y,Bs),D]),
    fmt_fail(Bl, Bs);
fmt_fail([{true,{X,D,Y}}|Bl], Bs) ->
    io:format("\n*~s/~s(~w)* ", [fmt_v(X,Bs),fmt_v(Y,Bs),D]),
    fmt_fail(Bl, Bs);
fmt_fail([{{X1,D1,Y1},{X,D,Y}}|Bl], Bs) ->
    io:format("[~s/~s(~w) -> ~s/~s(~w)] ", 
	      [fmt_v(X1,Bs),fmt_v(Y1,Bs),D1,
	       fmt_v(X,Bs),fmt_v(Y,Bs),D]),
    fmt_fail(Bl, Bs);
fmt_fail([mark|Bl], Bs) ->
    io:format("|", []),
    fmt_fail(Bl, Bs);
fmt_fail([], _Bs) ->
    io:format("\n", []).

%% compact version of fmt_var
fmt_v(?TRUE,_)  -> "1";
fmt_v(?FALSE,_) -> "0";
fmt_v(X, Bs) ->
    if X < 0 -> fmt_var_(-X, Bs, "~", "");
       true ->  fmt_var_(X, Bs, "", "")
    end.


fmtq(X, Bs) ->
    fmt_var(X, Bs, "\"").

fmt_var(X, Bs) ->
    fmt_var(X, Bs, "").

		  
fmt_var(?TRUE, _Bs, _Q)  -> "true";
fmt_var(?FALSE, _Bs, _Q) -> "false";
fmt_var(X, Bs, Q) ->
    if X < 0 ->
	    fmt_var_(-X, Bs, "~", Q);
       true ->
	    fmt_var_(X, Bs, "", Q)
    end.

fmt_var_(X, Bs, P, Q) ->
    case dict:find(X, Bs#bs.vs) of
	error ->
	    [Q,P,$$,integer_to_list(X),Q];
	{ok,[{T,V,_N,I}|_Ns]} when ?is_vec_type(T),is_integer(I) ->
	    [Q,P,io_lib:format("~p[~w]", [V,I]),Q];
	{ok,[{A,I}|_Ns]} when is_atom(A),is_integer(I) ->
	    [Q,P,io_lib:format("~p[~w]", [A,I]),Q];
	{ok,[{A,I,J}|_Ns]} when is_atom(A),is_integer(I),is_integer(J) ->
	    [Q,P,io_lib:format("~p[~w,~w]", [A,I,J]),Q];
	{ok,[N|_Ns]} ->
	    [Q,P,io_lib:format("~p", [N]),Q]
    end.



fmt_var_list([X],Bs) ->
    fmt_var(X,Bs);
fmt_var_list([X|Xs],Bs) ->
    [fmt_var(X,Bs),",",fmt_var_list(Xs,Bs)];
fmt_var_list([],_Bs) ->
    "".

fmt_var_value_list([?pair(X,V)],Bs) ->
    [fmt_var(X,Bs),"=",fmt_value(V)];
fmt_var_value_list([?pair(X,V)|Xs],Bs) ->
    [fmt_var(X,Bs),"=",fmt_value(V),"," | fmt_var_value_list(Xs,Bs)];
fmt_var_value_list([],_Bs) ->
    "".

fmt_value(?TRUE) -> "true";
fmt_value(?FALSE) ->  "false";
fmt_value(X) when X < 0 -> "~$"++integer_to_list(-X);
fmt_value(X) when X > 0 -> "$"++integer_to_list(X).

fmt_triples([], _Bs) ->
    [];
fmt_triples([T], Bs) ->
    [fmt_triple(T,Bs)];
fmt_triples([T|Ts], Bs) ->
    [fmt_triple(T,Bs),"," | fmt_triples(Ts,Bs)].

fmt_triple({Op,X,Y,Z}, Bs) ->
    [fmt_var(X,Bs),":",fmt_var(Y,Bs),fmtop(Op),fmt_var(Z,Bs)].

fmtop(imp) -> "->";
fmtop(equ) -> "<->";
fmtop('xor') -> " ^ ";
fmtop('and') -> " & ";
fmtop('or') -> " | ";
fmtop('not') -> "~".
