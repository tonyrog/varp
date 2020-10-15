%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2020, Tony Rogvall
%%% @doc
%%%    Various circuit building functions
%%% @end
%%% Created :  1 Sep 2020 by Tony Rogvall <tony@rogvall.se>

-module(varp_circuit).

-export([inv_gate/2, inv_gate/3,
	 inv_pin/2,
	 or_gate/3, or_gate/4,
	 nor_gate/3, nor_gate/4,
	 imp_gate/3, imp_gate/4,
	 nimp_gate/3, nimp_gate/4,
	 and_gate/3, and_gate/4, 
	 nand_gate/3, nand_gate/4, 
	 xor_gate/3, xor_gate/4,
	 xnor_gate/3, xnor_gate/4,
	 min_gate/3, min_gate/4,
	 max_gate/3, max_gate/4,
	 half_adder/3, half_adder/4, half_adder/5,
	 full_adder/3, full_adder/4, full_adder/5, full_adder/6]).

-export([comparator/3, comparator/5]).
-export([left_assoc/3, left_assoc/4]).
-export([right_assoc/3, right_assoc/4]).
-export([none_assoc/3, none_assoc/4]).
-export([any/2, any/3]).
-export([all/2, all/3]).
-export([none/2, none/3]).
-export([one/2, one/3]).
-export([odd/2, odd/3]).
-export([even/2, even/3]).
-export([parity/2, parity/3]).

-export([eqk/3, eqk/4]).
-export([neqk/3, neqk/4]).
-export([ltk/3, ltk/4]).
-export([ltek/3, ltek/4]).
-export([gtk/3, gtk/4]).
-export([gtek/3, gtek/4]).

-export([add/3, add/4]).
-export([add_ci/4, add_ci/5]).
-export([add_co/4, add_co/5]).
-export([add_ci_co/5, add_ci_co/6]).

-export([symbol_value/2]).
-export([unsigned_value/2]).
-export([signed_value/2]).

-export([bind_symbol/3]).
-export([bind_value/3]).
-export([bind_integer/3]).
-export([bind_bits/3]).

-compile(export_all).

inv(true) -> false;
inv(false) -> true;
inv(X) -> -X.

var(Vp) -> var(Vp, undefined).
var(Vp, Symbol) ->
    X = varc:add_variable(Vp,false),
    varc:isused(Vp, X, true),
    sym(Vp, X, Symbol).

atom(Vp, Symbol) ->
    X = varc:add_variable(Vp,true),
    varc:isused(Vp, X, true),
    sym(Vp, X, Symbol).

sym(_Vp, X, undefined) -> X;
sym(Vp, X, Symbol) ->
    varc:add_symbol(Vp, X, Symbol),
    X.

or_clauses(Vp, X, Y, Z) ->
    clause(Vp, [inv(X),Y,Z]),
    clause(Vp, [X,inv(Y)]),
    clause(Vp, [X,inv(Z)]),
    X.

%% x = y AND z ( x = -(-y OR -z) )
and_clauses(Vp, X, Y, Z) ->
    or_clauses(Vp, inv(X), inv(Y), inv(Z)),
    X.


xor_clauses(Vp, X, Y, Z) ->
    clause(Vp,[X,inv(Y),Z]),
    clause(Vp,[X,Y,inv(Z)]),
    clause(Vp,[inv(X),inv(Y),inv(Z)]),
    clause(Vp,[inv(X),Y,Z]),
    X.

%% x = not y
inv_clauses(Vp, X, Y) ->
    clause(Vp,[X,Y]),
    clause(Vp,[inv(X),inv(Y)]),
    X.

inv_gate(Vp, Y) ->
    inv_gate(Vp, var(Vp), Y).

inv_gate(Vp, X, Y) ->
    inv_clauses(Vp, X, Y).

inv_pin(_Vp, Y) ->
    inv(Y).

%% x = y OR z
or_gate(Vp, Y, Z) ->
    or_gate(Vp, var(Vp), Y, Z).

or_gate(Vp, X, Y, Z) ->
    or_clauses(Vp, X, Y, Z).

%% x = NOT (y OR z)
nor_gate(Vp, Y, Z) ->
    nor_gate(Vp, var(Vp), Y, Z).

nor_gate(Vp, X, Y, Z) ->
    inv(or_clauses(Vp, X, Y, Z)).

%% x = y -> z (NOT y OR z)
imp_gate(Vp, Y, Z) ->
    imp_gate(Vp, var(Vp), Y, Z).

imp_gate(Vp, X, Y, Z) ->
    or_clauses(Vp, X, inv(Y), Z).

%% = y -/> z ( NOT (y -> z) ) = NOT (NOT y OR Z) =  (y AND NOT z)
nimp_gate(Vp, Y, Z) ->
    nimp_gate(Vp, var(Vp), Y, Z).

nimp_gate(Vp, X, Y, Z) ->
    and_clauses(Vp, X, Y, inv(Z)).

%% x = y AND z
and_gate(Vp, Y, Z) ->
    and_gate(Vp, var(Vp), Y, Z).

and_gate(Vp, X, Y, Z) ->
    and_clauses(Vp, X, Y, Z).

%% x = NOT (y AND z)
nand_gate(Vp, Y, Z) ->
    nand_gate(Vp, var(Vp), Y, Z).
nand_gate(Vp, X, Y, Z) ->
    inv(and_clauses(Vp, X, Y, Z)).

%% x = y XOR z
xor_gate(Vp, Y, Z) ->
    xor_gate(Vp, var(Vp), Y, Z).

xor_gate(Vp, X, Y, Z) ->
    xor_clauses(Vp, X, Y, Z).

%% x = NOT (y XOR z)
xnor_gate(Vp, Y, Z) ->
    xnor_gate(Vp, var(Vp), Y, Z).

xnor_gate(Vp, X, Y, Z) ->
    inv(xor_clauses(Vp, X, Y, Z)).

%% x = (y == z)
equ_gate(Vp, Y, Z) ->
    equ_gate(Vp, var(Vp), Y, Z).

equ_gate(Vp, X, Y, Z) ->
    inv(xor_clauses(Vp, X, Y, Z)).

gate(_Vp,'not',Y) -> inv(Y);
gate(Vp,'all',Ys) -> all(Vp, Ys);
gate(Vp,'any',Ys) -> any(Vp, Ys);
gate(Vp,'none',Ys) -> none(Vp, Ys);
gate(Vp,'one',Ys) -> one(Vp, Ys);
gate(Vp,'odd',Ys) -> odd(Vp, Ys);
gate(Vp,'even',Ys) -> even(Vp, Ys);
gate(Vp,'parity',Ys) -> parity(Vp, Ys).
		     
%% return gate function from name
gate(Vp,'or',X,Y,Z) -> or_gate(Vp,X,Y,Z);
gate(Vp,'nor',X,Y,Z) -> nor_gate(Vp,X,Y,Z);
gate(Vp,'imp',X,Y,Z) -> imp_gate(Vp,X,Y,Z);
gate(Vp,'nimp',X,Y,Z) -> nimp_gate(Vp,X,Y,Z);
gate(Vp,'and',X,Y,Z) -> and_gate(Vp,X,Y,Z);
gate(Vp,'nand',X,Y,Z) -> nand_gate(Vp,X,Y,Z);
gate(Vp,'xor',X,Y,Z) -> xor_gate(Vp,X,Y,Z);
gate(Vp,'xnor',X,Y,Z) -> xnor_gate(Vp,X,Y,Z);
gate(Vp,'equ',X,Y,Z) -> equ_gate(Vp,X,Y,Z);

gate(Vp,'eq',K,X,Ys) -> eqk(Vp,K,X,Ys);
gate(Vp,'neq',K,X,Ys) -> neqk(Vp,K,X,Ys);
gate(Vp,'lt',K,X,Ys) -> ltk(Vp,K,X,Ys);
gate(Vp,'lte',K,X,Ys) -> ltek(Vp,K,X,Ys);
gate(Vp,'gt',K,X,Ys) -> gtk(Vp,K,X,Ys);
gate(Vp,'gte',K,X,Ys) -> gtek(Vp,K,X,Ys).


gate(Vp,'not',X,Y) -> inv_clauses(Vp, X, Y), X;
gate(Vp,'or',Y,Z) -> or_gate(Vp,Y,Z);
gate(Vp,'nor',Y,Z) -> nor_gate(Vp,Y,Z);
gate(Vp,'imp',Y,Z) -> imp_gate(Vp,Y,Z);
gate(Vp,'nimp',Y,Z) -> nimp_gate(Vp,Y,Z);
gate(Vp,'and',Y,Z) -> and_gate(Vp,Y,Z);
gate(Vp,'nand',Y,Z) -> nand_gate(Vp,Y,Z);
gate(Vp,'xor',Y,Z) -> xor_gate(Vp,Y,Z);
gate(Vp,'xnor',Y,Z) -> xnor_gate(Vp,Y,Z);
gate(Vp,'equ',Y,Z) -> equ_gate(Vp,Y,Z);

gate(Vp,'all',X,Ys) -> all(Vp,X,Ys);
gate(Vp,'any',X,Ys) -> any(Vp,X,Ys);
gate(Vp,'none',X,Ys) -> none(Vp,X,Ys);
gate(Vp,'one',X,Ys) -> one(Vp,X,Ys);
gate(Vp,'odd',X,Ys) -> odd(Vp,X,Ys);
gate(Vp,'even',X,Ys) -> even(Vp,X,Ys);
gate(Vp,'parity',X,Ys) -> parity(Vp,X,Ys);

gate(Vp,'eq',K,Ys) -> eqk(Vp,K,Ys);
gate(Vp,'neq',K,Ys) -> neqk(Vp,K,Ys);
gate(Vp,'lt',K,Ys) -> ltk(Vp,K,Ys);
gate(Vp,'lte',K,Ys) -> ltek(Vp,K,Ys);
gate(Vp,'gt',K,Ys) -> gtk(Vp,K,Ys);
gate(Vp,'gte',K,Ys) -> gtek(Vp,K,Ys).


%% x = MIN(y,z) = (y AND z)
min_gate(Vp, Y, Z) ->
    min_gate(Vp, var(Vp), Y, Z).

min_gate(Vp, X, Y, Z) ->
    and_clauses(Vp, X, Y, Z).

%% x = MAX(y,z) = (y OR z)
max_gate(Vp, Y, Z) ->
    max_gate(Vp, var(Vp), Y, Z).

max_gate(Vp, X, Y, Z) ->
    or_clauses(Vp, X, Y, Z).

half_adder(Vp, Y, Z) ->
    half_adder(Vp, var(Vp), Y, Z).

half_adder(Vp, X, Y, Z) ->
    half_adder(Vp, X, Y, Z, var(Vp)).

half_adder(Vp, X, Y, Z, Co) ->
    S1 = xor_gate(Vp, X, Y, Z),
    Co1 = and_gate(Vp, Co, Y, Z),
    {S1, Co1}.

full_adder(Vp, Y, Z) ->
    full_adder(Vp, var(Vp), Y, Z).

full_adder(Vp, X, Y, Z) ->
    full_adder(Vp, X, Y, Z, false).

full_adder(Vp, X, Y, Z, Ci) ->
    full_adder(Vp, X, Y, Z, Ci, var(Vp)).

full_adder(Vp, X, Y, Z, Ci, Co) ->
    S1 = xor_gate(Vp,Y,Z),
    S2 = xor_gate(Vp,X,S1,Ci),  %% S2==X!
    A1 = and_gate(Vp,S1,Ci),
    A2 = and_gate(Vp,Y,Z),
    Co1 = or_gate(Vp,Co,A1,A2),
    {S2, Co1}.

%% (min,max) = SORT(y, z)
comparator(Vp, Y, Z) ->
    comparator(Vp, Y, Z, var(Vp), var(Vp)).

comparator(Vp, Y, Z, X0, X1) ->
    {min_gate(Vp, X0, Y, Z), max_gate(Vp, X1, Y, Z)}.

%% "bubbel" sort Xs n times
sort(_Vp,0,Xs) -> 
    Xs;
sort(Vp,I,Xs) ->
    [X|Xs1] = minmax(Vp,Xs),
    Xs2 = sort(Vp,I-1,lists:reverse(Xs1)),
    Xs2++[X].

%% bubbel sort Xs one lap
minmax(Vp,Xs) ->
    minmax(Vp,Xs,[]).

minmax(_Vp,[X1],_Ys) ->
    [X1];
minmax(Vp,[X1,X2],Ys) ->
    {Min,Max} = comparator(Vp,X1,X2),
    [Max,Min|Ys];
minmax(Vp,[X1,X2|Xs],Ys) ->
    {Min,Max} = comparator(Vp,X1,X2),
    minmax(Vp,[Max|Xs],[Min|Ys]).


any(Vp,Ys) -> none_assoc(Vp,'or',Ys).
any(Vp,X,Ys) -> none_assoc(Vp,'or',X,Ys).

all(Vp,Ys) -> none_assoc(Vp,'and',Ys).
all(Vp,X,Ys) -> none_assoc(Vp,'and',X,Ys).

none(Vp,Ys) -> inv(any(Vp,Ys)).
none(Vp,X,Ys) -> inv(any(Vp,X,Ys)).

odd(Vp,Ys) -> parity(Vp,Ys).
odd(Vp,X,Ys) -> parity(Vp,X,Ys).

even(Vp,Ys) -> inv(parity(Vp,Ys)).
even(Vp,X,Ys) -> inv(parity(Vp,X,Ys)).

parity(_Vp,[]) -> false;
parity(Vp,Ys) -> left_assoc(Vp,'xor',Ys).

parity(Vp,X,[]) -> or_gate(Vp,X,false,false);
parity(Vp,X,Ys) -> left_assoc(Vp,'xor',X,Ys).
    
    
%% left balanced circuit 
left_assoc(Vp,Gate,Ys) ->
    left_assoc(Vp,Gate,var(Vp),Ys).

left_assoc(Vp,Gate,X,[X1,X2]) ->
    gate(Vp,Gate,X,X1,X2);
left_assoc(Vp,Gate,X,[X1,X2|Xs]) ->
    Y1 = var(Vp),
    gate(Vp,Gate,Y1,X1,X2),
    left_assoc_(Vp,Gate,X,Xs,Y1).

left_assoc_(Vp,Gate,X,[Xn],Yi) ->
    gate(Vp,Gate,X,Yi,Xn);
left_assoc_(Vp,Gate,X,[Xi|Xs],Yi) ->
    Yj = var(Vp),
    gate(Vp,Gate,Yj,Yi,Xi),
    left_assoc_(Vp,Gate,X,Xs,Yj).

%% right balanced 
right_assoc(Vp,Gate,Xs) ->
    right_assoc(Vp,Gate,var(Vp),Xs).
    
right_assoc(Vp,Gate,X,Xs) ->
    left_assoc(Vp,Gate,X,lists:reverse(Xs)).

none_assoc(Vp,Gate,Xs) ->
    none_assoc(Vp,Gate,var(Vp),Xs).

none_assoc(Vp,Gate,X,Xs) when is_list(Xs) ->
    case Gate of
	'or' ->
	    clause(Vp, [inv(X)|Xs]),
	    lists:foreach(
	      fun(Xi) ->
		      clause(Vp,[X,inv(Xi)])
	      end, Xs),
	    X;
	'and' ->
	    clause(Vp, [X|[inv(Xi)||Xi<-Xs]]),
	    lists:foreach(
	      fun(Xi) ->
		      clause(Vp,[inv(X),Xi])
	      end, Xs),
	    X;
	_ ->
	    none_assoc_(Vp,Gate,X,Xs)
    end.

none_assoc_(Vp,Gate,X,Xs) ->
    case lists:split(length(Xs) div 2,Xs) of
	{[U],[V]} ->
	    gate(Vp,Gate,X,U,V);
	{[U],[V1,V2]} ->
	    X1 = var(Vp),
	    gate(Vp,Gate,X1,V1,V2),
	    gate(Vp,Gate,X,U,X1);
	{Us,Vs} ->
	    X1 = var(Vp),
	    _R = none_assoc_(Vp,Gate,X1,Us),
	    X2 = var(Vp),
	    _L = none_assoc_(Vp,Gate,X2,Vs),
	    gate(Vp,Gate,X,X1,X2)
    end.

eqk(Vp,K,Ys) ->  eqk(Vp,K,var(Vp),Ys).
neqk(Vp,K,Ys) -> neqk(Vp,K,var(Vp),Ys).
ltk(Vp,K,Ys) ->  ltk(Vp,K,var(Vp),Ys).
ltek(Vp,K,Ys) -> ltek(Vp,K,var(Vp),Ys).
gtk(Vp,K,Ys) ->  gtk(Vp,K,var(Vp),Ys).
gtek(Vp,K,Ys) -> gtek(Vp,K,var(Vp),Ys).

neqk(Vp,K,X,Ys) -> inv(eqk(Vp,K,X,Ys)).
    
ltk(Vp,1,X,Ys) -> none(Vp,X,Ys);
ltk(Vp,K,X,Ys) when is_integer(K), K>1 ->
    N = length(Ys),
    gtk_(Vp, N-K, N, X, [inv(Yi) || Yi <- Ys]).

ltek(Vp,0,X,Ys) -> none(Vp,X,Ys);
ltek(Vp,K,X,Ys) when is_integer(X), X>0 ->
    N = length(Ys),
    gtk_(Vp,N-K-1, N, X, [inv(Yi) || Yi <- Ys]).

gtek(Vp,0,X,Ys) -> any(Vp,X,Ys);
gtek(Vp,K,X,Ys) when is_integer(K), K>0 ->
    gtk(Vp, K-1, X, Ys).

gtk(Vp, K, X, Ys) when is_integer(K), K >= 0 ->
    gtk_(Vp, K, length(Ys), X, Ys).

gtk_(Vp,0,_N,X,Ys) ->
    any(Vp,X,Ys);
gtk_(_Vp,K,N,_X,_Ys) when K >= N -> %% no models
    false;
gtk_(Vp,K,N,X,Ys) ->
    Ys1 = sort(Vp,K,Ys),
    {A,B} = lists:split(N-K, Ys1),
    A1 = any(Vp,A),
    B1 = all(Vp,B),
    and_gate(Vp, X, A1, B1).

%% Generate a formula where exact K out of N formulas are true.
eqk(Vp,1,X,Ys) ->
    one(Vp, X, Ys);
eqk(Vp,K,X,Ys) ->
    eqk_(Vp,K,length(Ys),X,Ys).
    
eqk_(Vp,0,_N,X,Ys) ->
    inv(any(Vp,X,Ys));
eqk_(_Vp,K,N,_X,_Ys) when K > N -> %% no models
    %% bind X = false?
    false;
eqk_(Vp,K,N,X,Ys) when K =:= N ->
    all(Vp,X,Ys);
eqk_(Vp,K,N,X,Ys) ->
    Ys1 = sort(Vp,K,Ys),
    {A,B} = lists:split(N-K, Ys1),
    A1 = any(Vp,A),
    B1 = all(Vp,B),
    and_gate(Vp, X, inv(A1), B1).

%% sort all ys one lap then or over the
%% fixme len(ys) < 2
one(Vp, Ys) ->
    one(Vp, var(Vp), Ys).

one(Vp, X, [Y0,Y1|Ys]) ->
    {Z0,Z1} = comparator(Vp, Y0, Y1),
    eq1_(Vp, X, Ys, Z1, [Z0]).

eq1_(Vp, X, [Y|Ys], Zi, Zs) ->
    {Z0,Z1} = comparator(Vp, Zi, Y),
    eq1_(Vp, X, Ys, Z1, [Z0|Zs]);
eq1_(Vp, X, [], Zi, Zs) ->
    and_gate(Vp, X, Zi, none(Vp,Zs)).

%% variables
vars(Vp,N) ->
    {L,H} = vars(Vp,N),
    lists:seq(L,H).

'bnot'(_Vp, Ys) ->
    [inv(Yi) || Yi <- Ys].

sub(Vp, Ys, Zs) ->
    add_ci(Vp, Ys, 'bnot'(Vp,Zs), true).

sub(Vp, Xs, Ys, Zs) ->
    add_ci(Vp, Xs, Ys, 'bnot'(Vp,Zs), true).

%% adder
add(Vp, Ys, Zs) ->
    add_(Vp, Ys, Zs, false, var(Vp)).

add(Vp, Xs, Ys, Zs) ->
    add_(Vp, Xs, Ys, Zs, false, var(Vp)).

%% adder with carry in
add_ci(Vp, Ys, Zs, Ci) ->
    add_(Vp, Ys, Zs, Ci, var(Vp)).

add_ci(Vp, Xs, Ys, Zs, Ci) ->
    add_(Vp, Xs, Ys, Zs, Ci, var(Vp)).

%% adder with carry out
add_co(Vp, Ys, Zs, Co) ->
    add_(Vp, Ys, Zs, false, Co).

add_co(Vp, Xs, Ys, Zs, Co) ->
    add_(Vp, Xs, Ys, Zs, false, Co).

%% adder with carry in and carry out
add_ci_co(Vp, Ys, Zs, Ci, Co) ->
    add_(Vp, Ys, Zs, Ci, Co).

add_ci_co(Vp, Xs, Ys, Zs, Ci, Co) ->
    add_(Vp, Xs, Ys, Zs, Ci, Co).

add_(Vp, Ys, Zs, Ci, Co) ->
    Xs = vars(Vp,length(Ys)),
    add_(Vp, Xs, Ys, Zs, Ci, Co).

add_(Vp, Xs, Ys, Zs, Ci, Co) ->
    Cs = add__(Vp, Xs, Ys, Zs, [Ci], Co),
    {[Co|Cs], Xs}.
    
add__(Vp, [X], [Y], [Z], Cs=[Ci|_], Co) ->
    {X,Co} = full_adder(Vp, X, Y, Z, Ci, Co),
    [Co|Cs];
add__(Vp, [X|Xs], [Y|Ys], [Z|Zs], Cs=[Ci|_], Co) ->
    {X,Cx} = full_adder(Vp, X, Y, Z, Ci),
    add__(Vp, Xs, Ys, Zs, [Cx|Cs], Co).

%% TEST

clause(Vp, Ls) ->
    %%io:format("clause [~s]\n", [string:join([literal(Vp,L)||L<-Ls], ",")]),
    varc:add_clause(Vp, Ls).

test_gate(Gate) ->
    Vp = varc:new(#{xref => true}),
    A = var(Vp, "A"),
    B = var(Vp, "B"),
    X = var(Vp, "X"),
    C = gate(Vp,Gate,X,A,B),
    varc:bind(Vp, C),
    varc:set_level(Vp, 1),
    bt_all(Vp).

test_or() ->
    test_gate('or').

test_nor() ->
    test_gate('nor').

test_and() ->
    test_gate('and').

test_nand() ->
    test_gate('nand').

test_xor() ->
    test_gate('xor').

test_xnor() ->
    test_gate('xnor').

test_any() ->
    Vp = varc:new(#{xref => true}),
    A = var(Vp, "A"),
    B = var(Vp, "B"),
    C = var(Vp, "C"),
    D = var(Vp, "D"),
    E = any(Vp, [A,B,C,D]),
    varc:bind(Vp, E),
    varc:set_level(Vp, 1),
    bt_all(Vp).

test_all() ->
    Vp = varc:new(#{xref => true}),
    A = var(Vp, "A"),
    B = var(Vp, "B"),
    C = var(Vp, "C"),
    D = var(Vp, "D"),
    E = all(Vp, [A,B,C,D]),
    varc:bind(Vp, E),
    varc:set_level(Vp, 1),
    bt_all(Vp).

test_none() ->
    Vp = varc:new(#{xref => true}),
    A = var(Vp, "A"),
    B = var(Vp, "B"),
    C = var(Vp, "C"),
    D = var(Vp, "D"),
    E = none(Vp, [A,B,C,D]),
    varc:bind(Vp, E),
    varc:set_level(Vp, 1),
    bt_all(Vp).


test_eq1() ->
    Vp = varc:new(#{xref => true}),
    A = var(Vp, "A"),
    B = var(Vp, "B"),
    C = var(Vp, "C"),
    D = var(Vp, "D"),
    E = one(Vp, [A,B,C,D]),
    varc:bind(Vp, E),
    varc:set_level(Vp, 1),
    bt_all(Vp).

test_eq1_2() ->
    Vp = varc:new(#{xref => true}),
    A = var(Vp, "A"),
    B = var(Vp, "B"),
    C = var(Vp, "C"),
    D = false,
    E = one(Vp, [A,B,C,D]),
    varc:bind(Vp, E),
    varc:set_level(Vp, 1),
    bt_all(Vp).

test_half_adder1() ->
    Vp = varc:new(#{xref => true}),
    S = var(Vp, "S"),
    A = var(Vp, "A"),
    B = var(Vp, "B"),
    C = var(Vp, "C"),
    half_adder(Vp, S, A, B, C),
    bt_all(Vp).

test_full_adder1() ->
    Vp = varc:new(#{xref => true}),
    X = var(Vp, "X"),
    Y = var(Vp, "Y"),
    Z = var(Vp, "Z"),
    Ci = var(Vp, "Ci"),
    Co = var(Vp, "Co"),
    full_adder(Vp, X, Y, Z, Ci, Co),
    bt_all(Vp).

test_add() ->
    test_add(3).

test_add(N) ->
    Vp = varc:new(#{xref => true}),
    {Y0,Y1} = varc:add_variables(Vp,N),
    {Z0,Z1} = varc:add_variables(Vp,N),
    Ys = lists:seq(Y0,Y1),
    varc:add_symbol(Vp, Ys, "Y"),
    io:format("Y = ~w\n", [Ys]),
    Zs = lists:seq(Z0,Z1),
    varc:add_symbol(Vp, Zs, "Z"),
    io:format("Z = ~w\n", [Zs]),
    {[Ci,_Cj|_], Xs} = add(Vp, Ys, Zs),
    varc:add_symbol(Vp, Ci, "Carry"),
    io:format("X = ~w\n", [Xs]),
    varc:add_symbol(Vp, Xs, "X"),
    set_status(Vp, Ci, false),
    %% set_overflow(Vp, uint, Ci, Cj, false),
    varc:set_level(Vp, 1),
    bt_all(Vp).


test_sub() ->
    test_sub(3).

test_sub(N) ->
    Vp = varc:new(#{xref => true}),
    {Y0,Y1} = varc:add_variables(Vp,N),
    {Z0,Z1} = varc:add_variables(Vp,N),
    Ys = lists:seq(Y0,Y1),
    varc:add_symbol(Vp, Ys, "Y"),
    io:format("Y = ~w\n", [Ys]),
    Zs = lists:seq(Z0,Z1),
    varc:add_symbol(Vp, Zs, "Z"),
    io:format("Z = ~w\n", [Zs]),
    {[Ci,_Cj|_], Xs} = sub(Vp, Ys, Zs),
    varc:add_symbol(Vp, -Ci, "Br"),
    io:format("X = ~w\n", [Xs]),
    varc:add_symbol(Vp, Xs, "X"),
    set_status(Vp, -Ci, false),
    %% set_overflow(Vp, uint, Ci, Cj, false),
    varc:set_level(Vp, 1),
    bt_all(Vp).

%% Handle carry (Is it wise to backtrack over a Carry variable?)
set_status(Vp, Ci, false) ->    %% never generate carry
    xor_gate(Vp,false,Ci,false);
set_status(Vp, Ci, true) ->     %% always generate carry
    xor_gate(Vp,false,Ci,true);
set_status(_Vp,_Ci, ignore) ->  %% allow carry overflow
    ignore.


set_overflow(Vp,int,Ci,Cj, false) -> %% never generate overflow
    xor_gate(Vp,false,Ci,Cj);
set_overflow(Vp,int,Ci,Cj, true) -> %% always generate overflow
    xor_gate(Vp,true,Ci,Cj);
set_overflow(Vp,_Type,Ci,_Cj,false) -> %% never generate overflow
    xor_gate(Vp,false,Ci,false);
set_overflow(Vp,_Type,Ci,_Cj,true) -> %% never generate overflow
    xor_gate(Vp,false,Ci,true);
set_overflow(_Vp,_Type,_Ci,_Cj, ignore) ->  %% allow carry overflow
    ignore.


bt(Vp) ->
    case not varc:nbcp(Vp) of
	true ->
	    case varc:undo(Vp) of
		false -> false;  %% contradiction
		true -> bt(Vp)
	    end;
	false ->
	    true  %% model
    end.

%% limit>=1 !
bt_all(Vp) ->
    bt_all(Vp, undefined).

bt_all(Vp, Limit) ->
    T0 = erlang:monotonic_time(),
    Count = 
	case varc:next_unbound(Vp) of
	    false ->
		0;
	    _ ->
		case bt(Vp) of
		    true ->
			io:format("~p\n", [model(Vp)]),
			bt_all_(Vp, 1, Limit);
		    false ->
			0
		end
	end,
    T1 = erlang:monotonic_time(),
    Time = erlang:convert_time_unit(T1-T0,native,microsecond),
    io:format("~w models found in ~w us\n", [Count, Time]),
    Count.

bt_all_(Vp, Count, Limit) ->
    case varc:undo(Vp) andalso not bt_done(Count, Limit) of
	true ->
	    case bt(Vp) of
		true ->
		    io:format("~p\n", [model(Vp)]),
		    bt_all_(Vp, Count+1, Limit);
		false ->
		    Count
	    end;
	false ->
	    Count
    end.

bt_done(_Count, undefined) -> false;
bt_done(Count, Limit) -> Count >= Limit.

%% model(Vp) ->
%%    N = varc:info(Vp, 'number_of_variables'),
%%    [symbol(Vp, X) ||
%%	X <- lists:seq(1, N),
%%	varc:value(Vp, X), varc:variable_info(Vp, X, 'is_atom')].

model(Vp) ->
    model_(Vp, varc:first_symbol(Vp), []).

model_(_Vp, false, Model) ->
    Model;
model_(Vp, Var, Model) ->
    case symbol_value(Vp, Var) of
	undefined ->
	    error({not_defined, Var});
	false -> 
	    model_(Vp, varc:next_symbol(Vp,Var), Model);
	Value ->
	    model_(Vp, varc:next_symbol(Vp,Var), [{Var,Value}|Model])
    end.

symbol_value(Vp, Symbol) ->
    case varc:find_symbol(Vp, Symbol) of
	false -> undefined;
	Xs when is_list(Xs) -> unsigned_value(Vp, Xs);
	X when is_integer(X) -> varc:value(Vp, X)
    end.

unsigned_value(Vp, Xs) ->
    unsigned_value_(Vp, Xs, 0, 0).

unsigned_value_(Vp, [X|Xs], I, Value) ->
    case varc:value(Vp, X) of
	undefined -> 
	    io:format("~w index=~w undefined\n", [X,I]),
	    undefined;
	true -> unsigned_value_(Vp, Xs, I+1, Value + (1 bsl I));
	false -> unsigned_value_(Vp, Xs, I+1, Value)
    end;
unsigned_value_(_Vp, [], _I, Value) ->
    Value.

signed_value(Vp, Xs) ->
    N = length(Xs),
    U = unsigned_value(Vp, Xs),
    if U bsr (N-1) =:= 1 ->
	    U - (1 bsl N);
       true ->
	    U
    end.

bind_symbol(Vp, Symbol, Value) ->
    case varc:find_symbol(Vp, Symbol) of
	false -> false;
	Xs when is_list(Xs) -> 
	    bind_value(Vp, Xs, Value);
	X when is_integer(X) ->
	    case Value of
		true -> varc:bind(Vp, X);
		false -> varc:bind(Vp, -X);
		1 -> varc:bind(Vp, X);
		0 -> varc:bind(Vp, -X)
	    end
    end.
	
bind_value(Vp, Xs, Value) when is_integer(Value) ->    
    bind_integer(Vp, Xs, Value);
bind_value(Vp, Xs, Value) when is_bitstring(Value) ->
    bind_bits(Vp, Xs, Value).

%% bind bits in integer
bind_integer(Vp, [X|Xs], Value) ->
    case Value band 1 of
	1 -> varc:bind(Vp, X);
	0 -> varc:bind(Vp, -X)
    end,
    bind_integer(Vp, Xs, Value bsr 1);
bind_integer(_Vp, [], _Value) ->
    ok.

%% bind bits (fixme what is the "natural" order?)
bind_bits(Vp, [X|Xs], <<Value:1,Rest/bits>>) ->
    case Value of
	1 -> varc:bind(Vp, X);
	0 -> varc:bind(Vp, -X)
    end,
    bind_bits(Vp, Xs, Rest);
bind_bits(Vp, [X|Xs], <<>>) ->
    varc:bind(Vp, -X),
    bind_bits(Vp, Xs, <<>>);
bind_bits(_Vp, [], _) ->
    ok.

symbol(_Vp,true) -> "t";
symbol(_Vp,false) -> "f";
symbol(Vp, X) when is_integer(X) ->
    case varc:variable_info(Vp, X, 'symbol') of
	[] ->
	    "X("++integer_to_list(X)++")";
	[{Name,0}|_] when is_binary(Name) ->
	    case varc:find_symbol(Vp,Name) of
		false -> "X("++integer_to_list(X)++")";
		Y when is_integer(Y), abs(Y) =:= X -> binary_to_list(Name);
		Ys when is_list(Ys) -> binary_to_list(Name)++"[0]"
	    end;
	[{Term,0}|_] when is_tuple(Term) ->
	    case varc:find_symbol(Vp,Term) of
		false -> "X("++integer_to_list(X)++")";
		Y when is_integer(Y), abs(Y) =:= X -> var_to_list(Term);
		Ys when is_list(Ys) -> var_to_list(Term)++"[0]"
	    end;
	[{Name,I}|_] when is_binary(Name) ->
	    binary_to_list(Name)++"["++integer_to_list(I)++"]";
	[{Term,I}|_] when is_tuple(Term) ->
	    var_to_list(Term)++"["++integer_to_list(I)++"]"
    end.


literal(_Vp,true) -> "t";
literal(_Vp,false) -> "f";
literal(Vp,X) when is_integer(X), X > 0 ->
    symbol(Vp,X);
literal(Vp,X) when is_integer(X), X < 0 ->
    "!"++symbol(Vp,-X).

var_to_list({P,[]}) when is_list(P) ->
    P;
var_to_list({P,Args}) when is_list(P) ->
    P++"("++ string:join([var_to_list_(A) || A <- Args], ",") ++ ")".

var_to_list_(Value) when is_integer(Value) ->
    integer_to_list(Value);
var_to_list_(Name) when is_list(Name) ->  %% unresolved literals
    Name;
var_to_list_({Op,Args}) -> %% unresolved function symbols
    Op++"("++string:join([var_to_list_(A) || A <- Args], ",") ++ ")".
