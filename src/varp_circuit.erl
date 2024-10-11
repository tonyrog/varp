%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2020, Tony Rogvall
%%% @doc
%%%    Various circuit building functions
%%% @end
%%% Created :  1 Sep 2020 by Tony Rogvall <tony@rogvall.se>

-module(varp_circuit).

-export([var/1, var/2, atom/2]).
-export([vars/2]).
-export([inv/1]).
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
	 equ_gate/3, equ_gate/4,
	 neq_gate/3, neq_gate/4,
	 min_gate/3, min_gate/4,
	 max_gate/3, max_gate/4,
	 lt_gate/3, lt_gate/4,
	 lte_gate/3, lte_gate/4,
	 gt_gate/3, gt_gate/4,
	 gte_gate/3, gte_gate/4,
	 gate/3, gate/4, gate/5,
	 ite/4, ite/5
	]).

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

-export([set/3]).
-export([half_adder/3, half_adder/4, half_adder/5]).
-export([full_adder/3, full_adder/4, full_adder/5, full_adder/6]).

-export([clause/2, clause/3]).

-export([symbol/2]).
-export([literal/2]).
-export([symbol_value/2, symbol_value/3]).
-export([unsigned_value/2]).
-export([signed_value/2]).

-export([bind_symbol/3]).
-export([bind_value/3]).
-export([bind_integer/3]).
-export([bind_bits/3]).
-export([mon/2]).

%% TEST
-export([bcp_match/2]).
-export([bt_match/2]).
-export([bt_all/3]).
-export([test/0]).
-export([test_mon/1]).
-export([test_or_clause/0]).

-include("varp.hrl").
%% -compile(export_all).

inv(?T) -> ?F;
inv(?F) -> ?T;
inv(X) -> -X.

var(Vp) ->
    var(Vp, undefined).
var(Vp, Symbol) ->
    X = varp_nif:add_variable(Vp, _IsAtom=false, _IsUsed=true),
    sym(Vp, X, Symbol).

vars(Vp, N) when is_integer(N), N > 0 ->
    {First,Last} = varp_nif:add_variables(Vp, N, _IsAtom=false, _IsUsed=true),
    lists:seq(First, Last).

atom(Vp, Symbol) ->
    X = varp_nif:add_variable(Vp, _IsAtom=true, _IsUsed=true),
    sym(Vp, X, Symbol).

sym(_Vp, X, undefined) -> X;
sym(Vp, X, Symbol) ->
    varp_nif:add_symbol(Vp, {Symbol,[]}, X, bool),
    X.

%% X = Y  - assignment
set(Vp, X, false) -> clause(Vp, [inv(X)]), X;
set(Vp, X, true) -> clause(Vp, [X]), X;
set(Vp, X, Y) ->
    clause(Vp, [inv(X),Y]),
    clause(Vp, [X,inv(Y)]),
    X.

or_clauses(Vp, X, Y, false) -> 
    set(Vp, X, Y);
or_clauses(Vp, X, Y, Z) ->
    clause(Vp, [inv(X),Y,Z]),
    clause(Vp, [X,inv(Y)]),
    clause(Vp, [X,inv(Z)]),
    X.

%% x = y AND z ( x = -(-y OR -z) )
and_clauses(Vp, X, Y, Z) ->
    or_clauses(Vp, inv(X), inv(Y), inv(Z)),
    X.

%% X = Y xor false  =>  X = Y
xor_clauses(Vp, X, Y, false) -> set(Vp, X, Y);
xor_clauses(Vp, X, false, Z) -> set(Vp, X, Z);
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

inv_gate(Vp, undefined, Y) -> inv_gate(Vp, Y);
inv_gate(Vp, X, Y) ->
    inv_clauses(Vp, X, Y).

inv_pin(_Vp, Y) ->
    inv(Y).

%% x = y OR z
or_gate(_Vp,?F,Z) -> Z;
or_gate(_Vp,Y,?F) -> Y;
or_gate(_Vp,_Y,?T) -> ?T;
or_gate(_Vp,?T,_Z) -> ?T;
or_gate(Vp, Y, Z) -> or_gate(Vp, var(Vp), Y, Z).

or_gate(Vp, undefined, Y, Z) -> or_gate(Vp, Y, Z);
or_gate(Vp,X,?F,Z) -> set(Vp,X,Z);
or_gate(Vp,X,Y,?F) -> set(Vp,X,Y);
or_gate(Vp,X,?T,_Z) -> set(Vp,X,?T);
or_gate(Vp,X,_Y,?T) -> set(Vp,X,?T);
or_gate(Vp, X, Y, Z) ->
    or_clauses(Vp, X, Y, Z).

%% x = NOT (y OR z)
nor_gate(Vp, Y, Z) -> nor_gate(Vp, var(Vp), Y, Z).

nor_gate(Vp, undefined, Y, Z) -> nor_gate(Vp, Y, Z);
nor_gate(Vp, X, Y, Z) ->
    or_clauses(Vp, inv(X), Y, Z),
    X.

%% x = y -> z (NOT y OR z)

imp_gate(_Vp,?T,Z) -> Z;
imp_gate(_Vp,Y,?F) -> inv(Y);
imp_gate(_Vp,_Y,?T) -> ?T;
imp_gate(_Vp,?F,_Z) -> ?T;
imp_gate(Vp, Y, Z) -> imp_gate(Vp, var(Vp), Y, Z).

imp_gate(Vp, undefined, Y, Z) -> imp_gate(Vp, Y, Z);
imp_gate(Vp, X, Y, Z) ->
    or_clauses(Vp, X, inv(Y), Z).

%% = y -/> z ( NOT (y -> z) ) = NOT (NOT y OR Z) =  (y AND NOT z)
nimp_gate(Vp, Y, Z) -> nimp_gate(Vp, var(Vp), Y, Z).

nimp_gate(Vp, undefined, Y, Z) -> nimp_gate(Vp, Y, Z);
nimp_gate(Vp, X, Y, Z) ->
    and_clauses(Vp, X, Y, inv(Z)).

%% x = y AND z
and_gate(_Vp,?F,_Z) -> ?F;
and_gate(_Vp,_Y, ?F) -> ?F;
and_gate(_Vp,?T, Z) -> Z;
and_gate(_Vp,Y, ?T) -> Y;
and_gate(Vp, Y, Z) -> and_gate(Vp, var(Vp), Y, Z).

and_gate(Vp, undefined, Y, Z) -> and_gate(Vp, Y, Z);
and_gate(Vp,X, ?F,_Z) -> set(Vp,X,?F);
and_gate(Vp,X, _Y, ?F) -> set(Vp,X,?F);
and_gate(Vp,X, ?T, Z) -> set(Vp,X,Z);
and_gate(Vp,X, Y, ?T) -> set(Vp,X,Y);
and_gate(Vp, X, Y, Z) -> and_clauses(Vp, X, Y, Z).

%% x = NOT (y AND z)
nand_gate(Vp, Y, Z) -> nand_gate(Vp, var(Vp), Y, Z).

nand_gate(Vp, undefined, Y, Z) -> nand_gate(Vp, Y, Z);
nand_gate(Vp, X, Y, Z) -> and_clauses(Vp, inv(X), Y, Z), X.
			   

%% x = y XOR z
xor_gate(_Vp, ?F, Z) -> Z;
xor_gate(_Vp, ?T, Z) -> inv(Z);
xor_gate(_Vp, Y, ?F) -> Y;
xor_gate(_Vp, Y, ?T) -> inv(Y);
xor_gate(Vp, Y, Z) -> xor_gate(Vp, var(Vp), Y, Z).

xor_gate(Vp, undefined, Y, Z) -> xor_gate(Vp, Y, Z);
xor_gate(Vp, X, Y, Z) -> xor_clauses(Vp, X, Y, Z).

%% x = NOT (y XOR z)
xnor_gate(Vp, Y, Z) -> xnor_gate(Vp, var(Vp), Y, Z).

xnor_gate(Vp, undefined, Y, Z) -> xnor_gate(Vp, Y, Z);
xnor_gate(Vp, X, Y, Z) -> xor_clauses(Vp, inv(X), Y, Z), X.
			  

%% x = (y == z)
equ_gate(_Vp, ?F, Z) -> inv(Z);
equ_gate(_Vp, ?T, Z) -> Z;
equ_gate(_Vp, Y, ?F) -> inv(Y);
equ_gate(_Vp, Y, ?T) -> Y;
equ_gate(Vp, Y, Z) -> equ_gate(Vp, var(Vp), Y, Z).

equ_gate(Vp, undefined, Y, Z) -> equ_gate(Vp, Y, Z);
equ_gate(Vp, X, Y, Z) -> xor_clauses(Vp, X, inv(Y), Z).

%% x = (y != z)
neq_gate(_Vp, ?F, Z) -> Z;
neq_gate(_Vp, ?T, Z) -> inv(Z);
neq_gate(_Vp, Y, ?F) -> Y;
neq_gate(_Vp, Y, ?T) -> inv(Y);
neq_gate(Vp, Y, Z) -> neq_gate(Vp, var(Vp), Y, Z).

neq_gate(Vp, undefined, Y, Z) -> neq_gate(Vp, Y, Z);
neq_gate(Vp, X, Y, Z) -> xor_clauses(Vp, X, Y, Z).

gate(_Vp,'not',Y) -> inv(Y);
gate(Vp,'all',Ys) -> all(Vp, Ys);
gate(Vp,'any',Ys) -> any(Vp, Ys);
gate(Vp,'none',Ys) -> none(Vp, Ys);
gate(Vp,'one',Ys) -> one(Vp, Ys);
gate(Vp,'odd',Ys) -> odd(Vp, Ys);
gate(Vp,'even',Ys) -> even(Vp, Ys);
gate(Vp,'parity',Ys) -> parity(Vp, Ys).

gate(Vp,'and',X,Y,Z)  -> and_gate(Vp,X,Y,Z);		     
gate(Vp,'or',X,Y,Z)   -> or_gate(Vp,X,Y,Z);
gate(Vp,'imp',X,Y,Z)  -> imp_gate(Vp,X,Y,Z);
gate(Vp,'equ',X,Y,Z)  -> equ_gate(Vp,X,Y,Z);
gate(Vp,'xor',X,Y,Z)  -> xor_gate(Vp,X,Y,Z);
gate(Vp,'nor',X,Y,Z)  -> nor_gate(Vp,X,Y,Z);
gate(Vp,'nimp',X,Y,Z) -> nimp_gate(Vp,X,Y,Z);
gate(Vp,'nand',X,Y,Z) -> nand_gate(Vp,X,Y,Z);
gate(Vp,'xnor',X,Y,Z) -> xnor_gate(Vp,X,Y,Z);

gate(Vp,'lt',X,Y,Z)   -> lt_gate(Vp,X,Y,Z);
gate(Vp,'lte',X,Y,Z)  -> lte_gate(Vp,X,Y,Z);
gate(Vp,'gt',X,Y,Z)   -> gt_gate(Vp,X,Y,Z);
gate(Vp,'gte',X,Y,Z)  -> gte_gate(Vp,X,Y,Z);
gate(Vp,'eq',X,Y,Z)   -> equ_gate(Vp,X,Y,Z);
gate(Vp,'neq',X,Y,Z)  -> neq_gate(Vp,X,Y,Z);

gate(Vp,'EQ',K,X,Ys) -> eqk(Vp,K,X,Ys);
gate(Vp,'NEQ',K,X,Ys) -> neqk(Vp,K,X,Ys);
gate(Vp,'LT',K,X,Ys) -> ltk(Vp,K,X,Ys);
gate(Vp,'LTE',K,X,Ys) -> ltek(Vp,K,X,Ys);
gate(Vp,'GT',K,X,Ys) -> gtk(Vp,K,X,Ys); 
gate(Vp,'GTE',K,X,Ys) -> gtek(Vp,K,X,Ys).

gate(Vp,'not',X,Y) -> inv_gate(Vp, X, Y);
gate(Vp,'=',X,Y) -> set(Vp,X,Y);
gate(Vp,'or',Y,Z) -> or_gate(Vp,Y,Z);
gate(Vp,'nor',Y,Z) -> nor_gate(Vp,Y,Z);
gate(Vp,'imp',Y,Z) -> imp_gate(Vp,Y,Z);
gate(Vp,'nimp',Y,Z) -> nimp_gate(Vp,Y,Z);
gate(Vp,'and',Y,Z) -> and_gate(Vp,Y,Z);
gate(Vp,'nand',Y,Z) -> nand_gate(Vp,Y,Z);
gate(Vp,'xor',Y,Z) -> xor_gate(Vp,Y,Z);
gate(Vp,'xnor',Y,Z) -> xnor_gate(Vp,Y,Z);
gate(Vp,'equ',Y,Z) -> equ_gate(Vp,Y,Z);
gate(Vp,'lt',Y,Z) -> lt_gate(Vp,Y,Z);
gate(Vp,'lte',Y,Z) -> lte_gate(Vp,Y,Z);
gate(Vp,'gt',Y,Z) -> gt_gate(Vp,Y,Z);
gate(Vp,'gte',Y,Z) -> gte_gate(Vp,Y,Z);
gate(Vp,'eq',X,Y) -> equ_gate(Vp, X, Y);
gate(Vp,'neq',X,Y) -> neq_gate(Vp,X,Y);

gate(Vp,'all',X,Ys) -> all(Vp,X,Ys);
gate(Vp,'any',X,Ys) -> any(Vp,X,Ys);
gate(Vp,'none',X,Ys) -> none(Vp,X,Ys);
gate(Vp,'one',X,Ys) -> one(Vp,X,Ys);
gate(Vp,'odd',X,Ys) -> odd(Vp,X,Ys);
gate(Vp,'even',X,Ys) -> even(Vp,X,Ys);
gate(Vp,'parity',X,Ys) -> parity(Vp,X,Ys);

gate(Vp,'EQ',K,Ys) -> eqk(Vp,K,Ys);
gate(Vp,'NEQ',K,Ys) -> neqk(Vp,K,Ys);
gate(Vp,'LT',K,Ys) -> ltk(Vp,K,Ys);
gate(Vp,'LTE',K,Ys) -> ltek(Vp,K,Ys);
gate(Vp,'GT',K,Ys) -> gtk(Vp,K,Ys);
gate(Vp,'GTE',K,Ys) -> gtek(Vp,K,Ys).

%% x = MIN(y,z) = (y AND z)
min_gate(Vp, Y, Z) -> min_gate(Vp, var(Vp), Y, Z).

min_gate(Vp, undefined, Y, Z) -> min_gate(Vp, Y, Z);
min_gate(Vp, X, Y, Z) -> and_gate(Vp, X, Y, Z).

%% x = MAX(y,z) = (y OR z)
max_gate(Vp, Y, Z) -> max_gate(Vp, var(Vp), Y, Z).

max_gate(Vp, undefined, Y, Z) -> max_gate(Vp, Y, Z);
max_gate(Vp, X, Y, Z) -> or_gate(Vp, X, Y, Z).

%% x = LT(y,z) = !y AND z
lt_gate(Vp, Y, Z) -> and_gate(Vp, inv(Y), Z).

lt_gate(Vp, undefined, Y, Z) -> lt_gate(Vp, Y, Z);
lt_gate(Vp, X, Y, Z) -> and_gate(Vp, X, inv(Y), Z).

%% x = LTE(y,z) = !GT(y,z)
lte_gate(Vp, Y, Z) -> lte_gate(Vp, var(Vp), Y, Z).

lte_gate(Vp, undefined, Y, Z) -> lte_gate(Vp, Y, Z);
lte_gate(Vp, X, Y, Z) -> gt_gate(Vp, inv(X), Y, Z), X.

%% x = GT(y,z) = LT(z,y)
gt_gate(Vp, Y, Z) -> lt_gate(Vp, Z, Y).
gt_gate(Vp, undefined, Y, Z) -> gt_gate(Vp, Y, Z);
gt_gate(Vp, X, Y, Z) -> lt_gate(Vp, X, Z, Y).

%% x = GTE(y,z) = !LT(y,z)
gte_gate(Vp, Y, Z) -> gte_gate(Vp, var(Vp), Y, Z).
gte_gate(Vp, undefined, Y, Z) -> gte_gate(Vp, Y, Z);
gte_gate(Vp, X, Y, Z) -> lt_gate(Vp, inv(X), Y, Z), X.

%%
%% if-then-else circuit
%%  (I & T) | (~I & E)
%%
ite(_Vp,?T,T,_E) -> T;
ite(_Vp,?F,_T,E) -> E;
ite(_Vp,_I,X,X) -> X;
%% (I & false) | (~I & E) == ~I & E
ite(Vp,I,?F,E) -> and_gate(Vp, inv(I),E);
%% (I & T) | (~I & false) == I & T
ite(Vp,I,T,?F) -> and_gate(Vp, I,T);
ite(Vp,I,T,E) ->
    A1 = and_gate(Vp,I,T),
    A2 = and_gate(Vp,inv(I),E),
    or_gate(Vp,A1,A2).

ite(Vp,undefined,I,T,E) -> ite(Vp,I,T,E);
ite(Vp,X,?T,T,_E) -> set(Vp, X, T);
ite(Vp,X,?F,_T,E) -> set(Vp, X, E);
ite(_Vp,X,_I,X,X) ->  X;
%% (I & false) | (~I & E) == ~I & E
ite(Vp,X,I,?F,E) -> and_gate(Vp,X,inv(I),E);
%% (I & T) | (~I & false) == I & T
ite(Vp,X,I,T,?F) -> and_gate(Vp,X,I,T);
ite(Vp,X,I,T,E) ->
    A1 = and_gate(Vp,I,T),
    A2 = and_gate(Vp,inv(I),E),
    or_gate(Vp,X,A1,A2).

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

any(Vp,Ys) -> any_(Vp,Ys,[]).
any_(_Vp,[true|_], _Acc) -> true;
any_(Vp,[false|Ys], Acc) -> any_(Vp,Ys,Acc);
any_(Vp,[Y|Ys],Acc) -> any_(Vp,Ys,[Y|Acc]);
any_(Vp,[],Acc) ->
    case Acc of
	[] -> false;
	[Y] -> Y;
	Ys1 -> none_assoc(Vp,'or',Ys1)
    end.

any(Vp,undefined,Ys) -> any(Vp,Ys);
any(Vp,X,Ys) -> any_(Vp,X,Ys,[]).
any_(Vp,X,[true|_], _Acc) -> clause(Vp,[X]), X;
any_(Vp,X,[false|Ys], Acc) -> any_(Vp,X,Ys,Acc);
any_(Vp,X,[Y|Ys],Acc) -> any_(Vp,X,Ys,[Y|Acc]);
any_(Vp,X,[],Acc) ->
    case Acc of
	[] -> clause(Vp,[inv(X)]);
	Ys1 -> none_assoc(Vp,'or',X,Ys1)
    end.

all(Vp,Ys) -> all_(Vp,Ys,[]).
all_(_Vp,[false|_], _Acc) -> false;
all_(Vp,[true|Ys], Acc) -> all_(Vp,Ys,Acc);
all_(Vp,[Y|Ys],Acc) -> all_(Vp,Ys,[Y|Acc]);
all_(Vp,[],Acc) ->
    case Acc of
	[] -> true;
	[Y] -> Y;
	Ys1 -> none_assoc(Vp,'and',Ys1)
    end.

all(Vp,undefined,Ys) -> all(Vp,Ys);
all(Vp,X,Ys) -> all_(Vp,X,Ys,[]).
all_(Vp,X,[false|_], _Acc) -> clause(Vp,[inv(X)]),X;
all_(Vp,X,[true|Ys], Acc) -> all_(Vp,X,Ys,Acc);
all_(Vp,X,[Y|Ys],Acc) -> all_(Vp,X,Ys,[Y|Acc]);
all_(Vp,X,[],Acc) ->
    case Acc of
	[] -> clause(Vp,[X]);
	Ys1 -> none_assoc(Vp,'and',X,Ys1)
    end.

none(Vp,Ys) -> none(Vp,var(Vp),Ys).

none(Vp,undefined,Ys) -> none(Vp,var(Vp),Ys);
none(Vp,X,Ys) -> all(Vp,X,[inv(Y) || Y <- Ys]).

odd(Vp,Ys) -> parity(Vp,Ys).
odd(Vp,X,Ys) -> parity(Vp,X,Ys).

even(Vp,Ys) -> parity(Vp,[?T|Ys]).
even(Vp,X,Ys) -> parity(Vp,X,[?T|Ys]).

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

%% right balanced  A B C D = A op (B op (C op D)) = 
%% ((D op C) op B) op A = left balanced (reverse Xs)
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
eqk(Vp,K,undefined,Ys) ->
    eqk(Vp,K,var(Vp),Ys);
eqk(Vp,1,X,Ys) ->
    one(Vp,X,Ys);
eqk(Vp,K,X,Ys) ->
    eqk_(Vp,K,length(Ys),X,Ys).

eqk_(Vp,0,_N,X,Ys) ->
    none(Vp,X,Ys);
eqk_(_Vp,K,N,_X,_Ys) when K > N -> %% no models
    false;
eqk_(Vp,K,N,X,Ys) when K =:= N ->
    all(Vp,X,Ys);
eqk_(Vp,K,N,X,Ys) ->
    Ys1 = sort(Vp,K,Ys),
    {A,B} = lists:split(N-K, Ys1),
    A1 = any(Vp,A),
    B1 = all(Vp,B),
    and_gate(Vp, X, inv(A1), B1).

%% sort all ys one lap then 'or' over result
one(_Vp, []) -> false;
one(_Vp, [Y]) -> Y;
one(Vp, Ys) -> one(Vp, var(Vp), Ys).

one(Vp, undefined, Ys) -> one(Vp, var(Vp), Ys);
one(Vp, X, [Y0,Y1|Ys]) ->
    {Z0,Z1} = comparator(Vp, Y0, Y1),
    eq1_(Vp, X, Ys, Z1, [Z0]).

eq1_(Vp, X, [Y|Ys], Zi, Zs) ->
    {Z0,Z1} = comparator(Vp, Zi, Y),
    eq1_(Vp, X, Ys, Z1, [Z0|Zs]);
eq1_(Vp, X, [], Zi, Zs) ->
    and_gate(Vp, X, Zi, none(Vp,Zs)).


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


%% make a monitor for array Ys
%% true when all variables in Ys are bound
%% 
%%  -X1 or  Y1
%%  -X1 or -Y1
%%  -X2 or  Y2
%%  -X2 or -Y2
%%  ...
%%  -Xn or  Yn
%%  -Xn or -Yn
%%  Z X1 X2 ... Xn
%% 
%%

mon(Vp, Ys) ->
    Xs = vars(Vp, length(Ys)),
    X = var(Vp),
    mon_clauses(Vp, Ys, Xs),
    clause(Vp, [X | Xs]),
    X.

mon_clauses(Vp, [Y|Ys], [X|Xs]) ->
    clause(Vp, [inv(X), Y]),
    clause(Vp, [inv(X), inv(Y)]),
    mon_clauses(Vp, Ys, Xs);
mon_clauses(_Vp, [], []) ->
    ok.

%% TEST
test() ->
    %% boolean gates
    true = test_and(),
    true = test_or(),
    true = test_imp(),
    true = test_equ(),
    true = test_xor(),
    true = test_nor(),
    true = test_nimp(),
    true = test_nand(),
    true = test_xnor(),
    %% boolean comparison
    true = test_lt(),
    true = test_lte(),
    true = test_gt(),
    true = test_gte(),
    true = test_eq(),
    true = test_neq(),
    %% multi input gates
    true = test_any(),
    true = test_all(),
    true = test_none(),
    true = test_one(),
    true = test_one_2(),
    true = test_eqk(0),
    true = test_eqk(1),
    true = test_eqk(2),
    true = test_eqk(3),
    true = test_eqk(4),

    true = test_half_adder(),
    true = test_full_adder(),

    %% true = test_ltk(0),
    true = test_ltk(1),
    true = test_ltk(2),
    true = test_ltk(3),
    true = test_ltk(4),

    true = test_ltek(0),
    true = test_ltek(1),
    true = test_ltek(2),
    true = test_ltek(3),
    %% true = test_ltek(4),

    true = test_gtk(0),
    true = test_gtk(1),
    true = test_gtk(2),
    true = test_gtk(3),
    %% true = test_gtk(4),

    %% true = test_gtek(0),
    true = test_gtek(1),
    true = test_gtek(2),
    true = test_gtek(3),
    true = test_gtek(4),

    ok.

clause(Vp, Ls) ->
    clause(Vp, Ls, ?DELTA).

clause(Vp, Ls, Set) ->
    %%io:format("clause [~s]\n", [string:join([literal(Vp,L)||L<-Ls], ",")]),
    case varp_nif:add_clause(Vp, Ls, Set) of
	{false,_I} ->
	    throw(contradiction);
	false ->
	    throw(contradiction);
	{true,I} -> %% non conflict
	    I;
	true ->
	    true
    end.

test_gate_2(Gate, Match) ->
    io:format("GATE: ~s\n", [Gate]),
    Vp = varp_nif:new(#{xref => true}),
    A = var(Vp, <<"a">>),
    B = var(Vp, <<"b">>),
    X = gate(Vp,Gate,A,B),
    _ = sym(Vp, X, <<"x">>),
    bt_match(Vp, Match).

test_gate_2x(Gate, Match) ->
    io:format("GATE: ~s\n", [Gate]),
    Vp = varp_nif:new(#{xref => true}),
    A = var(Vp, <<"a">>),
    B = var(Vp, <<"b">>),
    X = var(Vp, <<"x">>),
    _C = gate(Vp,Gate,X,A,B),
    %% varp_nif:bind(Vp, C),
    bt_match(Vp, Match).

test_gate(Gate, Match) ->
    test_gate_2(Gate, Match),
    test_gate_2x(Gate, Match).

test_gate_m(Gate, Vars, Match) ->
    io:format("GATE: ~s\n", [Gate]),
    Vp = varp_nif:new(#{xref => true}),
    Ys = [var(Vp, V) || V <- Vars],
    X = gate(Vp,Gate,Ys),
    _ = sym(Vp, X, <<"x">>),
    bt_match(Vp, Match).

test_gate_mx(Gate, Vars, Match) ->
    false = lists:member(<<"x">>, Vars),
    io:format("GATE: ~s\n", [Gate]),
    Vp = varp_nif:new(#{xref => true}),
    Ys = [var(Vp, V) || V <- Vars],
    X = var(Vp, <<"x">>),
    _ = gate(Vp,Gate,X,Ys),
    bt_match(Vp, Match).

test_gate_n(Gate, Vars, Match) ->
    test_gate_m(Gate, Vars, Match),
    test_gate_mx(Gate, Vars, Match).

test_gate_mk(Gate, K, Vars, Match) ->
    io:format("GATE: ~s\n", [Gate]),
    Vp = varp_nif:new(#{xref => true}),
    Ys = [var(Vp, V) || V <- Vars],
    X = gate(Vp,Gate,K,Ys),
    _ = sym(Vp, X, <<"x">>),
    bt_match(Vp, Match).

test_gate_mkx(Gate, K, Vars, Match) ->
    false = lists:member(<<"x">>, Vars),
    io:format("GATE: ~s\n", [Gate]),
    Vp = varp_nif:new(#{xref => true}),
    Ys = [var(Vp, V) || V <- Vars],
    X = var(Vp, <<"x">>),
    _ = gate(Vp,Gate,K,X,Ys),
    bt_match(Vp, Match).

test_gate_nk(Gate, K, Vars, Match) ->
    test_gate_mk(Gate, K, Vars, Match),
    test_gate_mkx(Gate, K, Vars, Match).

bt_match(Vp, Match0) ->
    Match = lists:sort([lists:sort(M) || M <- Match0]),
    varp_nif:push(Vp),
    case bt_all(Vp, undefined, []) of
	{_Count, Match} ->
	    true;
	{_Count, Models} ->
	    bt_diff(Models, Match),
	    false
    end.

bcp_match(Vp, M0) ->
    M = lists:sort(M0),
    varp_nif:push(Vp),
    case varp_nif:bcp(Vp) of
	true ->
	    case model(Vp, []) of
		[M] -> true;
		_ -> false
	    end;
	false -> false
    end.

bt_diff([M|Ms], Match) ->
    case lists:member(M, Match) of
	true ->
	    bt_diff(Ms, Match -- [M]);
	false ->
	    io:format("model ~w is not matched\n", [M]),
	    bt_diff(Ms, Match)
    end;
bt_diff([], Match) ->
    io:format("matches not generated:\n"),
    lists:foreach(
      fun(M) ->
	      io:format("match ~p\n", [M])
      end, Match).

-define(sym(Name), {<<??Name>>,[]}).

eval2(Fun) ->
    lists:sort([ [{?sym(a),A},{?sym(b),B},{?sym(x),Fun(A,B)}] || 
		   A <- [false,true],
		   B <- [false,true]]).

eval3(Fun) ->
    lists:sort([ [{?sym(a),A},{?sym(b),B},{?sym(c),C},{?sym(x),Fun(A,B,C)}] || 
		   A <- [false,true], 
		   B <- [false,true],
		   C <- [false,true]]).

eval4(Fun) ->
    lists:sort([ [{?sym(a),A},{?sym(b),B},{?sym(c),C},{?sym(d),D},
		  {?sym(x),Fun(A,B,C,D)}] || 
		   A <- [false,true], 
		   B <- [false,true],
		   C <- [false,true],
		   D <- [false,true]
	       ]).

eval_half_adder() ->
    lists:sort([ [{?sym(s), A xor B},
		  {?sym(co), A and B},
		  {?sym(a),A},{?sym(b),B}] || 
		   A <- [false,true],
		   B <- [false,true]
	       ]).

test_half_adder() ->
    Vp = varp_nif:new(#{xref => true}),
    half_adder(Vp, 
	       var(Vp,<<"s">>), 
	       var(Vp,<<"a">>), 
	       var(Vp,<<"b">>), 
	       var(Vp,<<"co">>)),
    bt_match(Vp, eval_half_adder()).

eval_full_adder() ->
    lists:sort([begin
		    S1 = A xor B,
		    S2 = S1 xor Ci,
		    [{?sym(s), S2}, 
		     {?sym(co), (S1 and Ci) or (A and B)},
		     {?sym(a),A},{?sym(b),B},{?sym(ci),Ci}] 
		end || 
		   A <- [false,true],
		   B <- [false,true],
		   Ci <- [false,true]
	       ]).

test_full_adder() ->
    Vp = varp_nif:new(#{xref => true}),
    full_adder(Vp, var(Vp,<<"s">>),
	       var(Vp,<<"a">>),
	       var(Vp,<<"b">>),
	       var(Vp,<<"ci">>),
	       var(Vp,<<"co">>)),
    bt_match(Vp, eval_full_adder()).

test_or_clause() ->
    test_or_clause_1(),
    test_or_clause_2(),
    test_or_clause_3(),
    test_or_clause_4(),
    test_or_clause_5(),
    ok.

%%operation('or',{bool,?F},{bool,?F}, Bs) -> {{bool,?F},Bs};
test_or_clause_1() ->
    Vp = varp_nif:new(#{}),
    X = var(Vp,<<"x">>),
    or_gate(Vp, X, ?F, ?F),
    false = varp_nif:value(Vp, X),
    ok.

%%operation('or',{bool,?T},{bool,_Z}, Bs) -> {{bool,?T},Bs};
test_or_clause_2() ->
    Vp = varp_nif:new(#{}),
    X = var(Vp,<<"x">>),
    Z = var(Vp,<<"z">>),
    or_gate(Vp, X, ?T, Z),
    true = varp_nif:value(Vp, X),
    undefined = varp_nif:value(Vp, Z),
    ok.

%%operation('or',{bool,_Y},{bool,?T}, Bs) -> {{bool,?T},Bs};
test_or_clause_3() ->
    Vp = varp_nif:new(#{}),
    X = var(Vp,<<"x">>),
    Y = var(Vp,<<"y">>),
    or_gate(Vp, X, Y, ?T),
    true = varp_nif:value(Vp, X),
    undefined = varp_nif:value(Vp, Y),
    ok.

%%operation('or',{bool,?F},{bool,Z}, Bs) -> {{bool,Z},Bs};
test_or_clause_4() ->
    Vp = varp_nif:new(#{}),
    X = var(Vp,<<"x">>),
    Z = var(Vp,<<"z">>),
    or_gate(Vp, X, ?F, Z),
    undefined = varp_nif:value(Vp, X),
    ok.

%%operation('or',{bool,Y},{bool,?F}, Bs) -> {{bool,Y},Bs};
test_or_clause_5() ->
    Vp = varp_nif:new(#{}),
    X = var(Vp,<<"x">>),
    Y = var(Vp,<<"y">>),
    or_gate(Vp, X, Y, ?F),
    undefined = varp_nif:value(Vp, X),
    ok.

test_and() ->
    M = eval2(fun erlang:'and'/2),
    test_gate('and', M).
    
test_or() ->
    M = eval2(fun erlang:'or'/2),
    test_gate('or', M).

test_imp() ->
    M = eval2(fun (X,Y) -> (not X) or Y end),
    test_gate('imp', M).

test_equ() ->
    M = eval2(fun (A,B) -> (A =:= B) end),
    test_gate('equ', M).

test_xor() ->
    M = eval2(fun erlang:'xor'/2),
    test_gate('xor', M).

test_nor() ->
    M = eval2(fun (A,B) -> not (A or B) end),
    test_gate('nor', M).

test_nimp() ->
    M = eval2(fun (X,Y) -> not ((not X) or Y) end),
    test_gate('nimp', M).

test_nand() ->
    M = eval2(fun (A,B) -> not (A and B) end),
    test_gate('nand', M).

test_xnor() ->
    M = eval2(fun (A,B) -> not (A xor B) end),
    test_gate('xnor', M).

test_lt() ->
    M = eval2(fun (A,B) -> (A < B) end),
    test_gate('lt', M).

test_lte() ->
    M = eval2(fun (A,B) -> (A =< B) end),
    test_gate('lte', M).

test_gt() ->
    M = eval2(fun (A,B) -> (A > B) end),
    test_gate('gt', M).

test_gte() ->
    M = eval2(fun (A,B) -> (A >= B) end),
    test_gate('gte', M).

test_eq() ->
    M = eval2(fun (A,B) -> (A =:= B) end),
    test_gate('eq', M).

test_neq() ->
    M = eval2(fun (A,B) -> (A =/= B) end),
    test_gate('neq', M).

test_any() ->
    M = eval4(fun(A,B,C,D) -> A or B or C or D end),
    test_gate_n('any', [<<"a">>,<<"b">>,<<"c">>,<<"d">>], M).

test_all() ->
    M = eval4(fun(A,B,C,D) -> A and B and C and D end),
    test_gate_n('all', [<<"a">>,<<"b">>,<<"c">>,<<"d">>], M).

test_none() ->
    M = eval4(fun(A,B,C,D) -> not (A or B or C or D) end),
    test_gate_n('none', [<<"a">>,<<"b">>,<<"c">>,<<"d">>], M).

test_one() ->
    M = eval4(fun(A,B,C,D) -> count([A,B,C,D]) =:= 1 end),
    test_gate_n('one', [<<"a">>,<<"b">>,<<"c">>,<<"d">>], M).

test_one_2() ->
    M = eval3(fun(A,B,C) -> count([A,B,C,false]) =:= 1 end),
    test_gate_n('one', [<<"a">>,<<"b">>,<<"c">>], M).

test_eqk(K) ->
    M = eval4(fun(A,B,C,D) -> count([A,B,C,D]) =:= K end),
    test_gate_nk('EQ', K, [<<"a">>,<<"b">>,<<"c">>,<<"d">>], M).

test_ltk(K) ->
    M = eval4(fun(A,B,C,D) -> count([A,B,C,D]) < K end),
    test_gate_nk('LT', K, [<<"a">>,<<"b">>,<<"c">>,<<"d">>], M).

test_ltek(K) ->
    M = eval4(fun(A,B,C,D) -> count([A,B,C,D]) =< K end),
    test_gate_nk('LTE', K, [<<"a">>,<<"b">>,<<"c">>,<<"d">>], M).

test_gtk(K) ->
    M = eval4(fun(A,B,C,D) -> count([A,B,C,D]) > K end),
    test_gate_nk('GT', K, [<<"a">>,<<"b">>,<<"c">>,<<"d">>], M).

test_gtek(K) ->
    M = eval4(fun(A,B,C,D) -> count([A,B,C,D]) >= K end),
    test_gate_nk('GTE', K, [<<"a">>,<<"b">>,<<"c">>,<<"d">>], M).


%% count number of 'true' in a list of booleans
count([true|As]) -> 1+count(As);
count([false|As]) -> count(As);
count([]) -> 0.
     
test_mon(N) ->
    Vp = varp_nif:new(#{xref => true}),
    Ys = vars(Vp, N),
    Ys1 = lists:sort([{rand:uniform(),
		       case rand:uniform(2) =:= 1 of
			   true -> -Y;
			   false -> Y
		       end} || Y <- Ys]),
    Ys2 = [Y || {_,Y} <- Ys1],
    X  = mon(Vp, Ys2),
    io:format("Ys=~w, X=~w\n", [Ys2, X]),
    varp_nif_test:print_clauses(Vp),
    test_mon_loop(Vp, Ys2, X).

test_mon_loop(Vp, [Y], X) ->
    varp_nif:bind(Vp, Y),
    true = varp_nif:bcp(Vp),
    V = varp_nif:value(Vp,X),
    io:format("mon: ~w/1, X=~w\n", [Y,V]),
    case varp_nif:value(Vp, X) of
	true -> ok;
	_ -> error
    end;
test_mon_loop(Vp, [Y|Ys], X) ->
    varp_nif:bind(Vp, Y),
    true = varp_nif:bcp(Vp),
    V = varp_nif:value(Vp, X),
    io:format("mon: ~w/1, X=~w\n", [Y,V]),
    case V of
	true -> false;
	false -> false;
	undefined  ->
	    test_mon_loop(Vp, Ys, X)
    end.

bt(Vp) ->
    case not varp_nif:nbcp(Vp) of
	true ->
	    case varp_nif:undo(Vp) of
		false -> false;  %% contradiction
		true -> bt(Vp)
	    end;
	false ->
	    true  %% model
    end.

bt_all(Vp, Limit, Acc) ->
    T0 = erlang:monotonic_time(),
    {Count,Acc1} = 
	case varp_nif:next_unbound(Vp) of
	    false ->
		{0,Acc};
	    _ ->
		case bt(Vp) of
		    true ->
			bt_all_(Vp, 1, Limit, model(Vp, Acc));
		    false ->
			{0,Acc}
		end
	end,
    T1 = erlang:monotonic_time(),
    Time = erlang:convert_time_unit(T1-T0,native,microsecond),
    io:format("~w models found in ~w us\n", [Count, Time]),
    if is_list(Acc1) ->
	    {Count,lists:sort(Acc1)};
       true ->
	    {Count, Acc1}
    end.

bt_all_(Vp, Count, Limit, Acc) ->
    case varp_nif:undo(Vp) andalso not bt_done(Count, Limit) of
	true ->
	    case bt(Vp) of
		true ->
		    Acc1 = model(Vp, Acc),
		    bt_all_(Vp, Count+1, Limit, Acc1);
		false ->
		    {Count,Acc}
	    end;
	false ->
	    {Count,Acc}
    end.

bt_done(_Count, undefined) -> false;
bt_done(Count, Limit) -> Count >= Limit.

model(Vp, Acc) ->
    M = model_(Vp, varp_nif:first_symbol(Vp), []),
    if Acc =:= print -> 
	    io:format("~w\n", [M]),
	    print;
       Acc =:= undefined ->
	    M;
       is_list(Acc) ->
	    [M|Acc]
    end.

model_(_Vp, false, Model) ->
    lists:sort(Model);
model_(Vp, Vt=[Type|Var], Model) when is_atom(Type) ->
    case symbol_value(Vp,Type,Vt) of
	undefined ->
	    error({not_defined, Var});
	Value ->
	    model_(Vp, varp_nif:next_symbol(Vp,Vt), [{Var,Value}|Model])
    end;
model_(Vp, Var, Model) ->
    case symbol_value(Vp,Var) of
	undefined ->
	    error({not_defined, Var});
	Value ->
	    model_(Vp, varp_nif:next_symbol(Vp,Var), [{Var,Value}|Model])
    end.

symbol_value(Vp,Symbol) ->
    symbol_value(Vp,uint,Symbol).

symbol_value(Vp,_Type,Symbol) ->
    Si = varp_nif:find_symbol(Vp, Symbol),
    case Si of
	false -> undefined;
	{Type,Xs} when is_list(Xs) ->
	    %% io:format("symbol_value: ~p,~p, xs=~p\n", [Type,Symbol,Xs]),
	    if Type =:= int -> signed_value(Vp, Xs);
	       true -> unsigned_value(Vp, Xs)
	    end;
	{bool,X} when is_integer(X) -> varp_nif:value(Vp, X)
    end.

unsigned_value(Vp, Xs) ->
    unsigned_value_(Vp, Xs, 0, 0).

unsigned_value_(Vp, [X|Xs], I, Value) ->
    case varp_nif:value(Vp, X) of
	undefined -> undefined; %% format as partial?
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
    case varp_nif:find_symbol(Vp, Symbol) of
	false -> false;
	Xs when is_list(Xs) -> 
	    bind_value(Vp, Xs, Value);
	X when is_integer(X) ->
	    case Value of
		true -> varp_nif:bind(Vp, X);
		false -> varp_nif:bind(Vp, -X);
		1 -> varp_nif:bind(Vp, X);
		0 -> varp_nif:bind(Vp, -X)
	    end
    end.
	
bind_value(Vp, Xs, Value) when is_integer(Value) ->    
    bind_integer(Vp, Xs, Value);
bind_value(Vp, Xs, Value) when is_bitstring(Value) ->
    bind_bits(Vp, Xs, Value).

%% bind bits in integer
bind_integer(Vp, [X|Xs], Value) ->
    case Value band 1 of
	1 -> varp_nif:bind(Vp, X);
	0 -> varp_nif:bind(Vp, -X)
    end,
    bind_integer(Vp, Xs, Value bsr 1);
bind_integer(_Vp, [], _Value) ->
    ok.

%% bind bits (fixme what is the "natural" order?)
bind_bits(Vp, [X|Xs], <<Value:1,Rest/bits>>) ->
    case Value of
	1 -> varp_nif:bind(Vp, X);
	0 -> varp_nif:bind(Vp, -X)
    end,
    bind_bits(Vp, Xs, Rest);
bind_bits(Vp, [X|Xs], <<>>) ->
    varp_nif:bind(Vp, -X),
    bind_bits(Vp, Xs, <<>>);
bind_bits(_Vp, [], _) ->
    ok.

symbol(_Vp,true) -> "t";
symbol(_Vp,false) -> "f";
symbol(Vp, X) when is_integer(X) ->
    case varp_nif:variable_info(Vp, X, 'symbol') of
	[] ->
	    "X("++integer_to_list(X)++")";
	[{Name,0}|_] when is_binary(Name) ->
	    case varp_nif:find_symbol(Vp,Name) of
		false -> "X("++integer_to_list(X)++")";
		Y when is_integer(Y), abs(Y) =:= X -> binary_to_list(Name);
		Ys when is_list(Ys) -> binary_to_list(Name)++"[0]"
	    end;
	[{Term,0}|_] when is_tuple(Term) ->
	    case varp_nif:find_symbol(Vp,Term) of
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
