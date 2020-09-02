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

-export([sort_gate/3, sort_gate/5]).
-export([left_assoc/3, left_assoc/4]).
-export([right_assoc/3, right_assoc/4]).
-export([none_assoc/3, none_assoc/4]).
-export([any_gate/2, any_gate/3]).
-export([all_gate/2, all_gate/3]).
-export([eq1/2, eq1/3]).

-compile(export_all).

inv(true) -> false;
inv(false) -> true;
inv(X) -> -X.

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
    inv_gate(Vp, varc:add_variable(Vp), Y).

inv_gate(Vp, X, Y) ->
    inv_clauses(Vp, X, Y).

inv_pin(_Vp, Y) ->
    inv(Y).

%% x = y OR z
or_gate(Vp, Y, Z) ->
    or_gate(Vp, varc:add_variable(Vp), Y, Z).

or_gate(Vp, X, Y, Z) ->
    or_clauses(Vp, X, Y, Z).

%% x = NOT (y OR z)
nor_gate(Vp, Y, Z) ->
    nor_gate(Vp, varc:add_variable(Vp), Y, Z).

nor_gate(Vp, X, Y, Z) ->
    inv(or_clauses(Vp, X, Y, Z)).

%% x = y -> z (NOT y OR z)
imp_gate(Vp, Y, Z) ->
    imp_gate(Vp, varc:add_variable(Vp), Y, Z).

imp_gate(Vp, X, Y, Z) ->
    or_clauses(Vp, X, inv(Y), Z).

%% = y -/> z ( NOT (y -> z) ) = NOT (NOT y OR Z) =  (y AND NOT z)
nimp_gate(Vp, Y, Z) ->
    nimp_gate(Vp, varc:add_variable(Vp), Y, Z).

nimp_gate(Vp, X, Y, Z) ->
    and_clauses(Vp, X, Y, inv(Z)).

%% x = y AND z
and_gate(Vp, Y, Z) ->
    and_gate(Vp, varc:add_variable(Vp), Y, Z).

and_gate(Vp, X, Y, Z) ->
    and_clauses(Vp, X, Y, Z).

%% x = NOT (y AND z)
nand_gate(Vp, Y, Z) ->
    nand_gate(Vp, varc:add_variable(Vp), Y, Z).
nand_gate(Vp, X, Y, Z) ->
    inv(and_clauses(Vp, X, Y, Z)).

%% x = y XOR z
xor_gate(Vp, Y, Z) ->
    xor_gate(Vp, varc:add_variable(Vp), Y, Z).

xor_gate(Vp, X, Y, Z) ->
    xor_clauses(Vp, X, Y, Z).

%% x = NOT (y XOR z)
xnor_gate(Vp, Y, Z) ->
    xnor_gate(Vp, varc:add_variable(Vp), Y, Z).

xnor_gate(Vp, X, Y, Z) ->
    inv(xor_clauses(Vp, X, Y, Z)).

%% x = MIN(y,z) = (y AND z)
min_gate(Vp, Y, Z) ->
    min_gate(Vp, varc:add_variable(Vp), Y, Z).

min_gate(Vp, X, Y, Z) ->
    and_clauses(Vp, X, Y, Z).

%% x = MAX(y,z) = (y OR z)
max_gate(Vp, Y, Z) ->
    max_gate(Vp, varc:add_variable(Vp), Y, Z).

max_gate(Vp, X, Y, Z) ->
    or_clauses(Vp, X, Y, Z).

half_adder(Vp, Y, Z) ->
    half_adder(Vp, varc:add_variable(Vp), Y, Z).

half_adder(Vp, X, Y, Z) ->
    half_adder(Vp, X, Y, Z, varc:add_variable(Vp)).

half_adder(Vp, X, Y, Z, Co) ->
    S1 = xor_gate(Vp, X, Y, Z),
    Co1 = and_gate(Vp, Co, Y, Z),
    {S1, Co1}.

full_adder(Vp, Y, Z) ->
    full_adder(Vp, varc:add_variable(Vp), Y, Z).

full_adder(Vp, X, Y, Z) ->
    full_adder(Vp, X, Y, Z, false).

full_adder(Vp, X, Y, Z, Ci) ->
    full_adder(Vp, X, Y, Z, Ci, varc:add_variable(Vp)).

full_adder(Vp, X, Y, Z, Ci, Co) ->
    S1 = xor_gate(Vp,Y,Z),
    S2 = xor_gate(Vp,X,S1,Ci),
    A1 = and_gate(Vp,S1,Ci),
    A2 = and_gate(Vp,Y,Z),
    Co1 = or_gate(Vp,A1,A2,Co),
    {S2, Co1}.

%% (min,max) = SORT(y, z)
sort_gate(Vp, Y, Z) ->
    sort_gate(Vp, Y, Z, varc:add_variable(Vp), varc:add_variable(Vp)).

sort_gate(Vp, Y, Z, X0, X1) ->
    {min_gate(Vp, X0, Y, Z), max_gate(Vp, X1, Y, Z)}.

any_gate(Vp,Xs) -> none_assoc(Vp,fun or_gate/4,Xs).
any_gate(Vp,X,Xs) -> none_assoc(Vp,fun or_gate/4,X,Xs).

all_gate(Vp,Xs) -> left_assoc(Vp,fun and_gate/4,Xs).
all_gate(Vp,X,Xs) -> left_assoc(Vp,fun and_gate/4,X,Xs).
    
%% left balanced circuit 
left_assoc(Vp,Gate,Xs) ->
    left_assoc(Vp,Gate,varc:add_variable(Vp),Xs).

left_assoc(Vp,Gate,X,[X1,X2]) ->
    Gate(Vp,X,X1,X2);
left_assoc(Vp,Gate,X,[X1,X2|Xs]) ->
    Y1 = varc:add_variable(Vp),
    Gate(Vp,Y1,X1,X2),
    left_assoc_(Vp,Gate,X,Xs,Y1).

left_assoc_(Vp,Gate,X,[Xn],Yi) ->
    Gate(Vp,X,Yi,Xn);
left_assoc_(Vp,Gate,X,[Xi|Xs],Yi) ->
    Yj = varc:add_variable(Vp),
    Gate(Vp,Yj,Yi,Xi),
    left_assoc_(Vp,Gate,X,Xs,Yj).

%% right balanced 
right_assoc(Vp,Gate,Xs) ->
    right_assoc(Vp,Gate,varc:add_variable(Vp),Xs).
    
right_assoc(Vp,Gate,X,Xs) ->
    left_assoc(Vp,Gate,X,lists:reverse(Xs)).


none_assoc(Vp,Gate,Xs) ->
    none_assoc(Vp,Gate,varc:add_variable(Vp),Xs).

none_assoc(Vp,Gate,X,Xs) when is_function(Gate,4), is_list(Xs) ->
    case Gate =:= fun or_gate/4 of
	true ->
	    varc:add_clause(Vp, [inv(X)|Xs]),
	    lists:foreach(
	      fun(Xi) ->
		      varc:add_clause(Vp,[X,inv(Xi)])
	      end, Xs),
	    X;
	false ->
	    none_assoc_(Vp,Gate,X,Xs)
    end.

none_assoc_(Vp,Gate,X,Xs) ->
    case lists:split(length(Xs) div 2,Xs) of
	{[U],[V]} ->
	    Gate(Vp,X,U,V);
	{[U],[V1,V2]} ->
	    X1 = varc:add_variable(Vp),
	    Gate(Vp,X1,V1,V2),
	    Gate(Vp,X,U,X1);
	{Us,Vs} ->
	    X1 = varc:add_variable(Vp),
	    _R = none_assoc_(Vp,Gate,X1,Us),
	    X2 = varc:add_variable(Vp),
	    _L = none_assoc_(Vp,Gate,X2,Vs),
	    Gate(Vp,X,X1,X2)
    end.


%% sort all ys one lap then or over the
%% fixme len(ys) < 2
eq1(Vp, Ys) ->
    eq1(Vp, varc:add_variable(Vp), Ys).

eq1(Vp, X, [Y0,Y1|Ys]) ->
    {Z0,Z1} = sort_gate(Vp, Y0, Y1),
    eq1_(Vp, X, Ys, Z1, [Z0]).

eq1_(Vp, X, [Y|Ys], Zi, Zs) ->
    {Z0,Z1} = sort_gate(Vp, Zi, Y),
    eq1_(Vp, X, Ys, Z1, [Z0|Zs]);
eq1_(Vp, X, [], Zi, Zs) ->
    and_gate(Vp, X, Zi, inv(any_gate(Vp,Zs))).

%% TEST

var(Vp, Name) ->
    X = varc:add_variable(Vp, true),
    varc:add_symbol(Vp, X, Name),
    X.

clause(Vp, Ls) ->
    io:format("clause [~s]\n", [string:join([literal(Vp,L)||L<-Ls], ",")]),
    varc:add_clause(Vp, Ls).

test_gate(Gate) when is_function(Gate, 4) ->
    Vp = varc:new(#{xref => true}),
    A = var(Vp, "A"),
    B = var(Vp, "B"),
    X = var(Vp, "X"),
    C = Gate(Vp, X, A, B),
    varc:bind(Vp, C),
    varc:set_level(Vp, 1),
    bt_all(Vp).

test_or() ->
    test_gate(fun or_gate/4).

test_nor() ->
    test_gate(fun nor_gate/4).

test_and() ->
    test_gate(fun and_gate/4).

test_nand() ->
    test_gate(fun nand_gate/4).

test_xor() ->
    test_gate(fun xor_gate/4).

test_xnor() ->
    test_gate(fun xnor_gate/4).

test_eq1_1() ->
    Vp = varc:new(#{xref => true}),
    A = var(Vp, "A"),
    B = var(Vp, "B"),
    C = var(Vp, "C"),
    D = var(Vp, "D"),
    E = eq1(Vp, [A,B,C,D]),
    varc:bind(Vp, E),
    varc:set_level(Vp, 1),
    bt_all(Vp).

test_eq1_2() ->
    Vp = varc:new(#{xref => true}),
    A = var(Vp, "A"),
    B = var(Vp, "B"),
    C = var(Vp, "C"),
    D = false,
    E = eq1(Vp, [A,B,C,D]),
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
	case bt(Vp) of
	    true ->
		io:format("~p\n", [model(Vp)]),
		bt_all_(Vp, 1, Limit);
	    false ->
		0
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

model(Vp) ->
    N = varc:info(Vp, 'number_of_variables'),
    [symbol(Vp, X) ||
	X <- lists:seq(1, N),
	varc:value(Vp, X), varc:variable_info(Vp, X, 'is_atom')].

symbol(_Vp,true) -> "t";
symbol(_Vp,false) -> "f";
symbol(Vp, X) when is_integer(X) ->
    case varc:variable_info(Vp, X, 'symbol') of
	[] ->
	    "X("++integer_to_list(X)++")";
	[{Name,_Pos}|_] ->
	    binary_to_list(Name)
    end.

literal(_Vp,true) -> "t";
literal(_Vp,false) -> "f";
literal(Vp,X) when is_integer(X), X > 0 ->
    symbol(Vp,X);
literal(Vp,X) when is_integer(X), X < 0 ->
    "!"++symbol(Vp,-X).
