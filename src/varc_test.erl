%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2019, Tony Rogvall
%%% @doc
%%%    Test of varc
%%% @end
%%% Created : 14 Mar 2019 by Tony Rogvall <tony@rogvall.se>

-module(varc_test).

-compile(export_all).

-export([all/0]).
-export([bench/0, bench/1]).

-include("varp.hrl").

all() ->
    lists:foreach(
      fun(Test) ->
	      io:format("< ~w: ", [Test]),
	      Result = sync_apply(?MODULE, Test, []),
	      io:format("> ~s\n", [Result])
      end, [test1,
	    test2,
	    test3,
	    clause_simplify,
	    bcp2,
	    bcp3,
	    bcp4,
	    bcp_turbo1,
	    clause_bcp,
	    clause_learn_d1,
	    clause_learn_a1,
	    watch1,

	    %% mark intersect
	    intersect1,
	    intersect2,
	    intersect_var0,
	    intersect_var1,

	    %% order checks
	    order_identity,
	    order_user,
	    order_degree,
	    order_rank,
	    order_first, %% BUGGY
	    order_last,  %% BUGGY
	    order_first_and_last,
	    order_random,

	    edge_list0,
	    edge_list1,
	    edge_list2,
	    edge_list3,
	    subst0a,
	    subst0b,
	    subst0c,
	    subst0d, 
	    subst1,
	    subst2,
	    subst3,
	    subst4,
	    subst5,
	    subst6,
	    cnf_install,
	    cnf_delete_sort,
	    cnf_sort_offset_delete
	   ]).

sync_apply(Mod, Fun, Args) ->
    PARENT = self(),
    Pid = spawn(fun() ->
			try apply(Mod, Fun, Args) of
			    _Res -> PARENT ! {self(),ok}
			catch 
			    error:_ ->
				PARENT ! {self(),error}
			end
		end),
    receive
	{Pid, Result} ->
	    Result
    end.

bindings1() ->
    V = varc:new(),
    X1 = var(V),
    X2 = var(V),
    X3 = var(V),
    X4 = var(V),
    X5 = var(V),
    X6 = var(V),

    clause(V, [-X1, X3]),
    clause(V, [-X1,-X2]),
    varc:set_level(V, 1),
    varc:bind(V, X1),
    true = varc:bcp(V),

    clause(V, [X4, -X6]),
    clause(V, [X4, X5]),
    varc:set_level(V, 2),
    varc:bind(V, -X4),
    true = varc:bcp(V),

    %% FIXME tests are deependent on clause order!!
    Match1a = [X1,-X2,X3],
    Match1a = varc:get_bindings_list(V, 1),
    Match1b = [X3,-X2,X1],
    Match1b = varc:get_bindings_list(V, 1, false, true),

    Match2a = [-X4,X5,-X6],
    Match2a = varc:get_bindings_list(V, 2),
    Match2b = [-X6,X5,-X4],
    Match2b = varc:get_bindings_list(V, 2, false, true),
    ok.

test1() ->
    V = varc:new(),
    X1 = var(V),
    X2 = var(V),
    X3 = var(V),
    Ls0 = lists:usort([X1, X2, X3]),
    C0 = clause(V, Ls0),
    io:format("C0=~w\n", [C0]),
    Ls0 = get_clause(V, C0),
    io:format("Ls0=~w\n", [Ls0]),
    
    Ls1 = lists:usort([X1,-X2,X3]),
    C1 = clause(V, Ls1),
    io:format("C0=~w\n", [C1]),
    Ls1 = get_clause(V, C1),
    io:format("Ls0=~w\n", [Ls1]),
    ok.

test1_gamma() ->
    V = varc:new(),
    X1 = var(V),
    X2 = var(V),
    X3 = var(V),
    Ls0 = lists:usort([X1, X2, X3]),
    C0 = clause(V, Ls0, gamma),
    io:format("C0=~w\n", [C0]),
    Ls0 = get_clause(V, C0),
    io:format("Ls0=~w\n", [Ls0]),
    
    Ls1 = lists:usort([X1,-X2,X3]),
    C1 = clause(V, Ls1),
    io:format("C0=~w\n", [C1]),
    Ls1 = get_clause(V, C1),
    io:format("Ls0=~w\n", [Ls1]),
    ok.
    
test2() ->
    V = varc:new(),
    X1 = var(V),
    X2 = var(V),
    X3 = var(V),
    X4 = var(V),
    
    C0 = clause(V, [X1, X2, X3]),
    C1 = clause(V, [X2, X3, X4]),

    [X1, X2, X3] = get_clause(V, C0),
    [X2, X3, X4] = get_clause(V, C1),
    ok.

%%
%% Test clause / queue 
%%    
test3() ->
    V = varc:new(#{xref=>true}),
    X1 = var(V),
    X2 = var(V),
    X3 = var(V),
    X4 = var(V),
    X5 = var(V),
    X6 = var(V),
    X7 = var(V),

    C0 = clause(V, [X1, X2, X3]),
    C1 = clause(V, [X2, X3, X4]),
    C2 = clause(V, [X3, X4, X5, X6]),
    C3 = clause(V, [X5, X6, X7]),

    [X1,X2,X3] = get_clause(V, C0),
    [X2,X3,X4] = get_clause(V, C1),
    [X3,X4,X5,X6] = get_clause(V, C2),
    [X5,X6,X7] = get_clause(V, C3),

    true = lists:sort([C0]) =:= lists:sort(varc:get_clauses(V, X1)),

    true = lists:sort([C0,C1]) =:= lists:sort(varc:get_clauses(V, X2)),
    true = lists:sort([C0,C1,C2]) =:= lists:sort(varc:get_clauses(V, X3)),
    true = lists:sort([C1,C2]) =:= lists:sort(varc:get_clauses(V, X4)),
    true = lists:sort([C2,C3]) =:= lists:sort(varc:get_clauses(V, X5)),
    true = lists:sort([C2,C3]) =:= lists:sort(varc:get_clauses(V, X6)),
    true = lists:sort([C3]) =:= lists:sort(varc:get_clauses(V, X7)),

    io:format("X5 clauses = ~p\n", [varc:get_clauses(V, X5)]),
    io:format("X6 clauses = ~p\n", [varc:get_clauses(V, X6)]),
    io:format("X7 clauses = ~p\n", [varc:get_clauses(V, X7)]),

    true = varc:bcp(V),
    true = varc:set_level(V, 1),
    true = varc:bind(V, X2),
    true = varc:bind(V, X3),
    {varc:get_bindings_list(V, 1), varc:get_number_of_clauses(V)}.

%% Test all clause simplifications
clause_simplify() ->
    V = varc:new(),
    X1 = var(V),
    X2 = var(V),
    X3 = var(V),
    X4 = var(V),
    X5 = var(V),
    C0 = clause(V, [X2,X3,X4,X5]),
    C1 = clause(V, [X5,X4,X3,X2]),
    C20 = clause(V, [X1,X1,X1,X1,X1]),
    C23 = clause(V, [X2,X3,X3,X3,X2]),
    L3 = [X2,X3,X2,X3,X4,?F],
    io:format("L3 = ~w\n", [L3]),
    C3 = clause(V, L3),
    C4 = clause(V, [X2,X3,X2,X3,X4]),
    C5 = clause(V, [X2,?T,X3,?F,X4,?T,X4,?T, X5,?F]),
    C6 = clause(V, [X2,?T,X3,?F,-X3,?T,X3,?T,-X3,?F,X4]),

    io:format("C3=~w, C4=~w\n", [C3,C4]),

    [X2,X3,X4,X5] = get_clause(V, C0),
    [X2,X3,X4,X5] = get_clause(V, C1),
    C20 = true,
    %% [X2] = get_clause(V, C2),
    [X2,X3] = get_clause(V, C23),
    [X2,X3,X4] = get_clause(V, C3),
    [X2,X3,X4] = get_clause(V, C4),
    C5 = true,
    C6 = true,
    ok.

bcp2() ->
    V = varc:new(),
    X = var(V, <<"X">>),
    Y = var(V, <<"Y">>),
    clause(V, [X, Y]),

    [Y] = eval_bindings(V, [-X]),
    [X] = eval_bindings(V, [-Y]),
    [] = eval_bindings(V, [X]),
    [] = eval_bindings(V, [Y]),
    ok.

bcp3() ->
    V = varc:new(),
    X = var(V, <<"X">>),
    Y = var(V, <<"Y">>),
    Z = var(V, <<"Z">>),
    _Cix = clause(V, [X, Y, Z]),

    [Z] = eval_bindings(V, [-X,-Y]),
    [X] = eval_bindings(V, [-Y,-Z]),
    [Y] = eval_bindings(V, [-Z,-X]),
    ok.

bcp4() ->
    V = varc:new(),
    X = var(V, <<"X">>),
    Y = var(V, <<"Y">>),
    Z = var(V, <<"Z">>),
    T = var(V, <<"T">>),
    _Cix = clause(V, [X, Y, Z, T]),

    [T] = eval_bindings(V, [-X,-Y,-Z]),
    [X] = eval_bindings(V, [-Y,-Z,-T]),
    [Y] = eval_bindings(V, [-X,-Z,-T]),
    [Z] = eval_bindings(V, [-X,-Y,-T]),

    ok.

bcp_turbo1() ->
    V = varc:new(#{xref=>true}),
    X = var(V, <<"X">>),
    Y = var(V, <<"Y">>),
    Y1 = var(V, <<"Y1">>),
    Y2 = var(V, <<"Y2">>),
    Y3 = var(V, <<"Y3">>),
    A  = var(V, <<"A">>),
    B  = var(V, <<"B">>),
    Z1 = var(V, <<"Z1">>),
    Z2 = var(V, <<"Z2">>),
    Z3 = var(V, <<"Z3">>),

    clause(V, [-X,A]),
    clause(V, [-X,B]),
    clause(V, [-A,Y1]),
    clause(V, [-B,Y2]),
    clause(V, [-A,-B,Y3]),
    clause(V, [X, Z1, Y1]),
    clause(V, [X, Z2, Y2]),
    clause(V, [X, Z3, Y3]),
    clause(V, [Y, Z1, Y1]),
    clause(V, [Y, Z2, Y2]),
    clause(V, [Y, Z3, Y3]),

    varc:set_level(V, 1),
    varc:bind(V, X),  %% X=1
    turbo = varc:bcp(V, [X]),
    turbo = varc:bcp(V, [Y]),
    {turbo,[Y,X]} = varc:bcp(V, [X,Y], true),
    ok.

bcp_add() ->
    V = varc:new(),
    X = var(V, <<"X">>),
    Y = var(V, <<"Y">>),
    Z = var(V, <<"Z">>),
    varc:set_level(V, 1),
    varc:bind(V, -Y),
    Cix1 = clause(V, [X, Y, Z]),
    varc:undo_level(V, 1),
    varc:set_level(V, 0),
    0 = varc:clause_info(V, Cix1, watch0),
    2 = varc:clause_info(V, Cix1, watch1),
    varc:bind(V, -X),
    true = varc:bcp(V),
    _Cix2 = clause(V, [X, -Z]),
    true = varc:bcp(V),
    Match = [-X,-Z,Y],
    Match = varc:get_bindings_list(V, 0),
    dump(V).


eval_bindings(V, Xs) ->
    varc:set_level(V, 1),
    _ = [(true = varc:bind(V, X)) || X <- Xs ],
    varc:set_level(V, 2),
    true = varc:bcp(V),
    R = varc:get_bindings_list(V, 2),
    varc:undo_level(V, 2),
    varc:undo_level(V, 1),
    R.

%% Test eval
clause_bcp() ->
    V = varc:new(),
    X1 = var(V),
    X2 = var(V),
    X3 = var(V),
    X4 = var(V),

    undefined = varc:value(V, X1),
    undefined = varc:value(V, X2),
    undefined = varc:value(V, X3),
    undefined = varc:value(V, X4),

    varc:set_level(V, 1),
    C0 = clause(V, [X1, ?F, ?F]),
    C1 = clause(V, [X2, ?T, ?T, ?T]),
    C2 = clause(V, [-X3, ?F, ?F, ?F]),
    C3 = clause(V, [X4, ?F, ?T, ?F, ?T]),
    io:format("clauses=~p\n", [[C0,C1,C2,C3]]),
    print_clauses(V),

    true = varc:bcp(V),

    V1 = varc:value(V, X1),
    true = V1 =:= ?T,

    V2 = varc:value(V, X2),
    true = V2 =:= undefined,

    V3 = varc:value(V, X3),
    true = V3 =:= ?F,

    V4 = varc:value(V, X4),
    true = V4 =:= undefined,

    true.

%% 
%% add clause with bindings
%%
or_bcp_bindings() ->
    V = varc:new(),
    X1 = var(V),
    X2 = var(V),
    X3 = var(V),
    X4 = var(V),

    varc:set_level(V, 1),
    clause(V, [-X1, -X2, -X3]),
    clause(V, [-X1, -X2,  X4]),
    clause(V, [-X1,  X2, -X3]),
    clause(V, [-X1,  X2,  X3]),
    io:format("Bindings@0 = ~w\n", [varc:get_bindings(V,0)]),
    io:format("Bindings@1 = ~w\n", [varc:get_bindings(V,1)]),
    io:format("watched = ~w\n", [get_watched(V)]),
    
    print_clauses(V),
    io:format("2/1\n", []),
    varc:bind(V, X1),
    true = varc:bcp(V),
    io:format("Bindings@1 = ~w\n", [varc:get_bindings(V,1)]),
    io:format("watched = ~w\n", [get_watched(V)]),
    print_clauses(V),

    varc:set_level(V, 2),
    clause(V, [-X1,  X2,  X3, -X4]),
    io:format("watched = ~w\n", [get_watched(V)]),
    io:format("3/1\n", []),
    varc:bind(V, X2),
    true = varc:bcp(V),
    io:format("bindings@2 = ~w\n", [varc:get_bindings(V,2)]),
    io:format("bindings@1 = ~w\n", [varc:get_bindings(V,1)]),
    io:format("bindings@0 = ~w\n", [varc:get_bindings(V,0)]),
    io:format("watched = ~w\n", [get_watched(V)]),
    print_clauses(V),

    io:format("undo 2\n", []),
    varc:undo_level(V, 2),
    io:format("bindings@2 = ~w\n", [varc:get_bindings(V,2)]),
    io:format("bindings@1 = ~w\n", [varc:get_bindings(V,1)]),
    io:format("bindings@0 = ~w\n", [varc:get_bindings(V,0)]),
    io:format("watched = ~w\n", [get_watched(V)]),
    print_clauses(V),

    io:format("undo 1\n", []),
    varc:undo_level(V, 1),
    io:format("bindings@2 = ~w\n", [varc:get_bindings(V,2)]),
    io:format("bindings@1 = ~w\n", [varc:get_bindings(V,1)]),
    io:format("bindings@0 = ~w\n", [varc:get_bindings(V,0)]),
    io:format("watched = ~w\n", [get_watched(V)]),
    print_clauses(V),
    ok.

%% pigeon=3
p3() ->
    V = varc:new(),
    X1 = var(V, <<"P(1,1)">>),
    X2 = var(V, <<"P(1,2)">>),
    X3 = var(V, <<"P(2,1)">>),
    X4 = var(V, <<"P(2,2)">>),
    X5 = var(V, <<"P(3,1)">>),
    X6 = var(V, <<"P(3,2)">>),
    clause(V, [X1,X2]),
    clause(V, [X3, X4]),
    clause(V, [X5, X6]),
    clause(V, [-X1, -X3]),
    clause(V, [-X1, -X5]),
    clause(V, [-X3, -X5]),
    clause(V, [-X2, -X4]),
    clause(V, [-X2, -X6]),
    clause(V, [-X4, -X6]),
    V.

%% pigeon=4
p4() ->
    V = varc:new(),
    X1 = var(V, <<"P(1,1)">>),
    X2 = var(V, <<"P(1,2)">>),
    X3 = var(V, <<"P(1,3)">>),
    X4 = var(V, <<"P(2,1)">>),
    X5 = var(V, <<"P(2,2)">>),
    X6 = var(V, <<"P(2,3)">>),
    X7 = var(V, <<"P(3,1)">>),
    X8 = var(V, <<"P(3,2)">>),
    X9 = var(V, <<"P(3,3)">>),
    X10 = var(V, <<"P(4,1)">>),
    X11 = var(V, <<"P(4,2)">>),
    X12 = var(V, <<"P(4,3)">>),

    clause(V, [X1,X2,X3]),
    clause(V, [X4,X5,X6]),
    clause(V, [X7,X8,X9]),
    clause(V, [X10,X11,X12]),
    clause(V, [-X1,-X4]),
    clause(V, [-X1,-X7]),
    clause(V, [-X1,-X10]),
    clause(V, [-X4,-X7]),
    clause(V, [-X4,-X10]),
    clause(V, [-X7,-X10]),
    clause(V, [-X2,-X5]),
    clause(V, [-X2,-X8]),
    clause(V, [-X2,-X11]),
    clause(V, [-X5,-X8]),
    clause(V, [-X5,-X11]),
    clause(V, [-X8,-X11]),
    clause(V, [-X3,-X6]),
    clause(V, [-X3,-X9]),
    clause(V, [-X3,-X12]),
    clause(V, [-X6,-X9]),
    clause(V, [-X6,-X12]),
    clause(V, [-X9,-X12]),
    V.

nbcp_p3() ->
    P3 = p3(),
    varc:set_level(P3, 1),
    false = varc:nbcp(P3),
    Bn1 = varc:get_all_bindings(P3),
    io:format("bindings = ~w\n", [Bn1]),
    varc:undo(P3),
    false = varc:nbcp(P3),
    Bn2 = varc:get_all_bindings(P3),
    io:format("bindings = ~w\n", [Bn2]),
    varc:undo(P3),
    BnX = varc:get_all_bindings(P3),
    io:format("bindings = ~w\n", [BnX]),
    ok.

nbcp_p4() ->
    P4 = p4(),
    ok = symlist_sort_first(P4,
			    [<<"P(1,2)">>,
			     <<"P(2,1)">>,
			     <<"P(2,3)">>,
			     <<"P(3,2)">>,
			     <<"P(4,1)">>,
			     <<"P(4,3)">>,
			     <<"P(1,1)">>,
			     <<"P(1,3)">>,
			     <<"P(2,2)">>,
			     <<"P(3,1)">>,
			     <<"P(3,3)">>,
			     <<"P(4,2)">>]),
    varc:set_level(P4, 1),
    nbcp_loop(P4).

symlist_sort_first(V, SymList) ->
    varc:order_first(V, [varc:find_symbol(V, Sym) || Sym <- SymList]).

nbcp_loop(V) ->
    false = varc:nbcp(V),
    Bs = varc:get_all_bindings(V),
    io:format("bindings = ~w\n", [Bs]),
    case varc:undo(V) of
	false ->
	    io:format("bcp_count = ~w\n", [varc:info(V, bcp_counter)]),
	    contradiction;
	true ->
	    nbcp_loop(V)
    end.
    
order_install() ->
    V = varc:new(#{}),
    X1 = var(V, <<"X1">>),
    X2 = var(V, <<"X2">>),
    X3 = var(V, <<"X3">>),
    X4 = var(V, <<"X4">>),
    X5 = var(V, <<"X5">>),
    X6 = var(V, <<"X6">>),
    Y1 = var(V),
    Y2 = var(V),
    Y3 = var(V),

    _Z0 = clause(V, [Y2, Y3], ?GAMMA),
    _Z1 = clause(V, [Y2, -Y3], ?GAMMA),
    _C0 = clause(V, [X1, X2, X3, X4, X5, X6, Y1], ?GAMMA),
    _C1 = clause(V, [    X2, X3, X4, X5, X6, Y1], ?GAMMA),
    _C2 = clause(V, [        X3, X4, X5, X6, Y1], ?GAMMA),
    _C3 = clause(V, [            X4, X5, X6, Y1], ?GAMMA),
    _C4 = clause(V, [                X5, X6, Y1], ?GAMMA),
    _C5 = clause(V, [                    X6, Y1], ?GAMMA),
    varc:bind(V, Y1),
    varc:bind(V, Y2),
    varc:bind(V, Y3),
    {V, [X1,X2,X3,X4,X5,X6]}.


order_identity() ->    
    {V, [X1,X2,X3,X4,X5,X6]} = order_install(),
    ok = varc:order_sort(V, ?ORDER_IDENTITY),
    [X1, X2, X3, X4, X5, X6] = varc:order_all(V),
    ok.
    
order_user() ->    
    {V, [X1,X2,X3,X4,X5,X6]} = order_install(),
    lists:foreach(
      fun({L,Cp,Cn}) ->
	      varc:set_user_count(V,L,Cp),
	      varc:set_user_count(V,-L,Cn)
      end, [{X1,12,10},{X2,11,13},{X3,16,14},{X4,15,17},{X5,20,18},{X6,19,21}]),
    ok = varc:order_sort(V, ?ORDER_USER bor ?ORDER_ASCEND),
    %% U1 = [X1,-X2,X3,-X4,X5,-X6],
    [X1,X2,X3,X4,X5,X6] = varc:order_all(V),
    [1,-1,1,-1,1,-1] = varc:phase_all(V),

    ok = varc:order_sort(V, ?ORDER_USER bor ?ORDER_DESCEND),
    %% U2 = [-X6,X5,-X4,X3,-X2,X1],
    [X6,X5,X4,X3,X2,X1] = varc:order_all(V),
    [-1,1,-1,1,-1,1] = varc:phase_all(V),
    ok.

order_degree() ->
    {V, [X1,X2,X3,X4,X5,X6]} = order_install(),
    %% d(X1) = 1
    %% d(X2) = 2
    %% d(X3) = 3
    %% d(X4) = 4
    %% d(X5) = 5
    %% d(X6) = 6

    ok = varc:order_sort(V, ?ORDER_DEGREE bor ?ORDER_DESCEND),
    [X6, X5, X4, X3, X2, X1] = varc:order_all(V),

    ok = varc:order_sort(V, ?ORDER_DEGREE bor ?ORDER_ASCEND),
    [X1, X2, X3, X4, X5, X6] = varc:order_all(V),
    ok.

order_rank() ->
    {V, [X1,X2,X3,X4,X5,X6]} = order_install(),
    %% r(X1) = 1/7,
    %% r(X2) = 1/7+1/6
    %% r(X3) = 1/7+1/6+1/5
    %% r(X4) = 1/7+1/6+1/5+1/4
    %% r(X5) = 1/7+1/6+1/5+1/4+1/3
    %% r(X6) = 1/7+1/6+1/5+1/4+1/3+1/2

    ok = varc:order_sort(V, ?ORDER_RANK bor ?ORDER_DESCEND),
    [X6, X5, X4, X3, X2, X1] = varc:order_all(V),

    ok = varc:order_sort(V, ?ORDER_RANK bor ?ORDER_ASCEND),
    [X1, X2, X3, X4, X5, X6] = varc:order_all(V),
    ok.

order_first() ->
    {V, [X1,X2,X3,X4,X5,X6]} = order_install(),
    %% first check
    ok = varc:order_sort(V, ?ORDER_IDENTITY, ?ORDER_UNDEFINED, 0),
    ok = varc:order_first(V, [X5, X6]),
    [X5, X6, X1, X2, X3, X4] = varc:order_all(V),
    ok.

order_last() ->
    {V, [X1,X2,X3,X4,X5,X6]} = order_install(),
    %% last check
    ok = varc:order_sort(V, ?ORDER_IDENTITY, ?ORDER_UNDEFINED, 0),
    ok = varc:order_last(V, [X1,X2]),
    [X3, X4, X5, X6, X1, X2] = varc:order_all(V),
    ok.

order_first_and_last() ->
    {V, [X1,X2,X3,X4,X5,X6]} = order_install(),
    %% first & last check
    ok = varc:order_sort(V, ?ORDER_IDENTITY, ?ORDER_UNDEFINED, 0),
    ok = varc:order_first(V, [X5, X6]),
    ok = varc:order_last(V, [X1,X2]),
    [X5, X6, X3, X4, X1, X2] = varc:order_all(V),
    ok.

order_random() ->
    {V, [X1,X2,X3,X4,X5,X6]} = order_install(),    
    ok = varc:order_sort(V, ?ORDER_RANDOM bor ?ORDER_INTERLEAVE, 
			 ?ORDER_UNDEFINED, 1001),
    %% Rand1001 = [X1,X6,-X3,X5,-X4,X2],
    [X1,X6,X3,X5,X4,X2] = varc:order_all(V),
    [1,1,-1,1,-1,1] = varc:phase_all(V),
    
    %% io:format("random,1001, Vs = ~p\n", [Sort1]),

    ok = varc:order_sort(V, ?ORDER_RANDOM bor ?ORDER_INTERLEAVE, 
			 ?ORDER_UNDEFINED, 1003),
    %% Rand1003 = [-X1,X4,-X6,-X2,X3,X5],
    [X1,X4,X6,X2,X3,X5] = varc:order_all(V),
    [-1,1,-1,-1,1,1] = varc:phase_all(V),
    %% io:format("random,1003, Vs = ~p\n", [Sort2]),
    ok.


subst0a() ->
    V = varc:new(#{xref=>true}),
    A = var(V),
    B = var(V),
    C = var(V),
    X = var(V),
    Y = var(V),

    _C0 = clause(V, [A, B, Y, C]),

    print_clauses(V),

    io:format(" [~w/~w]\n", [X,Y]),
    varc:subst(V, X, Y),

    io:format("clause after\n"),
    print_clauses(V,true),
    Bs = varc:get_bindings(V,0),
    io:format("bindings@0 = ~w\n", [Bs]),
    Bs.

subst0b() ->
    V = varc:new(#{xref=>true}),
    A = var(V),
    B = var(V),
    C = var(V),
    X = var(V),
    Y = var(V),

    _C0 = clause(V, [A, X, B, Y, C]),

    print_clauses(V),

    io:format(" [~w/~w]\n", [X,Y]),
    varc:subst(V, X, Y),

    io:format("clause after\n"),
    print_clauses(V,true),
    Bs = varc:get_bindings(V,0),
    io:format("bindings@0 = ~w\n", [Bs]),
    Bs.

subst0c() ->
    V = varc:new(#{xref=>true}),
    A = var(V),
    B = var(V),
    C = var(V),
    X = var(V),
    Y = var(V),

    _C0 = clause(V, [A, X, B, -Y, C]),

    print_clauses(V),

    io:format(" [~w/~w]\n", [X,Y]),
    varc:subst(V, X, Y),

    io:format("clause after\n"),
    print_clauses(V,true),
    Bs = varc:get_bindings(V,0),
    io:format("bindings@0 = ~w\n", [Bs]),
    Bs.

subst0d() ->
    V = varc:new(#{xref=>true}),
    X = var(V),
    Y = var(V),

    _C0 = clause(V, [X, Y]),

    print_clauses(V),

    io:format(" [~w/~w]\n", [X,Y]),
    varc:subst(V, X, Y),

    io:format("clause after\n"),
    print_clauses(V,true),
    Bs = varc:get_bindings(V,0),
    io:format("bindings@0 = ~w\n", [Bs]),
    Bs.
    
%% simply substitute {X2,X3},{X2,-X3} [X4/X3] => {X2,X4},{X2,-X4}
subst1() ->
    V = varc:new(#{xref=>true}), 
    X1 = var(V),
    X2 = var(V),
    X3 = var(V),
    NX3 = -X3,
    C0 = clause(V, [X1,X2]),
    C1 = clause(V, [X1,-X2]),
    io:format("\nbefore\n"),
    print_clauses(V),
    varc:subst(V, X3, X2),
    io:format("clause after\n"),
    print_clauses(V),
    [X1,X3] = lists:sort(varc:get_clause(V, C0)),
    [NX3,X1] = lists:sort(varc:get_clause(V, C1)),
    ok.

%% simply substitute {X1,X2} [X1/X2] => {X1}
subst2() ->
    V = varc:new(#{xref=>true}), 
    X1 = var(V),
    X2 = var(V),
    C0 = clause(V, [X1,X2]),
    io:format("\nbefore\n"),
    print_clauses(V),
    varc:subst(V, X1, X2),
    io:format("clause after\n"),
    print_clauses(V),
    io:format("raw clause = ~w\n", [varc:get_clause(V, C0, undefined, true)]),
    [] = lists:sort(varc:get_clause(V, C0)),
    ?T = varc:value(V, X1),
    ok.

subst3() ->
    V = varc:new(#{xref=>true}), 
    X2 = var(V),
    X3 = var(V),
    C0 = clause(V, [-X2,X3]),
    io:format("\nbefore\n"),
    print_clauses(V),
    varc:subst(V, -X2, X3),
    io:format("clause after\n"),
    print_clauses(V),
    io:format("raw clause = ~w\n", [varc:get_clause(V, C0, undefined, true)]),
    [] = lists:sort(varc:get_clause(V, C0)),
    ?F = varc:value(V, X2),
    ok.
    
subst4() ->
    V = varc:new(#{xref=>true}),
    X2 = var(V),
    X3 = var(V),
    X4 = var(V),
    X5 = var(V),
    X6 = var(V),
    X7 = var(V),
    
    _C0 = clause(V, [-X4,-X3,-X2]),
    _C1 = clause(V, [-X5,-X4,-X3]),
    _C2 = clause(V, [X6, X3, X2]),
    _C3 = clause(V, [X7, X6, X2]),
    _C4 = clause(V, [-X6, X3]),
    _C5 = clause(V, [X4, X2]),
    _C6 = clause(V, [X7, X4, -X2]),

    io:format("\nbefore\n"),
    print_clauses(V),

    io:format(" [~w/~w]\n", [X6,X3]),
    varc:subst(V, X6, X3),
    io:format("clause after\n"),

    %% FIXME: clause 2 has bad watch points should be {0,1} is {0,2}!

    print_clauses(V),

    true = varc:bcp(V),
    Bs = varc:get_bindings(V,0),
    io:format("bindings@0 = ~w\n", [Bs]),
    Bs.

subst5() ->
    V = varc:new(#{xref=>true}),
    X2 = var(V),
    X3 = var(V),
    X4 = var(V),
    X5 = var(V),
    X6 = var(V),
    X7 = var(V),

    _C0 = clause(V, [X4,-X3]),
    _C1 = clause(V, [X7,X3]),
    _C2 = clause(V, [X7,-X5]),
    _C3 = clause(V, [X3,X2]),
    _C4 = clause(V, [-X4,X6]),

    print_clauses(V),
    %% io:format(" [~w/~w]\n", [X7,X3]),
    %% varc:subst(V, X7, X3),
    io:format(" [~w/~w]\n", [X3,X7]),
    varc:subst(V, X3, X7),

    %% FIXME: clause 1 has bad watch points should be {0,1} should be {-1,-1}

    io:format("clause after\n"),
    print_clauses(V,true),
    true = varc:bcp(V),
    Bs = [X3,X4,X6] = lists:sort(varc:get_bindings_list(V,0)),
    io:format("bindings@0 = ~w\n", [Bs]),
    Bs.

subst6() ->
    V = varc:new(#{xref=>true}),
    Y = var(V),
    B = var(V),
    C = var(V),
    X = var(V),
    A = var(V),

    _C0 = clause(V, [A, X, B, Y, C]),
    _C1 = clause(V, [A, -X, B, Y, C]),
    _C2 = clause(V, [A, X, B, -C]),
    _C3 = clause(V, [-A, B, -Y, C]),
    _C4 = clause(V, [-A, B, -X, C]),
    _C5 = clause(V, [A, -Y, B, -X, C]),

    print_clauses(V),

    io:format(" [~w/~w]\n", [X,Y]),
    varc:subst(V, X, Y),

    io:format("clause after\n"),
    print_clauses(V,true),
    ok.

intersect1() ->
    V = varc:new(),
    _Vs = [ var(V) || _ <- lists:seq(1,20)], %% install variables
    varc:mark(V, [1,3,5,7,9,11,13,15,17,19]),
    varc:intersect_marks(V, [2,4,6,8,10,12,14,16,18,20]),
    {} = varc:get_marked(V, true),

    varc:mark(V, [1,3,5,7,-8,9,10,11,-12,13,15,17,19]),
    varc:intersect_marks(V, [2,4,6,8,10,12,14,16,18,20]),
    {10} = varc:get_marked(V, true),

    varc:mark(V, [1,3,5,7,-8,9,-10,11,-12,13,15,17,19]),
    varc:intersect_marks(V, [2,4,6,-8,10,-12,14,16,18,20]),
    {-8,-12} = varc:get_marked(V, true),

    varc:mark(V, []),
    {} = varc:get_marked(V, true),
    ok.

intersect2() ->
    V = varc:new(),    
    _Vs = [ var(V) || _ <- lists:seq(1,20)], %% install variables
    varc:mark(V, {1,3,5,7,9,11,13,15,17,19}),
    varc:intersect_marks(V, {2,4,6,8,10,12,14,16,18,20}),
    {} = varc:get_marked(V, true),

    varc:mark(V, {1,3,5,7,-8,9,10,11,-12,13,15,17,19}),
    varc:intersect_marks(V, {2,4,6,8,10,12,14,16,18,20}),
    {10} = varc:get_marked(V, true),

    varc:mark(V, {1,3,5,7,-8,9,-10,11,-12,13,15,17,19}),
    varc:intersect_marks(V, {2,4,6,-8,10,-12,14,16,18,20}),
    {-8,-12} = varc:get_marked(V, true),

    varc:mark(V, {}),
    {} = varc:get_marked(V, true),
    ok.

intersect_var0() ->
    X1 = 1, X2 = 2, X3 = 3, X4 = 4, X5 = 5, X6 = 6,
    Bs0 = [-X2,X3,-X4,X5,X6],
    Bs1 = [-X2,X3,X4,-X5],
    Di = [-X2,X3,{X1,X4},{X1,-X5}],
    Di = varc:intersect_var0(dummy, X1, Bs0, Bs1),
    ok.

intersect_var1() ->
    V = varc:new(),
    X1 = var(V),
    X2 = var(V),
    X3 = var(V),
    X4 = var(V),
    X5 = var(V),
    X6 = var(V),
    %% X1 -> {-X2,X3,X4,-X5}
    varc:mark(V, {-X2,X3,X4,-X5}),  
    %% -X1 -> {-X2,X3,-X4,X5,X6}
    Di = {-X2,X3,{X1,X4},{X1,-X5}},
    Di = varc:intersect_var(V, X1, {-X2,X3,-X4,X5,X6}, true),
    ok.

watch1() ->
    V = varc:new(),
    X1 = var(V),
    X2 = var(V),
    X3 = var(V),
    X4 = var(V),
    X5 = var(V),

    C1 = clause(V, [X5,X4,X3,X2,X1]),
       [X1,X2,X3,X4,X5] = varc:get_clause(V, C1),
    %%  0  A   0  0  0
    %% initial watch points are set in the end!
    0 = varc:clause_info(V, C1, watch0),
    1 = varc:clause_info(V, C1, watch1),

    %% bind X4, move wp 0
    varc:set_level(V, 1),
    varc:bind(V, -X4),
    true = varc:bcp(V),

    0 = varc:clause_info(V, C1, watch0),
    1 = varc:clause_info(V, C1, watch1),

    %% bind -X3, not watched, watch points should stay the same
    varc:set_level(V, 2),
    varc:bind(V, -X3),
    true = varc:bcp(V),

    0 = varc:clause_info(V, C1, watch0),
    1 = varc:clause_info(V, C1, watch1),

    varc:set_level(V, 3),
    varc:bind(V, -X1),
    true = varc:bcp(V),

    4 = varc:clause_info(V, C1, watch0),
    1 = varc:clause_info(V, C1, watch1),

    varc:set_level(V, 4),
    varc:bind(V, -X5),
    true = varc:bcp(V),

    4 = varc:clause_info(V, C1, watch0),
    1 = varc:clause_info(V, C1, watch1),

    ?T = varc:value(V, X2),

    C1 = varc:implication_clause(V, X2),
    1 = varc:implication_pos(V, X2),
    4 = varc:implication_level(V, X2),

    %% add clauses under the above bindings
    Y3 = -X5, Y2 = -X4, Y1 = -X2, 
    C2 = clause(V, [Y3, Y2, Y1]),
    [Y1, Y2, Y3] = varc:get_clause(V, C2),

    0 = varc:clause_info(V, C2, watch0),
    2 = varc:clause_info(V, C2, watch1),

    Z3 = X4, Z2 = X3, Z1 = -X1,
    C3 = clause(V, [Z3,Z2,Z1]),
    [Z1,Z2,Z3] = varc:get_clause(V, C3),

    0 = varc:clause_info(V, C3, watch0),
    1 = varc:clause_info(V, C3, watch1),

    ok.

edge_list0() ->
    V = varc:new(#{edge=>true}),
    true = varc:info(V, edge),

    A = var(V),
    B = var(V),

    {true,_C0} = varc:add_clause(V, [A, B]),
    
    %% eval should put in edges (A,B) ~A -> B, ~B -> A 
    [B] = varc:literal_info(V, -A, edge),
    [A] = varc:literal_info(V, -B, edge),
    ok.

edge_list1() ->
    V = varc:new(#{edge=>true}),
    true = varc:info(V, edge),

    A = var(V),
    B = var(V),
    C = var(V),

    {true,_C0} = varc:add_clause(V, [A, B, C]),
    %% assume A,B are watched
    varc:bind(V, -A),
    true = varc:bcp(V),

    %% eval should put in edges (B,C) ~C -> B, ~B -> C
    [B] = varc:literal_info(V, -C, edge),
    [C] = varc:literal_info(V, -B, edge),
    ok.

edge_list2() ->
    V = varc:new(#{edge=>true}),
    true = varc:info(V, edge),

    A = var(V),
    B = var(V),
    C = var(V),

    varc:bind(V, -C),

    {true,_C0} = varc:add_clause(V, [A, B, C]),

    %% eval should put in edges (A,B) ~A -> B, ~B -> A 
    [B] = varc:literal_info(V, -A, edge),
    [A] = varc:literal_info(V, -B, edge),
    ok.

edge_list3() ->
    V = varc:new(#{edge=>true}),
    true = varc:info(V, edge),

    A = var(V),
    B = var(V),
    C = var(V),
    D = var(V),

    {true,_C0} = varc:add_clause(V, [A, B]),
    {true,_C1} = varc:add_clause(V, [A, C]),
    {true,_C2} = varc:add_clause(V, [A, -D]),

    %% eval should put in edges (A,B) -A -> B, -B -> A 
    %% eval should put in edges (A,C) -A -> C, -C -> A
    %% eval should put in edges (A,-D) -A -> -D, D -> A
    ND = -D,
    [ND,B,C] = lists:sort(varc:literal_info(V, -A, edge)),

    [A] = varc:literal_info(V, -B, edge),
    [A] = varc:literal_info(V, -C, edge),
    [A] = varc:literal_info(V, D, edge),

    true = varc:bind(V, -A),
    true = varc:bcp(V),
    ?T = varc:value(V, B),
    ?T = varc:value(V, C),
    ?F = varc:value(V, D),
    ok.

clone1() ->
    V = varc:new(),
    X1 = var(V, <<"P(1,1)">>),
    X2 = var(V, <<"P(1,2)">>),
    X3 = var(V, <<"P(2,1)">>),
    X4 = var(V, <<"P(2,2)">>),
    X5 = var(V, <<"P(3,1)">>),
    X6 = var(V, <<"P(3,2)">>),

    clause(V, [X1,X2]),
    clause(V, [X3, X4]),
    clause(V, [X5, X6]),
    clause(V, [-X1, -X3]),
    clause(V, [-X1, -X5]),
    clause(V, [-X3, -X5]),
    clause(V, [-X2, -X4]),
    clause(V, [-X2, -X6]),
    clause(V, [-X4, -X6]),

    varc:set_level(V, 1),
    false = varc:nbcp(V),

    print_clauses(V),
    dump_variables(V, [X1,X2,X3,X4,X5,X6]),

    W = varc:clone(V),

    varc:set_level(W, 1),
    false = varc:nbcp(W),

    print_clauses(W),
    dump_variables(W, [X1,X2,X3,X4,X5,X6]),
    ok.

%% install and check integrity
cnf_install() ->
    %% install 20 clauses of size 3 with literals -10 .. 10
    cnf_install(20, 3, 10).

cnf_install(N,M,K) ->
    V = varc:new(#{xref=>true,hash=>true}),
    _Vs = [ var(V) || _ <- lists:seq(1,K)], %% install K variables
    CNF = generate_cnf(N, M, K),
    _ = install_cnf(V, CNF, delta),
    verify_xref(V, CNF),
    verify_hash(V, CNF),
    V.    

%% install random 3-CNF
%% remove clause 5
%% sort 
%% check integrity
%%
cnf_delete_sort() ->
    %% install 20 clauses of size 3 with literals -10 .. 10
    cnf_delete_sort(20, 3, 10).

cnf_delete_sort(N, M, K) ->
    V = varc:new(#{xref=>true,hash=>true}),
    _Vs = [ var(V) || _ <- lists:seq(1,K)], %% install K variables
    CNF = generate_cnf(N, M, K),
    _ = install_cnf(V, CNF, delta),
    C5 = lists:nth(5, CNF),
    Ci = varc:find_clause(V, C5),
    varc:del_clause(V, Ci),
    CNF1 = CNF -- [C5],
    varc:clauseset_sort(V, delta),
    verify_xref(V, CNF1),
    verify_hash(V, CNF1),
    V.

%% install random 3-CNF
%% use_clauses
%% sort
%% remove clauses 5..19
%% check integrity
%%
cnf_sort_offset_delete() ->
    %% install 20 clauses of size 3 with literals -10 .. 10
    cnf_sort_offset_delete(20, 3, 10).

cnf_sort_offset_delete(N, M, K) ->
    V = varc:new(#{xref=>true,hash=>true}),
    _Vs = [ var(V) || _ <- lists:seq(1,K)], %% install K variables
    CNF = generate_cnf(N, M, K),
    _ = install_cnf(V, CNF, delta),
    use_clauses(V, delta),
    varc:clauseset_sort(V, delta),
    varc:clauseset_offset(V, delta, 5),
    CiList = clause_list(V, delta),
    CNF1 = lists:foldr(
	     fun(Ci,CNFi) ->
		     Clause = varc:get_clause(V, Ci),
		     CNFi -- [Clause]
	     end, CNF, CiList),
    ok = delete_clauses(V, delta),
    varc:clauseset_offset(V, delta, 0),
    verify_xref(V, CNF1),
    verify_hash(V, CNF1),    
    V.

clause_learn_d1() ->
    V = varc:new(),
    ok = varc:config(V, max_conflicting, 1),
    A = var(V, <<"A">>),  %% 1
    B = var(V, <<"B">>),  %% 2
    C = var(V, <<"C">>),  %% 3
    X = var(V, <<"X">>),  %% 4
    Y = var(V, <<"Y">>),  %% 5
    Z = var(V, <<"Z">>),  %% 6
    clause(V, [A,B]),
    clause(V, [B,C]),
    clause(V, [-A,-X,Y]),  %% Y=1
    clause(V, [-A,X,Z]),
    clause(V, [-A,-Y,Z]),  %% Z=1
    clause(V, [-A,X,-Z]),
    clause(V, [-A,-Y,-Z]), %% Z=0

    %% io:format("DUMP1\n"),
    dump(V, false),

    %% bind A/1 B/1 C/1 X/1
    true = bind_and_bcp(V, 1, A),
    true = bind_and_bcp(V, 2, B),
    true = bind_and_bcp(V, 3, C),
    false = bind_and_bcp(V, 4, X),

    _Dix = varc:conflicting_clause(V, 0),
    %% io:format("conflicting_clause1: ~w: ~w\n",[Dix,varc:get_clause(V,_Dix)]),
    Learnt1 = varp_conflict:analyze_clause(V, 4, 1.0, 0),
    io:format("learnt_clause: ~w\n", [Learnt1]),
    true = ([-1,-5] == abs_sort(Learnt1)),

    undo_until(V, 4, 1),

    %% io:format("DUMP2\n"),
    %% dump(V, false),

    %% add learnt clause to gamma
    _Gix1 = clause(V, Learnt1, gamma),
    %% io:format("DUMP3\n"),
    %% dump(V, false),

    false = varc:bcp(V),
    Cix2 = varc:conflicting_clause(V, 0),
    io:format("conflicting_clause2: ~w: ~w\n", [Cix2,varc:get_clause(V, Cix2)]),
    %% io:format("DUMP4\n"),
    %% dump(V, false),
    Learnt2 = varp_conflict:analyze_clause(V, 1, 1.0, 0),
    io:format("learnt_clause: ~w\n", [Learnt2]),
    true = ([-1] == abs_sort(Learnt2)),
    varc:undo_level(V,1),
    varc:set_level(V, 0),
    true = clause(V, Learnt2, gamma),
    
    true = varc:bcp(V),
    Match = [-A,B],
    Match = varc:get_bindings_list(V, 0),
    ok.


clause_learn_a1() ->
    V = varc:new(),
    ok = varc:config(V, max_conflicting, 1),
    A = var(V, <<"A">>),  %% 1
    B = var(V, <<"B">>),  %% 2
    C = var(V, <<"C">>),  %% 3
    X = var(V, <<"X">>),  %% 4
    Y = var(V, <<"Y">>),  %% 5
    Z = var(V, <<"Z">>),  %% 6
    clause(V, [A,B]),
    clause(V, [B,C]),
    clause(V, [-A,-X,Y]),  %% Y=1
    clause(V, [-A,X,Z]),
    clause(V, [-A,-Y,Z]),  %% Z=1
    clause(V, [-A,X,-Z]),
    clause(V, [-A,-Y,-Z]), %% Z=0

    %% io:format("DUMP1\n"),
    dump(V, false),

    %% bind A/1 B/1 C/1 X/1
    true = bind_and_bcp(V, 1, A),
    true = bind_and_bcp(V, 2, B),
    true = bind_and_bcp(V, 3, C),
    false = bind_and_bcp(V, 4, X),

    Aix1 = varc:conflict(V, 4, 1.0, 0),
    Learnt1 = varc:get_clause(V,Aix1),
    io:format("conflicting_clause1: ~w: ~w\n",
	      [split_cix(Aix1),Learnt1]),
    io:format("learnt_clause: ~w\n", [Learnt1]),
    true = ([-1,-5] == abs_sort(Learnt1)),

    undo_until(V, 4, 1),

    io:format("DUMP2\n"),
    dump(V, false),

    %% add learnt clause to gamma
    {true,_Gix1} = varc:move_clause(V, Aix1, gamma),

    io:format("DUMP3\n"),
    dump(V, false),

    false = varc:bcp(V),
    Aix2 = varc:conflict(V, 1, 1.0, 0),
    Learnt2 = varc:get_clause(V,Aix2),
    io:format("conflicting_clause2: ~w: ~w\n",
	      [split_cix(Aix2),Learnt2]),
    io:format("learnt_clause: ~w\n", [Learnt2]),
    true = ([-1] == abs_sort(Learnt2)),

    io:format("DUMP4\n"),
    dump(V, false),

    undo_until(V, 1, 0),
    true = varc:move_clause(V, Aix2, gamma),
    
    true = varc:bcp(V),
    Match = [-A,B],
    Match = varc:get_bindings_list(V, 0),

    io:format("DUMP5\n"),
    dump(V, false),
    ok.

implication_depth() ->
    V = varc:new(),
    Y1 = var(V, <<"Y1">>),
    Y2 = var(V, <<"Y2">>),
    Y3 = var(V, <<"Y3">>),
    Y4 = var(V, <<"Y4">>),
    Y5 = var(V, <<"Y5">>),
    Y6 = var(V, <<"Y6">>),
    X  = var(V, <<"X">>),
    clause(V, [-X, Y1]),
    clause(V, [-X, Y2]),
    clause(V, [-Y1,-Y2,Y3]),
    clause(V, [-X,-Y2,Y4]),
    clause(V, [-X,-Y3,Y5]),
    clause(V, [-Y4,-Y5,Y6]),
    true = bind_and_bcp(V, 1, X),
    ?T = varc:value(V, Y1),
    ?T = varc:value(V, Y2),
    ?T = varc:value(V, Y3),
    ?T = varc:value(V, Y4),
    ?T = varc:value(V, Y5),
    ?T = varc:value(V, Y6),
    M0 = #{ X => 0 },
    {1, M1} = depth(V, Y1, M0),
    {1, M2} = depth(V, Y2, M1),
    {2, M3} = depth(V, Y3, M2),
    {2, M4} = depth(V, Y4, M3),
    {3, M5} = depth(V, Y5, M4),
    {4, _}  = depth(V, Y6, M5),
    ok.

depth(V, Yi, DepthMap) ->
    Cix = varc:implication_clause(V, Yi),
    Clause = varc:get_clause(V, Cix, Yi),
    Depth = lists:max([maps:get(-Li, DepthMap) || Li <- Clause])+1,
    {Depth, DepthMap#{ Yi => Depth }}.

%% 
%% bcp 999 clauses
%% {literal_integer,true},{literal_size,32},{value_packing,1} => 33412
%% {literal_integer,false},{literal_size,64},{value_packing,1} => 34047
%% {literal_integer,false},{literal_size,64},{value_packing,no} => 35276
%% 
bench() ->
    bench(20000).

bench(N) ->
    V = bench_cnf_build(),
    T0 = erlang:monotonic_time(),
    Bcp = bench_(V,1,N),
    T1 = erlang:monotonic_time(),
    Time = erlang:convert_time_unit(T1-T0,native,microsecond),
    Ts = Time/1000000,
    io:format("BCP/s=~w,"
	      "NUM_CLAUSES=~w,"
	      "LIT_INTEGER=~w,"
	      "LITERAL_SIZE=~w,"
	      "VALUE_PACKING=~w\n",
	      [Bcp/Ts, 
	       varc:info(V, number_of_clauses),
	       varc:info(V, literal_integer),
	       varc:info(V, literal_size),
	       varc:info(V, value_packing)]),
    Bcp / Ts.

bench_(V, _X0, 0) ->
    varc:info(V, bcp_counter);
bench_(V, X0, I) ->
    varc:set_level(V, 1),
    true = varc:bind(V, X0),
    true = varc:bcp(V),
    varc:undo_level(V, 1),
    bench_(V, X0, I-1).

bench_cnf_build() ->
    bench_install_cnf(bench_cnf()).

bench_cnf_build(N) ->
    bench_install_cnf(bench_cnf(N)).
    
bench_install_cnf(CNF) ->
    V = varc:new(),
    Vs = lists:usort(lists:append([[abs(L) || L <- Ci] || Ci <- CNF])),
    K  = lists:max(Vs),
    _ = [ var(V) || _ <- lists:seq(1,K)], %% install K variables
    install_cnf(V, CNF),
    V.

bench_cnf() ->
    bench_cnf(111).
bench_cnf(N) ->
    bench_var_init(),
    Xs0 = [bench_var()],
    lists:reverse(
      lists:foldl(
	fun(_, CNF0) ->
		Xs1 = [bench_var()|| _ <- lists:seq(1,2)],
		CNF1 = bench_clauses(Xs0, Xs1, CNF0),
		Xs2 = [bench_var()|| _ <- lists:seq(1,3)],
		CNF2 = bench_clauses(Xs1, Xs2, CNF1),
		Xs3 = [bench_var()|| _ <- lists:seq(1,4)],
		CNF3 = bench_clauses(Xs2, Xs3, CNF2),
		CNF3
	end, [], lists:seq(1, N))).

bench_var_init() ->
    put(bench_var_next, 1).

bench_var() ->
    I = get(bench_var_next),
    put(bench_var_next, I+1),
    I.

%% first variable 
bench_clauses([X1],[Y1,Y2],T) ->
    [[Y1,-X1], [Y2,-X1] | T];

bench_clauses([X1,X2],[Y1,Y2,Y3],T) ->
    [[Y1,-X1,-X2],[Y2,-X1,-X2],[Y3,-X1,-X2] | T];

bench_clauses([X1,X2,X3],[Y1,Y2,Y3,Y4], T) ->
    [[Y1,-X1,-X2,-X3],[Y2,-X1,-X2,-X3],
     [Y3,-X1,-X2,-X3],[Y4,-X1,-X2,-X3] | T];

bench_clauses(Xs, Ys, T) ->
    NXs = [-Xi || Xi <- Xs],
    [ [ [Yi | NXs] || Yi <- Ys] | T].


bind_and_bcp(V, Level, X) ->
    varc:set_level(V, Level),
    varc:bind(V, X) andalso varc:bcp(V).

undo_until(V, From, To) when From > To ->
    varc:undo_level(V, From),
    undo_until(V, From-1, To);
undo_until(V, _From, To) ->
    varc:set_level(V, To),
    To.

%% will have the effect that clause 1 have stamp T1 and clause N have stamp Tn
use_clauses(V, Set) ->
    use_clauses(V, Set, varc:clauseset_first(V, Set)).

use_clauses(_V, _Set, false) ->
    ok;
use_clauses(V, Set, I) ->
    varc:bcp(V),
    use_clauses(V, Set, varc:clauseset_next(V, I)).

%% get list of all clauses
clause_list(V) ->
    clause_list(V, delta).

clause_list(V, Set) ->
    clause_list_(V, Set, varc:clauseset_first(V, Set)).

clause_list_(_V, _Set, false) ->
    [];
clause_list_(V, Set, I) ->
    [I|clause_list_(V, Set, varc:clauseset_next(V, I))].
    

%% delete all clauses (from offset to end)
delete_clauses(V, Set) ->
    delete_clauses(V, Set, varc:clauseset_first(V, Set)).

delete_clauses(_V, _Set, false) ->
    ok;
delete_clauses(V, Set, I) ->
    io:format("delete clause ~w\n", [I]),
    ok = varc:del_clause(V, I),
    delete_clauses(V, Set, varc:clauseset_next(V, I)).

random_cnf() ->
    random_cnf(20, 6, 7).

random_cnf(N, M, K) ->
    random_cnf(N, M, K, delta).
random_cnf(N, M, K, Set) ->
    V = varc:new(),
    _Vs = [ var(V) || _ <- lists:seq(1,K)], %% install K variables
    CNF = generate_cnf(N, M, K),
    _ = install_cnf(V, CNF, Set),
    V.

write_cnf(CNF) ->
    io:put_chars(
      [format_preamable(CNF),"\n",
       [[format_clause(C),"\n"] || C <- CNF]]).

format_clause(C) ->
    [[[integer_to_list(L)," "] || L <- C],"0"].

format_preamable(CNF) ->
    M = length(CNF),
    Vs = lists:usort(lists:append([[abs(L) || L <- Ci] || Ci <- CNF])),
    N = length(Vs),
    ["p cnf ", integer_to_list(N), " ", integer_to_list(M)].

install_cnf(V, CNF) ->
    install_cnf(V, CNF, delta).

install_cnf(V, CNF, Set) ->
    lists:foldr(
      fun(Clause,Acc) ->
	      case clause(V, Clause, Set) of
		  false ->
		      %% the clause is contradictory 
		      assert_eval(V, Clause, false),
		      [false|Acc];
		  true ->
		      %% the clause is true 
		      %% either evaluate to true or has X -X in the clause
		      assert_eval(V, Clause, true),
		      [true|Acc];
		  Ci ->
		      %% check the clause
		      GetClause = varc:get_clause(V, Ci),
		      assert_equal(GetClause, abs_sort(Clause)),
		      [Ci|Acc]
	      end
      end, [], CNF).

assert_eval(V, Clause, Value) ->
    case eval(V, Clause) of
	Value -> ok;
	Other -> 
	    io:format("assertion failed: eval(~w) ~w =/= ~w\n",
		      [Clause,Other,Value]),
	    throw(badmatch)
    end.

assert_equal(Value1, Value2) ->
    if Value1 =:= Value2 -> ok;
       true ->
	    io:format("assertion failed: get ~w =/= norm ~w\n",
		      [Value1,Value2]),
	    throw(badmatch)
    end.
	    
eval(_V, true) ->
    true;
eval(V, [Li]) ->
    case varc:value(V, Li) of
	?T -> true;
	?F -> false;
	undefined -> true
    end;
eval(V, Ls) ->
    eval(V, Ls, false).

eval(V, [Li|Ls], Sum) ->
    case varc:value(V, Li) of
	?T -> true;
	?F -> eval(V, Ls, Sum);
	undefined -> eval(V,Ls,undefined)
    end;
eval(_V, [], Sum) -> Sum.

%% Verify that we can reach all clauses via xref
verify_xref(V, CNF) ->
    true = varc:info(V, xref),  %% assert we have xref enabled
    DegLs = deg_literal_list(CNF),
    %% check that clauses reached by Ls are in CNF
    lists:foreach(
      fun({Li,Deg}) ->
	      XRefs = varc:get_clauses(V, Li, literal),
	      XRefLen = length(XRefs),
	      if XRefLen =:= Deg -> ok;
		 true ->
		      io:format("Literal degree mismatch: ~w xref = ~w\n",
				[Li,XRefs]),
		      io:format("cnf = \n~w\n", [CNF]),
		      error(bad_degree)
	      end,
	      lists:foreach(
		fun(Ci) ->
			Clause = varc:get_clause(V, Ci),
			true = lists:member(Clause, CNF)
		end, XRefs)
      end, DegLs).

verify_hash(V, CNF) ->
    true = varc:info(V, hash),  %% assert we have hash enabled
    lists:foreach(
      fun(Clause) ->
	      Ci = varc:find_clause(V, Clause),
	      Clause = varc:get_clause(V, Ci)
      end, CNF).

%% Utils

get_watched(V) ->
    get_watched(V, lists:seq(2, varc:info(V, number_of_variables)+1)).

get_watched(V, [Xi|Xs]) ->
    Wi0 = varc:get_clauses(V, Xi, watch),
    Wi1 = varc:get_clauses(V, -Xi, watch),
    [{Xi,Wi0},{-Xi,Wi1}|get_watched(V, Xs)];
get_watched(_V, []) ->
    [].

dump(V) ->
    dump(V, true).
dump(V, Verb) ->
    io:format("STATE of ~p\n", [V]),
    if Verb ->
	    lists:foreach(
	      fun({Key, Value}) ->
		      io:format("  ~s: ~p\n", [Key,Value])
	      end, varc:info(V));
       true -> ok
    end,
    io:format("VARIABLES\n"),
    dump_variables(V, lists:seq(1, varc:info(V,number_of_variables)), Verb),
    io:format("CLAUSES DELTA\n"),
    dump_clauses(V, true, varc:clauseset_first(V,delta), Verb),
    io:format("CLAUSES GAMMA\n"),
    dump_clauses(V, true, varc:clauseset_first(V,gamma), Verb),
    io:format("CLAUSES BETA\n"),
    dump_clauses(V, true, varc:clauseset_first(V,beta), Verb),
    io:format("CLAUSES ALPHA\n"),
    dump_clauses(V, true, varc:clauseset_first(V,alpha), Verb),
    io:format("BINDINGS\n"),
    lists:foreach(
      fun(L) ->
	      io:format("~w: ~p\n", [L, varc:get_bindings(V, L)])
      end, lists:seq(0, varc:info(V,level))),
    ok.

print_clauses(V) ->  print_clauses(V, true).
print_clauses(V, Verb) ->  print_clauses(V,false,Verb).

print_clauses(V,Raw,Verb) ->
    dump_clauses(V, Raw, varc:clauseset_first(V,delta), Verb).

dump_clauses(_V, _Raw, false, _Verb) ->
    ok;
dump_clauses(V, Raw, I, Verb) ->
    {_,SI,IX} = split_cix(I),
    WATCH = case varc:clause_info(V, I, watch) of
		{-1,-1} -> "";
		{P1,P2} -> " watch:"++integer_to_list(P1)++","++
			       integer_to_list(P2)
	    end,
    STATUS = case varc:clause_info(V, I, status) of
		 ok -> "";
		 Status -> io_lib:format(" ~p", [Status])
	     end,
    io:format("~w - ~s:~w~s~s\n", [I,SI,IX,WATCH,STATUS]),
    io:format("  ~w\n", [varc:get_clause(V,I,undefined,Raw)]),
    dump_clauses(V, Raw, varc:clauseset_next(V, I), Verb).

dump_variables(V, List) ->
    dump_variables(V, List, true).

dump_variables(V, List, Verb) ->
    lists:foreach(
      fun(X) ->
	      Keys = varc:variable_info_keys() -- [implication,symbol,level],
	      [{Sym,_Pos}] = varc:variable_info(V,X,symbol),
	      Level = varc:variable_info(V,X,level),
	      Value = varc:value(V, X),
	      io:format("~w: ~s = ~w @~w\n", [X, Sym, Value,Level]),
	      if Verb ->
		      lists:foreach(
			fun(Key) ->
				io:format("  ~s: ~p\n", 
					  [Key,varc:variable_info(V,X,Key)])
			end, Keys),
		      io:format(" +xref: ~p\n", [get_cix_list(V,X,literal)]),
		      io:format(" +watch: ~p\n", [get_cix_list(V,X,watch)]),
		      io:format(" -xref: ~p\n", [get_cix_list(V,-X,literal)]),
		      io:format(" -watch: ~p\n", [get_cix_list(V,-X,watch)]);
		 true ->
		      ok
	      end
      end, List).

get_cix_list(V, X, How) ->
    [split_cix(I) || I <- varc:get_clauses(V, X, How)].

split_cix(I) ->
    {I, case (I bsr 30) band 3 of 
	    ?DELTA -> delta;
	    ?GAMMA -> gamma;
	    ?BETA -> beta;
	    ?ALPHA -> alpha
	end,
     I band 16#3fffffff}.
    

var(V) ->
    varc:add_variable(V).

var(V, Sym) ->
    Vi = varc:add_variable(V),
    varc:add_symbol(V, Vi, Sym),
    Vi.

clause(V, Ls) ->
    clause(V, Ls, delta).

clause(V, Ls, Set) ->
    case varc:add_clause(V, Ls, Set) of
	{true,Ci} -> Ci;
	true -> true;
	false -> false
    end.

get_clause(V, ClauseIndex) ->
    Literals = varc:get_clause(V, ClauseIndex),
    lists:sort(Literals).

format_clause_flags(Fs) ->
    lists:join(",", [format_clause_flag(F) || F <- Fs]).

format_clause_flag({watch,{P1,P2}}) -> io_lib:format("w:(~w,~w)",[P1,P2]);
format_clause_flag({status,inqueue}) -> "s:inqueue";
format_clause_flag({status,dead}) -> "s:dead";
format_clause_flag({status,ok}) -> "s:ok".

%% literal list from clauses (CNF or DNF)
literal_list(Cs) ->
    literal_list_(Cs,#{},false).

deg_literal_list(Cs) ->
    literal_list_(Cs,#{},true).

literal_list_([C|Cs],Map,Deg) ->
    Map1 = lists:foldl(
	     fun(Li,Mi) ->
		     maps:put(Li,maps:get(Li,Mi,0)+1,Mi)
	     end, Map, C),
    literal_list_(Cs, Map1, Deg);
literal_list_([], Map, true) ->
    maps:fold(fun(Li,Deg,Acc) -> [{Li,Deg}|Acc] end, [], Map);
literal_list_([], Map, false) ->
    maps:fold(fun(Li,_Deg,Acc) -> [Li|Acc] end, [], Map).

%% make CNF from DNF

dnf_to_cnf([]) ->
    [];
dnf_to_cnf([D]) ->
    normalize_cnf([[Di] || Di <- D]);
dnf_to_cnf([D1,D2|Ds]) ->
    normalize_cnf(dnf_to_cnf_(Ds, [[Di,Dj] || Di <- D1, Dj <- D2])).

dnf_to_cnf_([D|Ds], CNF) ->
    dnf_to_cnf_(Ds,  lists:append([[[Di|Ci] || Di <- D] || Ci <- CNF]));
dnf_to_cnf_([], CNF) ->
    CNF.

%% Generate a random CNF
%% N clauses with clause length M with K variables (-K..K)

generate_cnf(N,M,K) ->
    [generate_clause(M,K) || _ <- lists:seq(1,N)].

%% generate a clause of length M of literals in range -K .. K
%% The clause can only contain wither X or -X 
%% do not include repeats
%%
generate_clause(M,K) ->
    L = lists:sort([{rand:uniform(),rand_sign(),Li} || 
		       Li <- lists:seq(1, K)]),
    abs_sort([S*Li || {_,S,Li} <- lists:sublist(L, M)]).

%% (1,2)  
%% (1,2)*2   = (2,4)
%% (2,4) - 3 = (-1,1)

rand_sign() ->
    rand:uniform(2)*2 -3.
       
%% generate one literal in range -K .. K but skip 0
generate_literal(K) ->
    A = rand:uniform(2*K-1)-(K+1),
    if A < 0 -> A;
       true -> A + 1
    end.

abs_sort(L) ->
    lists:sort(fun(A,B) -> abs(B) >= abs(A) end, L).

rev_abs_sort(L) ->
    lists:sort(fun(A,B) -> abs(A) >= abs(B) end, L).

%% remove repeats, kill clauses with both X and -X
normalize_clause(Clause) ->
    L = rev_abs_sort(Clause),
    normalize_abs_clause(L).

normalize_abs_clause([]) -> 
    [];
normalize_abs_clause([Li|L]) ->
    normalize_abs_clause_(L, Li, []).

normalize_abs_clause_([Li|L], Li, Acc) ->
    normalize_abs_clause_(L, Li, Acc);
normalize_abs_clause_([Lj|_L], Li, _Acc) when Li =:= -Lj ->
    true;
normalize_abs_clause_([Lj|L], Li, Acc) ->
    normalize_abs_clause_(L, Lj,[Li|Acc]);
normalize_abs_clause_([], Li, Acc) ->
    [Li|Acc].

%%
%% "normalize" cnf
%% 1 - remove tautology clauses X,..,!X
%% 2 - remove repeats X...X
%% 3 - propagate units
%%
normalize_cnf(Cs) ->
    propagate_cnf(normalize_cnf_(Cs,[])).

normalize_cnf_([Ci|Cs],Acc) ->
    case normalize_clause(Ci) of
	true ->
	    normalize_cnf_(Cs,Acc);
	[] ->
	    [];
	Cj ->
	    normalize_cnf_(Cs,[Cj|Acc])
    end;
normalize_cnf_([],Acc) ->
    Acc.

%% propagate unit clauses
propagate_cnf(Cs) ->
    {Units, Clauses} = lists:partition(fun([_]) -> true; (_) -> false end, Cs),
    propagate_units_(Units, Clauses, Units).

propagate_units_([[Q]|Qs], Clauses, Units) ->
    propagate_unit_(Q, Qs, Clauses, [], Units);
propagate_units_([], Clauses, Units) ->
    Units ++ Clauses.

%% propagte U
propagate_unit_(U, Qs, [Clause|Clauses], Acc, Units) ->
    case lists:member(U, Clause) of
	true ->
	    propagate_unit_(U, Qs, Clauses, Acc, Units);
	false ->
	    case Clause -- [-U] of
		[V] ->  %% new unit
		    propagate_unit_(U, Qs++[V], Clauses, Acc, [V|Units]);
		Clause1 ->
		    propagate_unit_(U, Qs, Clauses, [Clause1|Acc], Units)
	    end
    end;
propagate_unit_(_U, Qs, [], Acc, Units) ->
    propagate_units_(Qs, Acc, Units).
			       
