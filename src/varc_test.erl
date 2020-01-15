%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2019, Tony Rogvall
%%% @doc
%%%    Test of varc
%%% @end
%%% Created : 14 Mar 2019 by Tony Rogvall <tony@rogvall.se>

-module(varc_test).

-compile(export_all).

-export([all/0]).

-include("varp.hrl").

all() ->
    lists:foreach(
      fun(Test) ->
	      io:format("< ~w: ", [Test]),
	      apply(?MODULE, Test, []),
	      io:format("> ok\n")
      end, [test1,
	    test2,
	    test3,
	    clause_simplify,
	    clause_bcp,
	    watch1,
	    order,
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
	    subst6
	   ]).

test1() ->
    V = varc:new(),
    X1 = add_variable(V),
    X2 = add_variable(V),
    X3 = add_variable(V),
    Ls0 = lists:usort([X1, X2, X3]),
    C0 = add_clause(V, Ls0),
    io:format("C0=~w\n", [C0]),
    Ls0 = get_clause(V, C0),
    io:format("Ls0=~w\n", [Ls0]),
    
    Ls1 = lists:usort([X1,-X2,X3]),
    C1 = add_clause(V, Ls1),
    io:format("C0=~w\n", [C1]),
    Ls1 = get_clause(V, C1),
    io:format("Ls0=~w\n", [Ls1]),
    ok.

test1_gamma() ->
    V = varc:new(),
    X1 = add_variable(V),
    X2 = add_variable(V),
    X3 = add_variable(V),
    Ls0 = lists:usort([X1, X2, X3]),
    C0 = add_clause(V, Ls0, ?GAMMA),
    io:format("C0=~w\n", [C0]),
    Ls0 = get_clause(V, C0),
    io:format("Ls0=~w\n", [Ls0]),
    
    Ls1 = lists:usort([X1,-X2,X3]),
    C1 = add_clause(V, Ls1),
    io:format("C0=~w\n", [C1]),
    Ls1 = get_clause(V, C1),
    io:format("Ls0=~w\n", [Ls1]),
    ok.
    
test2() ->
    V = varc:new(),
    X1 = add_variable(V),
    X2 = add_variable(V),
    X3 = add_variable(V),
    X4 = add_variable(V),
    
    C0 = add_clause(V, [X1, X2, X3]),
    C1 = add_clause(V, [X2, X3, X4]),

    [X1, X2, X3] = get_clause(V, C0),
    [X2, X3, X4] = get_clause(V, C1),
    ok.

%%
%% Test clause / queue 
%%    
test3() ->
    V = varc:new([{xref,true}]),
    X1 = add_variable(V),
    X2 = add_variable(V),
    X3 = add_variable(V),
    X4 = add_variable(V),
    X5 = add_variable(V),
    X6 = add_variable(V),
    X7 = add_variable(V),

    C0 = add_clause(V, [X1, X2, X3]),
    C1 = add_clause(V, [X2, X3, X4]),
    C2 = add_clause(V, [X3, X4, X5, X6]),
    C3 = add_clause(V, [X5, X6, X7]),

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
    {varc:get_bindings(V, 1), varc:get_number_of_clauses(V)}.

%% Test all clause simplifications
clause_simplify() ->
    V = varc:new(),
    X1 = add_variable(V),
    X2 = add_variable(V),
    X3 = add_variable(V),
    X4 = add_variable(V),
    X5 = add_variable(V),
    C0 = add_clause(V, [X2,X3,X4,X5]),
    C1 = add_clause(V, [X5,X4,X3,X2]),
    C20 = add_clause(V, [X1,X1,X1,X1,X1]),
    C23 = add_clause(V, [X2,X3,X3,X3,X2]),
    L3 = [X2,X3,X2,X3,X4,?F],
    io:format("L3 = ~w\n", [L3]),
    C3 = add_clause(V, L3),
    C4 = add_clause(V, [X2,X3,X2,X3,X4]),
    C5 = add_clause(V, [X2,?T,X3,?F,X4,?T,X4,?T, X5,?F]),
    C6 = add_clause(V, [X2,?T,X3,?F,-X3,?T,X3,?T,-X3,?F,X4]),

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

%% Test eval
clause_bcp() ->
    V = varc:new(),
    X1 = add_variable(V),
    X2 = add_variable(V),
    X3 = add_variable(V),
    X4 = add_variable(V),

    undefined = varc:value(V, X1),
    undefined = varc:value(V, X2),
    undefined = varc:value(V, X3),
    undefined = varc:value(V, X4),

    varc:set_level(V, 1),
    C0 = add_clause(V, [X1, ?F, ?F]),
    C1 = add_clause(V, [X2, ?T, ?T, ?T]),
    C2 = add_clause(V, [-X3, ?F, ?F, ?F]),
    C3 = add_clause(V, [X4, ?F, ?T, ?F, ?T]),
    io:format("clauses=~p\n", [[C0,C1,C2,C3]]),
    print_clauses(V),

    io:format("queue=~p\n", [varc:get_queue(V)]),
    true = varc:bcp(V),

    V1 = varc:value(V, X1),
    io:format("X1 = ~w\n", [V1]),
    true = V1 =:= ?T,

    V2 = varc:value(V, X2),
    io:format("X2 = ~w\n", [V2]),
    true = V2 =:= undefined,

    V3 = varc:value(V, X3),
    io:format("X3 = ~w\n", [V3]),
    true = V3 =:= ?F,

    V4 = varc:value(V, X4),
    io:format("X4 = ~w\n", [V4]),
    true = V4 =:= undefined,

    io:format("Bindings@0 = ~w\n", [varc:get_bindings(V,0)]),
    io:format("Bindings@1 = ~w\n", [varc:get_bindings(V,1)]),

    true.

%% 
%% add clause with bindings
%%
or_bcp_bindings() ->
    V = varc:new(),
    X1 = add_variable(V),
    X2 = add_variable(V),
    X3 = add_variable(V),
    X4 = add_variable(V),

    varc:set_level(V, 1),
    add_clause(V, [-X1, -X2, -X3]),
    add_clause(V, [-X1, -X2,  X4]),
    add_clause(V, [-X1,  X2, -X3]),
    add_clause(V, [-X1,  X2,  X3]),
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
    add_clause(V, [-X1,  X2,  X3, -X4]),
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

nbcp_p3() ->
    V = varc:new(),
    X1 = add_variable(V), varc:add_symbol(V, X1, <<"P(1,1)">>),
    X2 = add_variable(V), varc:add_symbol(V, X2, <<"P(1,2)">>),
    X3 = add_variable(V), varc:add_symbol(V, X3, <<"P(2,1)">>),
    X4 = add_variable(V), varc:add_symbol(V, X4, <<"P(2,2)">>),
    X5 = add_variable(V), varc:add_symbol(V, X5, <<"P(3,1)">>),
    X6 = add_variable(V), varc:add_symbol(V, X6, <<"P(3,2)">>),
    %% pigeon=3
    varc:add_clause(V, [X1,X2]),
    varc:add_clause(V, [X3, X4]),
    varc:add_clause(V, [X5, X6]),
    varc:add_clause(V, [-X1, -X3]),
    varc:add_clause(V, [-X1, -X5]),
    varc:add_clause(V, [-X3, -X5]),
    varc:add_clause(V, [-X2, -X4]),
    varc:add_clause(V, [-X2, -X6]),
    varc:add_clause(V, [-X4, -X6]),

    varc:set_level(V, 1),

    false = varc:nbcp(V),
    Bn1 = varc:get_all_bindings(V),
    io:format("bindings = ~w\n", [Bn1]),
    varc:undo(V),

    false = varc:nbcp(V),
    Bn2 = varc:get_all_bindings(V),
    io:format("bindings = ~w\n", [Bn2]),
    varc:undo(V),

    BnX = varc:get_all_bindings(V),
    io:format("bindings = ~w\n", [BnX]),
    ok.

nbcp_p4() ->
    V = varc:new(),
    X1 = add_variable(V), varc:add_symbol(V, X1, <<"P(1,1)">>),
    X2 = add_variable(V), varc:add_symbol(V, X2, <<"P(1,2)">>),
    X3 = add_variable(V), varc:add_symbol(V, X3, <<"P(1,3)">>),
    X4 = add_variable(V), varc:add_symbol(V, X4, <<"P(2,1)">>),
    X5 = add_variable(V), varc:add_symbol(V, X5, <<"P(2,2)">>),
    X6 = add_variable(V), varc:add_symbol(V, X6, <<"P(2,3)">>),
    X7 = add_variable(V), varc:add_symbol(V, X7, <<"P(3,1)">>),
    X8 = add_variable(V), varc:add_symbol(V, X8, <<"P(3,2)">>),
    X9 = add_variable(V), varc:add_symbol(V, X9, <<"P(3,3)">>),
    X10 = add_variable(V), varc:add_symbol(V, X10, <<"P(4,1)">>),
    X11 = add_variable(V), varc:add_symbol(V, X11, <<"P(4,2)">>),
    X12 = add_variable(V), varc:add_symbol(V, X12, <<"P(4,3)">>),

    ok = varc:order_sort_first(V, [X2,X4,X6,X8,X10,X12,X1,X3,X5,X7,X9,X11]),

    varc:add_clause(V, [X1,X2,X3]),
    varc:add_clause(V, [X4,X5,X6]),
    varc:add_clause(V, [X7,X8,X9]),
    varc:add_clause(V, [X10,X11,X12]),
    varc:add_clause(V, [-X1,-X4]),
    varc:add_clause(V, [-X1,-X7]),
    varc:add_clause(V, [-X1,-X10]),
    varc:add_clause(V, [-X4,-X7]),
    varc:add_clause(V, [-X4,-X10]),
    varc:add_clause(V, [-X7,-X10]),
    varc:add_clause(V, [-X2,-X5]),
    varc:add_clause(V, [-X2,-X8]),
    varc:add_clause(V, [-X2,-X11]),
    varc:add_clause(V, [-X5,-X8]),
    varc:add_clause(V, [-X5,-X11]),
    varc:add_clause(V, [-X8,-X11]),
    varc:add_clause(V, [-X3,-X6]),
    varc:add_clause(V, [-X3,-X9]),
    varc:add_clause(V, [-X3,-X12]),
    varc:add_clause(V, [-X6,-X9]),
    varc:add_clause(V, [-X6,-X12]),
    varc:add_clause(V, [-X9,-X12]),

    varc:set_level(V, 1),

    nbcp_loop(V).

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
    

order() ->
    V = varc:new([{activity, mvsids}]),
    X1 = varc:add_variable(V), varc:add_symbol(V, X1, <<"X1">>),
    X2 = varc:add_variable(V), varc:add_symbol(V, X2, <<"X2">>),
    X3 = varc:add_variable(V), varc:add_symbol(V, X3, <<"X3">>),
    X4 = varc:add_variable(V), varc:add_symbol(V, X4, <<"X4">>),
    X5 = varc:add_variable(V), varc:add_symbol(V, X5, <<"X5">>),
    X6 = varc:add_variable(V), varc:add_symbol(V, X6, <<"X6">>),
    Y1 = varc:add_variable(V),
    Y2 = varc:add_variable(V),
    Y3 = varc:add_variable(V),

    _Z0 = add_clause(V, [Y2, Y3], ?GAMMA),
    _Z1 = add_clause(V, [Y2, -Y3], ?GAMMA),
    _C0 = add_clause(V, [X1, X2, X3, X4, X5, X6, Y1], ?GAMMA),
    _C1 = add_clause(V, [    X2, X3, X4, X5, X6, Y1], ?GAMMA),
    _C2 = add_clause(V, [        X3, X4, X5, X6, Y1], ?GAMMA),
    _C3 = add_clause(V, [            X4, X5, X6, Y1], ?GAMMA),
    _C4 = add_clause(V, [                X5, X6, Y1], ?GAMMA),
    _C5 = add_clause(V, [                    X6, Y1], ?GAMMA),
    varc:bind(V, Y1),

    lists:foreach(
      fun({L,Xi}) ->
	      varc:set_level(V,L), varc:bind(V, Xi),
	      varc:set_level(V,L+1), varc:bind(V, -Y2), false = varc:bcp(V),
	      varc:undo_level(V,L+1)
      end, [{X1,1},{X2,2},{X3,3},{X4,4},{X5,5},{X6,6}]),

    lists:foreach(
      fun(L) ->
	      varc:undo_level(V, L)
      end, lists:seq(7,1,-1)),

    lists:foreach(
      fun({L,Cp,Cn}) ->
	      varc:set_user_count(V,L,Cp),
	      varc:set_user_count(V,-L,Cn)
      end, [{X1,12,10},{X2,11,13},{X3,16,14},{X4,15,17},{X5,20,18},{X6,19,21}]),
	      
    varc:bind(V, Y2),
    varc:bind(V, Y3),

    dump_variables(V, [X1,X2,X3,X4,X5,X6]),

    Index = varc:first_unbound_index(V),
    io:format("First unbound index = ~w\n", [Index]),
    if Index =:= false ->
	    ok;
       true ->
	    Index1 = varc:next_unbound_index(V, Index),
	    io:format("Next unbound index = ~w\n", [Index1])
    end,

    ok = varc:order_sort(V, ?ORDER_IDENTITY),
    [X1, X2, X3, X4, X5, X6] = varc:order_all(V),

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

    ok = varc:order_sort(V, ?ORDER_ACTIVITY  bor ?ORDER_DESCEND),
    [X6, X5, X4, X3, X2, X1] = varc:order_all(V),

    ok = varc:order_sort(V, ?ORDER_ACTIVITY  bor ?ORDER_ASCEND),
    [X1, X2, X3, X4, X5, X6] = varc:order_all(V),

    ok = varc:decay(V, 0.1),

    dump_variables(V, [X1,X2,X3,X4,X5,X6]),

    ok = varc:order_sort(V, ?ORDER_USER bor ?ORDER_ASCEND),
    U1 = [X1,-X2,X3,-X4,X5,-X6],
    U1 = varc:order_all(V),

    ok = varc:order_sort(V, ?ORDER_USER bor ?ORDER_DESCEND),
    U2 = [-X6,X5,-X4,X3,-X2,X1],
    U2 = varc:order_all(V),

    %% first check
    ok = varc:order_sort(V, ?ORDER_IDENTITY, ?ORDER_UNDEFINED, 0),
    ok = varc:order_sort_first(V, [X5, X6]),
    [X5, X6, X1, X2, X3, X4] = varc:order_all(V),

    %% last check
    ok = varc:order_sort(V, ?ORDER_IDENTITY, ?ORDER_UNDEFINED, 0),
    ok = varc:order_sort_last(V, [X2, X1]),  %% reversed
    [X3, X4, X5, X6, X1, X2] = varc:order_all(V),

    %% first & last check
    ok = varc:order_sort(V, ?ORDER_IDENTITY, ?ORDER_UNDEFINED, 0),
    ok = varc:order_sort_first(V, [X5, X6]),
    ok = varc:order_sort_last(V, [X2, X1]),  %% reversed
    [X5, X6, X3, X4, X1, X2] = varc:order_all(V),

    ok = varc:order_sort(V, ?ORDER_RANDOM bor ?ORDER_INTERLEAVE, 
			 ?ORDER_UNDEFINED, 1001),
    Rand1001 = [X1,X6,-X3,X5,-X4,X2],
    Rand1001 = varc:order_all(V),
    %% io:format("random,1001, Vs = ~p\n", [Sort1]),

    ok = varc:order_sort(V, ?ORDER_RANDOM bor ?ORDER_INTERLEAVE, 
			 ?ORDER_UNDEFINED, 1003),
    Rand1003 = [-X1,X4,-X6,-X2,X3,X5],
    Rand1003 = varc:order_all(V),
    %% io:format("random,1003, Vs = ~p\n", [Sort2]),

    ok.

subst0a() ->
    V = varc:new([{xref,true}]),
    A = varc:add_variable(V),
    B = varc:add_variable(V),
    C = varc:add_variable(V),
    X = varc:add_variable(V),
    Y = varc:add_variable(V),

    _C0 = varc:add_clause(V, [A, B, Y, C]),

    print_clauses(V),

    io:format(" [~w/~w]\n", [X,Y]),
    varc:subst(V, X, Y),

    io:format("clause after\n"),
    print_clauses(V,true),
    Bs = varc:get_bindings(V,0),
    io:format("bindings@0 = ~w\n", [Bs]),
    Bs.

subst0b() ->
    V = varc:new([{xref,true}]),
    A = varc:add_variable(V),
    B = varc:add_variable(V),
    C = varc:add_variable(V),
    X = varc:add_variable(V),
    Y = varc:add_variable(V),

    _C0 = varc:add_clause(V, [A, X, B, Y, C]),

    print_clauses(V),

    io:format(" [~w/~w]\n", [X,Y]),
    varc:subst(V, X, Y),

    io:format("clause after\n"),
    print_clauses(V,true),
    Bs = varc:get_bindings(V,0),
    io:format("bindings@0 = ~w\n", [Bs]),
    Bs.

subst0c() ->
    V = varc:new([{xref,true}]),
    A = varc:add_variable(V),
    B = varc:add_variable(V),
    C = varc:add_variable(V),
    X = varc:add_variable(V),
    Y = varc:add_variable(V),

    _C0 = varc:add_clause(V, [A, X, B, -Y, C]),

    print_clauses(V),

    io:format(" [~w/~w]\n", [X,Y]),
    varc:subst(V, X, Y),

    io:format("clause after\n"),
    print_clauses(V,true),
    Bs = varc:get_bindings(V,0),
    io:format("bindings@0 = ~w\n", [Bs]),
    Bs.

subst0d() ->
    V = varc:new([{xref,true}]),
    X = varc:add_variable(V),
    Y = varc:add_variable(V),

    _C0 = varc:add_clause(V, [X, Y]),

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
    V = varc:new([{xref,true}]), 
    X1 = varc:add_variable(V),
    X2 = varc:add_variable(V),
    X3 = varc:add_variable(V),
    NX3 = -X3,
    C0 = add_clause(V, [X1,X2]),
    C1 = add_clause(V, [X1,-X2]),
    io:format("\nbefore\n"),
    print_clauses(V),
    varc:subst(V, X3, X2),
    io:format("clause after\n"),
    print_clauses(V),
    [X1,X3] = lists:sort(varc:get_clause(V, C0)),
    [NX3,X1] = lists:sort(varc:get_clause(V, C1)),
    ok.

%% simply substitute {X2,X3} [X2/X3] => {X2}
subst2() ->
    V = varc:new([{xref,true}]), 
    X1 = varc:add_variable(V),
    X2 = varc:add_variable(V),
    C0 = add_clause(V, [X1,X2]),
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
    V = varc:new([{xref,true}]), 
    X2 = varc:add_variable(V),
    X3 = varc:add_variable(V),
    C0 = add_clause(V, [-X2,X3]),
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
    V = varc:new([{xref,true}]),
    X2 = varc:add_variable(V),
    X3 = varc:add_variable(V),
    X4 = varc:add_variable(V),
    X5 = varc:add_variable(V),
    X6 = varc:add_variable(V),
    X7 = varc:add_variable(V),
    
    _C0 = add_clause(V, [-X4,-X3,-X2]),
    _C1 = add_clause(V, [-X5,-X4,-X3]),
    _C2 = add_clause(V, [X6, X3, X2]),
    _C3 = add_clause(V, [X7, X6, X2]),
    _C4 = add_clause(V, [-X6, X3]),
    _C5 = add_clause(V, [X4, X2]),
    _C6 = add_clause(V, [X7, X4, -X2]),

    io:format("\nbefore\n"),
    print_clauses(V),

    io:format(" [~w/~w]\n", [X6,X3]),
    varc:subst(V, X6, X3),
    io:format("clause after\n"),    
    print_clauses(V),

    true = varc:bcp(V),
    Bs = varc:get_bindings(V,0),
    io:format("bindings@0 = ~w\n", [Bs]),
    Bs.

subst5() ->
    V = varc:new([{xref,true}]),
    X2 = varc:add_variable(V),
    X3 = varc:add_variable(V),
    X4 = varc:add_variable(V),
    X5 = varc:add_variable(V),
    X6 = varc:add_variable(V),
    X7 = varc:add_variable(V),

    _C0 = add_clause(V, [X4,-X3]),
    _C1 = add_clause(V, [X7,X3]),
    _C2 = add_clause(V, [X7,-X5]),
    _C3 = add_clause(V, [X3,X2]),
    _C4 = add_clause(V, [-X4,X6]),

    print_clauses(V),
    %% io:format(" [~w/~w]\n", [X7,X3]),
    %% varc:subst(V, X7, X3),
    io:format(" [~w/~w]\n", [X3,X7]),
    varc:subst(V, X3, X7),

    io:format("clause after\n"),
    print_clauses(V,true),
    true = varc:bcp(V),
    Bs = [X3,X4,X6] = lists:sort(varc:get_bindings(V,0)),
    io:format("bindings@0 = ~w\n", [Bs]),
    Bs.

subst6() ->
    V = varc:new([{xref,true}]),
    Y = varc:add_variable(V),
    B = varc:add_variable(V),
    C = varc:add_variable(V),
    X = varc:add_variable(V),
    A = varc:add_variable(V),

    _C0 = varc:add_clause(V, [A, X, B, Y, C]),
    _C1 = varc:add_clause(V, [A, -X, B, Y, C]),
    _C2 = varc:add_clause(V, [A, X, B, -C]),
    _C3 = varc:add_clause(V, [-A, B, -Y, C]),
    _C4 = varc:add_clause(V, [-A, B, -X, C]),
    _C5 = varc:add_clause(V, [A, -Y, B, -X, C]),

    print_clauses(V),

    io:format(" [~w/~w]\n", [X,Y]),
    varc:subst(V, X, Y),

    io:format("clause after\n"),
    print_clauses(V,true),
    ok.


watch1() ->
    V = varc:new(),
    X1 = varc:add_variable(V),
    X2 = varc:add_variable(V),
    X3 = varc:add_variable(V),
    X4 = varc:add_variable(V),
    X5 = varc:add_variable(V),

    C1 = add_clause(V, [X5,X4,X3,X2,X1]),
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
    C2 = add_clause(V, [Y3, Y2, Y1]),
    [Y1, Y2, Y3] = varc:get_clause(V, C2),

    0 = varc:clause_info(V, C2, watch0),
    2 = varc:clause_info(V, C2, watch1),

    Z3 = X4, Z2 = X3, Z1 = -X1,
    C3 = add_clause(V, [Z3,Z2,Z1]),
    [Z1,Z2,Z3] = varc:get_clause(V, C3),

    0 = varc:clause_info(V, C3, watch0),
    1 = varc:clause_info(V, C3, watch1),

    ok.

edge_list0() ->
    V = varc:new([{edge, true}]),
    true = varc:info(V, edge),

    A = varc:add_variable(V),
    B = varc:add_variable(V),

    {true,_C0} = varc:add_clause(V, [A, B]),
    
    %% eval should put in edges (A,B) ~A -> B, ~B -> A 
    [B] = varc:literal_info(V, -A, edge),
    [A] = varc:literal_info(V, -B, edge),
    ok.

edge_list1() ->
    V = varc:new([{edge, true}]),
    true = varc:info(V, edge),

    A = varc:add_variable(V),
    B = varc:add_variable(V),
    C = varc:add_variable(V),

    {true,_C0} = varc:add_clause(V, [A, B, C]),
    %% assume A,B are watched
    varc:bind(V, -A),
    true = varc:bcp(V),

    %% eval should put in edges (B,C) ~C -> B, ~B -> C
    [B] = varc:literal_info(V, -C, edge),
    [C] = varc:literal_info(V, -B, edge),
    ok.

edge_list2() ->
    V = varc:new([{edge, true}]),
    true = varc:info(V, edge),

    A = varc:add_variable(V),
    B = varc:add_variable(V),
    C = varc:add_variable(V),

    varc:bind(V, -C),

    {true,_C0} = varc:add_clause(V, [A, B, C]),

    %% eval should put in edges (A,B) ~A -> B, ~B -> A 
    [B] = varc:literal_info(V, -A, edge),
    [A] = varc:literal_info(V, -B, edge),
    ok.

edge_list3() ->
    V = varc:new([{edge, true}]),
    true = varc:info(V, edge),

    A = varc:add_variable(V),
    B = varc:add_variable(V),
    C = varc:add_variable(V),
    D = varc:add_variable(V),

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
    X1 = add_variable(V), varc:add_symbol(V, X1, <<"P(1,1)">>),
    X2 = add_variable(V), varc:add_symbol(V, X2, <<"P(1,2)">>),
    X3 = add_variable(V), varc:add_symbol(V, X3, <<"P(2,1)">>),
    X4 = add_variable(V), varc:add_symbol(V, X4, <<"P(2,2)">>),
    X5 = add_variable(V), varc:add_symbol(V, X5, <<"P(3,1)">>),
    X6 = add_variable(V), varc:add_symbol(V, X6, <<"P(3,2)">>),

    varc:add_clause(V, [X1,X2]),
    varc:add_clause(V, [X3, X4]),
    varc:add_clause(V, [X5, X6]),
    varc:add_clause(V, [-X1, -X3]),
    varc:add_clause(V, [-X1, -X5]),
    varc:add_clause(V, [-X3, -X5]),
    varc:add_clause(V, [-X2, -X4]),
    varc:add_clause(V, [-X2, -X6]),
    varc:add_clause(V, [-X4, -X6]),

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

%% Utils

get_watched(V) ->
    get_watched(V, lists:seq(2, varc:info(V, number_of_variables)+1)).

get_watched(V, [Xi|Xs]) ->
    Wi0 = varc:get_clauses(V, Xi, watch),
    Wi1 = varc:get_clauses(V, -Xi, watch),
    [{Xi,Wi0},{-Xi,Wi1}|get_watched(V, Xs)];
get_watched(_V, []) ->
    [].

print_clauses(V) ->
    print_clauses(V,false).
print_clauses(V,Raw) ->
    print_clauses_(V, Raw, varc:clauseset_first(V)).

print_clauses_(_V, _Raw, false) ->
    ok;
print_clauses_(V, Raw, I) ->
    Fs = varc:clause_info(V, I),
    io:format("~w: ~s ~w\n",
	      [I, format_clause_flags(Fs),
	       varc:get_clause(V,I,undefined,Raw)]),
    print_clauses_(V, Raw, varc:clauseset_next(V, I)).

dump_variables(V, List) ->
    lists:foreach(
      fun(X) ->
	      io:format("~w: ~p\n", [X, varc:variable_info(V, X)])
      end, List).

add_variable(V) ->
    varc:add_variable(V).

add_clause(V, Literals) ->
    add_clause(V, Literals, ?DELTA).

add_clause(V, Literals, Set) ->
    case varc:add_clause(V, Literals, Set) of
	{true,Ci} -> Ci;
	true -> true
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
