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
      end, [test1, test2, test3,
	    or_simplify, or_eval,
	    watch1,
	    edge_list0,edge_list1, edge_list2, edge_list3,
	    subst0a, subst0b, subst0c, subst0d, 
	    subst1, subst2, subst3, subst4, subst5, subst6
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

    true = varc:eval(V),
    true = varc:set_level(V, 1),
    true = varc:bind(V, X2),
    true = varc:bind(V, X3),
    {varc:get_bindings(V, 1), varc:get_number_of_clauses(V)}.

%% Test all clause simplifications
or_simplify() ->
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
    C3 = add_clause(V, [X2,X3,X2,X3,X4,?F]),
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
or_eval() ->
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
    true = varc:eval(V),

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
or_eval_bindings() ->
    V = varc:new(),
    X2 = add_variable(V),
    X3 = add_variable(V),
    X4 = add_variable(V),
    X5 = add_variable(V),

    varc:set_level(V, 1),
    add_clause(V, [-X2, -X3, -X4]),
    add_clause(V, [-X2, -X3,  X5]),
    add_clause(V, [-X2,  X3, -X4]),
    add_clause(V, [-X2,  X3,  X4]),
    io:format("Bindings@0 = ~w\n", [varc:get_bindings(V,0)]),
    io:format("Bindings@1 = ~w\n", [varc:get_bindings(V,1)]),
    io:format("watched = ~w\n", [get_watched(V)]),
    
    print_clauses(V),
    io:format("2/1\n", []),
    varc:bind(V, X2),
    true = varc:eval(V),
    io:format("Bindings@1 = ~w\n", [varc:get_bindings(V,1)]),
    io:format("watched = ~w\n", [get_watched(V)]),
    print_clauses(V),

    varc:set_level(V, 2),
    add_clause(V, [-X2,  X3,  X4, -X5]),
    io:format("watched = ~w\n", [get_watched(V)]),
    io:format("3/1\n", []),
    varc:bind(V, X3),
    true = varc:eval(V),
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


order() ->
    V = varc:new(),
    X1 = varc:add_variable(V),
    X2 = varc:add_variable(V),
    X3 = varc:add_variable(V),
    X4 = varc:add_variable(V),
    X5 = varc:add_variable(V),
    X6 = varc:add_variable(V),
    
    _C0 = add_clause(V, [-X1, -X2, -X3]),
    _C1 = add_clause(V, [-X2, -X3, -X4]),
    _C2 = add_clause(V, [X5, X1, X2]),
    _C3 = add_clause(V, [X6, X5, X1]),

    %% d(-X1)=1, d(X1)=2, d(-X2)=2 d(X2)=1
    %% d(-X3)=2, d(X3)=0, d(-X4)=1, d(X4)=0
    %% d(-X5)=0, d(X5)=2, d(-X6)=0, d(X6)=1

    ok = varc:order_sort(V, identity, undefined, 0),
    [X1, X2, X3, X4, X5, X6] = varc:order_all(V),

    ok = varc:order_sort(V, identity, undefined, 0),
    ok = varc:order_sort_first(V, [X5, X6]),
    [X5, X6, X1, X2, X3, X4] = varc:order_all(V),

    ok = varc:order_sort(V, identity, undefined, 0),
    ok = varc:order_sort_last(V, [X2, X1]),  %% reversed
    [X3, X4, X5, X6, X1, X2] = varc:order_all(V),

    ok = varc:order_sort(V, identity, undefined, 0),
    ok = varc:order_sort_first(V, [X5, X6]),
    ok = varc:order_sort_last(V, [X2, X1]),  %% reversed
    [X6, X5, X4, X3, X1, X2] = varc:order_all(V),

    ok = varc:order_sort(V, random, undefined, 1001),
    Sort1 = varc:order_all(V),
    io:format("random,1001, Vs = ~p\n", [Sort1]),

    ok = varc:order_sort(V, random, undefined, 1003),
    Sort2 = varc:order_all(V),
    io:format("random,1003, Vs = ~p\n", [Sort2]),

    ok = varc:order_sort(V, '+degree', undefined, 0),
    io:format("+degree, Vs = ~p\n", [varc:order_all(V)]),
    
    ok = varc:order_sort(V, '-degree', undefined, 0),
    io:format("-degree, Vs = ~p\n", [varc:order_all(V)]),

    ok = varc:order_sort(V, '+rank', undefined, 0),
    io:format("rank>0, Vs = ~p\n", [varc:order_all(V)]),

    ok = varc:order_sort(V, '-rank', undefined, 0),
    io:format("rank<0, Vs = ~p\n", [varc:order_all(V)]),

%%    ok = varc:order_sort(V, '+degree', '+rank', 0),
%%    io:format("occur,depth>0, Vs = ~p\n", [varc:order_all(V)]),
%%    ok = varc:order_sort(V, '-degree', '-rank, 0),
%%    io:format("occur,depth<0, Vs = ~p\n", [varc:order_all(V)]),

%%    ok = varc:order_sort(V, '+rank', '+degree', 0),
%%    io:format("depth,occur>0, Vs = ~p\n", [varc:order_all(V)]),

%%    ok = varc:order_sort(V, '-rank', '-degree', 0),
%%    io:format("depth,occur<0, Vs = ~p\n", [varc:order_all(V)]),
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

    true = varc:eval(V),
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
    true = varc:eval(V),
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
    4 = varc:clause_info(V, C1, watch0),
    3 = varc:clause_info(V, C1, watch1),

    %% bind X4, move wp 0
    varc:set_level(V, 1),
    varc:bind(V, -X4),
    true = varc:eval(V),

    4 = varc:clause_info(V, C1, watch0),
    0 = varc:clause_info(V, C1, watch1),

    %% bind -X3, not watched, watch points should stay the same
    varc:set_level(V, 2),
    varc:bind(V, -X3),
    true = varc:eval(V),

    4 = varc:clause_info(V, C1, watch0),
    0 = varc:clause_info(V, C1, watch1),

    varc:set_level(V, 3),
    varc:bind(V, -X1),
    true = varc:eval(V),

    4 = varc:clause_info(V, C1, watch0),
    1 = varc:clause_info(V, C1, watch1),

    varc:set_level(V, 4),
    varc:bind(V, -X5),
    true = varc:eval(V),

    4 = varc:clause_info(V, C1, watch0),
    1 = varc:clause_info(V, C1, watch1),

    ?T = varc:value(V, X2),

    {C1,_Pos=1,_Lev=4} = varc:implication_clause(V, X2),

    %% add clauses under the above bindings
    Y3 = -X5, Y2 = -X4, Y1 = -X2, 
    C2 = add_clause(V, [Y3, Y2, Y1]),
    [Y1, Y2, Y3] = varc:get_clause(V, C2),

    2 = varc:clause_info(V, C2, watch0),
    0 = varc:clause_info(V, C2, watch1),

    Z3 = X4, Z2 = X3, Z1 = -X1,
    C3 = add_clause(V, [Z3,Z2,Z1]),
    [Z1,Z2,Z3] = varc:get_clause(V, C3),

    0 = varc:clause_info(V, C3, watch0),
    1 = varc:clause_info(V, C3, watch1),

    ok.

edge_list0() ->
    V = varc:new([{edge_list, true}]),
    true = varc:info(V, edge_list),

    A = varc:add_variable(V),
    B = varc:add_variable(V),

    {true,C0} = varc:add_clause(V, [A, B]),
    
    %% eval should put in edges (A,B) ~A -> B, ~B -> A 
    [{C0,B}] = varc:literal_info(V, -A, edge_list),
    [{C0,A}] = varc:literal_info(V, -B, edge_list),
    ok.

edge_list1() ->
    V = varc:new([{edge_list, true}]),
    true = varc:info(V, edge_list),

    A = varc:add_variable(V),
    B = varc:add_variable(V),
    C = varc:add_variable(V),

    {true,C0} = varc:add_clause(V, [A, B, C]),

    varc:bind(V, -C),
    true = varc:eval(V),

    %% eval should put in edges (A,B) ~A -> B, ~B -> A 
    [{C0,B}] = varc:literal_info(V, -A, edge_list),
    [{C0,A}] = varc:literal_info(V, -B, edge_list),
    ok.

edge_list2() ->
    V = varc:new([{edge_list, true}]),
    true = varc:info(V, edge_list),

    A = varc:add_variable(V),
    B = varc:add_variable(V),
    C = varc:add_variable(V),

    varc:bind(V, -C),

    {true,C0} = varc:add_clause(V, [A, B, C]),

    %% eval should put in edges (A,B) ~A -> B, ~B -> A 
    [{C0,B}] = varc:literal_info(V, -A, edge_list),
    [{C0,A}] = varc:literal_info(V, -B, edge_list),
    ok.

edge_list3() ->
    V = varc:new([{edge_list, true}]),
    true = varc:info(V, edge_list),

    A = varc:add_variable(V),
    B = varc:add_variable(V),
    C = varc:add_variable(V),
    D = varc:add_variable(V),

    {true,C0} = varc:add_clause(V, [A, B]),
    {true,C1} = varc:add_clause(V, [A, C]),
    {true,C2} = varc:add_clause(V, [A, -D]),

    %% eval should put in edges (A,B) -A -> B, -B -> A 
    %% eval should put in edges (A,C) -A -> C, -C -> A
    %% eval should put in edges (A,-D) -A -> -D, D -> A

    R1 = lists:sort([{C0,B},{C2,-D},{C1,C}]),
    R1 = lists:sort(varc:literal_info(V, -A, edge_list)),
    [{C0,A}] = varc:literal_info(V, -B, edge_list),
    [{C1,A}] = varc:literal_info(V, -C, edge_list),
    [{C2,A}] = varc:literal_info(V, D, edge_list),

    true = varc:bind(V, -A),
    true = varc:eval(V),
    ?T = varc:value(V, B),
    ?T = varc:value(V, C),
    ?F = varc:value(V, D),
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
    print_clauses_(V, Raw, varc:clause_first(V)).

print_clauses_(_V, _Raw, false) ->
    ok;
print_clauses_(V, Raw, I) ->
    Fs = varc:clause_info(V, I),
    io:format("~w: ~s ~w\n",
	      [I, format_clause_flags(Fs),
	       varc:get_clause(V,I,undefined,Raw)]),
    print_clauses_(V, Raw, varc:clause_next(V, I)).

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
    
