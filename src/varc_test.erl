%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2019, Tony Rogvall
%%% @doc
%%%    Test of varc
%%% @end
%%% Created : 14 Mar 2019 by Tony Rogvall <tony@rogvall.se>

-module(varc_test).

-compile(export_all).

-export([all/0]).

-define(TRUE,   1).
-define(FALSE, -1). %% 0 also works, mapped to -1 internally

all() ->
    test1(),
    test2(),
    test3(),

    or_simplify(),
    or_eval(),

    watch1(),

    subst1(),
    subst2(),

    ok.

test1() ->
    V = varc:new(),
    X2 = add_variable(V),
    X3 = add_variable(V),
    X4 = add_variable(V),
    Ls0 = lists:usort([X2, X3, X4]),
    C0 = add_clause(V, Ls0),
    io:format("C0=~w\n", [C0]),
    Ls0 = get_clause(V, C0),
    io:format("Ls0=~w\n", [Ls0]),
    
    Ls1 = lists:usort([X2,-X3,X4]),
    C1 = add_clause(V, Ls1),
    io:format("C0=~w\n", [C1]),
    Ls1 = get_clause(V, C1),
    io:format("Ls0=~w\n", [Ls1]),
    ok.
    
test2() ->
    V = varc:new(),
    X2 = add_variable(V),
    X3 = add_variable(V),
    X4 = add_variable(V),
    X5 = add_variable(V),
    
    C0 = add_clause(V, [X2, X3, X4]),
    C1 = add_clause(V, [X3, X4, X5]),

    [X2, X3, X4] = get_clause(V, C0),
    [X3, X4, X5] = get_clause(V, C1),
    ok.

%%
%% Test clause / queue 
%%    
test3() ->
    V = varc:new(),
    X2 = add_variable(V),
    X3 = add_variable(V),
    X4 = add_variable(V),
    X5 = add_variable(V),
    X6 = add_variable(V),
    X7 = add_variable(V),
    X8 = add_variable(V),

    C0 = add_clause(V, [X2, X3, X4]),
    C1 = add_clause(V, [X3, X4, X5]),
    C2 = add_clause(V, [X4, X5, X6, X7]),
    C3 = add_clause(V, [X6, X7, X8]),

    [X2,X3,X4] = get_clause(V, C0),
    [X3,X4,X5] = get_clause(V, C1),
    [X4,X5,X6,X7] = get_clause(V, C2),
    [X6,X7,X8] = get_clause(V, C3),

    true = lists:sort([C0]) =:= lists:sort(varc:get_clauses(V, X2)),

    true = lists:sort([C0,C1]) =:= lists:sort(varc:get_clauses(V, X3)),
    true = lists:sort([C0,C1,C2]) =:= lists:sort(varc:get_clauses(V, X4)),
    true = lists:sort([C1,C2]) =:= lists:sort(varc:get_clauses(V, X5)),
    true = lists:sort([C2,C3]) =:= lists:sort(varc:get_clauses(V, X6)),
    true = lists:sort([C2,C3]) =:= lists:sort(varc:get_clauses(V, X7)),
    true = lists:sort([C3]) =:= lists:sort(varc:get_clauses(V, X8)),

    io:format("X6 clauses = ~p\n", [varc:get_clauses(V, X6)]),
    io:format("X7 clauses = ~p\n", [varc:get_clauses(V, X7)]),
    io:format("X8 clauses = ~p\n", [varc:get_clauses(V, X8)]),

    true = varc:eval(V),
    true = varc:set_level(V, 1),
    true = varc:bind(V, X3),
    true = varc:bind(V, X4),
    {varc:get_bindings(V, 1), varc:get_number_of_clauses(V)}.

%% Test all clause simplifications
or_simplify() ->
    V = varc:new(),
    X20 = add_variable(V),
    X2 = add_variable(V),
    X3 = add_variable(V),
    X4 = add_variable(V),
    X5 = add_variable(V),
    C0 = add_clause(V, [X2,X3,X4,X5]),
    C1 = add_clause(V, [X5,X4,X3,X2]),
    C20 = add_clause(V, [X20,X20,X20,X20,X20]),
    C23 =add_clause(V, [X2,X3,X3,X3,X2]),
    C3 = add_clause(V, [X2,X3,X2,X3,X4,?FALSE]),
    C4 = add_clause(V, [X2,X3,X2,X3,X4]),
    C5 = add_clause(V, [X2,?TRUE,X3,?FALSE,X4,?TRUE,X4,?TRUE, X5,?FALSE]),
    C6 = add_clause(V, [X2,?TRUE,X3,?FALSE,-X3,?TRUE,X3,?TRUE,-X3,?FALSE,X4]),

    [X2,X3,X4,X5] = get_clause(V, C0),
    [X2,X3,X4,X5] = get_clause(V, C1),
    C20 = true,
    %% [X2] = get_clause(V, C2),
    [X2,X3] = get_clause(V, C23),
    [X2,X3,X4] = get_clause(V, C3),
    [X2,X3,X4] = get_clause(V, C4),
    C5 = true,
    C6 = true,
    %% [?TRUE,X2,X3,X4,X5] = get_clause(V, C5),
    %% [?TRUE,X2,X4] = get_clause(V, C6),
    ok.

%% Test eval
or_eval() ->
    V = varc:new(),
    X2 = add_variable(V),
    X3 = add_variable(V),
    X4 = add_variable(V),
    X5 = add_variable(V),

    0 = varc:value(V, X2),
    0 = varc:value(V, X3),
    0 = varc:value(V, X4),
    0 = varc:value(V, X5),

    varc:set_level(V, 1),
    C0 = add_clause(V, [X2, ?FALSE, ?FALSE]),
    C1 = add_clause(V, [X3, ?TRUE, ?TRUE, ?TRUE]),
    C2 = add_clause(V, [-X4, ?FALSE, ?FALSE, ?FALSE]),
    C3 = add_clause(V, [X5, ?FALSE, ?TRUE, ?FALSE, ?TRUE]),
    io:format("clauses=~p\n", [[C0,C1,C2,C3]]),
    print_clauses(V),

    io:format("queue=~p\n", [varc:get_queue(V)]),
    true = varc:eval(V),

    V2 = varc:value(V, X2),
    io:format("X2 = ~w\n", [V2]),
    true = V2 =:= ?TRUE,

    V3 = varc:value(V, X3),
    io:format("X3 = ~w\n", [V3]),
    true = V3 =:= 0,

    V4 = varc:value(V, X4),
    io:format("X4 = ~w\n", [V4]),
    true = V4 =:= ?FALSE,

    V5 = varc:value(V, X5),
    io:format("X5 = ~w\n", [V5]),
    true = V5 =:= 0,

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
    X2 = varc:add_variable(V),
    X3 = varc:add_variable(V),
    X4 = varc:add_variable(V),
    X5 = varc:add_variable(V),
    X6 = varc:add_variable(V),
    X7 = varc:add_variable(V),
    
    _C0 = add_clause(V, [-X2, -X3, -X4]),
    _C1 = add_clause(V, [-X3, -X4, -X5]),
    _C2 = add_clause(V, [X6, X2, X3]),
    _C3 = add_clause(V, [X7, X6, X2]),

    ok = varc:order_sort(V, identity, undefined, 0),
    [X2, X3, X4, X5, X6, X7] = varc:order_all(V),

    ok = varc:order_sort(V, identity, undefined, 0),
    ok = varc:order_sort_first(V, [X6, X7]),
    [X6, X7, X2, X3, X4, X5] = varc:order_all(V),

    ok = varc:order_sort(V, identity, undefined, 0),
    ok = varc:order_sort_last(V, [X3, X2]),  %% reversed
    [X4, X5, X6, X7, X2, X3] = varc:order_all(V),

    ok = varc:order_sort(V, identity, undefined, 0),
    ok = varc:order_sort_first(V, [X6, X7]),
    ok = varc:order_sort_last(V, [X3, X2]),  %% reversed
    [X6, X7, X4, X5, X2, X3] = varc:order_all(V),

    ok = varc:order_sort(V, random, undefined, 1001),
    Sort1 = varc:order_all(V),
    io:format("random,1001, Vs = ~p\n", [Sort1]),

    ok = varc:order_sort(V, random, undefined, 1003),
    Sort2 = varc:order_all(V),
    io:format("random,1003, Vs = ~p\n", [Sort2]),

    ok = varc:order_sort(V, '+degree', undefined, 0),
    io:format("+degree, Vs = ~p\n", [varc:order_all(V)]),
    
    ok = varc:order_sort(V, '-degree', undefined, 0),
    io:format("-degreer, Vs = ~p\n", [varc:order_all(V)]),

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
 

subst1() ->
    V = varc:new(),
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

    io:format("subst1: Clause before\n"),
    print_clauses(V),

    io:format(" [~w/~w]\n", [X6,X3]),
    varc:subst(V, X6, X3),
    io:format("subst1: Clause after\n"),    
    print_clauses(V),

    true = varc:eval(V),
    Bs = varc:get_bindings(V,0),
    io:format("bindings@0 = ~w\n", [Bs]),
    Bs.

subst2() ->
    V = varc:new(),
    X2 = varc:add_variable(V),
    X3 = varc:add_variable(V),
    X4 = varc:add_variable(V),
    X5 = varc:add_variable(V),
    X6 = varc:add_variable(V),
    X7 = varc:add_variable(V),

    io:format("subst2: Clause before\n"),    
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

    io:format("subst2: Clause after\n"),
    print_clauses(V,true),
    true = varc:eval(V),
    Bs = varc:get_bindings(V,0),
    io:format("bindings@0 = ~w\n", [Bs]),
    Bs.

watch1() ->
    V = varc:new(),
    X2 = varc:add_variable(V),
    X3 = varc:add_variable(V),
    X4 = varc:add_variable(V),
    X5 = varc:add_variable(V),
    X6 = varc:add_variable(V),

    C1 = add_clause(V, [X6,X5,X4,X3,X2]),
    [X6,X5,X4,X3,X2] = varc:get_clause(V, C1),

    %% initial watch points are set in the end!
    4 = varc:clause_info(V, C1, watch0),
    3 = varc:clause_info(V, C1, watch1),

    %% bind X3, move wp 0
    varc:set_level(V, 1),
    varc:bind(V, -X3),
    true = varc:eval(V),

    4 = varc:clause_info(V, C1, watch0),
    0 = varc:clause_info(V, C1, watch1),

    %% bind -X5, not watched, watch points should stay the same
    varc:set_level(V, 2),
    varc:bind(V, -X5),
    true = varc:eval(V),

    4 = varc:clause_info(V, C1, watch0),
    0 = varc:clause_info(V, C1, watch1),

    varc:set_level(V, 3),
    varc:bind(V, -X2),
    true = varc:eval(V),

    2 = varc:clause_info(V, C1, watch0),
    0 = varc:clause_info(V, C1, watch1),

    varc:set_level(V, 4),
    varc:bind(V, -X6),
    true = varc:eval(V),

    2 = varc:clause_info(V, C1, watch0),
    0 = varc:clause_info(V, C1, watch1),
    ?TRUE = varc:value(V, X4),

    {C1,_Pos=2,_Lev=4} = varc:implication_clause(V, X4),

    %% add clauses under the above bindings
    Y3 = -X6, Y2 = -X5, Y1 = -X3, 
    C2 = add_clause(V, [Y3, Y2, Y1]),
    [Y3, Y2, Y1] = varc:get_clause(V, C2),

    0 = varc:clause_info(V, C2, watch0),
    1 = varc:clause_info(V, C2, watch1),

    Z3 = X5, Z2 = X4, Z1 = -X2,
    C3 = add_clause(V, [Z3,Z2,Z1]),
    [Z3,Z2,Z1] = varc:get_clause(V, C3),

    1 = varc:clause_info(V, C3, watch0),
    2 = varc:clause_info(V, C3, watch1),

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
    case varc:add_clause(V, Literals) of
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
    
