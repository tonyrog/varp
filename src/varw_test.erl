%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2019, Tony Rogvall
%%% @doc
%%%    Test of varw
%%% @end
%%% Created : 14 Mar 2019 by Tony Rogvall <tony@rogvall.se>

-module(varw_test).

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

    ok.


test1() ->
    V = varc:new(),
    X2 = add_variable(V),
    X3 = add_variable(V),
    X4 = add_variable(V),
    Ls0 = lists:usort([X2, X3, X4]),
    C0 = add_clause(V, Ls0),
    Ls0 = get_clause(V, C0),
    
    Ls1 = lists:usort([X2,-X3,X4]),
    C1 = add_clause(V, Ls1),
    Ls1 = get_clause(V, C1),
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
    true = varc:mark(V, 1),
    true = varc:put(V, X3, ?TRUE),
    true = varc:put(V, X4, ?FALSE),
    {varc:get_bindings(V, 1), varc:get_number_of_clauses(V)}.

%% Test all clause simplifications
or_simplify() ->
    V = varc:new(),
    X2 = add_variable(V),
    X3 = add_variable(V),
    X4 = add_variable(V),
    X5 = add_variable(V),
    C0 = add_clause(V, [X2,X3,X4,X5]),
    C1 = add_clause(V, [X5,X4,X3,X2]),
    C2 = add_clause(V, [X2,X2,X2,X2,X2]),
    C23 =add_clause(V, [X2,X3,X3,X3,X2]),
    C3 = add_clause(V, [X2,X3,X2,X3,X4,?FALSE]),
    C4 = add_clause(V, [X2,X3,X2,X3,X4]),
    C5 = add_clause(V, [X2,?TRUE,X3,?FALSE,X4,?TRUE,X4,?TRUE, X5,?FALSE]),
    C6 = add_clause(V, [X2,?TRUE,X3,?FALSE,-X3,?TRUE,X3,?TRUE,-X3,?FALSE,X4]),

    [X2,X3,X4,X5] = get_clause(V, C0),
    [X2,X3,X4,X5] = get_clause(V, C1),
    [X2] = get_clause(V, C2),
    [X2,X3] = get_clause(V, C23),
    [X2,X3,X4] = get_clause(V, C3),
    [X2,X3,X4] = get_clause(V, C4),
    [?TRUE,X2,X3,X4,X5] = get_clause(V, C5),
    [?TRUE,X2,X4] = get_clause(V, C6),
    ok.

%% Test eval
or_eval() ->
    V = varc:new(),
    X2 = add_variable(V),
    X3 = add_variable(V),
    X4 = add_variable(V),
    X5 = add_variable(V),

    0 = varc:get(V, X2),
    0 = varc:get(V, X3),
    0 = varc:get(V, X4),
    0 = varc:get(V, X5),

    varc:mark(V, 1),
    C0 = add_clause(V, [X2, ?FALSE, ?FALSE]),
    C1 = add_clause(V, [X3, ?TRUE, ?TRUE, ?TRUE]),
    C2 = add_clause(V, [-X4, ?FALSE, ?FALSE, ?FALSE]),
    C3 = add_clause(V, [X5, ?FALSE, ?TRUE, ?FALSE, ?TRUE]),
    io:format("clauses=~p\n", [[C0,C1,C2,C3]]),
    io:format("queue=~p\n", [varc:get_queue(V)]),
    true = varc:eval(V),

    V2 = varc:get(V, X2),
    io:format("X2 = ~w\n", [V2]),
    true = V2 =:= ?TRUE,

    V3 = varc:get(V, X3),
    io:format("X3 = ~w\n", [V3]),
    true = V3 =:= 0,

    V4 = varc:get(V, X4),
    io:format("X4 = ~w\n", [V4]),
    true = V4 =:= ?FALSE,

    V5 = varc:get(V, X5),
    io:format("X5 = ~w\n", [V5]),
    true = V5 =:= 0,

    io:format("Bindings = ~w\n", [varc:get_nbindings(V,4)]),

    true.


add_variable(V) ->
    varc:add_variable(V).

add_clause(V, Literals) ->
    varc:add_clause(V, 'or', [?TRUE|Literals]).

get_clause(V, ClauseIndex) ->
    {'or',[?TRUE|Literals]} = varc:get_clause(V, ClauseIndex),
    lists:sort(Literals).
