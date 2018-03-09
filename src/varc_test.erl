%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2015, Tony Rogvall
%%% @doc
%%%     Test varc
%%% @end
%%% Created : 21 Aug 2015 by Tony Rogvall <tony@rogvall.se>

-module(varc_test).

-compile(export_all).

-export([all/0]).

-define(TRUE,   1).
-define(FALSE, -1). %% 0 also works, mapped to -1 internally

all() ->
    test1(),
    test2(),
    test3(),
    %% test4(),
    or_eval(),
    or_clause(true),
    or_clause(false),
    or_conflict(),
    and_eval(),
    and_clause(true),
    and_clause(false),
    xor_eval(),
    xor_clause(true),
    xor_clause(false),
    order().

test1() ->
    V = varc:new(),
    X2 = varc:add_variable(V),
    X3 = varc:add_variable(V),
    X4 = varc:add_variable(V),
    X5 = varc:add_variable(V),
    
    C0 = varc:add_clause(V, 'and', [X2, X3, X4]),
    C1 = varc:add_clause(V, 'and', [X3, X4, X5]),

    R0 = varc:get_clause(V, C0),
    R0 = {'and', [X2, X3, X4]},

    R1 = varc:get_clause(V, C1),
    R1 = {'and', [X3, X4, X5]}.


test2() ->
    V = varc:new(),
    X2 = varc:add_variable(V),
    X3 = varc:add_variable(V),
    X4 = varc:add_variable(V),
    X5 = varc:add_variable(V),
    
    C0 = varc:add_clause(V, 'and', X2, X3, X4),
    C1 = varc:add_clause(V, 'and', X3, X4, X5),

    R0 = varc:get_clause(V, C0),
    R0 = {'and', [X2, X3, X4]},

    R1 = varc:get_clause(V, C1),
    R1 = {'and', [X3, X4, X5]}.
    
%%
%% Test clause / queue 
%%    
test3() ->
    V = varc:new(),
    X2 = varc:add_variable(V),
    X3 = varc:add_variable(V),
    X4 = varc:add_variable(V),
    X5 = varc:add_variable(V),
    X6 = varc:add_variable(V),
    X7 = varc:add_variable(V),
    X8 = varc:add_variable(V),

    C0 = varc:add_clause(V, 'and', X2, X3, X4),
    C1 = varc:add_clause(V, 'and', X3, X4, X5),
    C2 = varc:add_clause(V, 'and', X4, X5, X6, X7),
    C3 = varc:add_clause(V, 'and', X6, X7, X8),

    {'and',[X2,X3,X4]} = varc:get_clause(V, C0),
    {'and',[X3,X4,X5]} = varc:get_clause(V, C1),
    {'and',[X4,X5,X6,X7]} = varc:get_clause(V, C2),
    {'and',[X6,X7,X8]} = varc:get_clause(V, C3),

    true = lists:sort([C0]) =:= lists:sort(varc:get_clauses(V, X2)),
    true = lists:sort([C0,C1]) =:= lists:sort(varc:get_clauses(V, X3)),
    true = lists:sort([C0,C1,C2]) =:= lists:sort(varc:get_clauses(V, X4)),
    true = lists:sort([C1,C2]) =:= lists:sort(varc:get_clauses(V, X5)),
    true = lists:sort([C2,C3]) =:= lists:sort(varc:get_clauses(V, X6)),
    true = lists:sort([C2,C3]) =:= lists:sort(varc:get_clauses(V, X7)),
    true = lists:sort([C3]) =:= lists:sort(varc:get_clauses(V, X8)),

    true = lists:sort([C0,C1,C2,C3]) =:= lists:sort(varc:get_queue(V)),

    varc:del_clause(V, C3),

    true = lists:sort([C0,C1,C2]) =:= lists:sort(varc:get_queue(V)),

    io:format("X6 clauses = ~p\n", [varc:get_clauses(V, X6)]),
    io:format("X7 clauses = ~p\n", [varc:get_clauses(V, X7)]),
    io:format("X8 clauses = ~p\n", [varc:get_clauses(V, X8)]),

    true = lists:sort([]) =:= lists:sort(varc:get_clauses(V, X8)),
    true = lists:sort([C0,C1,C2]) =:= lists:sort(varc:get_queue(V)),
    true = varc:eval(V),
    true = lists:sort([]) =:= lists:sort(varc:get_queue(V)),
    true = varc:mark(V, 1),
    true = varc:put(V, X3, ?TRUE),
    true = lists:sort([C0,C1]) =:= lists:sort(varc:get_clauses(V, X3)),
    true = varc:put(V, X4, ?FALSE),
    true = lists:sort([C0,C1,C2]) =:= lists:sort(varc:get_queue(V)),

    {varc:get_bindings(V, 0), varc:get_number_of_clauses(V)}.

%%  Test various bindings ( only in bcp = false !!! )
test4() ->
    V = varc:new([{bcp, false}]),
    X2 = varc:add_variable(V),
    X3 = varc:add_variable(V),
    X4 = varc:add_variable(V),
    X5 = varc:add_variable(V),
    X6 = varc:add_variable(V),
    X7 = varc:add_variable(V),

    true = varc:mark(V, 1),
    varc:put(V, X2, X3),
    varc:put(V, X4, X5),
    varc:put(V, X6, X7),

    varc:put(V, X3, X5),
    varc:put(V, X5, X7),

    %% varc:put(V, X6, 1),

    varc:get_bindings(V, 0).


%% Test eval
or_eval() ->
    V = varc:new(),
    X2 = varc:add_variable(V),
    X3 = varc:add_variable(V),
    X4 = varc:add_variable(V),
    X5 = varc:add_variable(V),

    X2 = varc:get(V, X2),
    X3 = varc:get(V, X3),
    X4 = varc:get(V, X4),
    X5 = varc:get(V, X5),

    C0 = varc:add_clause(V, 'or', X2, ?TRUE, ?FALSE, ?TRUE, ?FALSE),
    C1 = varc:add_clause(V, 'or', X3, ?TRUE, ?TRUE, ?TRUE, ?TRUE),
    C2 = varc:add_clause(V, 'or', X4, ?FALSE, ?FALSE, ?FALSE, ?FALSE),
    C3 = varc:add_clause(V, 'or', X5, ?TRUE, ?FALSE, ?TRUE, ?FALSE, ?TRUE),
    io:format("clauses=~p\n", [[C0,C1,C2,C3]]),
    io:format("queue=~p\n", [varc:get_queue(V)]),
    true = varc:eval(V),

    V2 = varc:get(V, X2),
    io:format("X2 = ~w\n", [V2]),
    true = V2 =:= ?TRUE,

    V3 = varc:get(V, X3),
    io:format("X3 = ~w\n", [V3]),
    true = V3 =:= ?TRUE,

    V4 = varc:get(V, X4),
    io:format("X4 = ~w\n", [V4]),
    true = V4 =:= ?FALSE,

    V5 = varc:get(V, X5),
    io:format("X5 = ~w\n", [V5]),
    true = V5 =:= ?TRUE,

    io:format("Bindings = ~w\n", [varc:get_bindings(V,0)]),

    true.

or_clause(Bcp) ->
    V = varc:new([{bcp,Bcp}]),
    X2 = varc:add_variable(V),
    X3 = varc:add_variable(V),
    X4 = varc:add_variable(V),
    X5 = varc:add_variable(V),

    C0 = varc:add_clause(V, 'or', ?TRUE, ?FALSE, X2, ?FALSE, ?FALSE),
    C1 = varc:add_clause(V, 'or', ?FALSE, ?FALSE, X3, ?FALSE, ?FALSE),
    C2 = varc:add_clause(V, 'or', X4, ?FALSE, ?FALSE, X5, ?FALSE),

    io:format("or clauses=~p\n", [[C0,C1,C2]]),
    io:format("or queue=~p\n", [varc:get_queue(V)]),
    true = varc:eval(V),

    V2 = varc:get(V, X2),
    io:format("X2 = ~w\n", [V2]),
    true = V2 =:= ?TRUE,

    V3 = varc:get(V, X3),
    io:format("X3 = ~w\n", [V3]),
    true = V3 =:= ?FALSE,

    case varc:info(V,bcp) of
	false ->
	    V4 = varc:get(V, X4),
	    V5 = varc:get(V, X5),
	    io:format("X4 = ~w, X5 = ~w\n", [V4,V5]),
	    true = V4 =:= X5;
	true ->
	    V4 = varc:get(V, X4),
	    V5 = varc:get(V, X5),
	    true = V4 =:= X4,
	    true = V5 =:= X5
    end,
    io:format("or Bindings = ~w\n", [varc:get_bindings(V,0)]),
    io:format("info = ~w\n", [varc:get_info(V)]),
    true.

or_conflict() ->
    V = varc:new(),
    X2 = varc:add_variable(V),
    X3 = varc:add_variable(V),
    _X4 = varc:add_variable(V),
    _X5 = varc:add_variable(V),

    C0 = varc:add_clause(V, 'or', ?TRUE, ?FALSE, ?FALSE, X2, X3),
    C1 = varc:add_clause(V, 'or', ?TRUE, ?FALSE, ?FALSE, X2, -X3),
    io:format("clauses=~p\n", [[C0,C1]]),
    true = varc:eval(V),

    true = varc:mark(V, 1),
    true = varc:put(V, X2, ?TRUE),
    true = varc:eval(V),

    varc:undo(V),
    true = varc:put(V, X2, ?FALSE),
    false = varc:eval(V),    
    ok.


    
and_eval() ->
    V = varc:new(),
    X2 = varc:add_variable(V),
    X3 = varc:add_variable(V),
    X4 = varc:add_variable(V),
    X5 = varc:add_variable(V),

    4 = varc:get_number_of_variables(V),
    X2 = varc:get(V, X2),
    X3 = varc:get(V, X3),
    X4 = varc:get(V, X4),
    X5 = varc:get(V, X5),

    C0 = varc:add_clause(V, 'and', X2, ?TRUE, ?FALSE, ?TRUE, ?FALSE),
    C1 = varc:add_clause(V, 'and', X3, ?TRUE, ?TRUE, ?TRUE, ?TRUE),
    C2 = varc:add_clause(V, 'and', X4, ?FALSE, ?FALSE, ?FALSE, ?FALSE),
    C3 = varc:add_clause(V, 'and', X5, ?TRUE, ?FALSE, ?TRUE, ?FALSE, ?TRUE),
    io:format("clauses=~p\n", [[C0,C1,C2,C3]]),
    io:format("queue=~p\n", [varc:get_queue(V)]),
    true = varc:eval(V),
    
    V2 = varc:get(V, X2),
    io:format("X1 = ~w\n", [V2]),
    true = V2 =:= ?FALSE,

    V3 = varc:get(V, X3),
    io:format("X2 = ~w\n", [V3]),
    true = V3 =:= ?TRUE,

    V4 = varc:get(V, X4),
    io:format("X3 = ~w\n", [V4]),
    true = V4 =:= ?FALSE,

    V5 = varc:get(V, X5),
    io:format("X4 = ~w\n", [V5]),
    true = V5 =:= ?FALSE,

    io:format("Bindings = ~w\n", [varc:get_bindings(V,0)]),

    true.

and_clause(Bcp) ->
    V = varc:new([{bcp,Bcp}]),
    X2 = varc:add_variable(V),
    X3 = varc:add_variable(V),
    X4 = varc:add_variable(V),
    X5 = varc:add_variable(V),

    C0 = varc:add_clause(V, 'and', ?FALSE, ?TRUE, X2, ?TRUE, ?TRUE),
    C1 = varc:add_clause(V, 'and', ?TRUE, ?TRUE, X3, ?TRUE, ?TRUE),
    C2 = varc:add_clause(V, 'and', X4, ?TRUE, ?TRUE, X5, ?TRUE),
    io:format("and clauses=~p\n", [[C0,C1,C2]]),
    io:format("and queue=~p\n", [varc:get_queue(V)]),
    true = varc:eval(V),

    V2 = varc:get(V, X2),
    io:format("X2 = ~w\n", [V2]),
    true = V2 =:= ?FALSE,

    V3 = varc:get(V, X3),
    io:format("X3 = ~w\n", [V3]),
    true = V3 =:= ?TRUE,

    V4 = varc:get(V, X4),
    V5 = varc:get(V, X5),
    io:format("X4=~w, X5=~w\n", [V4,V5]),

    case varc:info(V,bcp) of
	false ->
	    true = V4 =:= X5;
	true ->
	    true = V4 =:= X4,
	    true = V5 =:= X5,
	    ok
    end,
    io:format("and Bindings = ~w\n", [varc:get_bindings(V,0)]),
    io:format("info = ~w\n", [varc:get_info(V)]),
    true.


xor_eval() ->
    V = varc:new(),
    X2 = varc:add_variable(V),
    X3 = varc:add_variable(V),
    X4 = varc:add_variable(V),
    X5 = varc:add_variable(V),

    C0 = varc:add_clause(V, 'xor', X2, ?TRUE, ?FALSE, ?TRUE, ?FALSE),
    {'xor', [X2,?TRUE,?FALSE,?TRUE,?FALSE]} = varc:get_clause(V, C0),
    [inqueue] = varc:get_clause_flags(V, C0),
    true = varc:eval(V),
    C1 = varc:add_clause(V, 'xor', X3, ?TRUE, ?TRUE, ?TRUE, ?TRUE),
    true = varc:eval(V),
    C2 = varc:add_clause(V, 'xor', X4, ?FALSE, ?FALSE, ?FALSE, ?FALSE),
    true = varc:eval(V),
    C3 = varc:add_clause(V, 'xor', X5, ?TRUE, ?FALSE, ?TRUE, ?FALSE, ?TRUE),
    true = varc:eval(V),
    io:format("clauses=~p\n", [[C0,C1,C2,C3]]),
    io:format("queue=~p\n", [varc:get_queue(V)]),
    
    V2 = varc:get(V, X2),
    io:format("X2 = ~w\n", [V2]),
    true = V2 =:= ?FALSE,

    V3 = varc:get(V, X3),
    io:format("X3 = ~w\n", [V3]),
    true = V3 =:= ?FALSE,

    V4 = varc:get(V, X4),
    io:format("X3 = ~w\n", [V4]),
    true = V4 =:= ?FALSE,

    V5 = varc:get(V, X5),
    io:format("X5 = ~w\n", [V5]),
    true = V5=:= ?TRUE,

    io:format("Bindings = ~w\n", [varc:get_bindings(V,0)]),

    true.


xor_clause(Bcp) ->
    V = varc:new([{bcp,Bcp}]),
    X2 = varc:add_variable(V),
    X3 = varc:add_variable(V),
    X4 = varc:add_variable(V),
    X5 = varc:add_variable(V),
    X6 = varc:add_variable(V),
    X7 = varc:add_variable(V),
    X8 = varc:add_variable(V),
    X9 = varc:add_variable(V),
    X10 = varc:add_variable(V),
    X11 = varc:add_variable(V),
    
    C0 = varc:add_clause(V, 'xor', ?TRUE, ?TRUE, X2, ?TRUE, ?FALSE),
    C1 = varc:add_clause(V, 'xor', ?FALSE, ?TRUE, X3, ?TRUE, ?TRUE),
    C2 = varc:add_clause(V, 'xor', X4, ?FALSE, X5, ?FALSE, ?FALSE),
    C3 = varc:add_clause(V, 'xor', X6, ?FALSE, X7, ?TRUE, ?FALSE),
    C4 = varc:add_clause(V, 'xor', ?FALSE, ?FALSE, X8, ?TRUE, X9, ?FALSE),
    C5 = varc:add_clause(V, 'xor', ?TRUE, ?FALSE, X10, ?TRUE, ?FALSE, X11),

    io:format("xor info = ~w\n", [varc:get_info(V)]),

    true = varc:eval(V),

    io:format("xor clauses=~p\n", [[C0,C1,C2,C3,C4,C5]]),
    io:format("xor queue=~p\n", [varc:get_queue(V)]),
    
    V2 = varc:get(V, X2),
    io:format("X2 = ~w\n", [V2]),
    true = V2 =:= ?TRUE,

    V3 = varc:get(V, X3),
    io:format("X3 = ~w\n", [V3]),
    true = V3 =:= ?TRUE,

    V4 = varc:get(V, X4),
    V5 = varc:get(V, X5),
    io:format("X4=~w, X5=~w\n", [V4,V5]),

    case varc:info(V, bcp) of
	false ->
	    true = V4 =:= V5;
	true ->
	    true = V4 =:= X4,
	    true = V5 =:= X5
    end,

    V6 = varc:get(V, X6),
    V7 = varc:get(V, X7),
    io:format("X6=~w, X7=~w\n", [V6,V7]),
    case varc:info(V, bcp) of
	false ->
	    true = V6 =:= -V7;
	true ->
	    true = V6 =:= X6,
	    true = V7 =:= X7,
	    ok
    end,

    V8 = varc:get(V, X8),
    V9 = varc:get(V, X9),
    io:format("X8=~w, X9=~w\n", [V8,V9]),

    case varc:info(V, bcp) of
	false ->
	    true = V8 =:= -V9;
	true ->
	    true = V8 =:= X8,
	    true = V9 =:= X9,
	    ok
    end,

    V10 = varc:get(V, X10),
    V11 = varc:get(V, X11),
    io:format("X10 = ~w, X11=~w\n", [V10,V11]),

    case varc:info(V, bcp) of
	false ->
	    true = V10 =:= V11;
	true ->
	    true = V10 =:= X10,
	    true = V11 =:= X11,
	    ok
    end,
    io:format("xor Bindings = ~w\n", [varc:get_bindings(V,0)]),
    io:format("xor end info = ~w\n", [varc:get_info(V)]),
    true.

order() ->    
    V = varc:new(),
    X2 = varc:add_variable(V),
    X3 = varc:add_variable(V),
    X4 = varc:add_variable(V),
    X5 = varc:add_variable(V),
    X6 = varc:add_variable(V),
    X7 = varc:add_variable(V),
    
    _C0 = varc:add_clause(V, 'and', [X2, X3, X4]),
    _C1 = varc:add_clause(V, 'and', [X3, X4, X5]),
    _C2 = varc:add_clause(V, 'or',  [X6, X2, X3]),
    _C3 = varc:add_clause(V, 'or',  [X7, X6, X2]),

    F1 = varc:order_sort(V, identity),
    [X2, X3, X4, X5, X6, X7] = varc:order_all(V),
    X2 = F1,

    F2 = varc:order_sort(V, identity, -1),
    [X7, X6, X5, X4, X3, X2] = varc:order_all(V),
    X2 = F2,

    F3 = varc:order_sort(V, random, 1001),
    Sort1 = varc:order_all(V),
    io:format("random,1001, F3=~w, Vs = ~p\n", [F3,Sort1]),

    F4 = varc:order_sort(V, random, 1003),
    Sort2 = varc:order_all(V),
    io:format("random,1003, F4=~w, Vs = ~p\n", [F4,Sort2]),

    F5 = varc:order_sort(V, occure, 1),
    io:format("occure>0, F5=~w, Vs = ~p\n", [F5,varc:order_all(V)]),
    
    F6 = varc:order_sort(V, occure, -1),
    io:format("occure<0, F6=~w, Vs = ~p\n", [F6,varc:order_all(V)]),

    F7 = varc:order_sort(V, depth, 1),
    io:format("depth>0, F7=~w, Vs = ~p\n", [F7,varc:order_all(V)]),

    F8 = varc:order_sort(V, depth, -1),
    io:format("depth<0, F8=~w, Vs = ~p\n", [F8,varc:order_all(V)]),

    F9 = varc:order_sort(V, occure_depth, 1),
    io:format("occure,depth>0, F9=~w, Vs = ~p\n", [F9,varc:order_all(V)]),
    F10 = varc:order_sort(V, occure_depth, -1),
    io:format("occure,depth<0, F10=~w, Vs = ~p\n", [F10,varc:order_all(V)]),

    F11 = varc:order_sort(V, depth_occure, 1),
    io:format("depth,occure>0, F11=~w, Vs = ~p\n", [F11,varc:order_all(V)]),
    F12 = varc:order_sort(V, depth_occure, -1),
    io:format("depth,occure<0, F12=~w, Vs = ~p\n", [F12,varc:order_all(V)]),

    ok.
