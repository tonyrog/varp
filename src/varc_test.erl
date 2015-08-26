%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2015, Tony Rogvall
%%% @doc
%%%     Test varc
%%% @end
%%% Created : 21 Aug 2015 by Tony Rogvall <tony@rogvall.se>

-module(varc_test).


-compile(export_all).

test1() ->
    V = varc:new(),
    X1 = varc:add_variable(V),
    X2 = varc:add_variable(V),
    X3 = varc:add_variable(V),
    X4 = varc:add_variable(V),
    
    C1 = varc:add_clause(V, 'and', [X1, X2, X3]),
    C2 = varc:add_clause(V, 'and', [X2, X3, X4]),

    R1 = varc:get_clause(V, C1),
    R1 = {'and', [X1, X2, X3]},

    R2 = varc:get_clause(V, C2),
    R2 = {'and', [X2, X3, X4]}.


test2() ->
    V = varc:new(),
    X1 = varc:add_variable(V),
    X2 = varc:add_variable(V),
    X3 = varc:add_variable(V),
    X4 = varc:add_variable(V),
    
    C1 = varc:add_clause(V, 'and', X1, X2, X3),
    C2 = varc:add_clause(V, 'and', X2, X3, X4),

    R1 = varc:get_clause(V, C1),
    R1 = {'and', [X1, X2, X3]},

    R2 = varc:get_clause(V, C2),
    R2 = {'and', [X2, X3, X4]}.
    
%%
%% Test clause / queue 
%%    
test3() ->
    V = varc:new(),
    X1 = varc:add_variable(V),
    X2 = varc:add_variable(V),
    X3 = varc:add_variable(V),
    X4 = varc:add_variable(V),
    X5 = varc:add_variable(V),
    X6 = varc:add_variable(V),
    X7 = varc:add_variable(V),

    C1 = varc:add_clause(V, 'and', X1, X2, X3),
    C2 = varc:add_clause(V, 'and', X2, X3, X4),
    C3 = varc:add_clause(V, 'and', X3, X4, X5, X6),
    C4 = varc:add_clause(V, 'and', X5, X6, X7),

    {'and',[X1,X2,X3]} = varc:get_clause(V, C1),
    {'and',[X2,X3,X4]} = varc:get_clause(V, C2),
    {'and',[X3,X4,X5,X6]} = varc:get_clause(V, C3),
    {'and',[X5,X6,X7]} = varc:get_clause(V, C4),

    true = lists:sort([C1]) =:= lists:sort(varc:get_clauses(V, X1)),
    true = lists:sort([C1,C2]) =:= lists:sort(varc:get_clauses(V, X2)),
    true = lists:sort([C1,C2,C3]) =:= lists:sort(varc:get_clauses(V, X3)),
    true = lists:sort([C2,C3]) =:= lists:sort(varc:get_clauses(V, X4)),
    true = lists:sort([C3,C4]) =:= lists:sort(varc:get_clauses(V, X5)),
    true = lists:sort([C3,C4]) =:= lists:sort(varc:get_clauses(V, X6)),
    true = lists:sort([C4]) =:= lists:sort(varc:get_clauses(V, X7)),

    true = lists:sort([C1,C2,C3,C4]) =:= lists:sort(varc:get_queue(V)),

    varc:del_clause(V, C4),

    true = lists:sort([]) =:= lists:sort(varc:get_clauses(V, X7)),
    true = lists:sort([C1,C2,C3]) =:= lists:sort(varc:get_queue(V)),
    true = varc:eval(V),
    true = lists:sort([]) =:= lists:sort(varc:get_queue(V)),
    true = varc:mark(V, 0),
    true = varc:put(V, X2, true),
    true = lists:sort([C1,C2]) =:= lists:sort(varc:get_clauses(V, X2)),
    true = varc:put(V, X3, false),
    true = lists:sort([C1,C2,C3]) =:= lists:sort(varc:get_queue(V)),

    {varc:get_bindings(V, 0), varc:get_number_of_clauses(V)}.

%%  Test various bindings
test4() ->
    V = varc:new(),
    X1 = varc:add_variable(V),
    X2 = varc:add_variable(V),
    X3 = varc:add_variable(V),
    X4 = varc:add_variable(V),
    X5 = varc:add_variable(V),
    X6 = varc:add_variable(V),

    true = varc:mark(V, 0),
    varc:put(V, X1, X2),
    varc:put(V, X3, X4),
    varc:put(V, X5, X6),

    varc:put(V, X2, X4),
    varc:put(V, X4, X6),

    %% varc:put(V, X6, 1),

    varc:get_bindings(V, 0).


%% Test eval
test_or_eval() ->
    V = varc:new(),
    X1 = varc:add_variable(V),
    X2 = varc:add_variable(V),
    X3 = varc:add_variable(V),
    X4 = varc:add_variable(V),

    X1 = varc:get(V, X1),
    X2 = varc:get(V, X2),
    X3 = varc:get(V, X3),
    X4 = varc:get(V, X4),

    C1 = varc:add_clause(V, 'or', X1, true, false, true, false),
    C2 = varc:add_clause(V, 'or', X2, true, true, true, true),
    C3 = varc:add_clause(V, 'or', X3, false, false, false, false),
    C4 = varc:add_clause(V, 'or', X4, true, false, true, false, true),
    io:format("clauses=~p\n", [[C1,C2,C3,C4]]),
    io:format("queue=~p\n", [varc:get_queue(V)]),
    true = varc:eval(V),

    V1 = varc:get(V, X1),
    io:format("X1 = ~w\n", [V1]),
    true = V1 =:= true,

    V2 = varc:get(V, X2),
    io:format("X2 = ~w\n", [V2]),
    true = V2 =:= true,

    V3 = varc:get(V, X3),
    io:format("X3 = ~w\n", [V3]),
    true = V3 =:= false,

    V4 = varc:get(V, X4),
    io:format("X4 = ~w\n", [V4]),
    true = V4 =:= true,

    io:format("Bindings = ~w\n", [varc:get_bindings(V,0)]),

    true.

test_or_clause() ->
    V = varc:new(),
    X1 = varc:add_variable(V),
    X2 = varc:add_variable(V),
    X3 = varc:add_variable(V),
    X4 = varc:add_variable(V),

    C1 = varc:add_clause(V, 'or', true, false, X1, false, false),
    C2 = varc:add_clause(V, 'or', false, false, X2, false, false),
    C3 = varc:add_clause(V, 'or', X3, false, false, X4, false),
    io:format("clauses=~p\n", [[C1,C2,C3]]),
    io:format("queue=~p\n", [varc:get_queue(V)]),
    true = varc:eval(V),

    V1 = varc:get(V, X1),
    io:format("X1 = ~w\n", [V1]),
    true = V1 =:= true,

    V2 = varc:get(V, X2),
    io:format("X2 = ~w\n", [V2]),
    true = V2 =:= false,

    V3 = varc:get(V, X3),
    V4 = varc:get(V, X4),
    io:format("X3 = ~w, X4 = ~w\n", [V3,V4]),
    true = V3 =:= X4,

    io:format("Bindings = ~w\n", [varc:get_bindings(V,0)]),

    true.
    
test_and_eval() ->
    V = varc:new(),
    X1 = varc:add_variable(V),
    X2 = varc:add_variable(V),
    X3 = varc:add_variable(V),
    X4 = varc:add_variable(V),

    4 = varc:get_number_of_variables(V),
    X1 = varc:get(V, X1),
    X2 = varc:get(V, X2),
    X3 = varc:get(V, X3),
    X4 = varc:get(V, X4),

    C1 = varc:add_clause(V, 'and', X1, true, false, true, false),
    C2 = varc:add_clause(V, 'and', X2, true, true, true, true),
    C3 = varc:add_clause(V, 'and', X3, false, false, false, false),
    C4 = varc:add_clause(V, 'and', X4, true, false, true, false, true),
    io:format("clauses=~p\n", [[C1,C2,C3,C4]]),
    io:format("queue=~p\n", [varc:get_queue(V)]),
    true = varc:eval(V),
    
    V1 = varc:get(V, X1),
    io:format("X1 = ~w\n", [V1]),
    true = V1 =:= false,

    V2 = varc:get(V, X2),
    io:format("X2 = ~w\n", [V2]),
    true = V2 =:= true,

    V3 = varc:get(V, X3),
    io:format("X3 = ~w\n", [V3]),
    true = V3 =:= false,

    V4 = varc:get(V, X4),
    io:format("X4 = ~w\n", [V4]),
    true = V4 =:= false,

    io:format("Bindings = ~w\n", [varc:get_bindings(V,0)]),

    true.

test_and_clause() ->
    V = varc:new(),
    X1 = varc:add_variable(V),
    X2 = varc:add_variable(V),
    X3 = varc:add_variable(V),
    X4 = varc:add_variable(V),

    C1 = varc:add_clause(V, 'and', false, true, X1, true, true),
    C2 = varc:add_clause(V, 'and', true, true, X2, true, true),
    C3 = varc:add_clause(V, 'and', X3, true, true, X4, true),
    io:format("clauses=~p\n", [[C1,C2,C3]]),
    io:format("queue=~p\n", [varc:get_queue(V)]),
    true = varc:eval(V),

    V1 = varc:get(V, X1),
    io:format("X1 = ~w\n", [V1]),
    true = V1 =:= false,

    V2 = varc:get(V, X2),
    io:format("X2 = ~w\n", [V2]),
    true = V2 =:= true,

    V3 = varc:get(V, X3),
    V4 = varc:get(V, X4),
    io:format("X3 = ~w, X4 = ~w\n", [V3,V4]),
    true = V3 =:= X4,

    io:format("Bindings = ~w\n", [varc:get_bindings(V,0)]),

    true.


test_xor_eval() ->
    V = varc:new(),
    X1 = varc:add_variable(V),
    X2 = varc:add_variable(V),
    X3 = varc:add_variable(V),
    X4 = varc:add_variable(V),
    
    C1 = varc:add_clause(V, 'xor', X1, true, false, true, false),
    {'xor', [X1,true,false,true,false]} = varc:get_clause(V, C1),
    [inqueue] = varc:get_clause_flags(V, C1),

    true = varc:eval(V),
    C2 = varc:add_clause(V, 'xor', X2, true, true, true, true),
    true = varc:eval(V),
    C3 = varc:add_clause(V, 'xor', X3, false, false, false, false),
    true = varc:eval(V),
    C4 = varc:add_clause(V, 'xor', X4, true, false, true, false, true),
    true = varc:eval(V),
    io:format("clauses=~p\n", [[C1,C2,C3,C4]]),
    io:format("queue=~p\n", [varc:get_queue(V)]),
    
    V1 = varc:get(V, X1),
    io:format("X1 = ~w\n", [V1]),
    true = V1 =:= false,

    V2 = varc:get(V, X2),
    io:format("X2 = ~w\n", [V2]),
    true = V2 =:= false,

    V3 = varc:get(V, X3),
    io:format("X3 = ~w\n", [V3]),
    true = V3 =:= false,

    V4 = varc:get(V, X4),
    io:format("X4 = ~w\n", [V4]),
    true = V4 =:= true,

    io:format("Bindings = ~w\n", [varc:get_bindings(V,0)]),

    true.


test_xor_clause() ->
    V = varc:new(),
    X1 = varc:add_variable(V),
    X2 = varc:add_variable(V),
    X3 = varc:add_variable(V),
    X4 = varc:add_variable(V),
    X5 = varc:add_variable(V),
    X6 = varc:add_variable(V),
    
    C1 = varc:add_clause(V, 'xor', true, true, X1, true, false),
    C2 = varc:add_clause(V, 'xor', false, true, X2, true, true),
    C3 = varc:add_clause(V, 'xor', X3, false, X4, false, false),
    C4 = varc:add_clause(V, 'xor', X5, false, X6, true, false),
    true = varc:eval(V),

    io:format("clauses=~p\n", [[C1,C2,C3,C4]]),
    io:format("queue=~p\n", [varc:get_queue(V)]),
    
    V1 = varc:get(V, X1),
    io:format("X1 = ~w\n", [V1]),
    true = V1 =:= true,

    V2 = varc:get(V, X2),
    io:format("X2 = ~w\n", [V2]),
    true = V2 =:= true,

    V3 = varc:get(V, X3),
    V4 = varc:get(V, X4),
    io:format("X3 = ~w, X4=~w\n", [V3,V4]),
    true = V3 =:= V4,

    V5 = varc:get(V, X5),
    V6 = varc:get(V, X6),
    io:format("X5 = ~w, X6=~w\n", [V5,V6]),
    true = V5 =:= -V6,

    io:format("Bindings = ~w\n", [varc:get_bindings(V,0)]),

    true.


test_order() ->    
    V = varc:new(),
    X1 = varc:add_variable(V),
    X2 = varc:add_variable(V),
    X3 = varc:add_variable(V),
    X4 = varc:add_variable(V),
    X5 = varc:add_variable(V),
    X6 = varc:add_variable(V),

    varc:order_sort(V, id),
    [X1, X2, X3, X4, X5, X6] = varc:order_all(V),

    varc:order_sort(V, id, -1),
    [X6, X5, X4, X3, X2, X1] = varc:order_all(V),

    varc:order_sort(V, random, 1001),
    Sort1 = varc:order_all(V),

    varc:order_sort(V, random, 1001),
    Sort1 = varc:order_all(V),

    ok.

%% Test CNF file

cnf(F) ->
    case dimacs:load(F) of
	Error={error,_Reason} ->
	    io:format("~s: error: ~p\n", [F,_Reason]),
	    Error;
	_Cnf = {cnf,{_NVars,_NClauses,CLs}} ->
	    V = varc:new(),
	    _Map = cnf_clauses(V, CLs, #{}),
	    varc:order_sort(V, random, 0),
	    M = varc:sat(V,1),
	    io:format("conflicts = ~w\n", [get(conflicts)]),
	    M
    end.

	    
cnf_clauses(V, [C|Cs], Map) ->
    Map1 = cnf_clause(V, C, Map, []),
    cnf_clauses(V, Cs, Map1);
cnf_clauses(_V, [], Map) ->
    Map.

cnf_clause(V, [{'not',Var}|Ls], Map, Acc) ->
    {Vi, Map1} = cnf_var(V, Var, Map),
    cnf_clause(V, Ls, Map1, [-Vi|Acc]);
cnf_clause(V, [Var|Ls], Map, Acc) ->
    {Vi, Map1} = cnf_var(V, Var, Map),
    cnf_clause(V, Ls, Map1, [Vi|Acc]);
cnf_clause(V, [], Map, Acc) ->
    varc:add_clause(V, 'or', [true|Acc]),
    Map.

cnf_var(V, Var, Map) ->
    case maps:find(Var, Map) of
	{ok,Vi} -> {Vi, Map};
	error ->
	    Vi = varc:add_variable(V),
	    Map1 = maps:put(Var, Vi, Map),
	    {Vi, Map1}
    end.

%% Test pigeon formula

%% generate the pigeon hole formula
%% n pigeons in n-1 holes
%%
pigeon(N) ->
    {ok,{_Defs,F}} = varp:file(filename:join([code:priv_dir(varp), "varp", "pigeon.varp"])),
    F1 = form:expand(F, [{n,N}]),
    {Cs,_} = cnf:clauses(F1),
    V = varc:new(),
    pigeon_clauses(V, Cs, #{}),
    varc:order_sort(V, random, 1000),
    M = varc:sat(V),
    io:format("conflicts = ~w\n", [get(conflicts)]),
    M.

pigeon_clauses(V, [C|Cs], Map) ->
    Map1 = pigeon_clause(V, C, Map, []),
    pigeon_clauses(V, Cs, Map1);
pigeon_clauses(_V, [], Map) ->
    Map.

pigeon_clause(V, [{'not',Var}|Ls], Map, Acc) ->
    {Vi, Map1} = pigeon_var(V, Var, Map),
    pigeon_clause(V, Ls, Map1, [-Vi|Acc]);
pigeon_clause(V, [Var|Ls], Map, Acc) ->
    {Vi, Map1} = pigeon_var(V, Var, Map),
    pigeon_clause(V, Ls, Map1, [Vi|Acc]);
pigeon_clause(V, [], Map, Acc) ->
    varc:add_clause(V, 'or', [true|Acc]),
    Map.

pigeon_var(V, Var, Map) ->
    case maps:find(Var, Map) of
	{ok,Vi} -> {Vi, Map};
	error ->
	    Vi = varc:add_variable(V),
	    Map1 = maps:put(Var, Vi, Map),
	    {Vi, Map1}
    end.


