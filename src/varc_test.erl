%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2015, Tony Rogvall
%%% @doc
%%%     Test varc
%%% @end
%%% Created : 21 Aug 2015 by Tony Rogvall <tony@rogvall.se>

-module(varc_test).

-compile(export_all).

-export([all/0]).

all() ->
    test1(),
    test2(),
    test3(),
    %% test4(),
    or_eval(),
    or_clause(),
    or_conflict(),
    and_eval(),
    and_clause(),
    xor_eval(),
    xor_clause(),
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
    true = varc:mark(V, 0),
    true = varc:put(V, X3, true),
    true = lists:sort([C0,C1]) =:= lists:sort(varc:get_clauses(V, X3)),
    true = varc:put(V, X4, false),
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

    true = varc:mark(V, 0),
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

    C0 = varc:add_clause(V, 'or', X2, true, false, true, false),
    C1 = varc:add_clause(V, 'or', X3, true, true, true, true),
    C2 = varc:add_clause(V, 'or', X4, false, false, false, false),
    C3 = varc:add_clause(V, 'or', X5, true, false, true, false, true),
    io:format("clauses=~p\n", [[C0,C1,C2,C3]]),
    io:format("queue=~p\n", [varc:get_queue(V)]),
    true = varc:eval(V),

    V2 = varc:get(V, X2),
    io:format("X2 = ~w\n", [V2]),
    true = V2 =:= true,

    V3 = varc:get(V, X3),
    io:format("X3 = ~w\n", [V3]),
    true = V3 =:= true,

    V4 = varc:get(V, X4),
    io:format("X4 = ~w\n", [V4]),
    true = V4 =:= false,

    V5 = varc:get(V, X5),
    io:format("X5 = ~w\n", [V5]),
    true = V5 =:= true,

    io:format("Bindings = ~w\n", [varc:get_bindings(V,0)]),

    true.

or_clause() ->
    V = varc:new(),
    X2 = varc:add_variable(V),
    X3 = varc:add_variable(V),
    X4 = varc:add_variable(V),
    X5 = varc:add_variable(V),

    C0 = varc:add_clause(V, 'or', true, false, X2, false, false),
    C1 = varc:add_clause(V, 'or', false, false, X3, false, false),
    C2 = varc:add_clause(V, 'or', X4, false, false, X5, false),
    io:format("clauses=~p\n", [[C0,C1,C2]]),
    io:format("queue=~p\n", [varc:get_queue(V)]),
    true = varc:eval(V),

    V2 = varc:get(V, X2),
    io:format("X2 = ~w\n", [V2]),
    true = V2 =:= true,

    V3 = varc:get(V, X3),
    io:format("X3 = ~w\n", [V3]),
    true = V3 =:= false,

    %% bcp = false
    %% V4 = varc:get(V, X4),
    %% V5 = varc:get(V, X5),
    %% io:format("X3 = ~w, X4 = ~w\n", [V4,V5]),
    %% true = V4 =:= X5,

    io:format("Bindings = ~w\n", [varc:get_bindings(V,0)]),

    true.

or_conflict() ->
    V = varc:new(),
    X2 = varc:add_variable(V),
    X3 = varc:add_variable(V),
    _X4 = varc:add_variable(V),
    _X5 = varc:add_variable(V),

    C0 = varc:add_clause(V, 'or', true, false, false, X2, X3),
    C1 = varc:add_clause(V, 'or', true, false, false, X2, -X3),
    io:format("clauses=~p\n", [[C0,C1]]),
    true = varc:eval(V),

    true = varc:mark(V, 0),
    true = varc:put(V, X2, true),
    true = varc:eval(V),

    varc:undo(V),
    true = varc:put(V, X2, false),
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

    C0 = varc:add_clause(V, 'and', X2, true, false, true, false),
    C1 = varc:add_clause(V, 'and', X3, true, true, true, true),
    C2 = varc:add_clause(V, 'and', X4, false, false, false, false),
    C3 = varc:add_clause(V, 'and', X5, true, false, true, false, true),
    io:format("clauses=~p\n", [[C0,C1,C2,C3]]),
    io:format("queue=~p\n", [varc:get_queue(V)]),
    true = varc:eval(V),
    
    V2 = varc:get(V, X2),
    io:format("X1 = ~w\n", [V2]),
    true = V2 =:= false,

    V3 = varc:get(V, X3),
    io:format("X2 = ~w\n", [V3]),
    true = V3 =:= true,

    V4 = varc:get(V, X4),
    io:format("X3 = ~w\n", [V4]),
    true = V4 =:= false,

    V5 = varc:get(V, X5),
    io:format("X4 = ~w\n", [V5]),
    true = V5 =:= false,

    io:format("Bindings = ~w\n", [varc:get_bindings(V,0)]),

    true.

and_clause() ->
    V = varc:new(),
    X2 = varc:add_variable(V),
    X3 = varc:add_variable(V),
    X4 = varc:add_variable(V),
    X5 = varc:add_variable(V),

    C0 = varc:add_clause(V, 'and', false, true, X2, true, true),
    C1 = varc:add_clause(V, 'and', true, true, X3, true, true),
    C2 = varc:add_clause(V, 'and', X4, true, true, X5, true),
    io:format("clauses=~p\n", [[C0,C1,C2]]),
    io:format("queue=~p\n", [varc:get_queue(V)]),
    true = varc:eval(V),

    V2 = varc:get(V, X2),
    io:format("X2 = ~w\n", [V2]),
    true = V2 =:= false,

    V3 = varc:get(V, X3),
    io:format("X2 = ~w\n", [V3]),
    true = V3 =:= true,

    %% bcp = true
    %% V4 = varc:get(V, X4),
    %% V5 = varc:get(V, X5),
    %% io:format("X4 = ~w, X5 = ~w\n", [V4,V5]),
    %% true = V4 =:= X5,

    io:format("Bindings = ~w\n", [varc:get_bindings(V,0)]),

    true.


xor_eval() ->
    V = varc:new(),
    X2 = varc:add_variable(V),
    X3 = varc:add_variable(V),
    X4 = varc:add_variable(V),
    X5 = varc:add_variable(V),

    C0 = varc:add_clause(V, 'xor', X2, true, false, true, false),
    {'xor', [X2,true,false,true,false]} = varc:get_clause(V, C0),
    [inqueue] = varc:get_clause_flags(V, C0),
    true = varc:eval(V),
    C1 = varc:add_clause(V, 'xor', X3, true, true, true, true),
    true = varc:eval(V),
    C2 = varc:add_clause(V, 'xor', X4, false, false, false, false),
    true = varc:eval(V),
    C3 = varc:add_clause(V, 'xor', X5, true, false, true, false, true),
    true = varc:eval(V),
    io:format("clauses=~p\n", [[C0,C1,C2,C3]]),
    io:format("queue=~p\n", [varc:get_queue(V)]),
    
    V2 = varc:get(V, X2),
    io:format("X2 = ~w\n", [V2]),
    true = V2 =:= false,

    V3 = varc:get(V, X3),
    io:format("X3 = ~w\n", [V3]),
    true = V3 =:= false,

    V4 = varc:get(V, X4),
    io:format("X3 = ~w\n", [V4]),
    true = V4 =:= false,

    V5 = varc:get(V, X5),
    io:format("X5 = ~w\n", [V5]),
    true = V5=:= true,

    io:format("Bindings = ~w\n", [varc:get_bindings(V,0)]),

    true.


xor_clause() ->
    V = varc:new(),
    X2 = varc:add_variable(V),
    X3 = varc:add_variable(V),
    X4 = varc:add_variable(V),
    X5 = varc:add_variable(V),
    X6 = varc:add_variable(V),
    X7 = varc:add_variable(V),
    
    C0 = varc:add_clause(V, 'xor', true, true, X2, true, false),
    C1 = varc:add_clause(V, 'xor', false, true, X3, true, true),
    C2 = varc:add_clause(V, 'xor', X4, false, X5, false, false),
    C3 = varc:add_clause(V, 'xor', X6, false, X7, true, false),
    true = varc:eval(V),

    io:format("clauses=~p\n", [[C0,C1,C2,C3]]),
    io:format("queue=~p\n", [varc:get_queue(V)]),
    
    V2 = varc:get(V, X2),
    io:format("X2 = ~w\n", [V2]),
    true = V2 =:= true,

    V3 = varc:get(V, X3),
    io:format("X3 = ~w\n", [V3]),
    true = V3 =:= true,

%%  bcp = false
%%    V4 = varc:get(V, X4),
%%    V5 = varc:get(V, X5),
%%    io:format("X4 = ~w, X5=~w\n", [V4,V5]),
%%    true = V4 =:= V5,

%%  bcp = false
%%    V6 = varc:get(V, X6),
%%    V7 = varc:get(V, X7),
%%    io:format("X5 = ~w, X6=~w\n", [V6,V7]),
%%    true = V6 =:= -V7,

    io:format("Bindings = ~w\n", [varc:get_bindings(V,0)]),

    true.

order() ->    
    V = varc:new(),
    X2 = varc:add_variable(V),
    X3 = varc:add_variable(V),
    X4 = varc:add_variable(V),
    X5 = varc:add_variable(V),
    X6 = varc:add_variable(V),
    X7 = varc:add_variable(V),

    varc:order_sort(V, id),
    [X2, X3, X4, X5, X6, X7] = varc:order_all(V),

    varc:order_sort(V, id, -1),
    [X7, X6, X5, X4, X3, X2] = varc:order_all(V),

    varc:order_sort(V, random, 1001),
    Sort1 = varc:order_all(V),

    varc:order_sort(V, random, 1001),
    Sort1 = varc:order_all(V),

    ok.

%% test saturate
saturate() ->
    V = varc:new(),
    X1 = varc:add_variable(V),
    X2 = varc:add_variable(V),
    X3 = varc:add_variable(V),
    X4 = varc:add_variable(V),
    X5 = varc:add_variable(V),
    X6 = varc:add_variable(V),
    X7 = varc:add_variable(V),
    X8 = varc:add_variable(V),

    _C0 = varc:add_clause(V, 'and', false, X1, X2),
    _C1 = varc:add_clause(V, 'or',  true,  X1, X2),
    %% X1 /= X2
    _C2 = varc:add_clause(V, 'and', X3, true, X4),
    _C3 = varc:add_clause(V, 'or',  X3, false, X4),
    %% X3 == X4
    _C4 = varc:add_clause(V, 'xor', true, X5, X6),
    %% X5 =/= X6
    _C5 = varc:add_clause(V, 'xor', false, X7, X8),
    %% X7 == X8
    true = varc:eval(V),
    true = varc:saturate(V, 1),

    L1 = varc:get(V, X1),
    L1 = -varc:get(V, X2),
    
    L2 = varc:get(V, X3),
    L2 = varc:get(V, X4),

    L3 = varc:get(V, X5),
    L3 = -varc:get(V, X6),

    L4 = varc:get(V, X7),
    L4 = varc:get(V, X8),
    ok.
    

%% Test CNF file

cnf(File) ->
    case cnf_load(File) of
	{ok,V} ->
	    varc:order_sort(V, random, 0),
	    M = varc:sat(V,1),
	    io:format("conflicts = ~w\n", [get(conflicts)]),
	    M
    end.

cnf_s(File) ->
    case cnf_load(File) of
	{ok,V} ->
	    varc:order_sort(V, random, 0),
	    varc:saturate(V,1)
    end.

factor_load() ->
    {ok,Vp} = cnf_load(filename:join([code:priv_dir(varp),"dimacs",
				      "factoring_109_1753.dimacs"])),
    {'or',[true|As]} = varc:get_clause(Vp,0),
    {'or',[true|Bs]} = varc:get_clause(Vp,1),
    varc:add_clause(Vp, reg, lists:reverse(As)), %% maybe reverse
    varc:add_clause(Vp, reg, lists:reverse(Bs)), %% maybe reverse
    Vp.
    

cnf_load(File) ->
    case varp_dimacs:load(File) of
	Error={error,_Reason} ->
	    io:format("~s: error: ~p\n", [File,_Reason]),
	    Error;
	_Cnf = {cnf,{_NVars,_NClauses,CLs}} ->
	    V = varc:new(),
	    _Map = cnf_clauses(V, CLs, #{}),
	    {ok,V}
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
    V = pigeon_load(N),
    varc:order_sort(V, random, 1000), %% seed=1000 !!!!
    M = varc:sat(V),
    io:format("conflicts = ~w\n", [get(conflicts)]),
    M.

pigeon_load(N) ->
    {ok,{_Defs,_Decls,_Code,F}} = 
	varp:file(filename:join([code:priv_dir(varp), "varp", "pigeon.varp"])),
    F1 = varp_expand:formula(F, [{"n",N}]),
    {Cs,_} = varp_cnf:clauses(F1),
    V = varc:new(),
    pigeon_clauses(V, Cs, #{}),
    V.

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
