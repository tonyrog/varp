%%
%% UNIT TESTS
%%
-module(varc_test).

-include_lib("eunit/include/eunit.hrl").

-compile(export_all).

%%
%% Test 
%%   V = W, W = 1 => V = 1
%%
basic_test() ->
    Vp = varc:new(),
    V = varc:add_variable(Vp),
    ?assert(varc:get(Vp,V) =:= V),
    W = varc:add_variable(Vp),
    ?assert(varc:get(Vp,W) =:= W),
    varc:put(Vp, V, W),
    ?assert(varc:is_equal(Vp, V, W)),
    ?assert(varc:get(Vp,V) =:= W),
    ?assert(varc:get(Vp,W) =:= W),
    varc:put(Vp,W,1),
    ?assert(varc:get(Vp, V) =:= 1).

test_graph() ->
    Vp = varc:new(),
    A = varc:add_variable(Vp),
    B = varc:add_variable(Vp),
    C = varc:add_variable(Vp),
    D = varc:add_variable(Vp),
    varc:add_clause(Vp, 'or', 1, A, B),
    varc:add_clause(Vp, 'or', 1, C, D),
    varc:mark(Vp, 20),
    varc:put(Vp, A, 0),
    varc:eval(Vp),
    get_graph(Vp, 20).

get_graph(Vp, Mark) ->
    Bs = varc:get_bindings(Vp, Mark, true),
    get_edges(Vp, Bs, []).

get_edges(Vp, [{Var,Value,-1,-1}|Bs], Es) ->
    [{Var,Value} | get_edges(Vp, Bs, Es)];
get_edges(Vp, [{Var,Value,Li,Cix}|Bs], Es) ->
    {'or',[1|Ls]} = varc:get_clause(Vp, Cix),
    B = lists:nth(Li, Ls),
    Es1 = [{A,B} || A <- Ls],
    get_edges(Vp, Bs, Es++Es1);
get_edges(_Vp, [], Es) ->
    Es.
    
