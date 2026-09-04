%%% SAT engine (c_src/varp_nif.c) self test plus a few direct checks.
-module(varp_nif_tests).

-include_lib("eunit/include/eunit.hrl").

nif_library_test_() ->
    {timeout, 900, fun() -> ?assertEqual(ok, varp_nif_test:all()) end}.

new_test() ->
    Vp = varp_nif:new(#{}),
    ?assert(is_reference(Vp)),
    ?assertEqual(0, varp:get_number_of_variables(Vp)).

add_variables_test() ->
    Vp = varp_nif:new(#{}),
    ?assertEqual(1, varp_nif:add_variable(Vp)),
    ?assertEqual({2,11}, varp_nif:add_variables(Vp, 10)),
    ?assertEqual(11, varp:get_number_of_variables(Vp)).

%% variables are "used" by default since the symbol handling moved
%% into the nif
default_is_used_test() ->
    Vp = varp_nif:new(#{}),
    {1,3} = varp_nif:add_variables(Vp, 3),
    ?assert(varp_nif:isused(Vp, 1)),
    Vp2 = varp_nif:new(#{}),
    {1,3} = varp_nif:add_variables(Vp2, 3, _IsAtom=false, _IsUsed=false),
    ?assertNot(varp_nif:isused(Vp2, 1)).

symbol_test() ->
    Vp = varp_nif:new(#{}),
    X = varp_nif:add_variable(Vp, true),
    varp_nif:add_symbol(Vp, {<<"A">>,[]}, X, bool),
    ?assertEqual({bool,X}, varp_nif:find_symbol(Vp, {<<"A">>,[]})),
    ?assertEqual(false, varp_nif:find_symbol(Vp, {<<"B">>,[]})).

clause_and_bcp_test() ->
    Vp = varp_nif:new(#{}),
    {1,2} = varp_nif:add_variables(Vp, 2),
    %% (1) and (-1 or 2)  =>  1 and 2 must be true
    varp_circuit:clause(Vp, [1]),
    varp_circuit:clause(Vp, [-1,2]),
    ?assertEqual(true, varp_nif:bcp(Vp)),
    ?assertEqual(true, varp_nif:bound(Vp, 1)),
    ?assertEqual(true, varp_nif:bound(Vp, 2)).

%% adding a clause that is already falsified is reported as a throw
contradiction_test() ->
    Vp = varp_nif:new(#{}),
    {1,1} = varp_nif:add_variables(Vp, 1),
    ?assertEqual(true, varp_circuit:clause(Vp, [1])),
    ?assertThrow(contradiction, varp_circuit:clause(Vp, [-1])),
    %% a fresh instance, x and (y or z) and (not y) and (not z)
    Vp2 = varp_nif:new(#{}),
    {1,3} = varp_nif:add_variables(Vp2, 3),
    varp_circuit:clause(Vp2, [2,3]),
    varp_circuit:clause(Vp2, [-2]),
    varp_circuit:clause(Vp2, [-3]),
    ?assertEqual(false, varp_nif:bcp(Vp2)).

%% every configuration flag must have a well defined default, an
%% uninitialised one shows up here as a badarg or a random value
default_option_test() ->
    Vp = varp_nif:new(#{}),
    lists:foreach(
      fun({Key,Expected}) ->
	      ?assertEqual({Key,Expected}, {Key,varp_nif:getopt(Vp,Key)})
      end,
      [{xref,false},{hash,false},{icase,false},{bcp2,false},
       {use_phase,false},{seed,0},{qtype,lifo}]).
