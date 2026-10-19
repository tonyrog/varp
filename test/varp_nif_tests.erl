%%% SAT engine (c_src/varp_nif.c) self test plus a few direct checks.
-module(varp_nif_tests).

-include_lib("eunit/include/eunit.hrl").
-include("varp.hrl").

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
      [{xref,false},{hash,false},{icase,false},{decay,0.0},
       {use_phase,false},{seed,0},{qtype,lifo}]).

%% a clone is a copy of the variables, the clauses, the level 0
%% bindings, the symbols, the options and the variable order, and
%% searching in the clone leaves the original alone
clone_test() ->
    Vp = varp_nif:new(#{}),
    {1,4} = varp_nif:add_variables(Vp, 4),
    varp_nif:add_symbol(Vp, {<<"A">>,[]}, 1, bool),
    varp_circuit:clause(Vp, [1,2]),
    varp_circuit:clause(Vp, [-1,3]),
    varp_circuit:clause(Vp, [-2,3]),
    varp_circuit:clause(Vp, [4]),       %% a level 0 binding
    ?assertEqual(true, varp_nif:bcp(Vp)),
    ok = varp_nif:setopt(Vp, partial, true),
    varp_nif:order_first(Vp, [3]),
    Order = varp:order_all(Vp),
    ?assertEqual(3, hd(Order)),
    W = varp_nif:clone(Vp, #{level => 0}),
    ?assertEqual(varp:get_number_of_variables(Vp), varp:get_number_of_variables(W)),
    ?assertEqual(varp_nif:getstat(Vp, number_of_clauses), varp_nif:getstat(W, number_of_clauses)),
    %% the clone continues the counters, so a stat difference stays positive
    ?assertEqual(varp_nif:getstat(Vp, bcp_counter), varp_nif:getstat(W, bcp_counter)),
    ?assertEqual(1, varp_nif:getstat(W, number_of_bound_variables)),
    ?assertEqual(true, varp_nif:value(W, 4)),
    ?assertEqual(0, varp_nif:variable_info(W, 4, level)),
    ?assertEqual({bool,1}, varp_nif:find_symbol(W, {<<"A">>,[]})),
    ?assertEqual(true, varp_nif:getopt(W, partial)),
    ?assertEqual(Order, varp:order_all(W)),
    %% a bad clone option is refused, not ignored
    ?assertError(badarg, varp_nif:clone(Vp, #{nonsense => 1})),
    %% search in the clone: 1 forces 3, the original keeps 1 unbound
    varp_nif:push(W),
    ?assertEqual(true, varp_nif:bind(W, 1)),
    ?assertEqual(true, varp_nif:bcp(W)),
    ?assertEqual(true, varp_nif:value(W, 3)),
    ?assertEqual(undefined, varp_nif:value(Vp, 1)),
    ?assertEqual(0, varp_nif:level(Vp)).

%% clones of a built formula solve it in processes of their own and
%% find the same model as the original
clone_solve_test_() ->
    {timeout, 60,
     fun() ->
	     {ok, Text} = file:read_file(filename:join(varp_tc:formula_dir("varp"), "send_more.varp")),
	     {continue, [], Bs} =
		 varp_tc:quiet(fun() -> varp_tc:run(binary_to_list(Text), [{satisfy,[]}]) end),
	     Vp = Bs#bs.vp,
	     [{varp_backjump, Param}] = varp:parse_do([{backjump,[]}]),
	     Self = self(),
	     [spawn_link(fun() ->
				 W = varp_nif:clone(Vp, #{level => 0, set => [alpha,beta,gamma,delta]}),
				 R = varp_tc:quiet(fun() -> varp_backjump:run(Bs#bs{vp = W}, Param) end),
				 Self ! {clone, I, R}
			 end) || I <- [1,2]],
	     Clones = [receive {clone, I, R} -> R end || I <- [1,2]],
	     ?assertEqual(0, varp_nif:level(Vp)),
	     {continue, [Model], _} = varp_tc:quiet(fun() -> varp_backjump:run(Bs, Param) end),
	     [?assertEqual({continue, [Model]}, {R, Ms}) || {R, Ms, _} <- Clones]
     end}.
