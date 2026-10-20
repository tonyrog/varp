%%% @doc
%%%    Tests of the backjump restart strategy (--restart): the parsing
%%%    of the step chain and the steps running at every restart.
%%% @end
-module(varp_backjump_tests).

-include_lib("eunit/include/eunit.hrl").

steps_test() ->
    ?assertEqual([], varp_backjump:restart_steps("")),
    [{varp_order, P1}, skip, {varp_saturate, P2}] =
	varp_backjump:restart_steps("order --sort rank,random | skip | saturate -k 1 -l 1 --timeout 1"),
    ?assertEqual([rank, random], maps:get(sort, P1)),
    ?assertEqual(-1, maps:get(seed, P1)),
    ?assertEqual(1, maps:get(level, P2)),
    ?assertEqual(1, maps:get(laps, P2)),
    ?assertEqual(1.0, maps:get(timeout, P2)),
    %% inside a search saturate reports no models and does not warn
    ?assertEqual(false, maps:get(model, P2)),
    ?assertEqual(false, maps:get(warn, P2)),
    %% the short plugin names work as well
    [{varp_saturate, _}, {varp_order, _}] = varp_backjump:restart_steps("s -k 2|ord"),
    ?assertMatch({error, _}, varp_backjump:restart_steps("order | nonsense -x")),
    ?assertMatch({error, _}, varp_backjump:restart_steps("order | | skip")),
    ?assertMatch({error, _}, varp_backjump:restart_steps("order x=1")).

%% pigeon n=7 has no models and restarts many times with a small
%% counter; an order step with --display shows every time it runs,
%% and the result stays unsatisfiable through every strategy
cli_test_() ->
    {timeout, 120,
     fun() ->
	     P = filename:join(varp_tc:formula_dir("varp"), "pigeon.varp"),
	     Run = fun(Args) ->
			   {0, Out} = varp_tc:cli(["sat", "bj", "--restart-counter", "200"] ++
						     Args ++ ["n=7", P]),
			   Out
		   end,
	     Out1 = Run(["--restart", "order --sort random --display | skip"]),
	     %% the display lines are the only ones naming variables
	     Displays = length([L || L <- string:split(Out1, "\n", all),
				     string:find(L, "P(") =/= nomatch]),
	     ?assert(Displays >= 2),
	     ?assertNotEqual(nomatch, string:find(Out1, "% 0")),
	     Out2 = Run(["--restart", "saturate -k 1 -l 1 | order --sort =degree,random"]),
	     ?assertNotEqual(nomatch, string:find(Out2, "% 0")),
	     %% a bad strategy is an error, not a crash
	     {_, Out3} = varp_tc:cli(["sat", "bj", "--restart", "nonsense", "n=7", P]),
	     ?assertNotEqual(nomatch, string:find(Out3, "unknown plugin")),
	     %% under parallel every clone starts at its own step
	     {0, Out4} = varp_tc:cli(["sat", "parallel", "--clones", "2", "--stat", "bj",
				      "--restart-counter", "200",
				      "--restart", "order --sort random | saturate -k 1 -l 1",
				      "n=7", P]),
	     ?assertNotEqual(nomatch, string:find(Out4, "parallel: total"))
     end}.
