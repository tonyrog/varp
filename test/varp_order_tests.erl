%%% @doc
%%%    Tests of the variable order: every sort key with its three
%%%    directions ('+' ascending, '-' descending, '=' interleaved, the
%%%    ascending order woven from both ends 1,2,3,4,5 => 1,5,2,4,3),
%%%    alone and in pairs, and the order plugin through the command line.
%%% @end
-module(varp_order_tests).

-include_lib("eunit/include/eunit.hrl").

%% six variables with the degrees 1..6 (and no unit clauses, a unit
%% would bind its variable and drop it from the order)
formula() ->
    Vp = varp_nif:new(#{}),
    {1,6} = varp_nif:add_variables(Vp, 6),
    varp_circuit:clause(Vp, [1,2,3,4,5,6]),
    varp_circuit:clause(Vp, [2,3,4,5,6]),
    varp_circuit:clause(Vp, [3,4,5,6]),
    varp_circuit:clause(Vp, [4,5,6]),
    varp_circuit:clause(Vp, [5,6]),
    varp_circuit:clause(Vp, [6,-1]),
    Vp.

order(Keys) ->
    Vp = formula(),
    ok = case Keys of
	     [K1] -> varp_nif:order_sort(Vp, K1, 17);
	     [K1,K2] -> varp_nif:order_sort(Vp, K1, K2, 17)
	 end,
    varp:order_all(Vp).

keys() ->
    [identity, '+identity', '-identity', '=identity',
     random, '+random', '-random', '=random',
     degree, '+degree', '-degree', '=degree',
     rank, '+rank', '-rank', '=rank'].

identity_test() ->
    ?assertEqual([1,2,3,4,5,6], order([identity])),
    ?assertEqual([1,2,3,4,5,6], order(['+identity'])),
    ?assertEqual([6,5,4,3,2,1], order(['-identity'])),
    ?assertEqual([1,6,2,5,3,4], order(['=identity'])).

degree_test() ->
    ?assertEqual([6,5,4,3,2,1], order([degree])),
    ?assertEqual([1,2,3,4,5,6], order(['+degree'])),
    ?assertEqual([6,5,4,3,2,1], order(['-degree'])),
    ?assertEqual([1,6,2,5,3,4], order(['=degree'])).

%% rank is the sum of 1/size over the clauses of the literal, the
%% larger of the two literals counts: 2 (1/6+1/5) ranks below 1 (1/2)
rank_test() ->
    ?assertEqual([6,5,4,3,1,2], order([rank])),
    ?assertEqual([2,1,3,4,5,6], order(['+rank'])),
    ?assertEqual([6,5,4,3,1,2], order(['-rank'])),
    ?assertEqual([2,6,1,5,3,4], order(['=rank'])).

%% random is a permutation, the same one for the same seed
random_test() ->
    lists:foreach(
      fun(Key) ->
	      Order = order([Key]),
	      ?assertEqual([1,2,3,4,5,6], lists:sort(Order)),
	      ?assertEqual(Order, order([Key]))
      end, [random, '+random', '-random', '=random']).

%% every pair of keys is accepted and orders every variable once
pairs_test() ->
    lists:foreach(
      fun({K1, K2}) ->
	      ?assertEqual({K1, K2, [1,2,3,4,5,6]},
			   {K1, K2, lists:sort(order([K1, K2]))})
      end, [{K1, K2} || K1 <- [undefined|keys()], K2 <- keys()]).

%% the second key breaks ties of the first: the degrees are distinct
%% here, so it changes nothing, and the weave applies to the first key
pair_test() ->
    ?assertEqual([1,6,2,5,3,4], order(['=identity', degree])),
    ?assertEqual([1,6,2,5,3,4], order(['=degree', '-identity'])),
    ?assertEqual([6,5,4,3,2,1], order([degree, '=identity'])),
    ?assertEqual([1,2,3,4,5,6], order([undefined, '+degree'])).

%% the plugin: the variables are numbered as first seen, A..E = 1..5
cli_test_() ->
    {timeout, 60,
     fun() ->
	     File = varp_tc:tmpfile("order_keys.varp"),
	     ok = file:write_file(File, <<"(A || B) && (B || C) && (C || D) && (D || E)\n">>),
	     %% the display line is the one made of variable names only
	     Display = fun(Sort) ->
			       {0, Out} = varp_tc:cli(["sat", "order", "--sort", Sort,
						       "--display", "bj", File]),
			       [Line] = [L || L <- string:split(Out, "\n", all),
					      re:run(L, "^([A-E] )+$") =/= nomatch],
			       Line
		       end,
	     ?assertEqual("A B C D E ", Display("identity")),
	     ?assertEqual("E D C B A ", Display("-identity")),
	     ?assertEqual("A E B D C ", Display("=identity")),
	     %% B, C and D have degree 2, A and E 1; ties keep input order
	     ?assertEqual("A E B C D ", Display("+degree,identity")),
	     ?assertEqual("A D E C B ", Display("=degree,identity"))
     end}.
