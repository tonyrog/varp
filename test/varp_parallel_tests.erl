%%% The parallel driver: the chain after it runs in cloned instances,
%%% the first clone to finish answers, and permanent bindings found
%%% in one clone reach the others through the distributor.
-module(varp_parallel_tests).
-include_lib("eunit/include/eunit.hrl").
-include("varp.hrl").

run(Text, Opts) ->
    varp_tc:quiet(fun() ->
			  varp_tc:run(Text, [{satisfy,[]},{parallel,Opts},{backjump,[]}])
		  end).

seq(Text) ->
    varp_tc:quiet(fun() -> varp_tc:run(Text, [{satisfy,[]},{backjump,[]}]) end).

named(Bs) ->
    [{binary_to_list(Name), V} || {{p,Name,[]},V} <- varp_formula:model(Bs)].

%% a unique model: every clone finds the same one
sat_test() ->
    F = "(A || B) && (!A || C) && (!B || !C) && (C || D) && !D",
    {R, [Model], Bs} = run(F, [{clones,3}]),
    ?assert(lists:member(R, [continue, done])),
    {_, [Model0], _} = seq(F),
    ?assertEqual(lists:sort(Model0), lists:sort(Model)),
    ?assertEqual([{"A",true},{"B",false},{"C",true},{"D",false}], named(Bs)).

%% no models: the race ends with inconsistent, also without sharing
unsat_test() ->
    F = "(A || B) && (!A || B) && (A || !B) && (!A || !B)",
    ?assertMatch({inconsistent, _, _}, run(F, [{clones,2}])),
    ?assertMatch({inconsistent, _, _}, run(F, [{clones,2},{share,false}])),
    ?assertMatch({inconsistent, _, _}, run(F, [{clones,1},{shuffle,false}])).

%% the formula is not touched by the clones: the original instance is
%% still at level 0 with its variables free
original_untouched_test() ->
    F = "(A || B) && (!A || C)",
    {continue, [_], Bs} = run(F, [{clones,2}]),
    %% the returned state is the winner's, with the model bound
    ?assertNotEqual(0, varp_nif:level(Bs#bs.vp)).

%% parallel with nothing after it has nothing to run
empty_chain_test() ->
    {continue, [], _} =
	varp_tc:quiet(fun() -> varp_tc:run("A || B", [{satisfy,[]},{parallel,[{clones,2}]}]) end).

%% a larger instance through the command line, with the statistics line
cli_test_() ->
    {timeout, 120,
     fun() ->
	     F = filename:join(varp_tc:formula_dir("varp"), "send_more.varp"),
	     {0, Out} = varp_tc:cli(["sat", "parallel", "--clones", "2", "--stat", "bj", F]),
	     ?assertNotEqual(nomatch, string:find(Out, "parallel: clone")),
	     ?assertNotEqual(nomatch, string:find(Out, "D=7,E=5,M=1,N=6,O=0,R=8,S=9,Y=2")),
	     %% the model is printed once
	     ?assertEqual(1, length(string:split(Out, "S=9", all)) - 1),
	     %% the shared facts reach the original: a monitor on it sees them
	     {0, Out1} = varp_tc:cli(["sat", "mon", "parallel", "--clones", "2", "bj", F]),
	     ?assertNotEqual(nomatch, string:find(Out1, "monitor: permanent")),
	     %% no models, with four clones sharing facts
	     P = filename:join(varp_tc:formula_dir("varp"), "pigeon.varp"),
	     {0, Out2} = varp_tc:cli(["sat", "parallel", "--clones", "4", "bj", "n=7", P]),
	     ?assertNotEqual(nomatch, string:find(Out2, "% 0"))
     end}.
