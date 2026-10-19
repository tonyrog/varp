%%% The parallel driver: the chain after it runs in cloned instances,
%%% the first clone with a decisive answer wins, and permanent bindings
%%% and substitutions found in one clone reach the others through the
%%% distributor. A saturate in the chain is divided between the clones
%%% by segments of the variables, and the result of a chain where every
%%% clone just continues is the original instance with all the facts.
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

%% saturate divided between three clones: C comes from probing A (both
%% ways give C), E from probing D, and A=B is a substitution. The
%% result is the original instance, at level 0, with all of it.
-define(SAT_F, "(A == B) && (A || C) && (!A || C) && (D || E) && (!D || E) && (F || G || H)").

saturate(Opts) ->
    varp_tc:quiet(fun() ->
			  varp_tc:run(?SAT_F, [{satisfy,[]},{parallel,Opts},{saturate,[{level,1}]}])
		  end).

var(Bs, Name) ->
    {_, X} = varp_nif:find_symbol(Bs#bs.vp, {list_to_binary(Name), []}),
    X.

saturate_segments_test() ->
    {continue, [], Seq} =
	varp_tc:quiet(fun() -> varp_tc:run(?SAT_F, [{satisfy,[]},{saturate,[{level,1}]}]) end),
    {continue, [], Bs} = saturate([{clones,3}]),
    Vp = Bs#bs.vp,
    ?assertEqual(0, varp_nif:level(Vp)),
    ?assertEqual(true, varp_nif:value(Vp, var(Bs, "C"))),
    ?assertEqual(true, varp_nif:value(Vp, var(Bs, "E"))),
    %% one of A and B stands for the other
    ?assert(is_integer(varp_nif:bound(Vp, var(Bs, "A"))) orelse
	    is_integer(varp_nif:bound(Vp, var(Bs, "B")))),
    ?assertEqual(varp:get_number_of_bound_variables(Seq#bs.vp),
		 varp:get_number_of_bound_variables(Vp)),
    %% the cross reference is as it was
    ?assertEqual(false, varp_nif:getopt(Vp, xref)).

%% without sharing every clone saturates it all, and the first one
%% answers with its instance
saturate_share_off_test() ->
    {continue, [], Bs} = saturate([{clones,2},{share,false}]),
    ?assertEqual(true, varp_nif:value(Bs#bs.vp, var(Bs, "C"))),
    ?assertEqual(true, varp_nif:value(Bs#bs.vp, var(Bs, "E"))).

%% saturate and then the search, in two clones: the model of the
%% formula with a unique one
saturate_then_backjump_test() ->
    F = "(A || B) && (!A || C) && (!B || !C) && (C || D) && !D",
    {_, [Model], _} =
	varp_tc:quiet(fun() ->
			      varp_tc:run(F, [{satisfy,[]},{parallel,[{clones,2}]},
					      {saturate,[{level,1}]},{backjump,[]}])
		      end),
    {_, [Model0], _} = seq(F),
    ?assertEqual(lists:sort(Model0), lists:sort(Model)).

%% clauses learned elsewhere go into the learned set as this instance
%% reads them: a true literal drops the clause, false literals are left
%% out (a unit binds), an empty one is a contradiction
import_clauses_test() ->
    {_, _, Bs} = varp_tc:quiet(fun() -> varp_tc:run("(A || B || C) && (D || E)", [{satisfy,[]}]) end),
    Vp = Bs#bs.vp,
    [A, B, D] = [var(Bs, N) || N <- ["A", "B", "D"]],
    true = varp_nif:bind(Vp, -D), true = varp_nif:bcp(Vp),
    G0 = varp_nif:clauseset_size(Vp, ?GAMMA),
    ?assertEqual(true, varp:import_clauses(Vp, [[-A, B, D]])),
    ?assertEqual(G0 + 1, varp_nif:clauseset_size(Vp, ?GAMMA)),
    %% the same one again is not added
    ?assertEqual(true, varp:import_clauses(Vp, [[-A, B, D]])),
    ?assertEqual(G0 + 1, varp_nif:clauseset_size(Vp, ?GAMMA)),
    %% satisfied: dropped
    ?assertEqual(true, varp:import_clauses(Vp, [[B, -D]])),
    ?assertEqual(G0 + 1, varp_nif:clauseset_size(Vp, ?GAMMA)),
    %% a unit after the false literal is left out
    ?assertEqual(true, varp:import_clauses(Vp, [[-A, D]])),
    ?assertEqual(false, varp_nif:value(Vp, A)),
    %% and a contradiction
    ?assertEqual(false, varp:import_clauses(Vp, [[A, D]])).

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
	     ?assertNotEqual(nomatch, string:find(Out, "clauses shared")),
	     ?assertNotEqual(nomatch, string:find(Out, "D=7,E=5,M=1,N=6,O=0,R=8,S=9,Y=2")),
	     %% the model is printed once
	     ?assertEqual(1, length(string:split(Out, "S=9", all)) - 1),
	     %% the shared facts reach the original: a monitor on it sees them
	     {0, Out1} = varp_tc:cli(["sat", "mon", "parallel", "--clones", "2", "bj", F]),
	     ?assertNotEqual(nomatch, string:find(Out1, "monitor: permanent")),
	     %% no models, with four clones sharing facts
	     P = filename:join(varp_tc:formula_dir("varp"), "pigeon.varp"),
	     {0, Out2} = varp_tc:cli(["sat", "parallel", "--clones", "4", "--stat", "bj", "n=7", P]),
	     ?assertNotEqual(nomatch, string:find(Out2, "% 0")),
	     %% and without clause sharing
	     {0, Out2b} = varp_tc:cli(["sat", "parallel", "--clones", "4", "--share-len", "0", "--stat",
				       "bj", "n=7", P]),
	     ?assertNotEqual(nomatch, string:find(Out2b, "% 0")),
	     ?assertNotEqual(nomatch, string:find(Out2b, "0 clauses shared")),
	     %% saturate in segments: the substitutions reach the original
	     %% too, and all clones are waited for
	     {0, Out3} = varp_tc:cli(["sat", "mon", "parallel", "--clones", "3", "--stat",
				      "saturate", "-k=1", F]),
	     ?assertNotEqual(nomatch, string:find(Out3, "monitor: substitut")),
	     ?assertNotEqual(nomatch, string:find(Out3, "monitor: permanent")),
	     ?assertNotEqual(nomatch, string:find(Out3, "parallel: all 3 clones finished")),
	     %% saturate in segments and then the race
	     {0, Out4} = varp_tc:cli(["sat", "parallel", "--clones", "3", "saturate", "-k=1", "bj", F]),
	     ?assertNotEqual(nomatch, string:find(Out4, "D=7,E=5,M=1,N=6,O=0,R=8,S=9,Y=2")),
	     ?assertEqual(1, length(string:split(Out4, "S=9", all)) - 1)
     end}.
