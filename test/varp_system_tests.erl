%%% Transition systems (`system { state ... next ... reach ... }`) and
%%% their expansion to the hand written unrolling, see
%%% doc/MODEL_CHECKING.md.  The reference is die_hard.varp: the system
%%% version must have exactly the same models for every bound.

-module(varp_system_tests).
-include_lib("eunit/include/eunit.hrl").

read(Name) ->
    File = filename:join(varp_tc:formula_dir("varp"), Name),
    {ok,Bin} = file:read_file(File),
    binary_to_list(Bin).

opts(Var, K) ->
    #{meta => #{Var => K}, undeclared => none}.

%% scan and parse only: the system expansion happens in the grammar
parse(Text) ->
    varp_scan:init(varp:remove_comments(Text)),
    varp_parse:parse_and_scan({varp_scan, one_token, []}).

%% the expansion of a small system, shape of the definitions
expand_test() ->
    {ok,{Defs,[],Formula}} =
	parse("system c { state x:2; input up;\n"
		    "  init x == 0;\n"
		    "  next up implies next(x) == x + 1;\n"
		    "  reach x == 3; }\n"),
    ?assertEqual({p,<<"c">>,[<<"k">>]}, Formula),
    Names = [N || {define,{p,N,_},_} <- Defs],
    ?assertEqual([<<"c_init">>,<<"c_next">>,<<"c_reach">>,<<"c">>], Names),
    ?assertMatch([{declare,[{{p,<<"x">>,[<<"$t">>]},uint,2}]},
		  {declare,[{p,<<"up">>,[<<"$t">>]}]} | _], Defs),
    %% next: x -> x($t-1), next(x) -> x($t), up -> up($t)
    [Next] = [B || {define,{p,<<"c_next">>,_},B} <- Defs],
    ?assertMatch({lop,imp,
		  {p,<<"up">>,[<<"$t">>]},
		  {lop,eq,
		   {p,<<"x">>,[<<"$t">>]},
		   {lop,add,{p,<<"x">>,[{op,sub,<<"$t">>,{const,1}}]},_}}},
		 Next).

%% a file with its own formula keeps it
own_formula_test() ->
    {ok,{_Defs,[],Formula}} =
	parse("system c { state x; init x; next next(x) equ not x; }\n"
	      "c_init(0) and c_next(1) and not x(1)\n"),
    ?assertMatch({lop,'and',_,_}, Formula).

next_outside_next_test() ->
    ?assertMatch({error,{1,varp_parse,_}},
		 parse("system c { state x; init next(x); reach x; }\n")).

%% die_hard.varp and die_hard_system.varp agree on every bound
die_hard_equivalence_test_() ->
    Old = read("die_hard.varp"),
    New = read("die_hard_system.varp"),
    [{"die hard k="++integer_to_list(K),
      {timeout, 300,
       fun() ->
	       NOld = varp_tc:count(Old, opts(<<"n">>, K)),
	       NNew = varp_tc:count(New, opts(<<"k">>, K)),
	       ?assertEqual({K,NOld}, {K,NNew}),
	       ?assertEqual(K >= 6, NNew > 0)
       end}} || K <- [4,5,6,7]].

die_hard_first_model_test() ->
    New = read("die_hard_system.varp"),
    [Model|_] = varp_tc:models(New, opts(<<"k">>, 6)),
    Text = lists:flatten(io_lib:format("~p", [Model])),
    %% the classic solution: fill big, pour, empty small, pour, fill, pour
    lists:foreach(fun(S) -> ?assert(string:find(Text, S) =/= nomatch) end,
		  ["fill_big", "big_to_small", "empty_small"]).

%% invariant B != 4 is violated first at k=6, eventually gives a lasso
properties_test_() ->
    New = read("die_hard_system.varp"),
    Inv = lists:flatten(string:replace(New, "reach B == 4;", "invariant B != 4;", all)),
    Ev  = lists:flatten(string:replace(New, "reach B == 4;", "eventually B == 4;", all)),
    Ev2 = lists:flatten(string:replace(New, "reach B == 4;", "eventually true;", all)),
    [{"invariant k=5", ?_assertEqual(0, varp_tc:count(Inv, opts(<<"k">>, 5)))},
     {"invariant k=6", ?_assertEqual(1, varp_tc:count(Inv, opts(<<"k">>, 6)))},
     {"eventually B==4 has a lasso",
      ?_assert(varp_tc:is_sat(Ev, opts(<<"k">>, 3)))},
     {"eventually true has none",
      ?_assertNot(varp_tc:is_sat(Ev2, opts(<<"k">>, 4)))}].

%% the exported macros combine with hand written constraints
macros_test() ->
    New = read("die_hard_system.varp"),
    Mixed = New ++ "\njugs(k) and [A s=1..k-1] not (fill_big(s) and fill_big(s+1))\n",
    ?assertEqual(16, varp_tc:count(Mixed, opts(<<"k">>, 7))),
    Direct = New ++ "\njugs_init(0) and [A s=1..k] jugs_next(s) and B(k) == 4 and L(k) == 3\n",
    ?assertEqual(17, varp_tc:count(Direct, opts(<<"k">>, 7))).
