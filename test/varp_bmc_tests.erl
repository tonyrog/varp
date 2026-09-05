%%% The bmc plugin: raise the bound until a counterexample appears,
%%% print it as a trace.  See doc/MODEL_CHECKING.md.

-module(varp_bmc_tests).
-include_lib("eunit/include/eunit.hrl").
-include("../src/varp.hrl").

read(Name) ->
    File = filename:join(varp_tc:formula_dir("varp"), Name),
    {ok,Bin} = file:read_file(File),
    binary_to_list(Bin).

value(Model, Name, Step) ->
    case lists:keyfind({p,Name,[Step]}, 1, Model) of
	{_, {_Type,Bits}} -> list_to_integer(tuple_to_list(Bits), 2);
	{_, V} -> V;
	false -> undefined
    end.

found_at_six_test_() ->
    {timeout, 120,
     fun() ->
	     Text = read("die_hard_system.varp"),
	     {R, [Model|_], _Bs} = varp_tc:run(Text, [{bmc,[{k_max,10}]}]),
	     ?assert(R =:= ?DONE orelse R =:= ?CONTINUE),
	     ?assertEqual(4, value(Model, <<"B">>, 6)),
	     ?assertEqual(3, value(Model, <<"L">>, 6)),
	     ?assertEqual(undefined, value(Model, <<"B">>, 7)),
	     %% the trace, one row per step
	     {Vectors, Rows} = varp_bmc:trace(Model),
	     ?assertEqual([{p,<<"B">>,[]},{p,<<"L">>,[]}], Vectors),
	     ?assertEqual(lists:seq(0,6), [S || {S,_,_} <- Rows]),
	     ?assertEqual({0,["0","0"],[]}, hd(Rows)),
	     ?assertEqual({6,["4","3"],["big_to_small"]}, lists:last(Rows)),
	     ?assertEqual({1,["5","0"],["fill_big"]}, lists:nth(2, Rows)),
	     Text1 = lists:flatten(varp_bmc:format_trace(Model)),
	     ?assert(string:find(Text1, "step") =/= nomatch),
	     ?assert(string:find(Text1, "fill_big") =/= nomatch)
     end}.

bound_too_small_test_() ->
    {timeout, 120,
     fun() ->
	     Text = read("die_hard_system.varp"),
	     ?assertMatch({?INCONSISTENT, [], _},
			  varp_tc:run(Text, [{bmc,[{k_max,5}]}])),
	     %% k-min skips the small bounds
	     {R, [Model|_], _} = varp_tc:run(Text, [{bmc,[{k_min,6},{k_max,6}]}]),
	     ?assert(R =:= ?DONE orelse R =:= ?CONTINUE),
	     ?assertEqual(4, value(Model, <<"B">>, 6))
     end}.

%% the search plugin and its options come after bmc
explicit_search_plugin_test_() ->
    {timeout, 120,
     fun() ->
	     Text = read("die_hard_system.varp"),
	     {R, [Model|_], _} =
		 varp_tc:run(Text, [{bmc,[{k_max,8}]},
				    {backjump,[{minimize,recursive}]}]),
	     ?assert(R =:= ?DONE orelse R =:= ?CONTINUE),
	     ?assertEqual(4, value(Model, <<"B">>, 6)),
	     {R2, [Model2|_], _} =
		 varp_tc:run(Text, [{bmc,[{k_max,8}]}, {backtrack,[]}]),
	     ?assert(R2 =:= ?DONE orelse R2 =:= ?CONTINUE),
	     ?assertEqual(4, value(Model2, <<"B">>, 6))
     end}.

%% a hand written unrolling works too, with its own bound name
hand_written_bound_test_() ->
    {timeout, 120,
     fun() ->
	     Text = read("die_hard.varp"),
	     {R, [Model|_], _} =
		 varp_tc:run(Text, [{bmc,[{bound,"n"},{k_max,8}]}]),
	     ?assert(R =:= ?DONE orelse R =:= ?CONTINUE),
	     ?assertEqual(4, value(Model, <<"B">>, 6)),
	     {_, Rows} = varp_bmc:trace(Model),
	     ?assertEqual(["Fill_big"], element(3, lists:nth(2, Rows)))
     end}.

invariant_test_() ->
    {timeout, 120,
     fun() ->
	     Text = lists:flatten(
		      string:replace(read("die_hard_system.varp"),
				     "reach B == 4;", "invariant B != 4;", all)),
	     {R, [Model|_], _} = varp_tc:run(Text, [{bmc,[{k_max,8}]}]),
	     ?assert(R =:= ?DONE orelse R =:= ?CONTINUE),
	     ?assertEqual(4, value(Model, <<"B">>, 6)),
	     ?assertEqual(undefined, value(Model, <<"B">>, 7))
     end}.

%% incremental and non-incremental agree on the bound and the trace
incremental_test_() ->
    Text = read("die_hard_system.varp"),
    Inv = lists:flatten(string:replace(Text, "reach B == 4;",
				       "invariant B != 4;", all)),
    Ev = lists:flatten(string:replace(Text, "reach B == 4;",
				      "eventually B == 4;", all)),
    %% same bound in both modes; the traces are compared only when
    %% the model is unique (die hard at k=6 has one solution)
    Both = fun(T, Opts, SameTrace) ->
		   {R1, [M1|_], _} = varp_tc:run(T, [{bmc,[{incremental,true}|Opts]}]),
		   {R2, [M2|_], _} = varp_tc:run(T, [{bmc,[{incremental,false}|Opts]}]),
		   ?assert(R1 =:= ?DONE orelse R1 =:= ?CONTINUE),
		   ?assert(R2 =:= ?DONE orelse R2 =:= ?CONTINUE),
		   {_, Rows1} = varp_bmc:trace(M1),
		   {_, Rows2} = varp_bmc:trace(M2),
		   ?assertEqual(length(Rows2), length(Rows1)),
		   SameTrace andalso
		       ?assertEqual(varp_bmc:trace(M2), varp_bmc:trace(M1)),
		   M1
	   end,
    [{"reach", {timeout, 120,
		fun() ->
			M = Both(Text, [{k_max,10}], true),
			?assertEqual(4, value(M, <<"B">>, 6))
		end}},
     {"invariant", {timeout, 120,
		    fun() ->
			    M = Both(Inv, [{k_max,10}], true),
			    ?assertEqual(4, value(M, <<"B">>, 6))
		    end}},
     {"invariant from k-min", {timeout, 120,
			       fun() ->
				       M = Both(Inv, [{k_min,3},{k_max,10}], true),
				       ?assertEqual(4, value(M, <<"B">>, 6))
			       end}},
     {"eventually", {timeout, 120,
		     fun() ->
			     M = Both(Ev, [{k_max,4}], false),
			     {_, Rows} = varp_bmc:trace(M),
			     ?assertEqual(2, length(Rows))
		     end}},
     {"bound too small", {timeout, 120,
			  fun() ->
				  ?assertMatch({?INCONSISTENT, [], _},
					       varp_tc:run(Text, [{bmc,[{k_max,5}]}]))
			  end}}].

%% keeping learned clauses is an option, and counting works with
%% assumptions: every model of length 7 after bounds 1,3,5 were refuted
keep_learned_and_count_test_() ->
    Text = read("die_hard_system.varp"),
    [{"keep learned", {timeout, 120,
		       fun() ->
			       {R, [M|_], _} = varp_tc:run(Text, [{bmc,[{keep_learned,true},{k_max,10}]}]),
			       ?assert(R =:= ?DONE orelse R =:= ?CONTINUE),
			       ?assertEqual(4, value(M, <<"B">>, 6))
		       end}},
     {"count under assumptions", {timeout, 120,
				  fun() ->
					  {R, Acc, _} = varp_tc:run(Text, [{bmc,[{k_min,1},{step,2},{k_max,7}]},
									   {backjump,[{max,0}]}]),
					  ?assertEqual(?DONE, R),
					  ?assertEqual(18, length(Acc))
				  end}}].

%% the same system with the sizes as bindings
jugs_test_() ->
    Text = read("jugs.varp"),
    Meta = #{<<"n">> => 5, <<"big">> => 13, <<"small">> => 9, <<"goal">> => 1},
    {timeout, 300,
     fun() ->
	     {R, [M|_], _} = varp_tc:run(Text, [{bmc,[{k_max,12}]}],
					#{meta => Meta}),
	     ?assert(R =:= ?DONE orelse R =:= ?CONTINUE),
	     {_, Rows} = varp_bmc:trace(M),
	     {K, Vals, _} = lists:last(Rows),
	     ?assertEqual(10, K),
	     ?assertEqual("1", hd(Vals))
     end}.
