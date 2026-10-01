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
	     ?assert(string:find(Text1, "fill_big") =/= nomatch),
	     %% with the input names, an input is listed on the row it
	     %% was chosen in (the one it leads away from); the last
	     %% row has none and the free input of step 0 is dropped
	     Inputs = [<<"fill_small">>,<<"fill_big">>,<<"empty_small">>,
		       <<"empty_big">>,<<"small_to_big">>,<<"big_to_small">>],
	     {_, Rows3} = varp_bmc:trace(Model, #{}, Inputs),
	     ?assertEqual({0,["0","0"],["fill_big"]}, hd(Rows3)),
	     ?assertEqual({6,["4","3"],[]}, lists:last(Rows3)),
	     ?assertEqual([S || {S,_,_} <- Rows], [S || {S,_,_} <- Rows3]),
	     [?assertEqual(I, I3) || {{_,_,[I]}, {_,_,[I3]}} <- lists:zip(tl(Rows), lists:droplast(Rows3))],
	     Text3 = lists:flatten(varp_bmc:format_trace(Model, #{}, Inputs)),
	     ?assertEqual(nomatch, string:find(Text3, " \n"))
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

%% k-induction: TRUE when the step case is unsatisfiable, FALSE with a
%% trace when the base case has a model, UNKNOWN past k-max
induction_test_() ->
    Sys = fun(Prop) ->
		  lists:flatten(string:replace(read("die_hard_system.varp"),
					       "reach B == 4;", Prop, all))
	  end,
    Run = fun(Prop, KMax) ->
		  varp_tc:run(Sys(Prop), [{bmc,[{induction,true},{k_max,KMax}]}])
	  end,
    [{"0-inductive", {timeout, 120,
      fun() ->
	      ?assertMatch({?INCONSISTENT, [], _}, Run("invariant B <= 5 and L <= 3;", 4))
      end}},
     {"2-inductive", {timeout, 120,
      fun() ->
	      ?assertMatch({?INCONSISTENT, [], _}, Run("invariant B + L <= 8;", 4))
      end}},
     {"false, counterexample at k=6", {timeout, 120,
      fun() ->
	      {R, [M|_], _} = Run("invariant B != 4;", 8),
	      ?assert(R =:= ?DONE orelse R =:= ?CONTINUE),
	      ?assertEqual(4, value(M, <<"B">>, 6)),
	      ?assertEqual(undefined, value(M, <<"B">>, 7))
      end}},
     {"unknown within k-max", {timeout, 120,
      fun() ->
	      %% B == 6 is unreachable but the step case wanders through
	      %% unreachable states, so 3-induction cannot prove it
	      ?assertMatch({?CONTINUE, [], _}, Run("reach B == 6;", 3))
      end}},
     {"reach is the invariant not P", {timeout, 120,
      fun() ->
	      {R, [M|_], _} = Run("reach B == 4;", 8),
	      ?assert(R =:= ?DONE orelse R =:= ?CONTINUE),
	      ?assertEqual(4, value(M, <<"B">>, 6))
      end}}].

%% deadlock freedom of the ordered dining philosophers, proved with a
%% strengthening invariant selected by --property; the same lemma on
%% the deadlocking version is refuted at k=n
strengthening_invariant_test_() ->
    Read = fun(Name) ->
		   File = filename:join(varp_tc:formula_dir("varp"), Name),
		   {ok,Bin} = file:read_file(File), binary_to_list(Bin)
	   end,
    Run = fun(Text, N, KMax) ->
		  varp_tc:run(Text, [{bmc,[{induction,true},{property,"dining_invariant"},
					   {k_max,KMax}]}], #{meta => #{<<"n">> => N}})
	  end,
    Correct = Read("dining_correct.varp"),
    [{"proved for n="++integer_to_list(N), {timeout, 300,
      fun() -> ?assertMatch({?INCONSISTENT,[],_}, Run(Correct, N, 2)) end}}
     || N <- [3,4,5]] ++
    [{"a weaker lemma is not inductive", {timeout, 300,
      fun() ->
	      Weak = lists:flatten(string:replace(Correct,
			"                     and ((st(p) == 1) implies ((forks(a) == p) and (forks(b) != p)))\n",
			"", all)),
	      ?assertMatch({?CONTINUE,[],_}, Run(Weak, 3, 2))
      end}}].

%% the GUI hands bmc a fun to write to (bmc_output): verdict, trace
%% and progress lines go there instead of the terminal
output_fun_test() ->
    Text = read("die_hard_system.varp"),
    {Sections, Assignments, Formula} = varp_tc:parse(Text, #{}),
    GOpts0 = varp:section_opts(Sections, varp:load_option_list([{print,true}])),
    Self = self(),
    GOpts = GOpts0#{ bmc_output => fun(Line) -> Self ! {bmc, Line} end },
    Do = varp:parse_do([{bmc,[{k_max,8}]}]),
    {R, [_|_], _} = varp:do_run(Do, Assignments, Formula, GOpts),
    ?assert(R =:= ?DONE orelse R =:= ?CONTINUE),
    Lines = collect([]),
    Out = lists:flatten(Lines),
    ?assert(string:find(Out, "bmc: counterexample at k=6") =/= nomatch),
    ?assert(string:find(Out, "step  B  L  input") =/= nomatch),
    ?assert(string:find(Out, "big_to_small") =/= nomatch),
    ?assert(string:find(Out, "% 1") =/= nomatch),
    %% progress lines come too, one per bound
    ?assert(length([L || L <- Lines, string:prefix(L, "bmc: k=") =/= nomatch]) >= 6).

collect(Acc) ->
    receive {bmc, L} -> collect([L|Acc]) after 0 -> lists:reverse(Acc) end.

%% --no-properties (alias --runs): unroll the transition relation alone.
%%
%% Two things it is for. Inspecting models of a file that HAS a property --
%% without it the property's formula is what gets solved, so a question about
%% the system comes back answered about the property. And checking that `next'
%% is consistent at all: an inconsistent one has no transitions, so every
%% property holds and every proof is vacuous.
no_properties_test_() ->
    Src =
	"system t {\n"
	"    state A:2;\n"
	"    input C:1;\n"
	"    init  A == 0;\n"
	"    next  (C == 1) implies (next(A) == A + 1);\n"
	"    next  (C == 0) implies (next(A) == A);\n"
	"    invariant A != 3;\n"
	"}\n",
    Run = fun(Opts, K) ->
		  {Sections, As, Formula} = varp_tc:parse(Src, #{}),
		  GOpts = varp:section_opts(
			    Sections, varp:load_option_list([{print,false}])),
		  Do = varp:parse_do([{bmc, [{k_min,K},{k_max,K},
					     {trace,false} | Opts]}]),
		  varp:do_run(Do, As, Formula, GOpts)
	  end,
    Sat = fun({R, Models, _}) -> R =/= ?INCONSISTENT andalso Models =/= [] end,
    [{"the invariant is not violated at k=1", ?_assertNot(Sat(Run([], 1)))},
     {"...but a run of length 1 exists",
      ?_assert(Sat(Run([{no_properties,true}], 1)))},
     {"the invariant IS violated at k=3", ?_assert(Sat(Run([], 3)))},
     {"--runs is the same flag",
      ?_assert(Sat(Run([{no_properties,true}], 2)))},
     %% an inconsistent next has no transitions: this is the check that has to
     %% pass before a proof means anything
     {"an inconsistent next has no runs",
      fun() ->
	      Bad = lists:flatten(
		      string:replace(Src,
				     "    next  (C == 0) implies (next(A) == A);\n",
				     "    next  (C == 0) implies (next(A) == A);\n"
				     "    next  next(A) == A + 1;\n"
				     "    next  next(A) == A + 2;\n", all)),
	      {Sections, As, Formula} = varp_tc:parse(Bad, #{}),
	      GOpts = varp:section_opts(
			Sections, varp:load_option_list([{print,false}])),
	      Do = varp:parse_do([{bmc, [{k_min,1},{k_max,1},{trace,false},
					 {no_properties,true}]}]),
	      ?assertNot(Sat(varp:do_run(Do, As, Formula, GOpts)))
      end}].

%% The word in the verdict line says which mode produced the model.
no_properties_word_test() ->
    Src = "system t {\n    state A:2;\n    input C:1;\n"
	  "    init  A == 0;\n"
	  "    next  next(A) == A + C;\n    invariant A != 3;\n}\n",
    {Sections, As, Formula} = varp_tc:parse(Src, #{}),
    Self = self(),
    GOpts0 = varp:section_opts(Sections,
			       varp:load_option_list([{print,true}])),
    GOpts = GOpts0#{ bmc_output => fun(L) -> Self ! {bmc, L} end },
    Do = varp:parse_do([{bmc, [{k_min,1},{k_max,1},{trace,false},
			       {no_properties,true}]}]),
    varp:do_run(Do, As, Formula, GOpts),
    Out = lists:flatten(collect([])),
    ?assert(string:find(Out, "bmc: run at k=1") =/= nomatch),
    ?assertEqual(nomatch, string:find(Out, "counterexample")).

%% --no-properties is GLOBAL as well, so it reaches satisfy/saturate/bt/bj and
%% not only bmc -- and it SUBSTITUTES rather than replaces, so a -f survives.
%% Replacing threw the -f away, which made `-f "X" --no-properties' quietly
%% answer about the system alone.
%%
%% varp_tc:run/3 goes through varp:do_run/4, not varp_run/4, so the CLI's
%% automatic substitution is applied here by hand -- which is also the unit
%% under test.
global_no_properties_test_() ->
    Src =
	"system t {\n"
	"    state A:2;\n"
	"    input C:1;\n"
	"    init  A == 0;\n"
	"    next  next(A) == A + C;\n"
	"    invariant A != 3;\n"
	"}\n",
    Sat = fun({R, Models, _}) -> R =/= ?INCONSISTENT andalso Models =/= [] end,
    Go = fun(Strip, Extra, K) ->
		 Opts = #{ meta => #{<<"k">> => K} },
		 {Sections, As, F0} = varp_tc:parse(Src, Opts),
		 G0 = varp:load_option_list([{print,false},{undeclared,none}]),
		 GOpts0 = varp:section_opts(Sections, G0#{ meta => #{<<"k">> => K} }),
		 GOpts = case Strip of
			     true  -> GOpts0#{ no_properties => true };
			     false -> GOpts0
			 end,
		 F1 = case Extra of
			  none -> F0;
			  Text ->
			      {_, _, E} = varp_tc:parse("declare z;\n" ++ Text
							++ "\n", Opts),
			      {lop,'and',F0,E}
		      end,
		 F = case Strip of
			 true  -> varp:strip_properties(F1, GOpts);
			 false -> F1
		     end,
		 %% satisfy alone does no SEARCH -- bmc adds backjump for you,
		 %% and without it every case answers "no models" for the wrong
		 %% reason.
		 varp:do_run(varp:parse_do([{satisfy,[]},{backjump,[]}]),
			     As, F, GOpts)
	 end,
    [{"satisfy sees the property by default",
      ?_assertNot(Sat(Go(false, none, 1)))},
     {"--no-properties reaches satisfy",
      ?_assert(Sat(Go(true, none, 1)))},
     %% A rises by at most 1 per step, so 3 is out of reach at k=2 and 2 is not
     {"a -f survives: unreachable value stays unsatisfiable",
      ?_assertNot(Sat(Go(true, "A(2) == 3", 2)))},
     {"a -f survives: reachable value is satisfiable",
      ?_assert(Sat(Go(true, "A(2) == 2", 2)))}].

%% Towers of Hanoi written with system macros (doc/MODEL_CHECKING.md):
%% the shortest solution has 2^n - 1 moves
hanoi_test_() ->
    {timeout, 300,
     fun() ->
	     Text = read("hanoi_macros.varp"),
	     {R, [Model|_], _} = varp_tc:run(Text, [{bmc,[{k_max,8}]}], #{meta => #{<<"n">> => 3}}),
	     ?assert(R =:= ?DONE orelse R =:= ?CONTINUE),
	     {_, Rows} = varp_bmc:trace(Model),
	     ?assertEqual(8, length(Rows)),
	     {7, Vals, _} = lists:last(Rows),
	     ?assertEqual(["0","0","0","0","0","0","1","2","3"], Vals),
	     ?assertMatch({?INCONSISTENT, [], _},
			  varp_tc:run(Text, [{bmc,[{k_max,6}]}], #{meta => #{<<"n">> => 3}}))
     end}.

%% --saturate 1: probing after every step gives the same bound and
%% trace, from a database with what the steps force bound for good
saturate_test_() ->
    {timeout, 300,
     fun() ->
	     Text = read("die_hard_system.varp"),
	     {_, [M1|_], _} = varp_tc:run(Text, [{bmc,[{k_max,10}]}]),
	     {_, [M2|_], _} = varp_tc:run(Text, [{bmc,[{k_max,10},{saturate,1}]}]),
	     ?assertEqual(varp_bmc:trace(M1), varp_bmc:trace(M2)),
	     Hanoi = read("hanoi_macros.varp"),
	     {R, [M|_], _} = varp_tc:run(Hanoi, [{bmc,[{k_max,8},{saturate,1}]}],
					 #{meta => #{<<"n">> => 3}}),
	     ?assert(R =:= ?DONE orelse R =:= ?CONTINUE),
	     {_, Rows} = varp_bmc:trace(M),
	     ?assertEqual(8, length(Rows))
     end}.
