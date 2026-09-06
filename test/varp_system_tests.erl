%%% Transition systems (`system { state ... next ... reach ... }`) and
%%% their expansion to the hand written unrolling, see
%%% doc/MODEL_CHECKING.md.  The reference is die_hard.varp: the system
%%% version must have exactly the same models for every bound.

-module(varp_system_tests).
-include_lib("eunit/include/eunit.hrl").
-include("../src/varp.hrl").

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

%% assume: a constraint in every step, here on the input.  The shortest
%% string of capital letters with the CRC-16/CCITT-FALSE of "HELLO" has
%% four letters, and the trace is a valid one (checked in Erlang)
crc16_system_test_() ->
    {timeout, 300,
     fun() ->
	     Text = read("crc16_system.varp"),
	     {R, [Model|_], _} = varp_tc:run(Text, [{bmc,[{k_max,6}]}]),
	     ?assert(R =:= ?DONE orelse R =:= ?CONTINUE),
	     {_, Rows} = varp_bmc:trace(Model),
	     ?assertEqual(5, length(Rows)),          %% steps 0..4
	     %% column order: CHAR, CRC (alphabetical)
	     Chars = [list_to_integer(C) || {S,[C,_],_} <- Rows, S > 0],
	     ?assert(lists:all(fun(C) -> C >= 65 andalso C =< 90 end, Chars)),
	     ?assertEqual(18902, crc16(Chars, 16#ffff)),
	     {4, [_, "18902"], _} = lists:last(Rows)
     end}.

crc16([], C) -> C;
crc16([B|Bs], C0) ->
    C1 = lists:foldl(fun(_, C) ->
			     case C band 16#8000 of
				 0 -> (C bsl 1) band 16#ffff;
				 _ -> ((C bsl 1) bxor 16#1021) band 16#ffff
			     end
		     end, C0 bxor (B bsl 8), lists:seq(1,8)),
    crc16(Bs, C1).

assume_test() ->
    %% without the assumption a two step path reaches 3, with it never
    Sys = fun(A) -> "system c { state x:4; input d:4; init x == 0;\n"
			"  next next(x) == x + d;\n" ++ A ++
			"  reach x == 3; }\n" end,
    ?assert(varp_tc:is_sat(Sys(""), opts(<<"k">>, 1))),
    ?assertNot(varp_tc:is_sat(Sys("  assume d == 1;\n"), opts(<<"k">>, 2))),
    ?assert(varp_tc:is_sat(Sys("  assume d == 1;\n"), opts(<<"k">>, 3))),
    ?assertNot(varp_tc:is_sat(Sys("  assume x < 3;\n"), opts(<<"k">>, 6))).

%% several systems compose synchronously and share variables by name
composition_test_() ->
    Two = "system sender {\n"
	"  state msg:4, turn;\n"
	"  init  msg == 0 and turn;\n"
	"  next  turn implies (next(msg) == msg + 1 and not next(turn));\n"
	"  next  (not turn) implies (next(msg) == msg and next(turn));\n"
	"}\n"
	"system receiver {\n"
	"  state msg:4, seen:4;\n"
	"  init  seen == 0;\n"
	"  next  next(seen) == seen + msg;\n"
	"  reach seen == 6;\n"
	"}\n",
    [{"sender constrains the receiver's msg", {timeout, 120,
      fun() ->
	      %% alone the receiver would see any msg at k=1; composed,
	      %% msg counts 0,1,1,2,2,3 and the sum reaches 6 at k=5
	      ?assertNot(varp_tc:is_sat(Two, opts(<<"k">>, 1))),
	      ?assertNot(varp_tc:is_sat(Two, opts(<<"k">>, 4))),
	      ?assert(varp_tc:is_sat(Two, opts(<<"k">>, 5))),
	      {R, [M|_], _} = varp_tc:run(Two, [{bmc,[{k_max,8}]}]),
	      ?assert(R =:= ?DONE orelse R =:= ?CONTINUE),
	      {_, Rows} = varp_bmc:trace(M),
	      ?assertEqual(6, length(Rows)),
	      ?assertEqual({5,["3","6"],[]}, lists:last(Rows))
      end}},
     {"per system macros stay pure", {timeout, 120,
      fun() ->
	      %% receiver_init/next alone: msg is free again
	      Own = Two ++ "receiver_init(0) and receiver_next(1) and seen(1) == 6\n",
	      ?assert(varp_tc:is_sat(Own, opts(<<"k">>, 1)))
      end}},
     {"handshake: ABC over valid/ready", {timeout, 300,
      fun() ->
	      Text = read("handshake.varp"),
	      {R, [M|_], _} = varp_tc:run(Text, [{bmc,[{k_max,12}]}]),
	      ?assert(R =:= ?DONE orelse R =:= ?CONTINUE),
	      {Vectors, Rows} = varp_bmc:trace(M),
	      %% columns: count, data, sum (alphabetical vectors)
	      ?assertEqual([{p,<<"count">>,[]},{p,<<"data">>,[]},{p,<<"sum">>,[]}],
			   Vectors),
	      {K, [Count,_Data,Sum], _} = lists:last(Rows),
	      ?assertEqual("198", Sum),
	      ?assertEqual("3", Count),
	      ?assert(K >= 6 andalso K =< 12)
      end}}].

%% channels are queues between systems, instances copy a template
channel_and_instance_test_() ->
    Q = read("queue.varp"),
    Prod = "channel ch:4[DEPTH];\n"
	"system producer(dst) { state v:4; init v == 1;\n"
	"  send dst v when v <= 3;\n"
	"  next (v <= 3) implies next(v) == v + 1;\n"
	"  next (v > 3) implies next(v) == v;\n"
	"  reach v == 4; }\n"
	"instance p = producer(ch);\n",
    Depth = fun(D) -> lists:flatten(string:replace(Prod, "DEPTH", integer_to_list(D))) end,
    [{"producer, queue, consumer: 1+2+3 in four steps", {timeout, 120,
      fun() ->
	      {R, [M|_], _} = varp_tc:run(Q, [{bmc,[{k_max,8}]}]),
	      ?assert(R =:= ?DONE orelse R =:= ?CONTINUE),
	      {Vectors, Rows} = varp_bmc:trace(M),
	      ?assertEqual(5, length(Rows)),
	      %% instance locals are prefixed, the channel keeps its name
	      Names = [binary_to_list(N) || {p,N,[]} <- Vectors],
	      ?assertEqual(["c_got","c_sum","ch_data","ch_n","ch_q0","ch_q1","p_v"], Names),
	      {4, Vals, _} = lists:last(Rows),
	      ?assertEqual("6", lists:nth(2, Vals)),      %% c_sum
	      ?assertEqual("0", lists:nth(4, Vals))       %% ch_n, drained
      end}},
     {"a full queue blocks the sender", {timeout, 120,
      fun() ->
	      %% three values through a queue of two with nobody reading
	      ?assertMatch({?INCONSISTENT, [], _},
			   varp_tc:run(Depth(2), [{bmc,[{k_max,8}]}])),
	      {R, [M|_], _} = varp_tc:run(Depth(3), [{bmc,[{k_max,8}]}]),
	      ?assert(R =:= ?DONE orelse R =:= ?CONTINUE),
	      {_, Rows} = varp_bmc:trace(M),
	      ?assertEqual(4, length(Rows))               %% k=3
      end}},
     {"errors", {timeout, 60,
      fun() ->
	      ?assertMatch({error,{1,varp_parse,_}}, parse("instance p = nothing;\n")),
	      ?assertMatch({error,{2,varp_parse,_}},
			   parse("system s(a) { state x; init x; }\ninstance t = s(b=y);\n")),
	      ?assertMatch({error,{2,varp_parse,_}},
			   parse("system s(a) { state x; init x; }\ninstance t = s(y, z);\n"))
      end}}].
