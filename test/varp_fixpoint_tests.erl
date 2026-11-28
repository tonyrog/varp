%%% Fixed point: /fixpoint declarations, float literals, the operators
%%% on the raw integers, the conversions and the model output.
-module(varp_fixpoint_tests).
-include_lib("eunit/include/eunit.hrl").

v(Text, Var) -> v(Text, Var, #{}).
v(Text, Var, Opts) ->
    [M] = varp_tc:models(Text, Opts),
    proplists:get_value(Var, M).

count(Text) -> varp_tc:count(Text).

%% a bare /fixpoint is Q16.16 (--fixpoint), fixpoint(f) and
%% fixpoint(i,f) say the width
%% --fixpoint reaches the declarations too (it did not, the dummy
%% binding state of the declare pass had no options)
fixpoint_option_decl_test() ->
    [M] = varp_tc:models("declare X:16/fixpoint; X == 1.5", #{fixpoint => 4}),
    ?assertEqual(1.5, proplists:get_value("X", M)),
    {0, Out} = varp_tc:cli(["--fixpoint","4","--hex","--print","model",
			     "-f","declare X:16/fixpoint; X == 1.5","sat","bj"]),
    ?assertNotEqual(nomatch, string:find(Out, "X=0x0018")).

declaration_test() ->
    ?assertEqual(1.5,  v("declare X:32/fixpoint; X == 1.5", "X")),
    ?assertEqual(2.25, v("declare X/fixpoint(8,8); X == 2.25", "X")),
    ?assertEqual(0.5,  v("declare X:16/fixpoint(4); X == 0.5", "X")),
    ?assertEqual(-0.75, v("declare X:32/fixpoint; X == -0.75", "X")),
    %% an integer is a fixed point value too
    ?assertEqual(3.0,  v("declare X:32/fixpoint; X == 3", "X")),
    %% float literal forms
    ?assertEqual(1500.0, v("declare X:32/fixpoint; X == 1.5e3", "X")),
    ?assertEqual(100.0,  v("declare X:32/fixpoint; X == 1e2", "X")),
    %% 1..4 is still a range
    ?assertEqual(1, count("[A i=1..4] P(i)")).

%% the fraction width is a meta expression too
meta_width_test() ->
    ?assertEqual(0.25, v("declare X:8/fixpoint(k); X == 0.25", "X",
			 #{meta => #{<<"k">> => 2}})).

arithmetic_test() ->
    D = "declare X:32/fixpoint,Y:32/fixpoint,Z:32/fixpoint; ",
    ?assertEqual(3.75,  v(D ++ "X == 1.5 && Y == 2.25 && Z == X + Y", "Z")),
    ?assertEqual(-0.75, v(D ++ "X == 1.5 && Y == 2.25 && Z == X - Y", "Z")),
    ?assertEqual(3.75,  v(D ++ "X == 1.5 && Y == 2.5 && Z == X * Y", "Z")),
    ?assertEqual(-3.0,  v(D ++ "X == -1.5 && Y == 2 && Z == X * Y", "Z")),
    ?assertEqual(0.75,  v(D ++ "X == 3 && Y == 4 && Z == X / Y", "Z")),
    ?assertEqual(-0.75, v(D ++ "X == -3 && Y == 4 && Z == X / Y", "Z")),
    %% 1/3 in Q16.16 is 21845/65536
    ?assertEqual(21845/65536, v(D ++ "X == 1 && Y == 3 && Z == X / Y", "Z")),
    ?assertEqual(1.25,  v(D ++ "X == 1.25 && Y == 2.5 && Z == min(X, Y)", "Z")),
    ?assertEqual(2.5,   v(D ++ "X == 1.25 && Y == 2.5 && Z == max(X, Y)", "Z")),
    ?assertEqual(-1.25, v(D ++ "X == 1.25 && Z == -X", "Z")),
    ?assertEqual(1.25,  v(D ++ "X == -1.25 && Z == abs(X)", "Z")),
    %% the remainder in raw units, the sign of the dividend
    ?assertEqual(0.5,   v(D ++ "X == 3.5 && Y == 1.5 && Z == X % Y", "Z")).

%% two integers divided in fixed point by way of a float literal
integer_operands_test() ->
    ?assertEqual(0.25, v("declare X:8,Y:8,Z:32/fixpoint; X == 1 && Y == 4 && Z == X * 1.0 / Y", "Z")),
    %% constant folding gives the same
    ?assertEqual(0.75, v("declare Z:32/fixpoint; Z == 1.5 * 0.5", "Z")),
    ?assertEqual(2.0,  v("declare Z:32/fixpoint; Z == 1.0 / 0.5", "Z")).

compare_test() ->
    %% Q4.4: 0.5 < X < 1 is 0.5625 .. 0.9375, seven values
    ?assertEqual(7, count("declare X:8/fixpoint(4); X > 0.5 && X < 1")),
    ?assertEqual(1, count("declare X:8/fixpoint(4); X >= 0.5 && X <= 0.5")),
    ?assertEqual(1.5, v("declare X:32/fixpoint; X == 1.5 && X != 2 && X <= 1.5 && X > -3", "X")).

%% a narrower fraction meets a wider one
mixed_width_test() ->
    ?assertEqual(1.5, v("declare X:8/fixpoint(4), Y:32/fixpoint; X == 1.5 && Y == X", "Y")),
    ?assertEqual(3.75, v("declare X:8/fixpoint(4), Y:32/fixpoint, Z:32/fixpoint; X == 1.5 && Y == 2.25 && Z == X + Y", "Z")).

conversion_test() ->
    D = "declare X:32/fixpoint, N:8/signed; ",
    ?assertEqual(1,  v(D ++ "X == 1.75 && N == floor(X)", "N")),
    ?assertEqual(-2, v(D ++ "X == -1.75 && N == floor(X)", "N")),
    ?assertEqual(2,  v(D ++ "X == 1.25 && N == ceil(X)", "N")),
    ?assertEqual(-1, v(D ++ "X == -1.25 && N == ceil(X)", "N")),
    ?assertEqual(2,  v(D ++ "X == 1.5 && N == round(X)", "N")),
    ?assertEqual(-1, v(D ++ "X == -1.5 && N == round(X)", "N")),
    ?assertEqual(1,  v(D ++ "X == 1.75 && N == trunc(X)", "N")),
    ?assertEqual(-1, v(D ++ "X == -1.75 && N == trunc(X)", "N")),
    ?assertEqual(-2, v(D ++ "X == -2.0 && N == trunc(X)", "N")),
    %% on a literal, folded
    ?assertEqual(3,  v("declare N:8; N == floor(3.9)", "N")),
    %% an integer argument is left alone
    ?assertEqual(5,  v("declare N:8, M:8; M == 5 && N == floor(M)", "N")).

%% the statement form: the target keeps its width and fraction
assignment_test() ->
    ?assertEqual(0.25, v("declare X:32/fixpoint; X = 1.0 / 4; X > 0", "X")),
    %% declared on the left hand side
    ?assertEqual(2.5,  v("declare Y:8; X:32/fixpoint = Y / 2.0; Y == 5 && X > 0", "X")),
    ?assertEqual(0.75, v("X:8/fixpoint(4) = 0.75; X > 0", "X")),
    %% a formula may still start with a division
    ?assertEqual(1, count("declare X:8; X / 2 == 3 && X == 7")),
    ?assertEqual(2.5,  v("declare X:32/fixpoint, Y:8; Y == 5 && X == Y / 2.0", "X")),
    %% an integer target needs a rounding function
    ?assertError({fixpoint_to_integer,_,_},
		 varp_tc:models("declare X:8, Y:32/fixpoint; X = Y; Y == 1.5")).


%% the circuit library: op_fixmul and op_fixdiv over op_smul/op_sdiv
lib_test_() ->
    D = "declare X:32/fixpoint,Y:32/fixpoint,Z:32/fixpoint; ",
    L = #{ops => lib},
    [{"mul", {timeout, 120, fun() ->
	?assertEqual(3.75, v(D ++ "X == 1.5 && Y == 2.5 && Z == X * Y", "Z", L)),
	?assertEqual(-3.0, v(D ++ "X == -1.5 && Y == 2 && Z == X * Y", "Z", L)) end}},
     {"div", {timeout, 120, fun() ->
	?assertEqual(0.75,  v(D ++ "X == 3 && Y == 4 && Z == X / Y", "Z", L)),
	?assertEqual(-0.75, v(D ++ "X == -3 && Y == 4 && Z == X / Y", "Z", L)) end}},
     {"add and compare", {timeout, 120, fun() ->
	?assertEqual(3.75, v(D ++ "X == 1.5 && Y == 2.25 && Z == X + Y && Z > X", "Z", L)) end}}].

%% sqrt in fixed point: floor(sqrt(v)) with the same fraction width,
%% a negative operand has no model, an integer operand is --fixpoint
sqrt_test_() ->
    D = "declare Q:32/fixpoint, R:32/fixpoint; ",
    [{"values", {timeout, 300, fun() ->
	?assertEqual(1.5, v(D ++ "R = sqrt(Q); Q == 2.25", "R")),
	?assertEqual(92681/65536, v(D ++ "R = sqrt(Q); Q == 2", "R")),
	?assertEqual(92681/65536, v(D ++ "R = sqrt(Q); Q == 2", "R", #{ops => lib})),
	?assertEqual(92681/65536, v("declare N:8, R:32/fixpoint; R = sqrt(N); N == 2", "R")),
	?assertEqual(0, varp_tc:count(D ++ "R = sqrt(Q); Q == -2")),
	?assertError({sqrt_negative,_}, varp_tc:models(D ++ "R == sqrt(-2.25)")),
	%% every Q4.2 value, builtin and library
	Want = [{Q, varp_math:isqrt(Q bsl 2)} || Q <- lists:seq(0, 31)],
	Got = fun(Opts) ->
		      {_, Ms, _} = varp_tc:run("declare Q:6/fixpoint(2), R:6/fixpoint(2); R = sqrt(Q); true",
					       [{satisfy,[]},{backjump,[{max,0}]}], Opts),
		      lists:sort([{raw(M, <<"Q">>), raw(M, <<"R">>)} || M <- Ms])
	      end,
	?assertEqual(Want, Got(#{})),
	?assertEqual(Want, Got(#{ops => lib})) end}}].

raw(M, Name) ->
    {_,{_,Vec}} = lists:keyfind({p,Name,[]}, 1, M),
    list_to_integer(tuple_to_list(Vec), 2).

%% a circuit parameter can be fixed point
circuit_test() ->
    T = "circuit half(in a:32/fixpoint; return r:32/fixpoint) { r = a / 2; }\n"
	"declare X:32/fixpoint, Y:32/fixpoint; X == 3.5 && Y == half(X)",
    ?assertEqual(1.75, v(T, "Y")).

%% bounded model checking with fixed point state, the trace in decimals
bmc_test_() ->
    Dir = filename:join([varp_tc:top(), "formulas", "varp"]),
    Tank = filename:join(Dir, "tank_system.varp"),
    Thermo = filename:join(Dir, "thermostat_system.varp"),
    [{"tank reach", {timeout, 300, fun() ->
	{0, Out} = varp_tc:cli(["bmc", "--k-max", "8", "--property", "tank_reach", Tank]),
	?assertNotEqual(nomatch, string:find(Out, "counterexample at k=6")),
	?assertNotEqual(nomatch, string:find(Out, "5.90625")) end}},
     {"tank invariant holds", {timeout, 300, fun() ->
	{0, Out} = varp_tc:cli(["bmc", "--k-max", "8", "--property", "tank_invariant", Tank]),
	?assertEqual(nomatch, string:find(Out, "counterexample")) end}},
     {"thermostat reach", {timeout, 300, fun() ->
	{0, Out} = varp_tc:cli(["bmc", "--k-max", "8", Thermo]),
	?assertNotEqual(nomatch, string:find(Out, "counterexample at k=6")),
	?assertNotEqual(nomatch, string:find(Out, "20.25")) end}},
     {"thermostat reach, library circuits", {timeout, 300, fun() ->
	{0, Out} = varp_tc:cli(["--ops", "lib", "bmc", "--k-max", "8", Thermo]),
	?assertNotEqual(nomatch, string:find(Out, "counterexample at k=6")) end}}].

%% the model prints a decimal number, exact
print_test_() ->
    {timeout, 120, fun() ->
	{0, Out} = varp_tc:cli(["--print","model","-f",
				"declare X:32/fixpoint, Y:8/fixpoint(4); X == -1.5 && Y == 0.0625",
				"sat","bt"]),
	?assertNotEqual(nomatch, string:find(Out, "X=-1.5")),
	?assertNotEqual(nomatch, string:find(Out, "Y=0.0625")),
	{0, Out2} = varp_tc:cli(["--print","model","-f",
				 "declare X:32/fixpoint; X == 2",
				 "sat","bt"]),
	?assertNotEqual(nomatch, string:find(Out2, "X=2.0"))
     end}.

%%
%% wrap(E) keeps the low raw bits as a C int32_t store does, fits(E, T)
%% says whether the exact value would have fit.  Needed to model a
%% runtime that wraps (candyspeak, 2026-11-28).
%%
wrap_test() ->
    D = "declare X:32/fixpoint, Y:32/fixpoint; ",
    ?assertEqual(-25536.0, v(D ++ "X == 20000.0 && Y == wrap(X + X)", "Y")),
    ?assertEqual(-25536.0, v(D ++ "X == 20000.0 && Y == wrap(X + X, 32/fixpoint)", "Y")),
    ?assertEqual(-25536.0, v(D ++ "X == 20000.0 && Y == wrap(X + X, 32/fixpoint(16))", "Y")),
    ?assertEqual(-25536.0, v(D ++ "X == 20000.0 && Y == wrap(X + X, fixpoint(16,16))", "Y")),
    ?assertEqual(-25536.0, v(D ++ "X == 200.0 && Y == wrap(X * X)", "Y")),
    ?assertEqual(-25536.0, v(D ++ "Y = wrap(X + X); X == 20000.0", "Y")),
    ?assertEqual(14464.0,  v(D ++ "X == -25536.0 && Y == wrap(X + X)", "Y")),
    ?assertEqual(-5.0,     v(D ++ "X == 20000.0 && Y == wrap(X - 20005.0)", "Y")),
    ?assertEqual(-32768.0, v(D ++ "X == 32767.0 && Y == wrap(X + 1.0)", "Y")),
    %% a constant, and the raw bits of a mask
    ?assertEqual(4464.5, v("declare Y:32/fixpoint; Y == wrap(70000.5, 32/fixpoint)", "Y")),
    ?assertEqual(-25536.0, v(D ++ "X == 20000.0 && Y == wrap((X + X) & 0xFFFFFFFF)", "Y")),
    ?assertEqual(7232.0,   v(D ++ "X == 20000.0 && Y == ((X + X) & 0x7FFFFFFF)", "Y")),
    %% the mask alone is no wrap: 0x9C400000 in 33 bits is still +40000
    ?assertEqual(0, count(D ++ "X == 20000.0 && Y == ((X + X) & 0xFFFFFFFF)")),
    %% an integer is scaled first; a fixed point value into an integer
    %% needs a rounding
    ?assertEqual(-3.0, v("declare X:8/signed, Y:16/fixpoint(4); X == -3 && Y == wrap(X)", "Y")),
    ?assertEqual(-3.0, v("declare X:8/signed, Y:16/fixpoint(4); X == -3 && Y == wrap(X, fixpoint(12,4))", "Y")),
    ?assertEqual(1.0,  v("declare X:8/signed, Y:8/fixpoint(4); X == 17 && Y == wrap(X)", "Y")),
    ?assertError({fixpoint_to_integer,_,_},
		 varp_tc:models("declare X:16/fixpoint(4), Y:8/signed; X == 1.5 && Y == wrap(X)")),
    %% a constant factor that is a power of two is a shift of the raw bits
    ?assertEqual(3.0, v(D ++ "X == 1.5 && Y == X * 2.0", "Y")),
    ?assertEqual(0.75, v(D ++ "X == 1.5 && Y == X * 0.5", "Y")),
    ?assertEqual(1.5, v(D ++ "X == 1.5 && Y == X + 0.0", "Y")),
    %% /float is what --float says
    ?assertEqual(-25536.0, v(D ++ "X == 20000.0 && Y == wrap(X + X, 32/float)", "Y",
			     #{float => "fixpoint"})).

fits_test() ->
    D = "declare X:32/fixpoint; ",
    ?assertEqual(0, count(D ++ "X == 20000.0 && fits(X + X, 32/fixpoint)")),
    ?assertEqual(1, count(D ++ "X == 16000.0 && fits(X + X, 32/fixpoint)")),
    ?assertEqual(1, count(D ++ "X == 20000.0 && fits(X + X, fixpoint(17,16))")),
    ?assertEqual(0, count(D ++ "X == 200.0 && fits(X * X, 32/fixpoint)")),
    ?assertEqual(1, count(D ++ "X == 100.0 && fits(X * X, 32/fixpoint)")),
    %% the edges: 32767.99998 is the largest, -32768.0 the smallest
    ?assertEqual(1, count(D ++ "X == 32767.0 && fits(X + 0.5, 32/fixpoint)")),
    ?assertEqual(0, count(D ++ "X == 32767.0 && fits(X + 1.0, 32/fixpoint)")),
    ?assertEqual(1, count(D ++ "X == -32767.0 && fits(X - 1.0, 32/fixpoint)")),
    ?assertEqual(0, count(D ++ "X == -32767.0 && fits(X - 1.5, 32/fixpoint)")),
    %% an integer scaled into a narrow format
    ?assertEqual(1, count("declare X:8/signed; X == 7 && fits(X, 8/fixpoint(4))")),
    ?assertEqual(0, count("declare X:8/signed; X == 8 && fits(X, 8/fixpoint(4))")).

%% the brief's system: without wrap the sum leaves 32 bits at step 1
%% and the run ends, with wrap it goes on as the C program does
system_wrap_test_() ->
    Sys = fun(Next) ->
	      "system ov2 {\n"
	      "    state X:32/fixpoint, N:3;\n"
	      "    init  X == 20000.0 and N == 0;\n"
	      "    next  next(X) == " ++ Next ++ ";\n"
	      "    next  next(N) == N + 1;\n"
	      "    reach N == 2;\n"
	      "}\n"
	  end,
    {timeout, 300, fun() ->
	File = varp_tc:tmpfile("ov2_wrap.varp"),
	ok = file:write_file(File, Sys("wrap(X + X)")),
	{0, Out} = varp_tc:cli(["bmc","--property","ov2_reach","--k-max","4",File]),
	?assertNotEqual(nomatch, string:find(Out, "counterexample at k=2")),
	?assertNotEqual(nomatch, string:find(Out, "-25536.0")),
	?assertNotEqual(nomatch, string:find(Out, "14464.0")),
	ok = file:write_file(File, Sys("X + X")),
	{0, Out2} = varp_tc:cli(["bmc","--property","ov2_reach","--k-max","4",File]),
	?assertEqual(nomatch, string:find(Out2, "counterexample")),
	%% & binds looser than ==: (next(X) == X + X) & M is a vector
	%% where a formula is expected, an error that says so
	ok = file:write_file(File, Sys("(X + X) & 0xFFFFFFFF")),
	{_, Out3} = varp_tc:cli(["bmc","--property","ov2_reach","--k-max","3",File]),
	?assertNotEqual(nomatch, string:find(Out3, "bind looser")),
	%% doubling from 1000.0 wraps at step 6 (64000.0 is -1536.0);
	%% fits as an assumption keeps only the runs that do not wrap
	Sys2 = fun(Assume) ->
	       "system ov3 {\n"
	       "    state X:32/fixpoint;\n"
	       "    init  X == 1000.0;\n"
	       "    next  next(X) == wrap(X + X);\n" ++ Assume ++
	       "    reach X < 0.0;\n"
	       "}\n"
	   end,
	ok = file:write_file(File, Sys2("")),
	{0, Out4} = varp_tc:cli(["bmc","--property","ov3_reach","--k-max","8",File]),
	?assertNotEqual(nomatch, string:find(Out4, "counterexample at k=6")),
	?assertNotEqual(nomatch, string:find(Out4, "-1536.0")),
	ok = file:write_file(File, Sys2("    assume fits(X + X, 32/fixpoint);\n")),
	{0, Out5} = varp_tc:cli(["bmc","--property","ov3_reach","--k-max","8",File]),
	?assertEqual(nomatch, string:find(Out5, "counterexample"))
     end}.
