%%% IEEE 754 light: /float754 declarations, literals, comparison, the
%%% conversions and the printing.  varp_float is checked against the
%%% binary syntax of Erlang, which rounds to nearest even.
-module(varp_float754_tests).
-include_lib("eunit/include/eunit.hrl").

v(Text, Var) -> v(Text, Var, #{}).
v(Text, Var, Opts) ->
    [M] = varp_tc:models(Text, Opts),
    proplists:get_value(Var, M).

count(Text) -> varp_tc:count(Text).

%% one model with backjumping, normalised like varp_tc:models/1
model_bj(Text) ->
    {_, [M|_], _} = varp_tc:run(Text, [{satisfy,[]},{backjump,[]}]),
    varp_tc:norm_model(M).

%% all models with backjumping: plain backtracking takes ages over a
%% free binary32
counts(Text) -> counts(Text, #{}).
counts(Text, Opts) ->
    case varp_tc:run(Text, [{satisfy,[]},{backjump,[{max,0}]}], Opts) of
	{_, Ms, _} when is_list(Ms) -> length(Ms);
	_ -> 0
    end.

%% the value of a double rounded to binary32 / binary16
f32(V) -> <<F:32/float>> = <<V:32/float>>, F.
f16(V) -> <<F:16/float>> = <<V:16/float>>, F.

%%% ---- varp_float, the pure part -------------------------------------

encode_test() ->
    Vs = [0.0, 1.0, 1.5, -2.75, 0.1, 3.0e-3, 123456.789, -1.0e-30, 1.0e30,
	  6.02214076e23, 16777217.0, 2.5e-40, 3.4e38],
    %% binary32 and binary64 agree with the binary syntax
    [begin
	 <<B32:32>> = <<V:32/float>>,
	 ?assertEqual({V,{ok,B32}}, {V,varp_float:encode(V, 8, 23)}),
	 <<B64:64>> = <<V:64/float>>,
	 ?assertEqual({V,{ok,B64}}, {V,varp_float:encode(V, 11, 52)})
     end || V <- Vs, V >= 1.0e-37 orelse V =< -1.0e-37 orelse V == 0.0],
    %% binary16 for the values it holds
    [begin
	 <<B16:16>> = <<V:16/float>>,
	 ?assertEqual({V,{ok,B16}}, {V,varp_float:encode(V, 5, 10)})
     end || V <- [0.0, 1.0, 1.5, -2.75, 0.1, 3.0e-3, 1234.5, 65504.0]],
    %% integers, with rounding past 24 bits
    ?assertEqual({ok, 16#4B800000}, varp_float:encode(16777216, 8, 23)),
    ?assertEqual({ok, 16#4B800000}, varp_float:encode(16777217, 8, 23)),
    ?assertEqual({ok, 16#4B800002}, varp_float:encode(16777219, 8, 23)),
    ?assertEqual({ok, 16#4F000000}, varp_float:encode(16#7fffffff, 8, 23)),
    %% below the normal range is zero, above it an error
    ?assertEqual({ok, 0}, varp_float:encode(1.0e-39, 8, 23)),
    ?assertEqual({ok, 1 bsl 31}, varp_float:encode(-1.0e-39, 8, 23)),
    ?assertMatch({error,{float754_range,_,_}}, varp_float:encode(1.0e39, 8, 23)),
    %% a scaled integer: 3/4 as Q16.16 raw 49152 with shift -16
    ?assertEqual({ok, 16#3F400000}, varp_float:encode_scaled(49152, -16, 8, 23)).

format_test() ->
    F = fun(V) -> {ok,B} = varp_float:encode(V, 8, 23), varp_float:format(B, 8, 23) end,
    ?assertEqual("1.5", F(1.5)),
    ?assertEqual("-0.0", F(-0.0)),
    ?assertEqual("0.1", F(0.1)),
    ?assertEqual("16777216.0", F(16777216.0)),
    ?assertEqual("1.0e-30", F(1.0e-30)),
    ?assertEqual("3.0e38", F(3.0e38)),
    G = fun(V) -> {ok,B} = varp_float:encode(V, 11, 52), varp_float:format(B, 11, 52) end,
    ?assertEqual("0.1", G(0.1)),
    %% an odd format is printed exactly
    {ok,B} = varp_float:encode(0.75, 3, 2),
    ?assertEqual("0.75", varp_float:format(B, 3, 2)),
    ?assertEqual("inf", varp_float:format(16#7f800000, 8, 23)).

%%% ---- the language -------------------------------------------------

declaration_test() ->
    ?assertEqual(1.5, v("declare X:32/float754; X == 1.5", "X")),
    ?assertEqual(1.5, v("declare X:16/float754; X == 1.5", "X")),
    ?assertEqual(1.5, v("declare X:64/float754; X == 1.5", "X")),
    ?assertEqual(1.5, v("declare X/float754(8,23); X == 1.5", "X")),
    %% bfloat16: 8 exponent bits of 16
    ?assertEqual(1.5, v("declare X:16/float754(8); X == 1.5", "X")),
    ?assertEqual(f32(0.1), v("declare X:32/float754; X == 0.1", "X")),
    ?assertEqual(0.1, v("declare X:64/float754; X == 0.1", "X")),
    ?assertEqual(f16(0.1), v("declare X:16/float754; X == 0.1", "X")),
    %% an integer literal, a negative, a signed zero
    ?assertEqual(3.0, v("declare X:32/float754; X == 3", "X")),
    ?assertEqual(-2.75, v("declare X:32/float754; X == -2.75", "X")),
    %% a signed zero: -0.0 == 0.0, so two models
    ?assertEqual(2, count("declare X:32/float754; X == -0.0")),
    ?assertEqual(f32(1.0e30), v("declare X:32/float754; X == 1.0e30", "X")).

%% the typed left hand side and the circuit parameter
forms_test() ->
    ?assertEqual(2.5, v("X:32/float754 = 2.5; X > 2", "X")),
    T = "circuit pick(in a:32/float754, b:32/float754; return r:32/float754) { r = min(a, b); }\n"
	"declare X:32/float754; X == pick(2.5, 1.25)",
    ?assertEqual(1.25, v(T, "X")).

%% every pattern of a tiny format against the sign/magnitude order
compare_test_() ->
    {timeout, 300, fun() ->
	%% float754(2,1): 16 patterns, two of them zero
	Vals = [{B bsr 3, B band 7} || B <- lists:seq(0, 15)],
	Num = fun({S,Mag}) -> case Mag of 0 -> 0; _ -> if S =:= 1 -> -Mag; true -> Mag end end end,
	Pairs = [{Num(A), Num(B)} || A <- Vals, B <- Vals],
	Lt = length([1 || {A,B} <- Pairs, A < B]),
	Eq = length([1 || {A,B} <- Pairs, A == B]),
	D = "declare X/float754(2,1), Y/float754(2,1); ",
	?assertEqual(Lt, count(D ++ "X < Y")),
	?assertEqual(Lt, count(D ++ "X > Y")),
	?assertEqual(Eq, count(D ++ "X == Y")),
	?assertEqual(256 - Eq, count(D ++ "X != Y")),
	?assertEqual(Lt + Eq, count(D ++ "X <= Y")),
	?assertEqual(Lt + Eq, count(D ++ "X >= Y"))
     end}.

compare_literal_test() ->
    %% three binary32 numbers lie strictly between 1 and 1.0000005
    ?assertEqual(3, counts("declare X:32/float754; X > 1.0 && X < 1.0000005")),
    ?assertEqual(2, counts("declare X:32/float754; X >= -0.0 && X <= 0.0 && X < 1")),
    ?assertEqual(1.5, v("declare X:32/float754; X == 1.5 && X > 1.25 && X <= 1.5 && X != 2", "X")).

sign_test() ->
    D = "declare X:32/float754, Y:32/float754; ",
    ?assertEqual(-1.5, v(D ++ "X == 1.5 && Y == -X", "Y")),
    ?assertEqual(1.5,  v(D ++ "X == -1.5 && Y == abs(X)", "Y")),
    ?assertEqual(1.25, v(D ++ "X == 2.5 && Y == min(X, 1.25)", "Y")),
    ?assertEqual(2.5,  v(D ++ "X == 2.5 && Y == max(X, -3)", "Y")),
    ?assertEqual(-3.0, v(D ++ "X == -3 && Y == (X < 0 ? X : 1.0)", "Y")).

%% integer and fixed point operands become floats, round to nearest even
to_float_test() ->
    ?assertEqual(-5.0, v("declare N:8/signed, X:32/float754; N == -5 && X == N", "X")),
    %% zero: X == 0.0 holds for both zeros
    ?assertEqual(2, count("declare N:8/signed, X:32/float754; N == 0 && X == N")),
    ?assertEqual(200.0, v("declare N:8, X:32/float754; N == 200 && X == N", "X")),
    ?assertEqual(16777216.0, v("declare N:32, X:32/float754; N == 16777217 && X == N", "X")),
    ?assertEqual(16777220.0, v("declare N:32, X:32/float754; N == 16777219 && X == N", "X")),
    ?assertEqual(2147483648.0, v("declare N:32, X:32/float754; N == 2147483647 && X == N", "X")),
    ?assertEqual(-2147483648.0, v("declare N:32/signed, X:32/float754; N == -2147483648 && X == N", "X")),
    ?assertEqual(1.75, v("declare Q:32/fixpoint, X:32/float754; Q == 1.75 && X == Q", "X")),
    ?assertEqual(-0.5, v("declare Q:8/fixpoint(4), X:32/float754; Q == -0.5 && X == Q", "X")),
    ?assertEqual(1.52587890625e-5, v("declare Q:32/fixpoint, X:32/float754; Q == 1.52587890625e-5 && X == Q", "X")),
    %% a small value in a small format is flushed to zero (either zero)
    ?assertEqual(2, count("declare Q:32/fixpoint, X:16/float754; Q == 1.52587890625e-5 && X == Q")),
    %% the comparison converts too
    ?assertEqual(1, count("declare N:4, X:32/float754; X == 2.5 && N > X && N < 4")).

to_int_test() ->
    D = "declare X:32/float754, N:8/signed; ",
    [begin
	 ?assertEqual({Fun,Val,Want},
		      {Fun,Val,v(D ++ "X == " ++ Val ++ " && N == " ++ Fun ++ "(X)", "N")})
     end || {Fun,Val,Want} <- [{"trunc","1.75",1}, {"trunc","-1.75",-1}, {"trunc","-2.0",-2},
			      {"floor","1.75",1}, {"floor","-1.75",-2}, {"floor","-0.3",-1},
			      {"ceil","1.25",2}, {"ceil","-1.25",-1}, {"ceil","0.001",1},
			      {"round","1.5",2}, {"round","-1.5",-1}, {"round","2.3",2},
			      {"round","2.49",2}, {"round","2.51",3}, {"round","-2.7",-3},
			      {"trunc","100.0",100}]],
    ?assertEqual(2, count(D ++ "X == 0.0 && N == trunc(X)")),
    ?assertEqual(2, count(D ++ "X == -0.0 && N == floor(X)")).

to_fix_test() ->
    D = "declare X:32/float754, Q:32/fixpoint; ",
    ?assertEqual(1.75, v(D ++ "Q = X; X == 1.75", "Q")),
    ?assertEqual(-1.75, v(D ++ "Q = X; X == -1.75", "Q")),
    ?assertEqual(300.5, v(D ++ "Q = X; X == 300.5", "Q")),
    %% below the resolution: truncated toward zero
    ?assertEqual(0.0, v(D ++ "Q = X; X == 1.0e-6", "Q")),
    ?assertEqual(0.0, v(D ++ "Q = X; X == -1.0e-6", "Q")),   %% no -0.0 in fixed point
    ?assertEqual(0.5, v("declare X:16/float754, Q:8/fixpoint(4); Q = X; X == 0.5", "Q")).

%%% ---- addition and subtraction ---------------------------------------

%% the sum of two binary32 numbers whose exponents are at most 29 apart
%% is exact as a double, so the rounded double sum is the answer
add_oracle(Vals, Width, Round) ->
    D = lists:flatten(io_lib:format("declare X:~w/float754, Y:~w/float754, Z:~w/float754; ",
				    [Width, Width, Width])),
    [begin
	 A = Round(A0), B = Round(B0),
	 %% the statement form pins the bits of a zero result
	 T = D ++ lists:flatten(io_lib:format("Z = X + Y; W = X - Y; X == ~w && Y == ~w",
					      [A, B])),
	 %% backjump: plain backtracking thrashes over the adder's outputs
	 M = model_bj("declare W:" ++ integer_to_list(Width) ++ "/float754; " ++ T),
	 ?assertEqual({A,B,Round(A+B),Round(A-B)},
		      {A,B,proplists:get_value("Z", M),proplists:get_value("W", M)})
     end || {A0,B0} <- Vals].

add_test_() ->
    Vals = [{1.5,2.5}, {1.5,-1.5}, {-1.5,1.5}, {1.0000001,1.0}, {1.0,1.0000001},
	    {1.0e38,-3.0e37}, {1.0e-3,1.0e3}, {0.1,0.2}, {-0.1,0.3},
	    {16777216.0,1.0}, {16777216.0,3.0}, {1.0,-0.9999999}, {2.5,-0.0}, {0.0,-2.5}],
    [{"binary32 against the double sum", {timeout, 900, fun() ->
	rand:seed(exsss, {17,19,23}),
	Rnd = [{(rand:uniform() - 0.5) * math:pow(10, rand:uniform(6) - 3),
		(rand:uniform() - 0.5) * math:pow(10, rand:uniform(6) - 3)} || _ <- lists:seq(1, 12)],
	add_oracle(Vals ++ Rnd, 32, fun f32/1) end}},
     {"binary16 against the double sum", {timeout, 300, fun() ->
	add_oracle([{1.5,2.5}, {1.5,-1.5}, {1.001,1.0}, {1000.0,-999.5}, {0.1,0.2}], 16, fun f16/1) end}}].

%% every pair of float754(3,2) against varp_float:add_bits
add_exhaustive_test_() ->
    {timeout, 900, fun() ->
	{_, Ms, _} = varp_tc:run("declare X/float754(3,2), Y/float754(3,2), Z/float754(3,2); Z = X + Y; true",
				 [{satisfy,[]},{backjump,[{max,0}]}]),
	?assertEqual(4096, length(Ms)),
	Bits = fun(M, Name) ->
		       {_,{_,Vec}} = lists:keyfind({p,Name,[]}, 1, M),
		       list_to_integer(tuple_to_list(Vec), 2)
	       end,
	Bad = [{A,B,Z,varp_float:add_bits(A, B, 3, 2)} || M <- Ms,
			  A <- [Bits(M, <<"X">>)], B <- [Bits(M, <<"Y">>)], Z <- [Bits(M, <<"Z">>)],
			  Z =/= varp_float:add_bits(A, B, 3, 2)],
	?assertEqual([], Bad)
     end}.

%% the sign of a zero: a cancelled difference is +0, -0 + -0 is -0
add_edge_test() ->
    D = "declare X:32/float754, Y:32/float754, Z:32/float754; ",
    ?assertEqual(0.0,  v(D ++ "X = 1.5; Y = -1.5; Z = X + Y; Z >= 0", "Z")),
    ?assertEqual(0.0,  v(D ++ "X = 1.5; Y = 1.5; Z = X - Y; Z >= 0", "Z")),
    ?assertEqual(-0.0, v(D ++ "X = -0.0; Y = -0.0; Z = X + Y; Z <= 0", "Z")),
    ?assertEqual(0.0,  v(D ++ "X = -0.0; Y = 0.0; Z = X + Y; Z >= 0", "Z")),
    ?assertEqual(-2.5, v(D ++ "X = -2.5; Y = 0.0; Z = X + Y; Z < 0", "Z")),
    %% an integer term, a literal, two literals
    ?assertEqual(5.5, v("declare N:4, X:32/float754, Z:32/float754; N == 3 && X == 2.5 && Z == X + N", "Z")),
    ?assertEqual(0.5, v(D ++ "X == 2.5 && Z == X - 2", "Z")),
    ?assertEqual(4.0, v(D ++ "Z == 1.5 + 2.5", "Z")),
    %% overflow is inf, and the invariant form holds in a sum
    {0, Out} = varp_tc:cli(["--print","model","-f", D ++ "X == 3.0e38 && Z == X + X", "sat","bj"]),
    ?assertNotEqual(nomatch, string:find(Out, "Z=inf")),
    ?assertEqual(1, counts("declare X:32/float754, Y:32/float754; X == 1.0 && Y == 2.0 && X + Y == 3.0")).

add_lib_test_() ->
    {timeout, 300, fun() ->
	L = #{ops => lib},
	D = "declare X:32/float754, Y:32/float754, Z:32/float754; ",
	?assertEqual(4.0, v(D ++ "X == 1.5 && Y == 2.5 && Z == X + Y", "Z", L)),
	%% from the rounded operands: f32(0.1) - f32(0.3) is a tie, even wins
	?assertEqual(f32(f32(0.1)-f32(0.3)), v(D ++ "X == 0.1 && Y == 0.3 && Z == X - Y", "Z", L))
     end}.

%%% ---- multiplication -----------------------------------------------

%% the product of two binary32 (binary16) numbers is exact as a double,
%% so the double product rounded to the format is the correct answer
mul_oracle(Vals, Width, Round) ->
    D = lists:flatten(io_lib:format("declare X:~w/float754, Y:~w/float754, Z:~w/float754; ",
				    [Width, Width, Width])),
    [begin
	 A = Round(A0), B = Round(B0),
	 T = D ++ lists:flatten(io_lib:format("X == ~w && Y == ~w && Z == X * Y",
					      [A, B])),
	 ?assertEqual({A,B,Round(A*B)}, {A,B,v(T, "Z")})
     end || {A0,B0} <- Vals].

mul_test_() ->
    Vals = [{1.5,2.5}, {-1.5,0.1}, {3.0,1.0e-3}, {123.456,-0.789}, {1.0e10,1.0e-10},
	    {0.3,3.0}, {1.0000001,1.0000001}, {-7.25,-0.125}, {65536.0,0.5}],
    [{"binary32 against the double product", {timeout, 600, fun() ->
	rand:seed(exsss, {7,11,13}),
	Rnd = [{(rand:uniform() - 0.5) * math:pow(10, rand:uniform(20) - 10),
		(rand:uniform() - 0.5) * math:pow(10, rand:uniform(20) - 10)} || _ <- lists:seq(1, 12)],
	mul_oracle(Vals ++ Rnd, 32, fun f32/1) end}},
     {"binary16 against the double product", {timeout, 300, fun() ->
	mul_oracle([{1.5,2.5}, {-1.5,0.125}, {3.0,0.001}, {12.3,-0.78}, {100.0,2.0}], 16, fun f16/1) end}}].

%% every pair of float754(3,2) against varp_float:mul_bits
mul_exhaustive_test_() ->
    {timeout, 600, fun() ->
	{_, Ms, _} = varp_tc:run("declare X/float754(3,2), Y/float754(3,2), Z/float754(3,2); Z = X * Y; true",
				 [{satisfy,[]},{backjump,[{max,0}]}]),
	?assertEqual(4096, length(Ms)),
	Bits = fun(M, Name) ->
		       {_,{_,Vec}} = lists:keyfind({p,Name,[]}, 1, M),
		       list_to_integer(tuple_to_list(Vec), 2)
	       end,
	Bad = [{A,B,Z} || M <- Ms,
			  A <- [Bits(M, <<"X">>)], B <- [Bits(M, <<"Y">>)], Z <- [Bits(M, <<"Z">>)],
			  Z =/= varp_float:mul_bits(A, B, 3, 2)],
	?assertEqual([], Bad)
     end}.

%% zero, overflow, the sign of a zero (the statement form pins the bits)
mul_edge_test() ->
    D = "declare X:32/float754, Y:32/float754, Z:32/float754; ",
    ?assertEqual(-0.0, v(D ++ "X = 0.0; Y = -2.5; Z = X * Y; Z <= 0", "Z")),
    ?assertEqual(-0.0, v(D ++ "X = -0.0; Y = 2.5; Z = X * Y; Z <= 0", "Z")),
    ?assertEqual(0.0,  v(D ++ "X = 1.0e-30; Y = 1.0e-10; Z = X * Y; Z >= 0", "Z")),
    ?assertEqual(-0.0, v(D ++ "X = -1.0e-30; Y = 1.0e-10; Z = X * Y; Z <= 0", "Z")),
    %% an integer factor, and a literal
    ?assertEqual(7.5, v("declare N:4, X:32/float754, Z:32/float754; N == 3 && X == 2.5 && Z == X * N", "Z")),
    ?assertEqual(-5.0, v(D ++ "X == 2.5 && Z == X * -2", "Z")),
    %% two literals fold
    ?assertEqual(3.75, v(D ++ "Z == 1.5 * 2.5", "Z")),
    %% overflow is the inf pattern
    {0, Out} = varp_tc:cli(["--print","model","-f", D ++ "X == 3.0e38 && Z == X * 10", "sat","bj"]),
    ?assertNotEqual(nomatch, string:find(Out, "Z=inf")).

mul_lib_test_() ->
    {timeout, 300, fun() ->
	L = #{ops => lib},
	D = "declare X:32/float754, Y:32/float754, Z:32/float754; ",
	?assertEqual(3.75, v(D ++ "X == 1.5 && Y == 2.5 && Z == X * Y", "Z", L)),
	?assertEqual(f32(-1.5*0.1), v(D ++ "X == -1.5 && Y == 0.1 && Z == X * Y", "Z", L))
     end}.

errors_test() ->
    %% (two literals fold as fixed point, a variable does not)
    ?assertError({float754_operator,'div',_},
		 varp_tc:models("declare X:32/float754, Y:32/float754; X == Y / 2.0")),
    ?assertError({float754_to_integer,_,_},
		 varp_tc:models("declare N:8, X:32/float754; N = X; X == 1.5")),
    ?assertError({float754_mixed,_},
		 varp_tc:models("declare X:32/float754, Y:16/float754; X == Y")),
    ?assertError({float754_range,_,_},
		 varp_tc:models("declare X:16/float754; X == 1.0e6")).

lib_test_() ->
    {timeout, 300, fun() ->
	L = #{ops => lib},
	?assertEqual(3, counts("declare X:32/float754; X > 1.0 && X < 1.0000005", L)),
	?assertEqual(-5.0, v("declare N:8/signed, X:32/float754; N == -5 && X == N", "X", L)),
	?assertEqual(-2, v("declare X:32/float754, N:8/signed; X == -1.75 && N == floor(X)", "N", L))
     end}.

print_test_() ->
    {timeout, 120, fun() ->
	{0, Out} = varp_tc:cli(["--print","model","-f",
				"declare X:32/float754, Y:16/float754, Z:64/float754; X == -1.5 && Y == 0.1 && Z == 0.1",
				"sat","bt"]),
	?assertNotEqual(nomatch, string:find(Out, "X=-1.5")),
	?assertNotEqual(nomatch, string:find(Out, "Y=0.1")),
	?assertNotEqual(nomatch, string:find(Out, "Z=0.1")),
	{0, Out2} = varp_tc:cli(["--hex","--print","model","-f",
				 "declare X:32/float754; X == 1.0", "sat","bt"]),
	?assertNotEqual(nomatch, string:find(Out2, "X=0x3f800000"))
     end}.
