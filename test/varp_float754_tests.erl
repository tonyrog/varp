%%% IEEE 754: /float754 declarations, literals, comparison, the
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

%% a value from one model with backjumping (bt enumerating all models
%% of a formula with a free binary32 can take hours)
vbj(Text, Var, Opts) ->
    {_, [M|_], _} = varp_tc:run(Text, [{satisfy,[]},{backjump,[]}], Opts),
    proplists:get_value(Var, varp_tc:norm_model(M)).

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
     end || V <- Vs],
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
    %% below the normal range a subnormal (zero in ftz), above it an error
    <<Sub:32>> = <<1.0e-39:32/float>>,
    ?assertEqual({ok, Sub}, varp_float:encode(1.0e-39, 8, 23)),
    ?assertEqual({ok, Sub bor (1 bsl 31)}, varp_float:encode(-1.0e-39, 8, 23)),
    ?assertEqual({ok, 0}, varp_float:encode(1.0e-39, 8, 23, ftz)),
    ?assertEqual({ok, 1 bsl 31}, varp_float:encode(-1.0e-39, 8, 23, ftz)),
    %% the status: tiny and inexact, half the smallest subnormal rounds to even
    ?assertEqual({ok, 0, true}, varp_float:encode_status(1, -150, 8, 23, ieee)),
    ?assertEqual({ok, 1, false}, varp_float:encode_status(1, -149, 8, 23, ieee)),
    ?assertEqual({ok, 0, true}, varp_float:encode_status(1, -149, 8, 23, ftz)),
    ?assertEqual({ok, 16#00800000, false}, varp_float:encode_status(1, -126, 8, 23, ieee)),
    %% 8 bits is E5M2
    ?assertEqual({5,2}, varp_float:standard(8)),
    ?assertEqual({ok, 16#3e}, varp_float:encode(1.5, 5, 2)),
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
    %% one argument is the fraction width: bfloat16 is (8,7)
    ?assertEqual(1.5, v("declare X:16/float754(7); X == 1.5", "X")),
    ?assert(abs(v("declare X:16/float754(7); X == 3.0e38", "X") - 3.0e38) < 3.0e36),
    ?assertEqual(3, counts("declare X:32/float754(23); X > 1.0 && X < 1.0000005")),
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
	%% float754(2,1): 16 patterns, two of them zero, two of them NaN
	%% (exponent 3, fraction 1), which are unordered
	Vals = [{B bsr 3, B band 7} || B <- lists:seq(0, 15)],
	Num = fun({_,7}) -> nan;
		 ({S,Mag}) -> case Mag of 0 -> 0; _ -> if S =:= 1 -> -Mag; true -> Mag end end
	      end,
	Pairs = [{Num(A), Num(B)} || A <- Vals, B <- Vals],
	Ord = fun(A, B) -> A =/= nan andalso B =/= nan end,
	Lt = length([1 || {A,B} <- Pairs, Ord(A, B), A < B]),
	Eq = length([1 || {A,B} <- Pairs, Ord(A, B), A == B]),
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
    %% a small value in a small format is a subnormal, zero (either) in ftz
    ?assertEqual(1.52587890625e-5, v("declare Q:32/fixpoint, X:16/float754; Q == 1.52587890625e-5 && X == Q", "X")),
    ?assertEqual(2, varp_tc:count("declare Q:32/fixpoint, X:16/float754; Q == 1.52587890625e-5 && X == Q", #{ftz => true})),
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

%% the same, flushed to zero
add_exhaustive_ftz_test_() ->
    {timeout, 900, fun() ->
	{_, Ms2, _} = varp_tc:run("declare X/float754(3,2), Y/float754(3,2), Z/float754(3,2); Z = X + Y; true",
				  [{satisfy,[]},{backjump,[{max,0}]}], #{ftz => true}),
	?assertEqual(4096, length(Ms2)),
	Bad2 = [{A,B,Z,varp_float:add_bits(A, B, 3, 2, ftz)} || M <- Ms2,
			  A <- [bits(M, <<"X">>)], B <- [bits(M, <<"Y">>)], Z <- [bits(M, <<"Z">>)],
			  Z =/= varp_float:add_bits(A, B, 3, 2, ftz)],
	?assertEqual([], Bad2)
     end}.

%% a model vector as an integer
bits(M, Name) ->
    {_,{_,Vec}} = lists:keyfind({p,Name,[]}, 1, M),
    list_to_integer(tuple_to_list(Vec), 2).

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

%% /float is fixed or floating point as --float says
float_type_test() ->
    F = "declare X:32/float, Y:32/float, Z:32/float; Z = X / Y; X == 1 && Y == 3",
    Third = f32(1/3),
    ?assertEqual(Third, v(F, "Z")),
    ?assertEqual(Third, v(F, "Z", #{float => "float754"})),
    ?assertEqual(Third, v(F, "Z", #{float => "32/float754(23)"})),
    ?assertEqual(21845/65536, v(F, "Z", #{float => "fixpoint"})),
    ?assertEqual(0.3125, v(F, "Z", #{float => "32/fixpoint(4)"})),
    %% the bare form takes its width from the option
    B = "declare X/float, Y/float; Y = X * 2; X == 1.5",
    ?assertEqual(3.0, v(B, "Y", #{float => "float754(8,23)"})),
    ?assertEqual(3.0, v(B, "Y", #{float => "fixpoint(16,16)"})),
    ?assertEqual(3.0, v(B, "Y", #{float => "16/float754"})),
    ?assertEqual(3.0, v(B, "Y", #{float => "16/fixpoint(4)"})),
    %% a circuit parameter and a typed left hand side
    C = "circuit c(in a/float; return r) { r = (a == 1.5); } declare X/float; c(X)",
    ?assertEqual(1.5, v(C, "X", #{float => "fixpoint(16,16)"})),
    ?assertEqual(1.5, v(C, "X", #{float => "float754(8,23)"})),
    L = "declare X:8/float754(3); Y:8/float = 1.5; Y == X",
    ?assertEqual(1.5, v(L, "X", #{float => "float754(4,3)"})),
    %% the option and the declaration must agree
    ?assertError({parse_failed,{error,{float_size_mismatch,16,_}}},
		 v("declare X:16/float; X == 1", "X", #{float => "fixpoint(16,16)"})),
    ?assertError({parse_failed,{error,{float_size_unknown,_}}},
		 v("declare X/float; X == 1", "X")),
    ?assertError({parse_failed,{error,{float_option,_}}},
		 v("declare X/float; X == 1", "X", #{float => "banan"})),
    %% the spec parser
    ?assertEqual({{float,default,default},undefined}, varp_formula:float_spec("float754")),
    ?assertEqual({{float,default,23},32}, varp_formula:float_spec("32/float754(23)")),
    ?assertEqual({{float,8,23},32}, varp_formula:float_spec("float754(8,23)")),
    ?assertEqual({{fix,16},32}, varp_formula:float_spec("fixpoint(16,16)")),
    ?assertEqual({{fix,default},16}, varp_formula:float_spec(" 16/fixpoint ")),
    ?assertEqual(error, varp_formula:float_spec("32/float754(8,23)")),
    %% and from the command line
    {0, Out} = varp_tc:cli(["--float","fixpoint(8,8)","--print","model","--hex",
			     "-f","declare X/float; X == 1.5","sat","bj"]),
    ?assertNotEqual(nomatch, string:find(Out, "X=0x0180")).

%% a width that is not a machine word is most likely a slip
odd_width_test() ->
    {0, Out1} = varp_tc:cli(["--print","model","-f","declare X/float754(8,8); X == 1",
			      "sat","bj"]),
    ?assertNotEqual(nomatch, string:find(Out1, "warning: X is 17 bits, a /float754")),
    {0, Out2} = varp_tc:cli(["--print","model","-f","declare Q:12/fixpoint(4); Q == 1",
			      "sat","bj"]),
    ?assertNotEqual(nomatch, string:find(Out2, "warning: Q is 12 bits, a /fixpoint")),
    {0, Out3} = varp_tc:cli(["--print","model","-f","declare X/float754(8,7), Q:32/fixpoint, N:12; X == 1 && Q == 1 && N == 1",
			      "sat","bj"]),
    ?assertEqual(nomatch, string:find(Out3, "warning")).

%% a float meta variable from the command line, limit=4.0
meta_test() ->
    ?assertEqual(4.0, varp_option:meta_value("4.0")),
    ?assertEqual(100000.0, varp_option:meta_value("1e5")),
    ?assertEqual(-0.0025, varp_option:meta_value("-2.5e-3")),
    ?assertEqual(7, varp_option:meta_value("7")),
    ?assertEqual("abc", varp_option:meta_value("abc")),
    Opts = #{meta => #{<<"limit">> => 1.5}},
    ?assertEqual(1.5, v("declare X:32/float754; X == limit", "X", Opts)),
    ?assertEqual(2.5, v("declare Q:32/fixpoint; Q == limit + 1", "Q", Opts)),
    ?assertEqual(1, counts("declare X:32/float754; X >= limit && X < 1.5000001", Opts)),
    %% through both command line paths: before and after the plugin
    {0, Out1} = varp_tc:cli(["--print","model","-f","declare X:32/float754; X == limit",
			      "limit=2.5","sat","bj"]),
    ?assertNotEqual(nomatch, string:find(Out1, "X=2.5")),
    {0, Out2} = varp_tc:cli(["--print","model","-f","declare X:32/float754; X == limit",
			      "sat","bj","limit=2.5e0"]),
    ?assertNotEqual(nomatch, string:find(Out2, "X=2.5")).

add_lib_test_() ->
    {timeout, 300, fun() ->
	L = #{ops => lib},
	D = "declare X:32/float754, Y:32/float754, Z:32/float754; ",
	?assertEqual(4.0, v(D ++ "X == 1.5 && Y == 2.5 && Z == X + Y", "Z", L)),
	%% from the rounded operands: f32(0.1) - f32(0.3) is a tie, even wins
	?assertEqual(f32(f32(0.1)-f32(0.3)), v(D ++ "X == 0.1 && Y == 0.3 && Z == X - Y", "Z", L))
     end}.

%%% ---- division -------------------------------------------------------

bits32(V) -> <<B:32>> = <<V:32/float>>, B.

div_test_() ->
    D = "declare X:32/float754, Y:32/float754, Z:32/float754; ",
    Ref = fun(A, B) -> varp_float:to_float(varp_float:div_bits(bits32(A), bits32(B), 8, 23), 8, 23) end,
    [{"binary32 against the exact quotient", {timeout, 600, fun() ->
	rand:seed(exsss, {29,31,37}),
	Rnd = [{(rand:uniform() - 0.5) * math:pow(10, rand:uniform(20) - 10),
		(rand:uniform() - 0.5) * math:pow(10, rand:uniform(20) - 10)} || _ <- lists:seq(1, 12)],
	Vals = [{3.0,4.0}, {1.0,3.0}, {-1.0,3.0}, {1.0,10.0}, {2.0,3.0}, {1.0e30,1.0e-8},
		{7.0,7.0}, {1.0,1.0000001}, {0.1,0.3}, {-123.456,0.0078125}] ++ Rnd,
	[begin
	     A = f32(A0), B = f32(B0),
	     T = D ++ lists:flatten(io_lib:format("Z = X / Y; X == ~w && Y == ~w", [A, B])),
	     M = model_bj(T),
	     ?assertEqual({A,B,Ref(A,B)}, {A,B,proplists:get_value("Z", M)})
	 end || {A0,B0} <- Vals] end}},
     {"known quotients", fun() ->
	?assertEqual(0.75, v(D ++ "X == 3 && Y == 4 && Z == X / Y", "Z")),
	?assertEqual(f32(1/3), v(D ++ "X == 1 && Y == 3 && Z == X / Y", "Z")),
	?assertEqual(f32(0.1), v(D ++ "X == 1 && Y == 10 && Z == X / Y", "Z")),
	%% two literals fold as a float, an integer divisor converts
	?assertEqual(0.75, v(D ++ "Z == 1.5 / 2.0", "Z")),
	?assertEqual(1.25, v("declare N:4, X:32/float754, Z:32/float754; N == 2 && X == 2.5 && Z == X / N", "Z"))
      end}].

%% every pair of float754(3,2) against varp_float:div_bits; a zero
%% divisor has no model by default (--fdivz false), inf with ignore
div_exhaustive_test_() ->
    {timeout, 900, fun() ->
	Bits = fun(M, Name) ->
		       {_,{_,Vec}} = lists:keyfind({p,Name,[]}, 1, M),
		       list_to_integer(tuple_to_list(Vec), 2)
	       end,
	T = "declare X/float754(3,2), Y/float754(3,2), Z/float754(3,2); Z = X / Y; true",
	{_, Ms, _} = varp_tc:run(T, [{satisfy,[]},{backjump,[{max,0}]}]),
	%% x/0 has no model, 0/0 is NaN and allowed by --nan ignore
	?assertEqual(4096 - 2*62, length(Ms)),
	Bad = [{A,B,Z} || M <- Ms, A <- [Bits(M, <<"X">>)], B <- [Bits(M, <<"Y">>)],
			  Z <- [Bits(M, <<"Z">>)], Z =/= varp_float:div_bits(A, B, 3, 2)],
	?assertEqual([], Bad),
	{_, Ms2, _} = varp_tc:run(T, [{satisfy,[]},{backjump,[{max,0}]}], #{fdivz => ignore}),
	?assertEqual(4096, length(Ms2)),
	Bad2 = [{A,B,Z} || M <- Ms2, A <- [Bits(M, <<"X">>)], B <- [Bits(M, <<"Y">>)],
			   Z <- [Bits(M, <<"Z">>)], Z =/= varp_float:div_bits(A, B, 3, 2)],
	?assertEqual([], Bad2)
     end}.

%% the same, flushed to zero
div_exhaustive_ftz_test_() ->
    {timeout, 900, fun() ->
	T = "declare X/float754(3,2), Y/float754(3,2), Z/float754(3,2); Z = X / Y; true",
	{_, Ms3, _} = varp_tc:run(T, [{satisfy,[]},{backjump,[{max,0}]}], #{fdivz => ignore, ftz => true}),
	?assertEqual(4096, length(Ms3)),
	Bad3 = [{A,B,Z} || M <- Ms3, A <- [bits(M, <<"X">>)], B <- [bits(M, <<"Y">>)],
			   Z <- [bits(M, <<"Z">>)], Z =/= varp_float:div_bits(A, B, 3, 2, ftz)],
	?assertEqual([], Bad3)
     end}.

%% inf: the literal, --inf and --fdivz
inf_test_() ->
    D = "declare X:32/float754, Y:32/float754, Z:32/float754; ",
    [{"the literal", {timeout, 120, fun() ->
	?assertEqual(1, counts("declare X:32/float754; X == inf")),
	?assertEqual(1, counts("declare X:32/float754; X == -inf")),
	?assertEqual(6.0, v(D ++ "X == 2.0 * 3.0 && X != inf", "X")),
	%% only the largest finite number lies above the second largest
	?assertEqual(1, counts("declare X:32/float754; X > 3.4028233e38 && X != inf")),
	?assertError({fixpoint_infinity,_}, varp_tc:models("declare Q:32/fixpoint; Q == inf"))
      end}},
     {"--inf", {timeout, 120, fun() ->
	?assertEqual(0, counts(D ++ "X == 3.0e38 && Z == X * 10", #{inf => false})),
	?assertEqual(0, counts(D ++ "X == 3.0e38 && Z == X + X", #{inf => false})),
	?assertEqual(0, counts(D ++ "X == 3.0e38 && Y == 1.0e-10 && Z == X / Y", #{inf => false})),
	?assertEqual(1, counts(D ++ "X == 3.0e38 && Z == X * 10 && Z == inf", #{inf => ignore})),
	?assertEqual(1, counts(D ++ "X == 3.0e38 && Z == X * 10 && Z == inf", #{inf => true})),
	?assertEqual(0, counts(D ++ "X == 3.0 && Z == X * 10", #{inf => true})),
	%% a literal above the range is an error, whatever the flag
	?assertError({float754_range,_,_}, varp_tc:models(D ++ "Z == 3.0e38 * 10"))
      end}},
     {"--fdivz", {timeout, 120, fun() ->
	?assertEqual(0, counts(D ++ "Y = 0.0; Z = X / Y; X == -1")),
	?assertEqual(-inf_f32(), v(D ++ "Y = 0.0; Z = X / Y; X == -1", "Z", #{fdivz => ignore})),
	?assertEqual(inf_f32(), v(D ++ "Y = -0.0; Z = X / Y; X == -1", "Z", #{fdivz => ignore})),
	?assertEqual(1, counts(D ++ "X = 0.0; Y = 0.0; Z = X / Y; isnan(Z)", #{fdivz => ignore})),
	%% 0/0 is not a division by zero but not a number
	?assertEqual(1, counts(D ++ "X = 0.0; Y = 0.0; Z = X / Y; isnan(Z)")),
	%% the integer rule is separate
	?assertEqual(0, counts("declare N:4, M:4; N == 3 && M == 0 && N / M == 2", #{fdivz => ignore}))
      end}}].

inf_f32() -> varp_float:to_float(varp_float:inf_bits(0, 8, 23), 8, 23).

%% below the normal range: subnormal results, --underflow and --ftz
underflow_test_() ->
    D = "declare X:32/float754, Y:32/float754, Z:32/float754; ",
    %% 2^-100 * 2^-33 is an exact subnormal, no underflow
    Ex = D ++ "Z = X * Y; X == 7.888609052210118e-31 && Y == 1.1641532182693481e-10",
    [{"subnormal results", {timeout, 600, fun() ->
	?assertEqual(f32(1.0e-40), v(D ++ "Z = X * Y; X == 1.0e-20 && Y == 1.0e-20", "Z")),
	?assertEqual(f32(1.0e-40), v(D ++ "Z = X / Y; X == 1.0e-20 && Y == 1.0e20", "Z")),
	?assertEqual(f32(2.0e-39), v(D ++ "Z = X + Y; X == 1.0e-39 && Y == 1.0e-39", "Z")),
	?assertEqual(f32(1.0e-39), v(D ++ "Z = X - Y; X == 2.0e-39 && Y == 1.0e-39", "Z")),
	?assertEqual(f32(1.0e-39), v("declare X:32/float754; X == 1.0e-39", "X")),
	?assertEqual(math:pow(2, -133), v(Ex, "Z")),
	%% the smallest subnormal, and half of it rounds to even
	?assertEqual(f32(1.4e-45), v(D ++ "Z = X * Y; X == 1.4e-45 && Y == 1.0", "Z")),
	?assertEqual(0.0, v(D ++ "Z = X * Y; X == 1.4e-45 && Y == 0.5 && Z >= 0", "Z")),
	?assertEqual(f32(1.4e-45), v(D ++ "Z = X * Y; X == 1.4e-45 && Y == 0.75", "Z")),
	%% the largest subnormal plus the smallest is the smallest normal
	?assertEqual(f32(1.17549435e-38), v(D ++ "Z = X + Y; X == 1.1754942e-38 && Y == 1.4e-45", "Z")),
	%% rounding carries a subnormal product up to the smallest normal
	?assertEqual(f32(f32(1.1754942e-38) * f32(1.0000001)),
		     v(D ++ "Z = X * Y; X == 1.1754942e-38 && Y == 1.0000001", "Z")),
	%% two literals fold, and so do two constants
	?assertEqual(f32(1.0e-40), v(D ++ "Z == 1.0e-20 * 1.0e-20", "Z")),
	?assertEqual(f32(1.0e-40), v(D ++ "X = 1.0e-20; Y = 1.0e-20; Z = X * Y; true", "Z")),
	%% binary16 against Erlang
	?assertEqual(f16(f16(1.0e-4) * f16(6.0e-4)),
		     v("declare X:16/float754, Y:16/float754, Z:16/float754; Z = X * Y; X == 1.0e-4 && Y == 6.0e-4", "Z")),
	?assertEqual(f16(f16(3.0e-5) + f16(2.0e-6)),
		     v("declare X:16/float754, Y:16/float754, Z:16/float754; Z = X + Y; X == 3.0e-5 && Y == 2.0e-6", "Z")),
	%% an integer that does not fit the format is inf, --inf applies
	?assertEqual(1, counts("declare N:32, X:16/float754; N == 100000 && X == N && X == inf")),
	?assertEqual(0, counts("declare N:32, X:16/float754; N == 100000 && X == N", #{inf => false})),
	%% 8 bits is E5M2
	?assertEqual(1.5, v("declare X:8/float754; X == 1.5", "X")),
	%% 0.001 is 2^-10 in two fraction bits, times 0.75
	?assertEqual(7.32421875e-4, v("declare X:8/float754, Y:8/float754, Z:8/float754; Z = X * Y; X == 0.001 && Y == 0.75", "Z"))
      end}},
     {"--underflow", {timeout, 600, fun() ->
	T = D ++ "Z = X * Y; X == 1.0e-20 && Y == 1.0e-20",
	?assertEqual(1, counts(T)),
	?assertEqual(0, counts(T, #{underflow => false})),
	?assertEqual(1, counts(T, #{underflow => true})),
	?assertEqual(0, counts(D ++ "Z = X * Y; X == 1.5 && Y == 2.5", #{underflow => true})),
	%% exact subnormal results are no underflow
	?assertEqual(1, counts(Ex, #{underflow => false})),
	?assertEqual(0, counts(Ex, #{underflow => true})),
	%% (1.0e-39 itself is inexact, 2^-130 is not)
	?assertEqual(1, counts(D ++ "Z = X + Y; X == 7.346839692639297e-40 && Y == 7.346839692639297e-40", #{underflow => false})),
	?assertEqual(0, counts(D ++ "Z = X + Y; X == 1.0e-39 && Y == 1.0e-39", #{underflow => false})),
	%% a tiny inexact literal, a folded product, a division
	?assertEqual(0, counts("declare X:32/float754; X == 1.0e-39", #{underflow => false})),
	?assertEqual(1, counts("declare X:32/float754; X == 1.0e-39", #{underflow => true})),
	?assertEqual(0, counts(D ++ "X = 1.0e-20; Y = 1.0e-20; Z = X * Y; true", #{underflow => false})),
	?assertEqual(0, counts(D ++ "Z = X / Y; X == 1.0e-20 && Y == 1.0e20", #{underflow => false})),
	%% lost below half the smallest subnormal as well
	?assertEqual(0, counts(D ++ "Z = X * Y; X == 1.0e-23 && Y == 1.0e-23", #{underflow => false}))
      end}},
     {"--ftz", {timeout, 600, fun() ->
	F = #{ftz => true},
	?assertEqual(0.0, vbj(D ++ "Z = X * Y; X == 1.0e-20 && Y == 1.0e-20", "Z", F)),
	?assertEqual(0.0, vbj(D ++ "Z = X / Y; X == 1.0e-20 && Y == 1.0e20", "Z", F)),
	?assertEqual(0.0, vbj(D ++ "Z = X * Y; X == 3.0e-39 && Y == 7.0", "Z", F)),
	%% a literal below the range is zero, either zero
	?assertEqual(2, counts("declare X:32/float754; X == 1.0e-39", F)),
	%% and that is an underflow, an exact tiny result too
	?assertEqual(0, counts(D ++ "Z = X * Y; X == 1.0e-20 && Y == 1.0e-20", F#{underflow => false})),
	?assertEqual(0, counts(Ex, F#{underflow => false})),
	?assertEqual(1, counts(Ex, F#{underflow => true})),
	?assertEqual(1, counts(D ++ "Z = X * Y; X == 1.5 && Y == 2.5", F#{underflow => false}))
      end}}].

%% sqrt: every float754(3,2) pattern against varp_float:sqrt_bits,
%% builtin and library, binary32 against math:sqrt (exact for it:
%% 53 >= 2*24+2), the special values and the literal
sqrt_test_() ->
    D = "declare X:32/float754, Y:32/float754; ",
    Exh = fun(Opts) ->
		  {_, Ms, _} = varp_tc:run("declare X/float754(3,2), Y/float754(3,2); Y = sqrt(X); true",
					   [{satisfy,[]},{backjump,[{max,0}]}], Opts),
		  {length(Ms), [{A,Y} || M <- Ms, A <- [bits(M, <<"X">>)], Y <- [bits(M, <<"Y">>)],
				      Y =/= varp_float:sqrt_bits(A, 3, 2)]}
	  end,
    [{"exhaustive", {timeout, 300, fun() ->
	?assertEqual({64, []}, Exh(#{})),
	?assertEqual({64, []}, Exh(#{ops => lib})) end}},
     {"binary32 against math:sqrt", {timeout, 600, fun() ->
	[begin
	     Want = f32(math:sqrt(f32(V))),
	     ?assertEqual({V,Want}, {V,vbj(D ++ "Y = sqrt(X); X == " ++ float_to_list(V, [short]), "Y", #{})}),
	     <<B:32>> = <<V:32/float>>,
	     ?assertEqual({V,Want}, {V,varp_float:to_float(varp_float:sqrt_bits(B, 8, 23), 8, 23)})
	 end || V <- [2.0, 2.25, 0.1, 123456.789, 1.0e-30, 3.0e38, 1.0000001, 0.5,
		      1.0e-40, 7.0e-46, 1.1754944e-38]],
	?assertEqual(f32(math:sqrt(2.0)), vbj(D ++ "Y = sqrt(X); X == 2", "Y", #{ops => lib})) end}},
     {"special values and the literal", {timeout, 300, fun() ->
	?assertEqual(1, counts(D ++ "Y = sqrt(X); X == -1 && isnan(Y)")),
	?assertEqual(0, counts(D ++ "Y = sqrt(X); X == -1", #{nan => false})),
	?assertEqual(-0.0, vbj(D ++ "Y = sqrt(X); X == -0.0 && Y <= 0", "Y", #{})),
	?assertEqual(1, counts(D ++ "Y = sqrt(X); X == inf && isinf(Y)")),
	?assertEqual(1, counts(D ++ "Y = sqrt(X); X == -inf && isnan(Y)")),
	%% a meta argument is the meta function, a literal
	?assertEqual(4.0, v("declare X:32/float754; X == sqrt(16)", "X")),
	?assertEqual(f32(math:sqrt(2)), v("declare X:32/float754; X == sqrt(2)", "X")),
	?assertEqual(f32(math:sqrt(2)), v("declare X:32/float754; X == sqrt(2.0)", "X")),
	?assertError({sqrt_negative,_}, varp_tc:models("declare X:32/float754; X == sqrt(-2.0)")) end}}].

%% fma: every triple of float754(2,1) against varp_float:fma_fold,
%% builtin and library in both modes, a sample of float754(3,2)
%% triples, binary32 cases (the rounding error of a product is exact)
%% and the special values
fma_test_() ->
    D = "declare X:32/float754, Y:32/float754, Z:32/float754, R:32/float754; ",
    Exh = fun(Opts) ->
		  {_, Ms, _} = varp_tc:run("declare X/float754(2,1), Y/float754(2,1), Z/float754(2,1), R/float754(2,1); R = fma(X, Y, Z); true",
					   [{satisfy,[]},{backjump,[{max,0}]}], Opts),
		  Mode = case maps:get(ftz, Opts, false) of true -> ftz; false -> ieee end,
		  {length(Ms), [{A,B,C,R} || M <- Ms, A <- [bits(M, <<"X">>)], B <- [bits(M, <<"Y">>)],
					  C <- [bits(M, <<"Z">>)], R <- [bits(M, <<"R">>)],
					  R =/= varp_float:fma_bits(A, B, C, 2, 1, Mode)]}
	  end,
    [{"exhaustive float754(2,1)", {timeout, 900, fun() ->
	?assertEqual({4096, []}, Exh(#{})),
	?assertEqual({4096, []}, Exh(#{ftz => true})),
	?assertEqual({4096, []}, Exh(#{ops => lib})),
	?assertEqual({4096, []}, Exh(#{ops => lib, ftz => true})) end}},
     {"a sample of float754(3,2) triples", {timeout, 900, fun() ->
	rand:seed(exsss, {3, 2, 1}),
	%% finite patterns only, as decimal literals (exact for (3,2))
	Fin = [B || B <- lists:seq(0, 63), (B band 16#1c) =/= 16#1c],
	Lit = fun(B) -> varp_float:format(B, 3, 2) end,
	[begin
	     A = lists:nth(rand:uniform(length(Fin)), Fin),
	     B = lists:nth(rand:uniform(length(Fin)), Fin),
	     C = lists:nth(rand:uniform(length(Fin)), Fin),
	     T = "declare X/float754(3,2), Y/float754(3,2), Z/float754(3,2), R/float754(3,2); "
		 "X = " ++ Lit(A) ++ "; Y = " ++ Lit(B) ++ "; Z = " ++ Lit(C) ++ "; R = fma(X, Y, Z); true",
	     {_, [M|_], _} = varp_tc:run(T, [{satisfy,[]},{backjump,[]}]),
	     ?assertEqual({A,B,C,varp_float:fma_bits(A, B, C, 3, 2)}, {A,B,C,bits(M, <<"R">>)})
	 end || _ <- lists:seq(1, 120)] end}},
     {"binary32", {timeout, 600, fun() ->
	?assertEqual(4.0, vbj(D ++ "R = fma(X, Y, Z); X == 1.5 && Y == 2.5 && Z == 0.25", "R", #{})),
	%% the rounding error of a product, exactly: (1+2^-23)^2 - (1+2^-22)
	Err = math:pow(2, -46),
	?assertEqual(Err, vbj(D ++ "R = fma(X, Y, -Z); X == 1.0000001 && Y == 1.0000001 && Z == X * Y", "R", #{})),
	?assertEqual(Err, vbj(D ++ "R = fma(X, Y, -Z); X == 1.0000001 && Y == 1.0000001 && Z == X * Y", "R", #{ops => lib})),
	%% a single rounding: 1 * 1 + 1e30 is 1e30, the product only sticky
	?assertEqual(f32(1.0e30), vbj(D ++ "R = fma(X, Y, Z); X == 1 && Y == 1 && Z == 1.0e30", "R", #{})),
	%% a tiny product survives into the sum, a subnormal result
	?assertEqual(f32(1.0e-40), vbj(D ++ "R = fma(X, Y, Z); X == 1.0e-20 && Y == 1.0e-20 && Z == 0", "R", #{})),
	?assertEqual(f32(f32(1.0e-39) + f32(1.0e-40)), vbj(D ++ "R = fma(X, Y, Z); X == 1.0e-20 && Y == 1.0e-20 && Z == 1.0e-39", "R", #{})),
	%% an exact zero difference is +0, a zero product keeps its sign with a zero addend
	?assertEqual(0.0, vbj(D ++ "R = fma(X, Y, Z); X == 2 && Y == 3 && Z == -6 && R >= 0", "R", #{})),
	?assertEqual(-0.0, vbj(D ++ "R = fma(X, Y, Z); X = -0.0; Y = 2.0; Z = -0.0; R <= 0", "R", #{})),
	?assertEqual(0.0, vbj(D ++ "R = fma(X, Y, Z); X = -0.0; Y = 2.0; Z = 0.0; R >= 0", "R", #{})),
	%% the flags
	?assertEqual(1, counts(D ++ "R = fma(X, Y, Z); X == 1.0e20 && Y == 1.0e20 && Z == -1 && R == inf")),
	?assertEqual(0, counts(D ++ "R = fma(X, Y, Z); X == 1.0e20 && Y == 1.0e20 && Z == -1", #{inf => false})),
	?assertEqual(0, counts(D ++ "R = fma(X, Y, Z); X == 1.0e-20 && Y == 1.0e-20 && Z == 0", #{underflow => false})),
	?assertEqual(0.0, vbj(D ++ "R = fma(X, Y, Z); X == 1.0e-20 && Y == 1.0e-20 && Z == 0", "R", #{ftz => true})) end}},
     {"special values", {timeout, 600, fun() ->
	?assertEqual(1, counts(D ++ "Y = 0.0; R = fma(X, Y, Z); X == inf && Z == 1 && isnan(R)")),
	?assertEqual(1, counts(D ++ "R = fma(X, Y, Z); X == inf && Y == 1 && Z == -inf && isnan(R)")),
	?assertEqual(1, counts(D ++ "R = fma(X, Y, Z); X == inf && Y == 1 && Z == inf && R == inf")),
	?assertEqual(1, counts(D ++ "R = fma(X, Y, Z); X == inf && Y == -1 && Z == 1 && R == -inf")),
	?assertEqual(1, counts(D ++ "R = fma(X, Y, Z); X == 1 && Y == 1 && Z == -inf && R == -inf")),
	?assertEqual(0, counts(D ++ "Y = 0.0; R = fma(X, Y, Z); X == inf && Z == 1", #{nan => false})),
	%% (one model: every NaN pattern is one, do not enumerate them)
	{0, Out1} = varp_tc:cli(["--print","model","-f", D ++ "Z = X * X; R = fma(X, X, -Z); isnan(X)", "sat","bj"]),
	?assertNotEqual(nomatch, string:find(Out1, "R=nan")),
	%% an operator or a call in an argument builds now
	{0, Out2} = varp_tc:cli(["--print","model","-f", "declare Z:32/float754; isnan(min(Z, Z))", "sat","bj"]),
	?assertNotEqual(nomatch, string:find(Out2, "Z=nan")),
	?assertEqual(0, counts("declare Z:32/float754; isnan(min(Z, Z)) && Z == 1")),
	?assertEqual(f32(1.0e30), vbj(D ++ "R = fma(X + 1, Y, Z); X == 0 && Y == 1 && Z == 1.0e30", "R", #{})) end}}].

%% the circuit library: op_fmul, op_fadd and op_fdiv over op_fnorm,
%% op_fpack, op_fresult and op_fclass, every pair of float754(3,2) in
%% both modes against the references, and the flags
float_lib_test_() ->
    L = #{ops => lib},
    Exh = fun(Op, Ref, Opts) ->
		  T = "declare X/float754(3,2), Y/float754(3,2), Z/float754(3,2); Z = X " ++ Op ++ " Y; true",
		  {_, Ms, _} = varp_tc:run(T, [{satisfy,[]},{backjump,[{max,0}]}], Opts),
		  Mode = case maps:get(ftz, Opts, false) of true -> ftz; false -> ieee end,
		  Bad = [{A,B,Z} || M <- Ms, A <- [bits(M, <<"X">>)], B <- [bits(M, <<"Y">>)],
				    Z <- [bits(M, <<"Z">>)], Z =/= varp_float:Ref(A, B, 3, 2, Mode)],
		  {length(Ms), Bad}
	  end,
    D = "declare X:32/float754, Y:32/float754, Z:32/float754; ",
    [{"mul exhaustive", {timeout, 600, fun() ->
	?assertEqual({4096, []}, Exh("*", mul_bits, L)),
	?assertEqual({4096, []}, Exh("*", mul_bits, L#{ftz => true})) end}},
     {"add exhaustive", {timeout, 600, fun() ->
	?assertEqual({4096, []}, Exh("+", add_bits, L)),
	?assertEqual({4096, []}, Exh("+", add_bits, L#{ftz => true})) end}},
     {"div exhaustive", {timeout, 900, fun() ->
	?assertEqual({4096, []}, Exh("/", div_bits, L#{fdivz => ignore})),
	?assertEqual({4096, []}, Exh("/", div_bits, L#{fdivz => ignore, ftz => true})),
	%% x/0 has no model by default
	?assertEqual({4096 - 2*62, []}, Exh("/", div_bits, L)) end}},
     {"binary32 and the flags", {timeout, 600, fun() ->
	?assertEqual(f32(1.0e-40), vbj(D ++ "Z = X * Y; X == 1.0e-20 && Y == 1.0e-20", "Z", L)),
	?assertEqual(f32(1.0e-40), vbj(D ++ "Z = X / Y; X == 1.0e-20 && Y == 1.0e20", "Z", L)),
	?assertEqual(f32(2.0e-39), vbj(D ++ "Z = X + Y; X == 1.0e-39 && Y == 1.0e-39", "Z", L)),
	?assertEqual(0.0, vbj(D ++ "Z = X * Y; X == 1.0e-20 && Y == 1.0e-20", "Z", L#{ftz => true})),
	?assertEqual(0, counts(D ++ "Z = X * Y; X == 1.0e-20 && Y == 1.0e-20", L#{underflow => false})),
	?assertEqual(1, counts(D ++ "Z = X * Y; X == 1.0e-20 && Y == 1.0e-20", L#{underflow => true})),
	?assertEqual(0, counts(D ++ "X == 3.0e38 && Z == X * 10", L#{inf => false})),
	?assertEqual(1, counts(D ++ "X == 3.0e38 && Z == X * 10 && Z == inf", L)),
	?assertEqual(0, counts(D ++ "Z = X + Y; X == inf && Y == -inf", L#{nan => false})),
	?assertEqual(1, counts(D ++ "Z = X + Y; X == inf && Y == -inf && isnan(Z)", L)),
	?assertEqual(0, counts(D ++ "Y = 0.0; Z = X / Y; X == -1", L)),
	?assertEqual(-inf_f32(), vbj(D ++ "Y = 0.0; Z = X / Y; X == -1", "Z", L#{fdivz => ignore})),
	?assertEqual(1, counts(D ++ "X = 0.0; Y = 0.0; Z = X / Y; isnan(Z)", L))
      end}}].

%% NaN: the invalid operations, propagation, unordered comparison,
%% isnan/isinf and --nan
nan_test_() ->
    D = "declare X:32/float754, Y:32/float754, Z:32/float754, W:32/float754; ",
    %% (a zero is pinned by a statement: Y == 0.0 has two models)
    [{"invalid operations give NaN", {timeout, 300, fun() ->
	?assertEqual(1, counts(D ++ "Z = X + Y; X == inf && Y == -inf && isnan(Z)")),
	?assertEqual(1, counts(D ++ "Z = X - Y; X == inf && Y == inf && isnan(Z)")),
	?assertEqual(1, counts(D ++ "Y = 0.0; Z = X * Y; X == inf && isnan(Z)")),
	?assertEqual(1, counts(D ++ "Z = X / Y; X == inf && Y == -inf && isnan(Z)")),
	?assertEqual(1, counts(D ++ "X = 0.0; Y = -0.0; Z = X / Y; isnan(Z)")),
	%% inf stays inf, x / inf is zero
	?assertEqual(1, counts(D ++ "Z = X - Y; X == inf && Y == 2.5 && isinf(Z) && Z > 0")),
	?assertEqual(1, counts(D ++ "Z = X + Y; X == -inf && Y == -inf && Z == -inf")),
	?assertEqual(1, counts(D ++ "Z = X * Y; X == inf && Y == -0.5 && Z == -inf")),
	?assertEqual(1, counts(D ++ "Z = X / Y; X == 2.5 && Y == inf && Z == 0.0 && !isinf(Z)")),
	%% a NaN operand propagates (six NaN patterns in float754(3,2)),
	%% the result is the quiet NaN
	S = "declare X/float754(3,2), Y/float754(3,2), Z/float754(3,2); ",
	?assertEqual(6, counts(S ++ "Z = X + Y; X == 1.5 && isnan(Y) && isnan(Z) && Z == Z == false")),
	?assertEqual(6, counts(S ++ "Z = X * Y; isnan(X) && Y == 2.0 && isnan(Z) && Z >= 0 == false")),
	?assertEqual(6, counts(S ++ "Z = X / Y; isnan(X) && Y == 2.0 && isnan(Z) && Z == Y == false"))
      end}},
     {"unordered", {timeout, 300, fun() ->
	N = D ++ "X = 0.0; Y = 0.0; Z = X / Y; ",
	?assertEqual(1, counts(N ++ "Z != Z")),
	?assertEqual(0, counts(N ++ "Z == Z")),
	?assertEqual(0, counts(N ++ "Z < 1")),
	?assertEqual(0, counts(N ++ "Z >= 1")),
	?assertEqual(0, counts(N ++ "Z == inf")),
	?assertEqual(1, counts(N ++ "Z != 1.0 && Z != inf")),
	%% minNum: the number wins, NaN only when both are
	?assertEqual(1, counts(N ++ "min(Z, 1.0) == 1.0")),
	?assertEqual(1, counts(N ++ "max(-2.0, Z) == -2.0")),
	%% (a call inside a call is a meta expression, so W is assigned)
	?assertEqual(1, counts(D ++ "X = 0.0; Y = 0.0; Z = X / Y; W = min(Z, Z); isnan(W)"))
      end}},
     {"isnan and isinf", fun() ->
	?assertEqual(1, counts("declare X:32/float754; isinf(X) && X > 0")),
	?assertEqual(1, counts("declare X:32/float754; isinf(X) && X < 0")),
	%% three NaN patterns of each sign in float754(3,2)
	?assertEqual(6, counts("declare X/float754(3,2); isnan(X)")),
	?assertEqual(2, counts("declare X/float754(3,2); isinf(X)")),
	?assertEqual(1, counts("declare N:4; N == 3 && !isnan(N) && !isinf(N)"))
      end},
     {"--nan", {timeout, 300, fun() ->
	?assertEqual(0, counts(D ++ "Z = X + Y; X == inf && Y == -inf", #{nan => false})),
	?assertEqual(0, counts(D ++ "X = 0.0; Y = 0.0; Z = X / Y; true", #{nan => false})),
	%% a NaN operand is a NaN result, forbidden as well
	?assertEqual(0, counts(D ++ "Z = X + 1.0; isnan(X)", #{nan => false})),
	?assertEqual(1, counts(D ++ "X = 0.0; Y = 0.0; Z = X / Y; true", #{nan => true})),
	?assertEqual(0, counts(D ++ "Z = X / Y; X == 1.0 && Y == 2.0", #{nan => true}))
      end}}].

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
	    {0.3,3.0}, {1.0000001,1.0000001}, {-7.25,-0.125}, {65536.0,0.5},
	    %% subnormal results, and a subnormal factor
	    {1.0e-20,1.0e-20}, {-3.0e-39,0.5}, {1.1e-38,0.75}, {2.0e-45,0.75}, {3.0e-39,7.0}],
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

%% the same, flushed to zero
mul_exhaustive_ftz_test_() ->
    {timeout, 900, fun() ->
	{_, Ms2, _} = varp_tc:run("declare X/float754(3,2), Y/float754(3,2), Z/float754(3,2); Z = X * Y; true",
				  [{satisfy,[]},{backjump,[{max,0}]}], #{ftz => true}),
	?assertEqual(4096, length(Ms2)),
	Bad2 = [{A,B,Z} || M <- Ms2,
			   A <- [bits(M, <<"X">>)], B <- [bits(M, <<"Y">>)], Z <- [bits(M, <<"Z">>)],
			   Z =/= varp_float:mul_bits(A, B, 3, 2, ftz)],
	?assertEqual([], Bad2)
     end}.

%% zero, overflow, the sign of a zero (the statement form pins the bits)
mul_edge_test() ->
    D = "declare X:32/float754, Y:32/float754, Z:32/float754; ",
    ?assertEqual(-0.0, v(D ++ "X = 0.0; Y = -2.5; Z = X * Y; Z <= 0", "Z")),
    ?assertEqual(-0.0, v(D ++ "X = -0.0; Y = 2.5; Z = X * Y; Z <= 0", "Z")),
    ?assertEqual(0.0,  v(D ++ "X = 1.0e-30; Y = 1.0e-20; Z = X * Y; Z >= 0", "Z")),
    ?assertEqual(-0.0, v(D ++ "X = -1.0e-30; Y = 1.0e-20; Z = X * Y; Z <= 0", "Z")),
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
    ?assertError({float754_operator,'rem'},
		 varp_tc:models("declare X:32/float754, Y:32/float754; X == Y % 2.0")),
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
