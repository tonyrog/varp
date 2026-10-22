%%% The circuit library lib/default: the arithmetic and comparison
%%% operators written in varp and loaded on first use.
%%%
%%% Two kinds of tests.  The value tests are the arithmetic and
%%% comparison tests of varp_formula_tests with the library circuits
%%% in place of the operators.  The proofs ask `prove' to show, for
%%% every input of the given widths, that a library circuit and the
%%% built in operator agree, which is what makes a library encoding
%%% safe to swap in.

-module(varp_lib_tests).
-include_lib("eunit/include/eunit.hrl").

models(Text) -> varp_tc:models(Text).
sat(Text) -> varp_tc:is_sat(Text).
unsat(Text) -> varp_tc:is_unsat(Text).

v(Text, Var) ->
    [M] = models(Text),
    proplists:get_value(Var, M).

%% the library files are found through the default path
autoload_test() ->
    ?assert(lists:any(fun(F) -> filename:basename(F) =:= "op_add.varp" end,
		      varp_lib:files())),
    %% a name that is not in the library stays a variable, and a
    %% circuit the file defines itself shadows the library's
    ?assert(sat("nosuch(1) && nosuch(2)")),
    ?assertEqual(1, v("circuit op_add(in a:n, b:m; return s:n) { s = a & b; }\n"
		      "declare X:4,Y:4,Z:4; X==3 && Y==5 && Z==op_add(X,Y)", "Z")).

%% an explicit import, imported once, and a missing file is an error
import_test() ->
    ?assertEqual(9, v("import op_add;\ndeclare X:4,Y:4,Z:4;\n"
		      "(X==5) && (Y==4) && (Z==op_add(X,Y))", "Z")),
    ?assertEqual(9, v("import op_add; import op_add; import op_full_adder;\n"
		      "declare X:4,Y:4,Z:4; (X==5) && (Y==4) && (Z==op_add(X,Y))", "Z")),
    ?assertMatch({error,{1,varp_parse,_}}, varp_tc:parse_only("import nosuchfile;\ntrue")).

%% a library circuit as the very first token, "varp -f 'op_bxor(2,3) == 1'"
first_token_test() ->
    ?assert(sat("op_bxor(2, 3) == 1")),
    ?assert(unsat("op_bxor(2, 3) == 0")),
    ?assert(sat("op_add(2, 3) == 5 && op_lt(2, 3)")).

%%%-------------------------------------------------------------------
%%% Values, mirroring varp_formula_tests
%%%-------------------------------------------------------------------

add_test() ->
    ?assertEqual(9, v("declare X:4,Y:4,Z:4; (X==5) && (Y==4) && (Z==op_add(X,Y))","Z")),
    ?assertEqual(0, v("declare X:4,Y:4,Z:4; (X==0) && (Y==0) && (Z==op_add(X,Y))","Z")),
    %% the carry is the top bit of the result
    ?assertEqual(17, v("declare X:4,Y:4,Z:5; (X==9) && (Y==8) && (Z==op_add(X,Y))","Z")).

sub_test() ->
    ?assertEqual(2, v("declare X:4,Y:4,Z:4; (X==5) && (Y==3) && (Z==op_sub(X,Y))","Z")),
    ?assertEqual(14, v("declare X:4,Y:4,Z:4; (X==3) && (Y==5) && (Z==op_sub(X,Y))","Z")).

neg_test() ->
    ?assertEqual(13, v("declare X:4,Z:4; (X==3) && (Z==op_neg(X))","Z")).

mul_test() ->
    ?assertEqual(12, v("declare X:4,Y:4,Z:8; (X==3) && (Y==4) && (Z==op_mul(X,Y))","Z")),
    ?assertEqual(225, v("declare X:4,Y:4,Z:8; (X==15) && (Y==15) && (Z==op_mul(X,Y))","Z")).

div_rem_test() ->
    ?assertEqual(3, v("declare X:8,Y:8,Z:8,R:8; (X==13) && (Y==4) && (Z==op_div(X,Y,R))","Z")),
    ?assertEqual(1, v("declare X:8,Y:8,Z:8,R:8; (X==13) && (Y==4) && (Z==op_div(X,Y,R))","R")),
    ?assertEqual(1, v("declare X:8,Y:8,Z:8; (X==13) && (Y==4) && (Z==op_rem(X,Y))","Z")).

sdiv_srem_test() ->
    D = "declare X:6/signed,Y:6/signed,Q:7/signed,R:6/signed;",
    ?assertEqual(-3, v(D ++ "(X==-13) && (Y==4) && (Q==op_sdiv(X,Y,R))", "Q")),
    ?assertEqual(-1, v(D ++ "(X==-13) && (Y==4) && (Q==op_sdiv(X,Y,R))", "R")),
    ?assertEqual(-3, v(D ++ "(X==13) && (Y==-4) && (Q==op_sdiv(X,Y,R))", "Q")),
    ?assertEqual(1,  v(D ++ "(X==13) && (Y==-4) && (Q==op_sdiv(X,Y,R))", "R")),
    ?assertEqual(3,  v(D ++ "(X==-13) && (Y==-4) && (Q==op_sdiv(X,Y,R))", "Q")),
    ?assertEqual(-1, v(D ++ "(X==-13) && (Y==4) && (R==op_srem(X,Y))", "R")),
    %% -8 / -1 = 8: the quotient has one bit more than the dividend
    ?assertEqual(8, v("declare X:4/signed,Y:4/signed,Q:5/signed,R:4/signed;"
		      "(X==-8) && (Y==-1) && (Q==op_sdiv(X,Y,R))", "Q")).

sadd_ssub_smul_test() ->
    D = "declare X:4/signed,Y:4/signed,S:5/signed,P:8/signed;",
    ?assertEqual(-15, v(D ++ "(X==-7) && (Y==-8) && (S==op_sadd(X,Y))", "S")),
    ?assertEqual(1,   v(D ++ "(X==-7) && (Y==-8) && (S==op_ssub(X,Y))", "S")),
    ?assertEqual(-15, v(D ++ "(X==-8) && (Y==7) && (S==op_ssub(X,Y))", "S")),
    ?assertEqual(56,  v(D ++ "(X==-7) && (Y==-8) && (P==op_smul(X,Y))", "P")),
    ?assertEqual(-56, v(D ++ "(X==7) && (Y==-8) && (P==op_smul(X,Y))", "P")),
    %% -8 * -8 = 64 needs all n+m bits
    ?assertEqual(64,  v(D ++ "(X==-8) && (Y==-8) && (P==op_smul(X,Y))", "P")),
    %% mixed widths: the narrower operand is sign extended
    ?assertEqual(11,  v("declare X:3/signed,Y:5/signed,S:6/signed;"
                        "(X==-4) && (Y==15) && (S==op_sadd(X,Y))", "S")),
    ?assertEqual(-60, v("declare X:3/signed,Y:5/signed,P:8/signed;"
                        "(X==-4) && (Y==15) && (P==op_smul(X,Y))", "P")).

compare_test() ->
    ?assert(sat("declare X:4,Y:4; (X==3) && (Y==5) && op_lt(X,Y)")),
    ?assert(unsat("declare X:4,Y:4; (X==3) && (Y==5) && op_gt(X,Y)")),
    ?assert(sat("declare X:4,Y:4; (X==3) && (Y==3) && op_lte(X,Y) && op_gte(X,Y)")),
    ?assert(sat("declare X:4,Y:4; (X==3) && (Y==5) && op_neq(X,Y)")),
    ?assert(unsat("declare X:4,Y:4; (X==3) && (Y==5) && op_eq(X,Y)")),
    ?assert(sat("declare X:4,Y:4; (X==3) && (Y==5) && op_lt(X,Y) && !op_gt(X,Y) && !op_eq(X,Y)")).

%% signed comparisons: the narrower operand is sign extended
scompare_test() ->
    D = "declare X:4/signed,Y:4/signed;",
    ?assert(sat(D ++ "(X==-3) && (Y==5) && op_slt(X,Y)")),
    ?assert(unsat(D ++ "(X==-3) && (Y==5) && op_sgt(X,Y)")),
    ?assert(sat(D ++ "(X==-8) && (Y==7) && op_slt(X,Y) && op_slte(X,Y) && op_sneq(X,Y)")),
    ?assert(sat(D ++ "(X==7) && (Y==-8) && op_sgt(X,Y) && op_sgte(X,Y)")),
    ?assert(sat(D ++ "(X==-3) && (Y==-3) && op_slte(X,Y) && op_sgte(X,Y) && op_seq(X,Y)")),
    ?assert(unsat(D ++ "(X==-3) && (Y==-3) && op_slt(X,Y)")),
    %% unsigned the same bits say 13 < 5 is false
    ?assert(unsat("declare X:4,Y:4; (X==13) && (Y==5) && op_lt(X,Y)")),
    %% mixed widths: -1:3 == -1:5, and -4:3 < 15:5
    ?assert(sat("declare X:3/signed,Y:5/signed; (X==-1) && (Y==-1) && op_seq(X,Y)")),
    ?assert(unsat("declare X:3/signed,Y:5/signed; (X==-1) && (Y==-1) && op_sneq(X,Y)")),
    ?assert(sat("declare X:3/signed,Y:5/signed; (X==-4) && (Y==15) && op_slt(X,Y)")).

smin_smax_sneg_test() ->
    D = "declare X:4/signed,Y:4/signed,Z:4/signed;",
    ?assertEqual(-3, v(D ++ "(X==-3) && (Y==5) && (Z==op_smin(X,Y))", "Z")),
    ?assertEqual(5,  v(D ++ "(X==-3) && (Y==5) && (Z==op_smax(X,Y))", "Z")),
    ?assertEqual(-8, v(D ++ "(X==7) && (Y==-8) && (Z==op_smin(X,Y))", "Z")),
    ?assertEqual(-4, v("declare X:3/signed,Y:5/signed,Z:5/signed;"
                       "(X==-4) && (Y==15) && (Z==op_smin(X,Y))", "Z")),
    ?assertEqual(3,  v("declare X:4/signed,Z:5/signed; (X==-3) && (Z==op_sneg(X))", "Z")),
    %% -(-8) = 8 needs the extra bit
    ?assertEqual(8,  v("declare X:4/signed,Z:5/signed; (X==-8) && (Z==op_sneg(X))", "Z")).

%% rotations by a build time constant
rotate_test() ->
    ?assertEqual(6,  v("declare X:4,Z:4; (X==3) && (Z==op_rol(1,X))", "Z")),
    ?assertEqual(9,  v("declare X:4,Z:4; (X==3) && (Z==op_ror(1,X))", "Z")),
    ?assertEqual(6,  v("declare X:4,Z:4; (X==3) && (Z==op_rol(5,X))", "Z")),
    ?assertEqual(3,  v("declare X:4,Z:4; (X==3) && (Z==op_rol(4,X))", "Z")),
    ?assertEqual(12, v("declare X:4,Z:4; (X==3) && (Z==op_ror(2,X))", "Z")).

%% shifts by a build time constant (a meta parameter)
shift_test() ->
    ?assertEqual(12, v("declare X:4,Z:6; (X==3) && (Z==op_shl(2,X))", "Z")),
    ?assertEqual(3,  v("declare X:4,Z:4; (X==13) && (Z==op_shr(2,X))", "Z")),
    ?assertEqual(0,  v("declare X:4,Z:4; (X==13) && (Z==op_shr(5,X))", "Z")),
    ?assertEqual(-2, v("declare X:4/signed,Z:4/signed; (X==-8) && (Z==op_sar(2,X))", "Z")),
    ?assertEqual(-1, v("declare X:4/signed,Z:4/signed; (X==-8) && (Z==op_sar(7,X))", "Z")),
    ?assertEqual(1,  v("declare X:4/signed,Z:4/signed; (X==7) && (Z==op_sar(2,X))", "Z")).

min_max_test() ->
    ?assertEqual(3, v("declare X:4,Y:4,Z:4; (X==3) && (Y==5) && (Z==op_min(X,Y))","Z")),
    ?assertEqual(5, v("declare X:4,Y:4,Z:4; (X==3) && (Y==5) && (Z==op_max(X,Y))","Z")).

bitwise_test() ->
    ?assertEqual(8, v("declare X:4,Y:4,Z:4; X==12 && Y==10 && Z==op_band(X,Y)","Z")),
    ?assertEqual(14, v("declare X:4,Y:4,Z:4; X==12 && Y==10 && Z==op_bor(X,Y)","Z")),
    ?assertEqual(6, v("declare X:4,Y:4,Z:4; X==12 && Y==10 && Z==op_bxor(X,Y)","Z")),
    ?assertEqual(3, v("declare X:4,Z:4; X==12 && Z==op_bnot(X)","Z")).

%% mixed widths: the narrower operand is zero extended
mixed_width_test() ->
    ?assertEqual(20, v("declare X:3,Y:5,Z:6; (X==7) && (Y==13) && (Z==op_add(X,Y))","Z")),
    ?assertEqual(91, v("declare X:3,Y:5,Z:8; (X==7) && (Y==13) && (Z==op_mul(X,Y))","Z")),
    ?assert(sat("declare X:3,Y:5; (X==7) && (Y==13) && op_lt(X,Y)")).

factoring_test() ->
    Ms = models("declare X:4,Y:4; (op_mul(X,Y) == 15) && op_gt(X,1) && op_gt(Y,1) && op_lte(X,Y)"),
    ?assertEqual([[{"X",3},{"Y",5}]],
		 [[{K,V} || {K,V} <- M, K =:= "X" orelse K =:= "Y"] || M <- Ms]).

%%%-------------------------------------------------------------------
%%% Proofs: library circuit == built in operator, for all inputs
%%%-------------------------------------------------------------------

proof(Text, N, M) ->
    varp_tc:is_tautology(Text, #{meta => #{<<"n">> => N, <<"m">> => M}}).

widths() -> [{2,2},{3,3},{4,4},{2,4},{4,3}].

proof_test_() ->
    Cases =
	[{"op_add",  "declare X:n, Y:m; op_add(X,Y) == X + Y"},
	 {"op_sub",  "declare X:n, Y:m, D:(max(n,m)); D = X - Y; op_sub(X,Y) == D"},
	 {"op_neg",  "declare X:n, D:n; D = 0 - X; op_neg(X) == D"},
	 {"op_mul",  "declare X:n, Y:m; op_mul(X,Y) == X * Y"},
	 {"op_div", "declare X:n, Y:m, R:m;"
	          "(Y != 0) implies ((op_div(X,Y,R) == X / Y) && (R == X % Y))"},
	 {"op_rem", "declare X:n, Y:m; (Y != 0) implies (op_rem(X,Y) == X % Y)"},
	 {"op_sdiv", "declare X:n/signed, Y:m/signed, R:m/signed;"
	           "(Y != 0) implies ((op_sdiv(X,Y,R) == X / Y) && (R == X % Y))"},
	 {"op_srem", "declare X:n/signed, Y:m/signed;"
	           "(Y != 0) implies (op_srem(X,Y) == X % Y)"},
	 {"op_sadd", "declare X:n/signed, Y:m/signed; op_sadd(X,Y) == X + Y"},
	 {"op_ssub", "declare X:n/signed, Y:m/signed; op_ssub(X,Y) == X - Y"},
	 {"op_smul", "declare X:n/signed, Y:m/signed; op_smul(X,Y) == X * Y"},
	 {"op_slt",  "declare X:n/signed, Y:m/signed; op_slt(X,Y) equ (X < Y)"},
	 {"op_slte", "declare X:n/signed, Y:m/signed; op_slte(X,Y) equ (X <= Y)"},
	 {"op_sgt",  "declare X:n/signed, Y:m/signed; op_sgt(X,Y) equ (X > Y)"},
	 {"op_sgte", "declare X:n/signed, Y:m/signed; op_sgte(X,Y) equ (X >= Y)"},
	 {"op_seq",  "declare X:n/signed, Y:m/signed; op_seq(X,Y) equ (X == Y)"},
	 {"op_sneq", "declare X:n/signed, Y:m/signed; op_sneq(X,Y) equ (X != Y)"},
	 {"op_smin", "declare X:n/signed, Y:m/signed; op_smin(X,Y) == min(X,Y)"},
	 {"op_smax", "declare X:n/signed, Y:m/signed; op_smax(X,Y) == max(X,Y)"},
	 {"op_sneg", "declare X:n/signed; op_sneg(X) == -X"},
	 {"op_shl",  "declare X:n; op_shl(m, X) == X << m"},
	 {"op_shr",  "declare X:n; op_shr(m, X) == X >> m"},
	 {"op_sar",  "declare X:n/signed; op_sar(m, X) == X >> m"},
	 {"op_rol",  "declare X:n; op_rol(m, X) == (X <<< m)"},
	 {"op_ror",  "declare X:n; op_ror(m, X) == (X >>> m)"},
	 {"op_rol op_ror", "declare X:n; op_rol(m, op_ror(m, X)) == X"},
	 {"op_lt",   "declare X:n, Y:m; op_lt(X,Y) equ (X < Y)"},
	 {"op_lte",  "declare X:n, Y:m; op_lte(X,Y) equ (X <= Y)"},
	 {"op_gt",   "declare X:n, Y:m; op_gt(X,Y) equ (X > Y)"},
	 {"op_gte",  "declare X:n, Y:m; op_gte(X,Y) equ (X >= Y)"},
	 {"op_eq",   "declare X:n, Y:m; op_eq(X,Y) equ (X == Y)"},
	 {"op_neq",  "declare X:n, Y:m; op_neq(X,Y) equ (X != Y)"},
	 {"op_min", "declare X:n, Y:m; op_min(X,Y) == min(X,Y)"},
	 {"op_max", "declare X:n, Y:m; op_max(X,Y) == max(X,Y)"},
	 {"op_band", "declare X:n, Y:m; op_band(X,Y) == (X & Y)"},
	 {"op_bor",  "declare X:n, Y:m; op_bor(X,Y) == (X | Y)"},
	 {"op_bxor", "declare X:n, Y:m; op_bxor(X,Y) == (X ^ Y)"},
	 {"op_bnot", "declare X:n, D:n; D = ~X; op_bnot(X) == D"}],
    [{Name ++ " n=" ++ integer_to_list(N) ++ " m=" ++ integer_to_list(M),
      {timeout, 300, fun() -> ?assert(proof(Text, N, M)) end}}
     || {Name, Text} <- Cases, {N, M} <- widths()].

%%%-------------------------------------------------------------------
%%% --ops lib: the operators built from the library.  Every model of a
%%% formula must be the same whichever way the operators are built,
%%% the library locals (op_add#3.C ...) left out.
%%%-------------------------------------------------------------------

project(Ms) ->
    [[KV || KV = {K,_} <- M, not lists:member($#, K)] || M <- Ms].

same_models(Text) ->
    Builtin = project(models(Text)),
    Lib = project(varp_tc:models(Text, #{ops => lib})),
    ?assertEqual(Builtin, Lib),
    Builtin.

ops_lib_test_() ->
    U = "declare X:3, Y:3, Z:6; ",
    S = "declare X:3/signed, Y:3/signed, Z:6/signed; ",
    Mx = "declare X:3/signed, Y:2, Z:6/signed; ",
    Cases =
	[{"add", U ++ "Z == X + Y"}, {"sadd", S ++ "Z == X + Y"}, {"madd", Mx ++ "Z == X + Y"},
	 {"sub", U ++ "Z == X - Y"}, {"ssub", S ++ "Z == X - Y"}, {"msub", Mx ++ "Z == X - Y"},
	 {"mul", U ++ "Z == X * Y"}, {"smul", S ++ "Z == X * Y"}, {"mmul", Mx ++ "Z == X * Y"},
	 {"div", U ++ "Y != 0 && Z == X / Y"}, {"sdiv", S ++ "Y != 0 && Z == X / Y"},
	 {"mdiv", Mx ++ "Y != 0 && Z == X / Y"},
	 {"rem", U ++ "Y != 0 && Z == X % Y"}, {"srem", S ++ "Y != 0 && Z == X % Y"},
	 {"min", U ++ "Z == min(X,Y)"}, {"smin", S ++ "Z == min(X,Y)"},
	 {"max", U ++ "Z == max(X,Y)"}, {"smax", S ++ "Z == max(X,Y)"},
	 {"lt", U ++ "X < Y"}, {"slt", S ++ "X < Y"}, {"mlt", Mx ++ "X < Y"},
	 {"lte", U ++ "X <= Y"}, {"slte", S ++ "X <= Y"},
	 {"gt", U ++ "X > Y"}, {"sgt", S ++ "X > Y"},
	 {"gte", U ++ "X >= Y"}, {"sgte", S ++ "X >= Y"},
	 {"eq", U ++ "X == Y"}, {"seq", "declare X:3/signed, Y:5/signed; X == Y"},
	 {"neq", U ++ "X != Y"}, {"sneq", "declare X:3/signed, Y:5/signed; X != Y"},
	 {"band", U ++ "Z == (X & Y)"}, {"bor", U ++ "Z == (X | Y)"}, {"bxor", U ++ "Z == (X ^ Y)"},
	 {"bnot", U ++ "Z == ~X"},
	 {"shl", U ++ "Z == X << 2"}, {"sshl", S ++ "Z == X << 2"},
	 {"shr", U ++ "Z == X >> 1"}, {"sar", S ++ "Z == X >> 1"},
	 {"rol", U ++ "Z == X <<< 1"}, {"ror", U ++ "Z == X >>> 2"},
	 {"srol", S ++ "Z == X <<< 1"}, {"sror", S ++ "Z == X >>> 1"},
	 {"neg", U ++ "Z == -X"}, {"sneg", S ++ "Z == -X"},
	 {"statement", "declare X:3, Y:3, Z:6; X = 5; Y = 3; Z = X * Y;"},
	 {"signed statement", "declare X:3/signed, Y:3/signed, Z:4/signed; X = -4; Y = 3; Z = X - Y;"},
	 {"compare statement", "declare X:3, Y:3, q; X = 5; Y = 3; q = (X < Y);"},
	 {"nested", U ++ "Z == (X + Y) * (X - Y) + 1"},
	 {"bool operand", "declare X:3, b, Z:4; Z == X + b"},
	 {"factoring", "declare X:4,Y:4; (X*Y == 15) && (X>1) && (Y>1) && (X<=Y)"}],
    [{Name, {timeout, 120, fun() -> same_models(Text) end}} || {Name, Text} <- Cases]
    ++
    [{"the library is in use", {timeout, 60,
      fun() ->
	      [M|_] = varp_tc:models("declare X:2,Y:2; X + Y == 3",
				     #{ops => lib, locals => true}),
	      ?assert(lists:any(fun({K,_}) -> lists:prefix("op_add#", K) end, M))
      end}},
     {"a file circuit shadows the library under --ops lib", {timeout, 60,
      fun() ->
	      %% op_add defined as bitwise and: 5 + 4 becomes 4
	      Text = "circuit op_add(in a:n, b:m; return s:n) { s = a & b; }\n"
		  "declare X:4,Y:4,Z:4; X==5 && Y==4 && Z==X+Y",
	      [M] = varp_tc:models(Text, #{ops => lib}),
	      ?assertEqual(4, proplists:get_value("Z", M))
      end}}].
