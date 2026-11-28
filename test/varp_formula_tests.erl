%%% Formula building (varp_formula:build/2) tests.
%%%
%%% Everything is checked by enumerating all models, which exercises the
%%% whole chain: parser -> bld -> gates/arithmetic -> clauses -> solver.
-module(varp_formula_tests).

-include_lib("eunit/include/eunit.hrl").
-include("../src/varp.hrl").

count(T) -> varp_tc:count(T).
models(T) -> varp_tc:models(T).
sat(T) -> varp_tc:is_sat(T).
unsat(T) -> varp_tc:is_unsat(T).
taut(T) -> varp_tc:is_tautology(T).

%% the models of a two variable formula, as a sorted list of {A,B}
tt2(T) ->
    lists:sort([{proplists:get_value("A",M), proplists:get_value("B",M)}
		|| M <- models(T)]).

%%%-------------------------------------------------------------------
%%% Constants
%%%-------------------------------------------------------------------

constant_test() ->
    ?assertEqual(1, count("true")),
    ?assertEqual(0, count("false")),
    ?assert(unsat("A && !A")),
    ?assert(sat("A || !A")),
    ?assertEqual(2, count("A || !A")).

%%%-------------------------------------------------------------------
%%% Truth tables
%%%-------------------------------------------------------------------

and_test() ->
    ?assertEqual([{true,true}], tt2("A and B")),
    ?assertEqual([{true,true}], tt2("A && B")).

or_test() ->
    ?assertEqual([{false,true},{true,false},{true,true}], tt2("A or B")).

xor_test() ->
    ?assertEqual([{false,true},{true,false}], tt2("A xor B")).

imp_test() ->
    ?assertEqual([{false,false},{false,true},{true,true}], tt2("A -> B")).

equ_test() ->
    ?assertEqual([{false,false},{true,true}], tt2("A <-> B")).

not_test() ->
    ?assertEqual([[{"A",false}]], models("not A")),
    ?assertEqual([[{"A",false}]], models("!A")).

ite_test() ->
    %% C ? A : B  with C true selects A
    ?assertEqual(1, count("(true ? A : B) && A && !B")),
    ?assertEqual(0, count("(true ? A : B) && !A")),
    ?assertEqual(0, count("(false ? A : B) && !B")).

de_morgan_test() ->
    ?assert(taut("!(A and B) <-> (!A or !B)")),
    ?assert(taut("!(A or B) <-> (!A and !B)")).

tautology_test() ->
    ?assert(taut("A or !A")),
    ?assert(taut("(A -> B) <-> (!A or B)")),
    ?assert(taut("((A -> B) and (B -> C)) -> (A -> C)")),
    ?assertNot(taut("A and B")),
    ?assertNot(taut("A")).

%%%-------------------------------------------------------------------
%%% Quantifiers
%%%-------------------------------------------------------------------

%% n free booleans P(1)..P(n) -> 2^n models
all_quantifier_test() ->
    ?assertEqual(1, count("[A i=1..4] P(i)")),
    ?assertEqual(1, count("[ALL i=1..4] P(i)")),
    ?assertEqual(1, count("[ALL](A,B)")).

any_quantifier_test() ->
    ?assertEqual(15, count("[E i=1..4] P(i)")),
    ?assertEqual(3,  count("[ANY](A,B)")).

%% a single argument is not a list in the parse tree; it used to crash
%% bld_args with a case_clause
single_argument_test() ->
    ?assertEqual(1, count("[ANY](A)")),
    ?assertEqual(1, count("[ONE](A)")),
    ?assertEqual(1, count("[ALL](A)")),
    ?assertEqual(1, count("[NONE](A)")),
    ?assertEqual(2, count("[LTE 1](A)")),
    ?assertEqual(1, count("[EQ 1](A)")),
    ?assertEqual(0, count("[EQ 2](A)")),
    ?assertEqual(1, count("[GT 0](A)")),
    ?assertEqual(1, count("[GTE 1](A)")),
    ?assertEqual(1, count("[LT 1](A)")),
    ?assertEqual(1, count("[LTE 0](A)")),
    ?assertEqual(1, count("[NEQ 1](A)")),
    ?assertEqual(4, count("[A i=1..2] ([ONE](P(i)) equ P(i))")),
    ?assertEqual(1, count("declare X:3; [ANY](X) && X < 2")).

one_quantifier_test() ->
    ?assertEqual(4, count("[E! i=1..4] P(i)")),
    ?assertEqual(4, count("[ONE i=1..4] P(i)")).

none_quantifier_test() ->
    ?assertEqual(1, count("[NONE i=1..4] P(i)")).

eqk_test() ->
    %% exactly k of 4
    ?assertEqual(1, count("[EQ 0,i=1..4] P(i)")),
    ?assertEqual(4, count("[EQ 1,i=1..4] P(i)")),
    ?assertEqual(6, count("[EQ 2,i=1..4] P(i)")),
    ?assertEqual(4, count("[EQ 3,i=1..4] P(i)")),
    ?assertEqual(1, count("[EQ 4,i=1..4] P(i)")).

gtk_test() ->
    ?assertEqual(15, count("[GT 0,i=1..4] P(i)")),
    ?assertEqual(11, count("[GT 1,i=1..4] P(i)")),
    ?assertEqual(5,  count("[GT 2,i=1..4] P(i)")),
    ?assertEqual(1,  count("[GT 3,i=1..4] P(i)")).

gtek_test() ->
    ?assertEqual(16, count("[GTE 0,i=1..4] P(i)")),
    ?assertEqual(15, count("[GTE 1,i=1..4] P(i)")),
    ?assertEqual(11, count("[GTE 2,i=1..4] P(i)")),
    ?assertEqual(5,  count("[GTE 3,i=1..4] P(i)")),
    ?assertEqual(1,  count("[GTE 4,i=1..4] P(i)")).

ltk_test() ->
    ?assertEqual(1,  count("[LT 1,i=1..4] P(i)")),
    ?assertEqual(5,  count("[LT 2,i=1..4] P(i)")),
    ?assertEqual(11, count("[LT 3,i=1..4] P(i)")),
    ?assertEqual(15, count("[LT 4,i=1..4] P(i)")).

ltek_test() ->
    ?assertEqual(1,  count("[LTE 0,i=1..4] P(i)")),
    ?assertEqual(5,  count("[LTE 1,i=1..4] P(i)")),
    ?assertEqual(11, count("[LTE 2,i=1..4] P(i)")),
    ?assertEqual(15, count("[LTE 3,i=1..4] P(i)")),
    ?assertEqual(16, count("[LTE 4,i=1..4] P(i)")).

%% counts outside 0..N are constant true/false
degenerate_count_test() ->
    ?assertEqual(0,  count("[EQ 5,i=1..4] P(i)")),
    ?assertEqual(0,  count("[GT 4,i=1..4] P(i)")),
    ?assertEqual(0,  count("[GTE 5,i=1..4] P(i)")),
    ?assertEqual(16, count("[GTE 0,i=1..4] P(i)")),
    ?assertEqual(0,  count("[LT 0,i=1..4] P(i)")),
    ?assertEqual(16, count("[LT 5,i=1..4] P(i)")),
    ?assertEqual(16, count("[LTE 5,i=1..4] P(i)")).

parity_test() ->
    %% an odd number of the four must be true
    ?assertEqual(8, count("[ODD i=1..4] P(i)")),
    ?assertEqual(8, count("[EVEN i=1..4] P(i)")),
    ?assertEqual(8, count("[PARITY i=1..4] P(i)")).

nested_quantifier_test() ->
    %% [A p][E h] with 2 pigeons and 2 holes
    ?assertEqual(9, count("[A p=1..2][E h=1..2] P(p,h)")).

quantifier_condition_test() ->
    %% only the pairs i<j are generated: (1,2),(1,3),(2,3)
    ?assertEqual(1, count("[A i=1..3,j=1..3,i<j] R(i,j)")),
    ?assertEqual(7, count("[E i=1..3,j=1..3,i<j] R(i,j)")).

%%%-------------------------------------------------------------------
%%% Integer quantifiers
%%%-------------------------------------------------------------------

sum_test() ->
    %% SUM over 3 booleans, exactly 2 must be true
    ?assertEqual(3, count("([SUM i=1..3] P(i)) == 2")).

prod_test() ->
    ?assertEqual(1, count("([PROD i=1..3] P(i)) == 1")).

%%%-------------------------------------------------------------------
%%% Arithmetic
%%%-------------------------------------------------------------------

v(Text, Var) ->
    [M] = models(Text),
    proplists:get_value(Var, M).

add_test() ->
    ?assertEqual(9, v("declare X:4,Y:4,Z:4; (X==5) && (Y==4) && (Z==X+Y)","Z")),
    ?assertEqual(0, v("declare X:4,Y:4,Z:4; (X==0) && (Y==0) && (Z==X+Y)","Z")).

sub_test() ->
    ?assertEqual(2, v("declare X:4,Y:4,Z:4; (X==5) && (Y==3) && (Z==X-Y)","Z")).

mul_test() ->
    ?assertEqual(12, v("declare X:4,Y:4,Z:8; (X==3) && (Y==4) && (Z==X*Y)","Z")).

%% the statement form keeps the width of the target: the low bits of a
%% wide product, sign extension into a wider signed target
mul_assign_test() ->
    ?assertEqual(105, v("declare X:4,Y:4,Z:8; X = 7; Y = 15; Z = X * Y;","Z")),
    ?assertEqual(41,  v("declare X:4,Y:4,Z:6; X = 7; Y = 15; Z = X * Y;","Z")),
    ?assertEqual(21,  v("declare X:4,Y:2,Z:10; X = 7; Y = 3; Z = X * Y;","Z")),
    ?assertEqual(56,  v("declare X:4/signed,Y:4/signed,Z:8/signed;"
                        "X = -7; Y = -8; Z = X * Y;","Z")),
    ?assertEqual(56,  v("declare X:4/signed,Y:4/signed,Z:10/signed;"
                        "X = -7; Y = -8; Z = X * Y;","Z")),
    ?assertEqual(-8,  v("declare X:4/signed,Y:4/signed,Z:5/signed;"
                        "X = -7; Y = -8; Z = X * Y;","Z")),
    ?assertEqual(-105, v("declare X:4/signed,Y:4,Z:9/signed;"
                         "X = -7; Y = 15; Z = X * Y;","Z")).

div_rem_test() ->
    ?assertEqual(3, v("declare X:8,Y:8,Z:8; (X==13) && (Y==4) && (Z==X/Y)","Z")),
    ?assertEqual(1, v("declare X:8,Y:8,Z:8; (X==13) && (Y==4) && (Z==X%Y)","Z")).

%% a variable shift amount: a barrel shifter that keeps the width of
%% the left operand; a constant amount still widens
variable_shift_test() ->
    ?assertEqual(40, v("declare X:8, K:3, Z:8; X == 5 && K == 3 && Z == X << K", "Z")),
    ?assertEqual(10, v("declare X:8, K:3, Z:8; X == 0xA5 && K == 4 && Z == X >> K", "Z")),
    ?assertEqual(-4, v("declare X:8/signed, K:3, Z:8/signed; X == -16 && K == 2 && Z == X >> K", "Z")),
    ?assertEqual(0,  v("declare X:8, K:4, Z:8; X == 0xff && K == 9 && Z == X << K", "Z")),
    ?assertEqual(-1, v("declare X:8/signed, K:4, Z:8/signed; X == -1 && K == 12 && Z == X >> K", "Z")),
    ?assertEqual(3,  v("declare X:8, K:3; (X << K) == 40 && X < 10 && K > 0", "K")),
    ?assertEqual(640, v("declare X:8, Z:16; X == 5 && Z == X << 7", "Z")),
    %% a constant gets the bits the amount can reach, a target widens first
    ?assertEqual(128, v("declare Y:16, Z:32; Y == 7 && Z == (1 << Y)", "Z")),
    ?assertEqual(8, varp_tc:count("declare Y:16, Z:32; (Y < 8) && (Z == (1 << Y)) && (Z <= 256)")),
    ?assertEqual(128, v("declare Y:16, Z:32; Z = 1 << Y; Y == 7", "Z")),
    ?assertEqual(640, v("declare X:8, K:4, Z:16; Z = X << K; X == 5 && K == 7", "Z")),
    ?assertEqual(128, v("declare X:8, K:4, Z:8; X == 5 && K == 7 && Z == X << K", "Z")),   %% 640 in 8 bits
    ?assertEqual(-128, v("declare Y:3, Z:8/signed; Y == 7 && Z == (-1 << Y)", "Z")),
    ?assertEqual(1, varp_tc:count("declare Y:8, Z:64; Y == 63 && Z == (1 << Y)")),
    ?assertEqual(0, varp_tc:count("declare Y:8, Z:64; Y == 64 && Z == (1 << Y) && Z != 0")).

%% signed division truncates toward zero, the remainder has the sign of
%% the dividend (C, Erlang div/rem); a signed operand makes it signed
signed_div_rem_test() ->
    D = "declare X:6/signed,Y:6/signed,Q:6/signed,R:6/signed;",
    ?assertEqual(-3, v(D ++ "(X==-13) && (Y==4) && (Q==X/Y)", "Q")),
    ?assertEqual(-1, v(D ++ "(X==-13) && (Y==4) && (R==X%Y)", "R")),
    ?assertEqual(-3, v(D ++ "(X==13) && (Y==-4) && (Q==X/Y)", "Q")),
    ?assertEqual(1,  v(D ++ "(X==13) && (Y==-4) && (R==X%Y)", "R")),
    ?assertEqual(3,  v(D ++ "(X==-13) && (Y==-4) && (Q==X/Y)", "Q")),
    ?assertEqual(-1, v(D ++ "(X==-13) && (Y==-4) && (R==X%Y)", "R")),
    ?assertEqual(0,  v(D ++ "(X==-13) && (Y==20) && (Q==X/Y)", "Q")),
    ?assertEqual(-13, v(D ++ "(X==-13) && (Y==20) && (R==X%Y)", "R")),
    %% mixed: the unsigned operand is widened with a zero sign bit
    ?assertEqual(-3, v("declare X:6/signed,Y:6,Q:6/signed; (X==-13) && (Y==4) && (Q==X/Y)", "Q")),
    ?assertEqual(-3, v("declare X:6,Y:6/signed,Q:6/signed; (X==13) && (Y==-4) && (Q==X/Y)", "Q")),
    %% the most negative value: -8 / -1 = 8 needs a fifth bit
    ?assertEqual(8, v("declare X:4/signed,Y:4/signed,Q:5/signed; (X==-8) && (Y==-1) && (Q==X/Y)", "Q")),
    ?assert(unsat("declare X:4/signed,Y:4/signed,Q:4/signed; (X==-8) && (Y==-1) && (Q==X/Y)")),
    %% division by zero has no model unless --divz says otherwise
    ?assert(unsat(D ++ "(X==-13) && (Y==0) && (Q==X/Y)")),
    %% the statement form
    ?assertEqual([{"Q",-3},{"R",-1},{"X",-13},{"Y",4}],
		 lists:sort(hd(models(D ++ "Q = X / Y; R = X % Y; (X==-13) && (Y==4)")))).

%% X == (X / Y) * Y + X % Y, |X % Y| < |Y| and the remainder has the sign
%% of X, for every signed X and Y of the given widths
signed_div_rem_law_test_() ->
    Law = "declare X:n/signed, Y:m/signed; (Y != 0) implies"
	  " ((X == (X / Y) * Y + X % Y) && (abs(X % Y) < abs(Y))"
	  "  && ((X % Y == 0) || ((X % Y < 0) equ (X < 0))))",
    Mixed = "declare X:n/signed, Y:m; (Y != 0) implies"
	  " ((X == (X / Y) * Y + X % Y) && (abs(X % Y) < Y))",
    [{lists:flatten(io_lib:format("~s n=~w m=~w", [Name, N, M])),
      {timeout, 300,
       fun() ->
	       ?assert(varp_tc:is_tautology(
			 Text, #{meta => #{<<"n">> => N, <<"m">> => M}}))
       end}}
     || {Name, Text} <- [{"law", Law}, {"mixed", Mixed}],
	{N, M} <- [{2,2},{3,3},{4,4},{3,5},{5,3}]].

shift_test() ->
    ?assertEqual(12, v("declare X:8,Z:8; (X==3) && (Z==X<<2)","Z")),
    ?assertEqual(3,  v("declare X:8,Z:8; (X==13) && (Z==X>>2)","Z")).

compare_test() ->
    ?assert(sat("declare X:4,Y:4; (X==3) && (Y==5) && (X<Y)")),
    ?assert(unsat("declare X:4,Y:4; (X==3) && (Y==5) && (X>Y)")),
    ?assert(sat("declare X:4,Y:4; (X==3) && (Y==3) && (X<=Y) && (X>=Y)")),
    ?assert(sat("declare X:4,Y:4; (X==3) && (Y==5) && (X!=Y)")),
    ?assert(unsat("declare X:4,Y:4; (X==3) && (Y==5) && (X==Y)")).

%% a comparison assigned to a boolean, including one of constants
compare_assign_test() ->
    ?assertEqual(true,  v("declare A:2,B:2,x; A = 1; B = 1; x = (A == B);", "x")),
    ?assertEqual(false, v("declare A:2,B:2,x; A = 1; B = 2; x = (A == B);", "x")),
    ?assertEqual(true,  v("declare A:2,B:2,x; A = 1; B = 2; x = (A < B);", "x")),
    ?assertEqual(true,  v("declare A:2,B:2,x; A = 1; B = 2; x = (A <= B);", "x")),
    ?assertEqual(false, v("declare A:2,B:2,x; A = 1; B = 2; x = (A > B);", "x")),
    ?assertEqual(true,  v("declare A:2,B:2,x; A = 1; B = 2; x = (A != B);", "x")),
    ?assertEqual(true,  v("declare x; x = (2 == 2);", "x")),
    ?assertEqual(false, v("declare x; x = (2 < 1);", "x")),
    ?assertEqual(1,     v("declare x:2; x = (3 == 3);", "x")).

%% one signed operand makes + - * signed; the sum and difference need
%% one more bit than the operands, the product n+m
signed_test() ->
    ?assertEqual(-2, v("declare X:4/signed,Y:4/signed,Z:4/signed;"
		       "(X==1) && (Y==3) && (Z==X-Y)","Z")),
    ?assertEqual(-15, v("declare X:4/signed,Y:4/signed,Z:5/signed;"
			"(X==-7) && (Y==-8) && (Z==X+Y)","Z")),
    ?assertEqual(-15, v("declare X:4/signed,Y:4/signed,Z:5/signed;"
			"(X==-8) && (Y==7) && (Z==X-Y)","Z")),
    ?assertEqual(56, v("declare X:4/signed,Y:4/signed,Z:8/signed;"
		       "(X==-7) && (Y==-8) && (Z==X*Y)","Z")),
    ?assertEqual(-105, v("declare X:4/signed,Y:4,Z:9/signed;"
			 "(X==-7) && (Y==15) && (Z==X*Y)","Z")),
    ?assertEqual(8, v("declare X:4/signed,Y:4,Z:6/signed;"
		      "(X==-7) && (Y==15) && (Z==X+Y)","Z")).

factoring_test() ->
    %% 15 = 3*5, the only factorisation with 1 < x <= y
    Ms = models("declare X:4,Y:4; (X*Y == 15) && (X>1) && (Y>1) && (X<=Y)"),
    ?assertEqual([[{"X",3},{"Y",5}]], Ms).

%%%-------------------------------------------------------------------
%%% Bitwise and arithmetic operators applied to booleans
%%%-------------------------------------------------------------------

%% on booleans the bitwise operators are the logical ones
bitwise_on_bool_test() ->
    ?assertEqual(tt2("A and B"), tt2("A & B")),
    ?assertEqual(tt2("A or B"),  tt2("A | B")),
    ?assertEqual(tt2("A xor B"), tt2("A ^ B")),
    ?assertEqual(models("not A"), models("~A")),
    %% and they compose with the logical ones
    ?assertEqual(1, count("A && (B & C)")),
    ?assert(taut("(A & B) <-> (A and B)")),
    ?assert(taut("(A | B) <-> (A or B)")),
    ?assert(taut("(A ^ B) <-> (A xor B)")),
    ?assert(taut("(~A) <-> (not A)")).

%% arithmetic on booleans widens them to one bit unsigned values
arith_on_bool_test() ->
    ?assertEqual(1, count("(A * B) == 1 && A && B")),
    ?assertEqual(0, count("(A * B) == 1 && !A")),
    ?assertEqual(3, count("(A + B) >= 1")).

%%%-------------------------------------------------------------------
%%% Vectors and bit selection
%%%-------------------------------------------------------------------

vector_test() ->
    %% {A,B,C} is a 3 bit vector with A as the least significant bit
    ?assertEqual([[{"A",true},{"B",false},{"C",true}]],
		 models("{A,B,C} == 5")),
    ?assertEqual([[{"A",false},{"B",true}]], models("{A,B} == 2")),
    ?assertEqual([[{"A",true}]], models("{A} == 1")),
    ?assertEqual(1, count("{A,B,C,D} == 15")),
    ?assertEqual(0, count("{A,B} == 4")).

bit_index_test() ->
    ?assertEqual(1, count("declare X:4; (X == 5) && X[0] && !X[1] && X[2]")),
    ?assertEqual(0, count("declare X:4; (X == 5) && X[1]")).

bit_range_test() ->
    ?assert(sat("declare X:8; (X == 0b10110011) && (X[0:3] == 0b0011)")).

%%%-------------------------------------------------------------------
%%% Definitions
%%%-------------------------------------------------------------------

define_test() ->
    ?assertEqual(1, count("define F(i) P(i) and Q(i); [A i=1..2] F(i)")),
    %% a define with a meta expression argument
    ?assertEqual(1, count("define F(i) P(i); [A i=1..3] F(i+1)")).

define_recursive_test() ->
    %% F(0) is a base case, F(n) recurses
    ?assert(sat("define F(0) true;"
		"define F(n) P(n) and F(n-1);"
		"F(3)")).

literals_test() ->
    ?assert(sat("literals red, green; P(red) and !P(green)")).

%%%-------------------------------------------------------------------
%%% Assignments
%%%-------------------------------------------------------------------

assignment_test() ->
    %% X is constrained to A and B
    ?assertEqual([[{"A",true},{"B",true},{"X",true}]],
		 models("X = A and B; X")),
    ?assertEqual(3, count("X = A and B; !X")).

%%%-------------------------------------------------------------------
%%% Classic problems
%%%-------------------------------------------------------------------

pigeon_hole_test_() ->
    %% n pigeons into n-1 holes is unsatisfiable for every n > 1
    F = "( ([A p=1..n] [E h=1..(n-1)] P(p,h)) and"
	"  ([A h=1..(n-1)] [A p=1..n] [A q=1..n,p<q]"
	"      not (P(p,h) and P(q,h))) )",
    [{"pigeon "++integer_to_list(N),
      {timeout, 60,
       fun() -> ?assert(varp_tc:is_unsat(F, #{meta => #{<<"n">> => N}})) end}}
     || N <- [2,3,4,5]].

queens_test_() ->
    %% 4 queens has 2 solutions, 5 queens has 10
    F = "([A i=1..n][E! j=1..n] Q(i,j)) and"
	"([A j=1..n][E! i=1..n] Q(i,j)) and"
	"([A i=1..n][A j=1..n][A k=1..n][A l=1..n,"
	"   i<k, (k-i)==(l-j) || (k-i)==(j-l)]"
	"      not (Q(i,j) and Q(k,l)))",
    [{"queens 4", {timeout,120,
		   fun() -> ?assertEqual(
			       2, varp_tc:count(F,#{meta=>#{<<"n">>=>4}})) end}},
     {"queens 5", {timeout,120,
		   fun() -> ?assertEqual(
			       10, varp_tc:count(F,#{meta=>#{<<"n">>=>5}})) end}}].

%%%-------------------------------------------------------------------
%%% Diagnostics
%%%-------------------------------------------------------------------

warn(Text, Mode) ->
    varp_tc:capture(
      fun() -> varp_tc:count(Text, #{undeclared => Mode}) end).

%% the default: a symbol used once that looks like a misspelling of a
%% symbol that is used properly
undeclared_typo_test() ->
    Out = warn("Example && Exampl && (Example || !Example)", typo),
    ?assertNotEqual(nomatch,
		    string:find(Out, "'Exampl' occurs once, did you mean"
				" 'Example'?")),
    %% Example itself occurs three times, it is not reported
    ?assertEqual(nomatch, string:find(Out, "'Example' occurs")).

%% a1, a2, a3 differ only in their digits, that is a family not a typo
undeclared_digit_family_test() ->
    ?assertEqual(nomatch,
		 string:find(warn("A1 && A2 && A3 && A1 && A2", typo),
			     "warning")),
    %% and single letters are all one edit apart, so they are never
    %% reported as typos
    ?assertEqual(nomatch,
		 string:find(warn("A && B && C && A && B", typo), "warning")).

%% a symbol used once and never declared, whether it looks like
%% anything else or not
undeclared_once_test() ->
    Out = warn("declare V:4; Example && Exampl && (V == 3)", once),
    ?assertNotEqual(nomatch, string:find(Out, "'Exampl' occurs once")),
    ?assertNotEqual(nomatch, string:find(Out, "'Example' occurs once")),
    %% a symbol used more than once is not reported in 'once' mode
    ?assertEqual(nomatch,
		 string:find(warn("A && B && A && B", once), "warning")),
    %% and nothing at all is reported when the check is off
    ?assertEqual(nomatch,
		 string:find(warn("Example && Exampl", none), "warning")).

%% an occurrence count is lexical, P(i) under a quantifier occurs once
%% but makes many variables.  the default must not report that.
undeclared_quantifier_test() ->
    ?assertEqual(nomatch,
		 string:find(warn("[EQ 1,i=1..6](A(i))", typo), "warning")),
    ?assertNotEqual(nomatch,
		    string:find(warn("[EQ 1,i=1..6](A(i))", once),
				"warning")).

undeclared_all_test() ->
    Out = warn("A && B && A && B", all),
    ?assertNotEqual(nomatch, string:find(Out, "'A' is not declared")),
    ?assertNotEqual(nomatch, string:find(Out, "'B' is not declared")).

%% declared symbols, defines and literals are never reported
undeclared_quiet_test() ->
    ?assertEqual(nomatch,
		 string:find(warn("declare A, B; A && B", all), "warning")),
    ?assertEqual(nomatch,
		 string:find(warn("define F(i) true; F(1)", all), "warning")),
    ?assertEqual(nomatch,
		 string:find(warn("literals red; declare P; P", all),
			     "warning")).

%% the line number comes from the parser symbol table
undeclared_line_test() ->
    Out = warn("declare V:4;\n\n\nExampl && (V==3)", once),
    ?assertNotEqual(nomatch, string:find(Out, ":4: warning:")).

%% a build error is reported once, in words, without an erlang stack
build_error_test() ->
    ?assertError({arity_mismatch,<<"P">>},
		 varp_tc:quiet(fun() -> varp_tc:count("P(1) && P(2,3)") end)),
    ?assertError({unbound,<<"n">>},
		 varp_tc:quiet(fun() -> varp_tc:count("[A i=1..n] P(i)") end)),
    Str = fun(E) -> binary_to_list(
		      iolist_to_binary(varp:format_error(E))) end,
    ?assertEqual("Variable P can only have one arity",
		 Str({arity_mismatch,<<"P">>})),
    ?assertEqual("Variable n is unbound\n", Str({unbound,<<"n">>})).

%%%-------------------------------------------------------------------
%%% define expansion
%%%-------------------------------------------------------------------

%% definitions are stored under {Name,Arity}; looking them up under the
%% bare name meant no 'define' with arguments was ever expanded, and the
%% call silently became a fresh propositional variable instead
define_is_expanded_test() ->
    %% F(1) must become P(1), not a variable called F
    [M] = models("define F(i) P(i); F(1)"),
    ?assertEqual([{"P(1)",true}], M),
    %% arity is part of the key, two definitions can share a name
    ?assertEqual([{"P(1)",true},{"Q(1,2)",true}],
		 hd(models("define F(i) P(i);"
			   "define F(i,j) Q(i,j);"
			   "F(1) and F(1,2)"))),
    %% a definition that cannot hold makes the formula false
    ?assertEqual(0, count("define F(i) P(i) and !P(i); F(1)")).

%% n pigeons into n-1 holes, written with definitions
define_pigeon_test() ->
    F = "define ONCE(p) [E h=1..(n-1)] P(p,h);"
	"define EXCL(h) [A p=1..n][A q=1..n,p<q] not (P(p,h) and P(q,h));"
	"([A p=1..n] ONCE(p)) and ([A h=1..(n-1)] EXCL(h))",
    ?assert(varp_tc:is_unsat(F, #{meta => #{<<"n">> => 4}})),
    ?assert(varp_tc:is_unsat(F, #{meta => #{<<"n">> => 5}})).

%%%-------------------------------------------------------------------
%%% Die hard
%%%-------------------------------------------------------------------

%% the classic 3 and 5 litre jug puzzle, it needs exactly 6 steps
die_hard_test_() ->
    File = filename:join(varp_tc:formula_dir("varp"), "die_hard.varp"),
    {ok,Bin} = file:read_file(File),
    Text = binary_to_list(Bin),
    [{"die hard n="++integer_to_list(N),
      {timeout, 300,
       fun() ->
	       Opts = #{meta => #{<<"n">> => N}, undeclared => none},
	       ?assertEqual(N >= 6, varp_tc:is_sat(Text, Opts))
       end}} || N <- [1,2,3,4,5,6]].

%%%-------------------------------------------------------------------
%%% Meta variables used as values
%%%-------------------------------------------------------------------

%% a small letter name bound on the command line (or by a quantifier)
%% is a number when it appears in a logic expression
meta_as_value_test() ->
    Ms = varp_tc:models("declare A:4, B:3; (A*B == n)",
			#{meta => #{<<"n">> => 15}}),
    ?assertEqual([[{"A",3},{"B",5}],[{"A",5},{"B",3}],[{"A",15},{"B",1}]], Ms),
    %% quantifier variables too
    ?assertEqual(1, count("declare X(i):3; [A i=1..3] (X(i) == i)")),
    %% and inside a define
    ?assertEqual(1, count("declare X:3; define F(i) (X == i); F(5)")),
    %% the is_prime formula: 100 = 25*4 = 20*5 = 50*2
    F = "declare A:(isize(n)-1); declare B:((isize(n)+1)/2);"
	"((A * B) == n) && (A > B) && (B > 1)",
    ?assertEqual(3, varp_tc:count(F, #{meta => #{<<"n">> => 100}})).

%%
%% wrap(E, T) is the C cast: the low bits of E as T.  fits(E, T) is
%% the overflow it hides.  2026-11-28.
%%

%% the number of variables a formula builds
nvars(Text) ->
    {_, _, Bs} = varp_tc:run(Text, [{satisfy,[]}]),
    varp:get_number_of_variables(Bs#bs.vp).

wrap_test() ->
    ?assertEqual(-56, v("declare X:8/signed, Y:8/signed; X == 100 && Y == wrap(X + X)", "Y")),
    ?assertEqual(-56, v("declare X:8/signed, Y:8/signed; X == 100 && Y == wrap(X + X, 8/signed)", "Y")),
    ?assertEqual(-56, v("declare X:8/signed, Y:8/signed; Y = wrap(X + X); X == 100", "Y")),
    ?assertEqual(-56, v("declare X:8/signed, Y:8/signed; X == 100 && wrap(X + X) == Y", "Y")),
    ?assertEqual(253, v("declare X:8/signed, Y:8/unsigned; X == -3 && Y == wrap(X, 8/unsigned)", "Y")),
    ?assertEqual(253, v("declare X:8/signed, Y:8/unsigned; X == -3 && Y == wrap(X)", "Y")),
    ?assertEqual(4,   v("declare X:8/signed, Y:4/unsigned; X == 100 && Y == wrap(X)", "Y")),
    %% a shorter value is extended first, with the sign of a signed one
    ?assertEqual(65533, v("declare X:8/signed, Y:16/unsigned; X == -3 && Y == wrap(X)", "Y")),
    ?assertEqual(253,   v("declare X:8/unsigned, Y:16/unsigned; X == 253 && Y == wrap(X)", "Y")),
    ?assertEqual(-3,    v("declare X:8/signed, Y:16/signed; X == -3 && Y == wrap(X)", "Y")),
    %% a constant wraps too
    ?assertEqual(44, v("declare Y:8/unsigned; Y == wrap(300, 8/unsigned)", "Y")),
    %% the type has to come from somewhere, and has to be a type
    ?assertError({wrap_type_unknown,_}, models("declare X:8; X == 1 && wrap(X)")),
    ?assertError({wrap_type_unknown,_}, models("declare X:8, Y:8; wrap(X) == wrap(Y)")),
    ?assertError({wrap_float754,_}, models("declare X:8, Y:8; Y == wrap(X, 8/float754)")),
    ?assertError({type_expected,_,_}, models("declare X:8, Y:8; Y == wrap(X, 8)")).

fits_test() ->
    ?assertEqual(1, count("declare X:8/signed; X == 60 && fits(X + X, 8/signed)")),
    ?assertEqual(0, count("declare X:8/signed; X == 64 && fits(X + X, 8/signed)")),
    ?assertEqual(1, count("declare X:8/signed; X == -64 && fits(X + X, 8/signed)")),
    ?assertEqual(0, count("declare X:8/signed; X == -65 && fits(X + X, 8/signed)")),
    ?assertEqual(0, count("declare X:8/signed; X == -1 && fits(X, 8/unsigned)")),
    ?assertEqual(1, count("declare X:8/signed; X == 5 && fits(X, 3/unsigned)")),
    ?assertEqual(0, count("declare X:8/signed; X == 8 && fits(X, 3/unsigned)")),
    ?assertEqual(1, count("declare X:8/unsigned; X == 200 && fits(X, 8/unsigned)")),
    ?assertEqual(0, count("declare X:8/unsigned; X == 200 && fits(X, 8/signed)")),
    ?assertEqual(1, count("declare X:8/unsigned; X == 127 && fits(X, 8/signed)")),
    %% a wider target always fits, a boolean is one unsigned bit
    ?assertEqual(256, count("declare X:8/signed; fits(X, 16/signed)")),
    ?assertEqual(2, count("declare X:8/unsigned; fits(X, 1/unsigned)")),
    %% the sums that fit: -64..63
    ?assertEqual(128, count("declare X:8/signed; fits(X + X, 8/signed)")),
    %% wrap and fits agree: the wrapped sum is the exact sum iff it fits
    ?assertEqual(0, count("declare X:8/signed; (wrap(X + X, 8/signed) == X + X) != fits(X + X, 8/signed)")),
    ?assertError({fits_float754,_}, models("declare X:8; fits(X, 8/float754)")).

%% cast(E, T) reads the same bits as another type; E/unsigned,
%% E/signed, E/float are the forms at the width of E
cast_test() ->
    ?assertEqual(255, v("declare X:8/signed, Y:8; X == -1 && Y == X/unsigned", "Y")),
    ?assertEqual(255, v("declare X:8/signed, Y:8; X == -1 && Y == cast(X, 8/unsigned)", "Y")),
    ?assertEqual(255, v("declare X:8/signed, Y:8; X == -1 && Y == cast(X)", "Y")),
    ?assertEqual(-1,  v("declare X:8, Y:8/signed; X == 255 && Y == X/signed", "Y")),
    ?assertEqual(-1,  v("declare X:8, Y:8/signed; Y = cast(X); X == 255", "Y")),
    %% the sum is 9 bits, a 9 bit signed value
    ?assertEqual(0, count("declare X:8, Y:8/signed; X == 255 && Y == (X + 1)/signed")),
    ?assertEqual(-256, v("declare X:8, Y:16/signed; X == 255 && Y == (X + 1)/signed", "Y")),
    %% float754 bit patterns both ways, a constant has the bits of its width
    ?assertEqual(16#3FC00000, v("declare F:32/float754, U:32; F == 1.5 && U == F/unsigned", "U")),
    ?assertEqual(16#3FC00000, v("declare F:32/float754, U:32; F == 1.5 && U == cast(F)", "U")),
    ?assertEqual(1.5, v("declare F:32/float754, U:32; U == 0x3FC00000 && F == cast(U)", "F")),
    ?assertEqual(1.5, v("declare F:32/float754; F == cast(0x3FC00000, 32/float754)", "F")),
    ?assertEqual(-1.5, v("declare F:32/float754; F == cast(0xBFC00000, 32/float754)", "F")),
    ?assertEqual(1, count("declare F:32/float754; isnan(F) && F/unsigned == 0x7FC00000")),
    ?assertEqual(1, count("declare F:32/float754; isinf(F) && F/unsigned == 0x7F800000")),
    ?assertEqual(0, count("declare F:32/float754; isinf(F) && F/unsigned == 0x7F800001")),
    %% the next float up is the next bit pattern; the sum is 33 bits
    %% wide, so it is wrapped to the width first
    ?assertEqual(1.5000001192092896,
		 v("declare F:32/float754, G:32/float754; F == 1.5 && G == cast(wrap(F/unsigned + 1, 32/unsigned), 32/float754)", "G")),
    ?assertError({cast_width,_,_,_}, models("declare F:32/float754, G:32/float754; F == 1.5 && G == cast(F/unsigned + 1, 32/float754)")),
    %% fixed point raw bits
    ?assertEqual(16#18000, v("declare Q:32/fixpoint, U:32; Q == 1.5 && U == cast(Q, 32/unsigned)", "U")),
    ?assertEqual(1.5, v("declare Q:32/fixpoint, U:32; U == 0x18000 && Q == cast(U)", "Q")),
    ?assertEqual(1.5, v("declare Q:32/fixpoint, U:32; U == 0x18000 && Q == cast(U, fixpoint(16,16))", "Q")),
    %% a boolean is one bit
    ?assertEqual(1, v("declare A, B:1; A && B == cast(A, 1/unsigned)", "B")),
    %% the widths must agree, a literal has no bits, the type has to come from somewhere
    ?assertError({cast_width,_,_,_}, models("declare X:16, F:32/float754; X == 1 && F == cast(X)")),
    ?assertError({cast_literal,_,_}, models("declare X:8; X == cast(1.5, 8/unsigned)")),
    ?assertError({cast_type_unknown,_}, models("declare X:8; X == 1 && cast(X)")).

%% X + 0, X - 0, X * 1 are X, X * 0 is 0 and X * 2^n is a shift: no
%% adder or multiplier, the variable count of Y == X
arith_fold_test() ->
    N0 = nvars("declare X:32, Y:32; Y == X"),
    ?assertEqual(N0, nvars("declare X:32, Y:32; Y == X + 0")),
    ?assertEqual(N0, nvars("declare X:32, Y:32; Y == 0 + X")),
    ?assertEqual(N0, nvars("declare X:32, Y:32; Y == X - 0")),
    ?assertEqual(N0, nvars("declare X:32, Y:32; Y == X * 1")),
    ?assert(nvars("declare X:32, Y:32; Y == X * 8") =< N0),
    ?assert(nvars("declare X:32, Y:32; Y == 8 * X") =< N0),
    ?assert(nvars("declare X:32, Y:32; Y == X * 0") < N0),
    ?assert(nvars("declare X:32, Y:32; Y == X * 3") > N0),
    %% and the values
    ?assertEqual(5,   v("declare X:4, Y:8; X == 5 && Y == X + 0", "Y")),
    ?assertEqual(5,   v("declare X:4, Y:8; X == 5 && Y == X - 0", "Y")),
    ?assertEqual(40,  v("declare X:4, Y:8; X == 5 && Y == X * 8", "Y")),
    ?assertEqual(40,  v("declare X:4, Y:8; X == 5 && Y == 8 * X", "Y")),
    ?assertEqual(0,   v("declare X:4, Y:8; X == 5 && Y == X * 0", "Y")),
    ?assertEqual(-12, v("declare X:4/signed, Y:8/signed; X == -3 && Y == X * 4", "Y")),
    %% the statement form keeps the width of the target: 20 in 3 bits
    ?assertEqual(4,   v("declare X:3, Y:3; Y = X * 4; X == 5", "Y")),
    %% --carry true asks for a carry that X + 0 never has
    ?assertEqual(0, length(varp_tc:models("declare X:4, Y:4; X == 5 && Y == X + 0", #{carry => true}))),
    ?assertEqual(16, length(varp_tc:models("declare X:4, Y:4; Y == X + 0", #{carry => false}))).

%% a constant operand of a bitwise operator folds in the gates: the
%% result is wiring, no new variable per bit (it was one per bit)
bitwise_fold_test() ->
    N0 = nvars("declare X:32, Y:32; Y == X"),
    ?assertEqual(N0, nvars("declare X:32, Y:32; Y == (X & 0xFFFFFFFF)")),
    %% a mask that clears bits fixes bits of Y too: fewer still
    ?assert(nvars("declare X:32, Y:32; Y == (X & 0xFF)") < N0),
    ?assertEqual(N0, nvars("declare X:32, Y:32; Y == (X | 0)")),
    ?assertEqual(N0, nvars("declare X:32, Y:32; Y == (X ^ 0xFFFFFFFF)")),
    ?assertEqual(N0, nvars("declare X:32, Y:32; Y == ~X")),
    ?assert(nvars("declare X:32, Y:32; Y == ((X & 0xFFFF0000) | (X & 0xFFFF))") =< N0),
    %% and the values are what they were
    ?assertEqual(16#F0, v("declare X:8, Y:8; X == 0xF3 && Y == (X & 0xF0)", "Y")),
    ?assertEqual(16#FF, v("declare X:8, Y:8; X == 0xF3 && Y == (X | 0x0F)", "Y")),
    ?assertEqual(16#0C, v("declare X:8, Y:8; X == 0xF3 && Y == (X ^ 0xFF)", "Y")),
    ?assertEqual(16#0C, v("declare X:8, Y:8; X == 0xF3 && Y == ~X", "Y")),
    ?assertEqual(16#F3, v("declare X:8, Y:8; X == 0xF3 && Y == ((X & 0xF0) | (X & 0x0F))", "Y")).
