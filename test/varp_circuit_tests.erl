%%% Circuits.
%%%
%%% Two things are covered here:
%%%   1) the gate library in varp_circuit (its own self test)
%%%   2) the 'circuit' language construct, ie varp_formula:build_circuit/3
-module(varp_circuit_tests).

-include_lib("eunit/include/eunit.hrl").

count(T) -> varp_tc:count(T).
models(T) -> varp_tc:models(T).
sat(T) -> varp_tc:is_sat(T).
unsat(T) -> varp_tc:is_unsat(T).

%%%-------------------------------------------------------------------
%%% Gate library
%%%-------------------------------------------------------------------

gate_library_test_() ->
    {timeout, 300, fun() -> ?assertEqual(ok, varp_circuit:test()) end}.

%%%-------------------------------------------------------------------
%%% circuit ... { ... }
%%%-------------------------------------------------------------------

-define(HA,
	"circuit half_adder(in y, z; return x; out co)\n"
	"{\n"
	"    x = y xor z;\n"
	"    co = y and z;\n"
	"}\n").

%% the return value of a circuit call is its 'return' parameter
return_value_test() ->
    ?assertEqual(1, count(?HA "S = half_adder(A,B,C); A && !B && S")),
    ?assertEqual(0, count(?HA "S = half_adder(A,B,C); A && B && S")).

%% an 'out' parameter constrains the caller's variable
out_parameter_test() ->
    ?assertEqual(1, count(?HA "S = half_adder(A,B,C); A && B && C")),
    ?assertEqual(0, count(?HA "S = half_adder(A,B,C); A && !B && C")).

%% the full half adder truth table, A+B = 2*C + S
half_adder_truth_table_test() ->
    Ms = models(?HA "S = half_adder(A,B,C); true"),
    ?assertEqual(4, length(Ms)),
    lists:foreach(
      fun(M) ->
	      A = b(proplists:get_value("A",M)),
	      B = b(proplists:get_value("B",M)),
	      S = b(proplists:get_value("S",M)),
	      C = b(proplists:get_value("C",M)),
	      ?assertEqual(A+B, 2*C+S)
      end, Ms).

b(true) -> 1;
b(false) -> 0.

%% locals get a unique per instance prefix, so two instances of the same
%% circuit do not share their internal variables
instance_prefix_test() ->
    [M] = models(?HA
		 "S1 = half_adder(A1,B1,C1);"
		 "S2 = half_adder(A2,B2,C2);"
		 "A1 && B1 && !A2 && !B2"),
    Names = [N || {N,_} <- M],
    ?assert(lists:member("half_adder#1.x", Names)),
    ?assert(lists:member("half_adder#2.x", Names)),
    %% instance 1 has 1+1, instance 2 has 0+0
    ?assertEqual(true,  proplists:get_value("C1", M)),
    ?assertEqual(false, proplists:get_value("C2", M)).

%% a circuit without a return parameter evaluates to true
no_return_test() ->
    %% note: the grammar does not (yet) accept a bare "c(A,B);" statement,
    %% see grammar_limitation_test_ in varp_parse_tests
    ?assertEqual(1, count("circuit c(in y; out o) { o = not y; }"
			  "Q = c(A,B); Q && A && !B")),
    ?assertEqual(0, count("circuit c(in y; out o) { o = not y; }"
			  "Q = c(A,B); Q && A && B")).

%% parameters may have defaults and may be passed by name
default_argument_test() ->
    ?assertEqual(1, count("circuit c(in a, b = true; return x) { x = a and b; }"
			  "Y = c(A); A && Y")),
    ?assertEqual(0, count("circuit c(in a, b = false; return x) { x = a and b; }"
			  "Y = c(A); Y")).

named_argument_test() ->
    ?assertEqual(1, count("circuit c(in a, b; return x) { x = a and b; }"
			  "Y = c(A, b = B); A && B && Y")),
    %% named and positional select the same parameter
    ?assertEqual(1, count("circuit c(in a, b; return x) { x = a and !b; }"
			  "Y = c(a = A, b = B); A && !B && Y")).

%% declare inside a body creates a local, sized, variable
local_declare_test() ->
    ?assert(sat("circuit c(in a, b; return x) { declare s1; s1 = a xor b; x = s1; }"
		"Y = c(A,B); A && !B && Y")),
    ?assert(unsat("circuit c(in a, b; return x) { declare s1; s1 = a xor b; x = s1; }"
		  "Y = c(A,B); A && B && Y")).

%% a circuit is a closed scope: a body name never refers to a global
closed_scope_test() ->
    %% 'A' inside the body is half_adder#1.A, not the outer A
    [M] = models("circuit c(in y; return x) { x = y and A; }"
		 "Y = c(B); !A && Y"),
    ?assertEqual(false, proplists:get_value("A", M)),
    ?assertEqual(true, proplists:get_value("c#1.A", M)).

nested_circuit_test() ->
    T = "circuit and3(in a1, a2, a3 = true; return x) { x = a1 and a2 and a3; }"
	"circuit mix(in a, b, c; return x; out t)"
	"{"
	"  circuit c1(in y, z; return x) { x = y xor z; }"
	"  t = c1(a,b);"
	"  x = and3(t, c);"
	"}"
	"R = mix(A,B,C,T); ",
    %% R <-> (A xor B) and C
    ?assertEqual(1, count(T ++ "A && !B && C && R")),
    ?assertEqual(0, count(T ++ "A && B && C && R")),
    ?assertEqual(0, count(T ++ "A && !B && !C && R")),
    %% the out parameter T carries A xor B, C is still free here
    ?assertEqual(2, count(T ++ "A && !B && T")),
    ?assertEqual(0, count(T ++ "A && B && T")).

%%%-------------------------------------------------------------------
%%% Typed (arithmetic) circuits
%%%-------------------------------------------------------------------

-define(PLUS,
	"circuit plus(in Y:4, Z:4 = 3; return X:4)\n"
	"{\n"
	"    X = Y+Z;\n"
	"}\n").

arith_circuit_test() ->
    [M] = models("declare R:4,A:4,B:4;" ?PLUS
		 "R = plus(A,B); (A == 5) && (B == 4)"),
    ?assertEqual(9, proplists:get_value("R", M)),
    ?assertEqual(9, proplists:get_value("plus#1.X", M)).

arith_circuit_default_test() ->
    [M] = models("declare R:4,A:4;" ?PLUS "R = plus(A); (A == 5)"),
    ?assertEqual(8, proplists:get_value("R", M)).

%% an undeclared argument gets the type/size of the parameter
arith_circuit_declares_argument_test() ->
    [M] = models("declare R:4;" ?PLUS "R = plus(A,B); (A == 5) && (B == 4)"),
    ?assertEqual(5, proplists:get_value("A", M)),
    ?assertEqual(4, proplists:get_value("B", M)),
    ?assertEqual(9, proplists:get_value("R", M)).

%%%-------------------------------------------------------------------
%%% A ripple carry adder built out of circuits
%%%-------------------------------------------------------------------

-define(RIPPLE,
	"circuit half_adder(in y, z; return x; out co)\n"
	"{ x = y xor z; co = y and z; }\n"
	"circuit full_adder(in y, z; in ci; return x; out co)\n"
	"{ declare s1;\n"
	"  s1 = y xor z;\n"
	"  x  = s1 xor ci;\n"
	"  co = (s1 and ci) or (y and z); }\n"
	"S1 = half_adder(A1,B1,C1);\n"
	"S2 = full_adder(A2,B2,C1,C2);\n").

ripple_carry_test() ->
    %% every 2 bit addition must satisfy a+b = 4*C2 + 2*S2 + S1
    Ms = models(?RIPPLE "true"),
    ?assertEqual(16, length(Ms)),
    lists:foreach(
      fun(M) ->
	      G = fun(N) -> b(proplists:get_value(N,M)) end,
	      A = G("A1") + 2*G("A2"),
	      B = G("B1") + 2*G("B2"),
	      ?assertEqual(A+B, G("S1") + 2*G("S2") + 4*G("C2"))
      end, Ms).

%%%-------------------------------------------------------------------
%%% Errors
%%%-------------------------------------------------------------------

err(Text) ->
    try varp_tc:quiet(fun() -> varp_tc:count(Text) end) of
	_ -> no_error
    catch
	error:Reason -> Reason
    end.

too_many_arguments_test() ->
    ?assertMatch({circuit_arity,<<"c">>,_,_},
		 err("circuit c(in a; return x) { x = not a; } Y = c(A,B); Y")).

missing_argument_test() ->
    ?assertMatch({circuit_missing_argument,<<"c">>,<<"b">>},
		 err("circuit c(in a, b; return x) { x = a and b; } Y = c(A); Y")).

unknown_argument_test() ->
    ?assertMatch({circuit_unknown_argument,<<"c">>,[<<"q">>]},
		 err("circuit c(in a; return x) { x = a; } Y = c(q = A); Y")).

duplicate_argument_test() ->
    ?assertMatch({circuit_duplicate_argument,<<"c">>,<<"a">>},
		 err("circuit c(in a, b; return x) { x = a and b; }"
		     "Y = c(A, a = B); Y")).

%%%-------------------------------------------------------------------
%%% A bare formula in a body is a constraint
%%%-------------------------------------------------------------------

%% this is what lets a body build a structure of any width, the
%% quantifier is the loop
constraint_statement_test() ->
    ?assertEqual(1, count("circuit c(in a; return x) { x <-> !a; } "
			  "Y = c(A); A && !Y")),
    ?assertEqual(0, count("circuit c(in a; return x) { x <-> !a; } "
			  "Y = c(A); A && Y")),
    %% a constraint that cannot hold makes the whole formula false
    ?assertEqual(0, count("circuit c(in a; return x) { false; x = a; } "
			  "Y = c(A); true")).

%% an n bit ripple carry adder written in varp
-define(RCA,
	"declare A:n, B:n, S:n, C:(n+1);\n"
	"circuit rca(in Y:n, Z:n; out CO:(n+1); return X:n)\n"
	"{\n"
	"    !CO[0];\n"
	"    [A i=0..n-1] ( (X[i]  <-> (Y[i] xor Z[i] xor CO[i])) and\n"
	"                   (CO[i+1] <-> ((Y[i] and Z[i]) or\n"
	"                                 (CO[i] and (Y[i] xor Z[i])))) );\n"
	"}\n"
	"S = rca(A, B, C);\n").

generic_adder_test_() ->
    [{"rca "++integer_to_list(N),
      {timeout, 60,
       fun() ->
	       Opts = #{meta => #{<<"n">> => N}},
	       [M] = varp_tc:models(?RCA "(A == 5) && (B == 6)", Opts),
	       ?assertEqual(11, proplists:get_value("S", M))
       end}} || N <- [4,6,8]].

%% and varp proves it equivalent to the built in adder
generic_adder_is_correct_test_() ->
    T = "declare T:(n+1);\n" ?RCA
	"T = A + B;\n"
	"(S == T[0:n-1]) && (C[n] == T[n])",
    [{"rca == builtin, n="++integer_to_list(N),
      {timeout, 120,
       fun() ->
	       ?assert(varp_tc:is_tautology(T, #{meta => #{<<"n">> => N}}))
       end}} || N <- [2,3,4,6]].

%%%-------------------------------------------------------------------
%%% Shifts assigned inside a circuit, macros as arguments, vector
%%% conditionals: the CRC-16 example (crc16.varp, crc16_hello.varp)
%%%-------------------------------------------------------------------

read_formula(Name) ->
    File = filename:join(varp_tc:formula_dir("varp"), Name),
    {ok,Bin} = file:read_file(File),
    binary_to_list(Bin).

%% "b = a << 1" used to build the result as {Type,Bits,N}
shift_assign_test() ->
    [M] = models("declare a:16, b:16; b = (a << 1); a == 3"),
    ?assertEqual(6, proplists:get_value("b", M)),
    [M2] = models("circuit f(in x:16; return y:16) { y = (x >> 1); }\n"
		  "declare a:16, b:16; b == f(a) and a == 6"),
    ?assertEqual(3, proplists:get_value("b", M2)).

%% a 17 bit value into an undeclared (boolean) local is an error,
%% not a silent truncation
width_mismatch_test() ->
    ?assertError({width_mismatch,{bool,1},{uint,17}},
		 models("circuit f(in x:16; return y:16) { declare t; t = (x << 1); y = t; }\n"
			"declare a:16, b:16; b == f(a) and a == 3")).

%% c ? a : b with vector branches is a bitwise mux
vector_ite_test() ->
    Ms = models("declare a:8, b:8, c; b = c ? a : (a ^ 255); a == 5"),
    ?assertEqual([{false,250},{true,5}],
		 lists:sort([{proplists:get_value("c",M), proplists:get_value("b",M)}
			     || M <- Ms])).

%% a zero-arity define used as a circuit argument is expanded, it used
%% to become a free vector variable of the parameter's width
define_as_argument_test() ->
    Ms = models("circuit f(in x:16; return y:16) { y = x; }\n"
		"define seed 0xffff;\n"
		"declare a:16; a == f(seed)"),
    ?assertEqual([65535], [proplists:get_value("a",M) || M <- Ms]),
    ?assertEqual(1, length(Ms)).

crc16_test_() ->
    [{"CRC-16/CCITT-FALSE of H", {timeout, 120,
      fun() ->
	      [M] = models(read_formula("crc16.varp")),
	      ?assertEqual(16#283c, proplists:get_value("CRC", M))
      end}},
     {"CRC-16/CCITT-FALSE of HELLO", {timeout, 300,
      fun() ->
	      [M] = models(read_formula("crc16_hello.varp")),
	      ?assertEqual(16#49d6, proplists:get_value("CRC", M)),
	      ?assertEqual(16#283c, proplists:get_value("c1", M))
      end}}].

%% rotations were mirrored: <<< rotated right and >>> rotated left,
%% both as a value and as an assignment target
rotate_test() ->
    [M] = models("declare a:8, b:8, c:8; b = (a <<< 1); c = (a >>> 3); a == 129"),
    ?assertEqual(3, proplists:get_value("b", M)),
    ?assertEqual(48, proplists:get_value("c", M)),
    [M2] = models("declare a:8, b:8, c:8; b == (a <<< 1) and c == (a >>> 3) and a == 129"),
    ?assertEqual(3, proplists:get_value("b", M2)),
    ?assertEqual(48, proplists:get_value("c", M2)),
    %% into a wider target the rotation is that of the source width
    [M3] = models("declare a:8, b:16; b = (a <<< 1); a == 129"),
    ?assertEqual(3, proplists:get_value("b", M3)),
    [M4] = models("circuit f(in x:8; return y:8) { y = (x >>> 1); }\n"
		  "declare a:8, b:8; b == f(a) and a == 3"),
    ?assertEqual(129, proplists:get_value("b", M4)),
    ?assertError({width_mismatch,{bool,1},{uint,8}},
		 models("declare a:8, b; b = (a <<< 1); a == 129")).

%% arithmetic shift right sign-extends a signed int, also into a wider
%% target; a negative shift count shifts the other way
signed_shift_test() ->
    Get = fun(Text, Name) ->
		  [M] = models(Text), proplists:get_value(Name, M)
	  end,
    ?assertEqual(-2, Get("declare a:8/signed, b:8/signed; b = (a >> 2); a == -8", "b")),
    ?assertEqual(-1, Get("declare a:8/signed, b:8/signed; b = (a >> 7); a == -1", "b")),
    ?assertEqual(16, Get("declare a:8/signed, b:8/signed; b = (a >> 2); a == 64", "b")),
    ?assertEqual(62, Get("declare a:8, b:8; b = (a >> 2); a == 248", "b")),
    ?assertEqual(-4, Get("declare a:8/signed, b:16/signed; b = (a >> 1); a == -8", "b")),
    ?assertEqual(-2, Get("declare a:8/signed, b:8/signed; b = (a << -2); a == -8", "b")),
    ?assertEqual(-16, Get("declare a:8/signed, b:8/signed; b = (a >> -1); a == -8", "b")),
    ?assertEqual(-2, Get("circuit f(in x:8/signed; return y:8/signed) { y = (x >> 2); }\n"
			 "declare a:8/signed, b:8/signed; b == f(a) and a == -8", "b")).

%%%-------------------------------------------------------------------
%%% Lookup tables: synthesis of a configuration by quantifying over
%%% the rows of the truth table (fpga.varp, fpga_adder.varp)
%%%-------------------------------------------------------------------

lut_synthesis_test_() ->
    [{"!x && y && z is cfg 64, and only that", {timeout, 120,
      fun() ->
	      Ms = models(read_formula("fpga.varp")),
	      ?assertEqual([64], [proplists:get_value("cfg", M) || M <- Ms])
      end}},
     {"full adder: sum 0x96, carry 0xe8", {timeout, 300,
      fun() ->
	      [M] = models(read_formula("fpga_adder.varp")),
	      ?assertEqual(16#96, proplists:get_value("cs", M)),
	      ?assertEqual(16#e8, proplists:get_value("cc", M))
      end}},
     {"a define called with a variable is an error", {timeout, 60,
      fun() ->
	      %% a bare name is taken for a meta variable first
	      ?assertError({unbound, _},
			   models("define T(x) (x); declare a; T(a)")),
	      ?assertError({define_argument, _},
			   models("define T(x) (x); declare a(i); T(a(1))"))
      end}}].

%% the fabric: four LUT3 cells with routing, programmed by the solver
%% to add two 2 bit numbers; the program is checked by simulating it
%% here on all 32 inputs
fabric_test_() ->
    {timeout, 300,
     fun() ->
	     %% one model: there are far too many symmetric programs to
	     %% enumerate them all
	     {_R, [M|_], _} = varp_tc:run(read_formula("fpga_fabric.varp"),
					 [{satisfy,[]},{backjump,[{max,1}]}]),
	     Val = fun(Name, Args) ->
			   {_, {uint,Bits}} = lists:keyfind({p,Name,Args}, 1, M),
			   list_to_integer(tuple_to_list(Bits), 2)
		   end,
	     Cfg = fun(C) -> Val(<<"CFG">>, [C]) end,
	     Sel = fun(C,K) -> Val(<<"SEL">>, [C,K]) end,
	     Lut = fun(Cfg0,X,Y,Z) -> (Cfg0 bsr (X + 2*Y + 4*Z)) band 1 end,
	     %% feed forward routing
	     lists:foreach(fun({C,K}) -> ?assert(Sel(C,K) < 5 + C) end,
			   [{C,K} || C <- lists:seq(0,3), K <- lists:seq(0,2)]),
	     lists:foreach(
	       fun(I) ->
		       In = [(I bsr K) band 1 || K <- lists:seq(0,4)],
		       Sig = lists:foldl(
			       fun(C, S) ->
				       [X,Y,Z] = [lists:nth(Sel(C,K)+1, S) || K <- lists:seq(0,2)],
				       S ++ [Lut(Cfg(C),X,Y,Z)]
			       end, In, lists:seq(0,3)),
		       [A0,A1,B0,B1,CI,_O0,O1,O2,O3] = Sig,
		       ?assertEqual(A0 + 2*A1 + B0 + 2*B1 + CI, O1 + 2*O3 + 4*O2)
	       end, lists:seq(0,31))
     end}.
