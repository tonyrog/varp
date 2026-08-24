%%% Grammar (varp_parse.yrl) tests.
%%%
%%% These test the grammar AS IT IS TODAY.  Constructs that appear in
%%% SYNTAX.md or in formulas/ but are not (yet) accepted are collected in
%%% the ?XFAIL list at the bottom, so that the corpus test stays green and
%%% the list itself is the TODO list for the grammar.
-module(varp_parse_tests).

-include_lib("eunit/include/eunit.hrl").

%% raw parse, main formula only
f(Text) ->
    {ok,{_Sections,_Assignments,F}} = varp_tc:parse_only(Text),
    F.

%% raw parse, assignment list only
a(Text) ->
    {ok,{_Sections,As,_F}} = varp_tc:parse_only(Text),
    As.

s(Text) -> varp_tc:sections(Text).
err(Text) -> varp_tc:parse_only(Text).

%%%-------------------------------------------------------------------
%%% Propositional variables
%%%-------------------------------------------------------------------

propvar_test() ->
    ?assertEqual({p,<<"B">>,[]}, f("B")),
    ?assertEqual({p,<<"B">>,[]}, f("B()")),
    ?assertEqual({p,<<"B">>,[{const,1}]}, f("B(1)")),
    ?assertEqual({p,<<"B">>,[{const,1},{const,2}]}, f("B(1,2)")),
    %% A and E are usable as symbol names
    ?assertEqual({p,<<"A">>,[]}, f("A")),
    ?assertEqual({p,<<"E">>,[]}, f("E")).

constant_test() ->
    ?assertEqual(true, f("true")),
    ?assertEqual(false, f("false")),
    ?assertEqual({uint,1,1}, f("1")),
    ?assertEqual({uint,1,0}, f("0")),
    ?assertEqual({uint,5,31}, f("0x1f")),
    ?assertEqual({uint,4,11}, f("0b1011")),
    ?assertEqual({uint,4,15}, f("017")).

%%%-------------------------------------------------------------------
%%% Connectives and precedence
%%%-------------------------------------------------------------------

connective_test() ->
    ?assertEqual({lop,'and',{p,<<"B">>,[]},{p,<<"C">>,[]}}, f("B and C")),
    ?assertEqual({lop,'and',{p,<<"B">>,[]},{p,<<"C">>,[]}}, f("B && C")),
    ?assertEqual({lop,'or',{p,<<"B">>,[]},{p,<<"C">>,[]}},  f("B or C")),
    ?assertEqual({lop,'or',{p,<<"B">>,[]},{p,<<"C">>,[]}},  f("B || C")),
    ?assertEqual({lop,'xor',{p,<<"B">>,[]},{p,<<"C">>,[]}}, f("B xor C")),
    ?assertEqual({lop,'imp',{p,<<"B">>,[]},{p,<<"C">>,[]}}, f("B -> C")),
    ?assertEqual({lop,'imp',{p,<<"B">>,[]},{p,<<"C">>,[]}}, f("B imp C")),
    ?assertEqual({lop,'imp',{p,<<"B">>,[]},{p,<<"C">>,[]}}, f("B implies C")),
    ?assertEqual({lop,'equ',{p,<<"B">>,[]},{p,<<"C">>,[]}}, f("B <-> C")),
    ?assertEqual({lop,'equ',{p,<<"B">>,[]},{p,<<"C">>,[]}}, f("B equ C")),
    ?assertEqual({lop,'not',{p,<<"B">>,[]}}, f("not B")),
    ?assertEqual({lop,'not',{p,<<"B">>,[]}}, f("!B")),
    ?assertEqual({lop,'bnot',{p,<<"B">>,[]}}, f("~B")).

%% not > and > xor > or > imp > equ
precedence_test() ->
    ?assertEqual({lop,'or',{lop,'and',{p,<<"B">>,[]},{p,<<"C">>,[]}},
		  {p,<<"D">>,[]}},
		 f("B and C or D")),
    ?assertEqual({lop,'or',{p,<<"B">>,[]},
		  {lop,'and',{p,<<"C">>,[]},{p,<<"D">>,[]}}},
		 f("B or C and D")),
    ?assertEqual({lop,'and',{lop,'not',{p,<<"B">>,[]}},{p,<<"C">>,[]}},
		 f("not B and C")),
    ?assertEqual({lop,'imp',{lop,'or',{p,<<"B">>,[]},{p,<<"C">>,[]}},
		  {p,<<"D">>,[]}},
		 f("B or C -> D")),
    ?assertEqual({lop,'equ',{lop,'imp',{p,<<"B">>,[]},{p,<<"C">>,[]}},
		  {p,<<"D">>,[]}},
		 f("B -> C equ D")),
    %% parenthesis override
    ?assertEqual({lop,'and',{p,<<"B">>,[]},
		  {lop,'or',{p,<<"C">>,[]},{p,<<"D">>,[]}}},
		 f("B and (C or D)")).

associativity_test() ->
    %% all binary connectives are left associative
    ?assertEqual({lop,'and',{lop,'and',{p,<<"B">>,[]},{p,<<"C">>,[]}},
		  {p,<<"D">>,[]}},
		 f("B and C and D")),
    ?assertEqual({lop,'imp',{lop,'imp',{p,<<"B">>,[]},{p,<<"C">>,[]}},
		  {p,<<"D">>,[]}},
		 f("B -> C -> D")).

ite_test() ->
    ?assertEqual({lop,'ite',{p,<<"B">>,[]},{p,<<"C">>,[]},{p,<<"D">>,[]}},
		 f("B ? C : D")).

%%%-------------------------------------------------------------------
%%% Arithmetic / bitwise
%%%-------------------------------------------------------------------

arith_test() ->
    ?assertMatch({lop,'add',_,_}, f("A + B")),
    ?assertMatch({lop,'sub',_,_}, f("A - B")),
    ?assertMatch({lop,'mul',_,_}, f("A * B")),
    ?assertMatch({lop,'div',_,_}, f("A / B")),
    ?assertMatch({lop,'rem',_,_}, f("A % B")),
    ?assertMatch({lop,'neg',_},   f("- A")).

arith_precedence_test() ->
    %% * binds tighter than +
    ?assertMatch({lop,'add',_,{lop,'mul',_,_}}, f("A + B * C")),
    ?assertMatch({lop,'add',{lop,'mul',_,_},_}, f("A * B + C")),
    %% + binds tighter than <<
    ?assertMatch({lop,'shl',{lop,'add',_,_},_}, f("A + B << C")),
    %% relational is looser than shift
    ?assertMatch({lop,'lt',{lop,'shl',_,_},_}, f("A << B < C")).

bitwise_test() ->
    ?assertMatch({lop,'band',_,_}, f("A & B")),
    ?assertMatch({lop,'bor',_,_},  f("A | B")),
    ?assertMatch({lop,'bxor',_,_}, f("A ^ B")),
    ?assertMatch({lop,'shl',_,_},  f("A << 2")),
    ?assertMatch({lop,'shr',_,_},  f("A >> 2")),
    ?assertMatch({lop,'rol',_,_},  f("A <<< 2")),
    ?assertMatch({lop,'ror',_,_},  f("A >>> 2")).

compare_test() ->
    ?assertMatch({lop,'lt',_,_},  f("A < B")),
    ?assertMatch({lop,'lte',_,_}, f("A <= B")),
    ?assertMatch({lop,'gt',_,_},  f("A > B")),
    ?assertMatch({lop,'gte',_,_}, f("A >= B")),
    ?assertMatch({lop,'eq',_,_},  f("A == B")),
    ?assertMatch({lop,'neq',_,_}, f("A != B")),
    ?assertMatch({lop,'alias',_,_}, f("A := B")).

builtin_test() ->
    ?assertMatch({p,<<"min">>,[_,_]}, f("min(A,B)")),
    ?assertMatch({p,<<"max">>,[_,_]}, f("max(A,B)")),
    ?assertMatch({p,<<"abs">>,[_]},   f("abs(A)")).

%%%-------------------------------------------------------------------
%%% Sized variables, vectors, bit selection
%%%-------------------------------------------------------------------

%% X:N is only accepted where an oexpr is expected, that is on the left
%% hand side of an assignment and in an order declaration, see
%% grammar_limitation_test_ below.
sized_test() ->
    ?assertEqual([{lop,'=',{uint,4,{p,<<"X">>,[]}},{p,<<"A">>,[]}}],
		 a("X:4/unsigned = A;")),
    ?assertEqual([{lop,'=',{int,4,{p,<<"X">>,[]}},{p,<<"A">>,[]}}],
		 a("X:4/signed = A;")),
    %% declared sizes are the normal way to size a variable
    #{ decls := D } = s("declare X:4/signed, Y:int; true"),
    ?assertEqual({int,0,4}, maps:get(<<"X">>, D)),
    ?assertEqual({uint,0,32}, maps:get(<<"Y">>, D)).

vector_test() ->
    ?assertEqual({vec,[{p,<<"B">>,[]},{p,<<"C">>,[]},{p,<<"D">>,[]}]},
		 f("{B,C,D}")).

%% note: a bit selection may not start the formula, the parser then
%% commits to the assignment (oexpr) production
bitselect_test() ->
    ?assertMatch({lop,'and',true,{bitindex,{p,<<"X">>,[]},{const,1}}},
		 f("true && X[1]")),
    ?assertMatch({lop,'and',true,{bitrange,{p,<<"X">>,[]},
				  {const,1},{const,5},1}},
		 f("true && X[1:5]")),
    ?assertMatch({lop,'and',true,{bit_range,{p,<<"X">>,[]},
				  {const,1},{const,5},{const,2}}},
		 f("true && X[1:5:2]")).

%%%-------------------------------------------------------------------
%%% Quantifiers
%%%-------------------------------------------------------------------

quantifier_test() ->
    ?assertMatch({{'ALL',_},_}, f("[A p=1..3] P(p)")),
    ?assertMatch({{'ANY',_},_}, f("[E p=1..3] P(p)")),
    ?assertMatch({{'ONE',_},_}, f("[E! p=1..3] P(p)")),
    ?assertMatch({{'ALL',_},_},  f("[ALL p=1..3] P(p)")),
    ?assertMatch({{'ANY',_},_},  f("[ANY p=1..3] P(p)")),
    ?assertMatch({{'NONE',_},_}, f("[NONE p=1..3] P(p)")),
    ?assertMatch({{'ONE',_},_},  f("[ONE p=1..3] P(p)")),
    ?assertMatch({{'EQ',_},_},   f("[EQ 1,p=1..3] P(p)")),
    ?assertMatch({{'NEQ',_},_},  f("[NEQ 1,p=1..3] P(p)")),
    ?assertMatch({{'GT',_},_},   f("[GT 1,p=1..3] P(p)")),
    ?assertMatch({{'GTE',_},_},  f("[GTE 1,p=1..3] P(p)")),
    ?assertMatch({{'LT',_},_},   f("[LT 1,p=1..3] P(p)")),
    ?assertMatch({{'LTE',_},_},  f("[LTE 1,p=1..3] P(p)")),
    ?assertMatch({{'SUM',_},_},  f("[SUM p=1..3] P(p)")),
    ?assertMatch({{'PROD',_},_}, f("[PROD p=1..3] P(p)")),
    ?assertMatch({{'PARITY',_},_}, f("[PARITY p=1..3] P(p)")),
    ?assertMatch({{'ODD',_},_},  f("[ODD p=1..3] P(p)")),
    ?assertMatch({{'EVEN',_},_}, f("[EVEN p=1..3] P(p)")).

quantifier_list_form_test() ->
    ?assertEqual({'ALL',[{p,<<"B">>,[]},{p,<<"C">>,[]}]}, f("[A](B,C)")),
    ?assertEqual({'ANY',[{p,<<"B">>,[]},{p,<<"C">>,[]}]}, f("[E](B,C)")),
    ?assertEqual({'ONE',[{p,<<"B">>,[]},{p,<<"C">>,[]}]}, f("[E!](B,C)")).

quantifier_condition_test() ->
    %% domain, condition, nested quantifiers
    ?assertMatch({{'ONE',[_,_,_]},_}, f("[ONE x=1..6,y=1..6,x<y] R(x,y)")),
    ?assertMatch({{'ALL',_},{{'ANY',_},_}}, f("[A p=1..3][E h=1..2] P(p,h)")).

%%%-------------------------------------------------------------------
%%% Sections
%%%-------------------------------------------------------------------

declare_test() ->
    #{ decls := D } = s("declare X:8, Y:4/signed, Z; true"),
    ?assertEqual({uint,0,8}, maps:get(<<"X">>, D)),
    ?assertEqual({int,0,4},  maps:get(<<"Y">>, D)),
    ?assertEqual({bool,0,1}, maps:get(<<"Z">>, D)).

define_test() ->
    #{ defs := Defs } = s("define F(i) P(i) and Q(i); true"),
    ?assertMatch([{[<<"i">>],{lop,'and',_,_}}],
		 maps:get({<<"F">>,1}, Defs)).

literals_test() ->
    #{ literals := L } = s("literals red, green; true"),
    ?assert(maps:is_key(<<"red">>, L)),
    ?assert(maps:is_key(<<"green">>, L)).

order_test() ->
    #{ order := O } = s("order rank, -degree, +random; true"),
    ?assertEqual(['rank','-degree','+random'], O).

assert_test() ->
    #{ assert := [A] } = s("assert 1 < 2; true"),
    ?assertMatch({op,'lt',_,_}, A).

input_output_test() ->
    #{ input := I, output := O } = s("input foo; output bar; true"),
    ?assertEqual([<<"foo">>], I),
    ?assertEqual([<<"bar">>], O).

assignment_test() ->
    ?assertMatch([{lop,'=',{p,<<"X">>,[]},{lop,'and',_,_}}],
		 a("X = A and B; true")),
    ?assertMatch([{lop,'=',_,_},{lop,'=',_,_}],
		 a("X = A; Y = B; true")).

%%%-------------------------------------------------------------------
%%% Circuits
%%%-------------------------------------------------------------------

circuit_decl_test() ->
    #{ circuits := [C] } =
	s("circuit ha(in y, z; return x; out co) { x = y xor z; co = y and z; } true"),
    {circuit,Name,Params,Defs} = C,
    ?assertEqual(<<"ha">>, Name),
    ?assertEqual([{in,[{p,<<"y">>,[]},{p,<<"z">>,[]}]},
		  {return,{p,<<"x">>,[]}},
		  {out,[{p,<<"co">>,[]}]}], Params),
    ?assertEqual(2, length(Defs)).

circuit_typed_param_test() ->
    #{ circuits := [C] } =
	s("circuit plus(in Y:4, Z:4; return X:4) { X = Y+Z; } true"),
    {circuit,_,Params,_} = C,
    ?assertEqual([{in,[{{p,<<"Y">>,[]},uint,4},{{p,<<"Z">>,[]},uint,4}]},
		  {return,{{p,<<"X">>,[]},uint,4}}], Params).

circuit_default_test() ->
    #{ circuits := [C] } =
	s("circuit c(in a, b = false; return x) { x = a and b; } true"),
    {circuit,_,[{in,[A,B]},_],_} = C,
    ?assertEqual({p,<<"a">>,[]}, A),
    ?assertEqual({'=',{p,<<"b">>,[]},false}, B).

circuit_nested_test() ->
    #{ circuits := [C] } =
	s("circuit outer(in a; return x) {"
	  "  circuit inner(in y; return z) { z = not y; }"
	  "  x = inner(a);"
	  "} true"),
    {circuit,<<"outer">>,_,Defs} = C,
    ?assertMatch([{circuit,<<"inner">>,_,_},{lop,'=',_,_}], Defs).

circuit_declare_in_body_test() ->
    #{ circuits := [C] } =
	s("circuit c(in a, b; return x) { declare s1; s1 = a xor b; x = s1; } true"),
    {circuit,_,_,[D|_]} = C,
    ?assertMatch({declare,[{p,<<"s1">>,[]}]}, D).

%% a circuit call is scanned as a cname because the scanner asks
%% varp_formula:is_circuit_def/2
circuit_call_test() ->
    ?assertMatch([{lop,'=',{p,<<"Y">>,[]},{cop,<<"c">>,[{p,<<"B">>,[]}]}}],
		 a("circuit c(in a; return x) { x = not a; } Y = c(B); true")).

circuit_named_argument_test() ->
    ?assertMatch([{lop,'=',_,{cop,<<"c">>,[{p,<<"B">>,[]},
					   {'=',<<"b">>,{p,<<"C">>,[]}}]}}],
		 a("circuit c(in a, b; return x) { x = a and b; }"
		   "Y = c(B, b = C); true")).

%%%-------------------------------------------------------------------
%%% Known grammar limitations
%%%
%%% Each of these SHOULD parse according to SYNTAX.md but does not.
%%% When the grammar is extended the corresponding assertion fails and
%%% this list must be trimmed.
%%%-------------------------------------------------------------------

grammar_limitation_test_() ->
    [{"X:N in a logic expression",
      ?_assertMatch({error,_}, err("A && X:4"))},
     {"X:N compared with a constant",
      ?_assertMatch({error,_}, err("X:4 == 3"))},
     {"bit selection first in a formula",
      ?_assertMatch({error,_}, err("X[1] && A"))},
     {"X:N on the left of an assignment without a sign",
      ?_assertMatch({error,_}, err("X:4 = A;"))},
     {"ALL as an ordinary symbol name",
      ?_assertMatch({error,_}, err("ALL && B"))},
     {"code {} block",
      ?_assertMatch({error,_}, err("code { int x = 1; }"))},
     {"bare circuit call statement",
      ?_assertMatch({error,_},
		    err("circuit c(in y; out o) { o = not y; } c(A,B); true"))}
    ].

%%%-------------------------------------------------------------------
%%% Errors
%%%-------------------------------------------------------------------

syntax_error_test() ->
    ?assertMatch({error,_}, err("A &&")),
    ?assertMatch({error,_}, err("(A && B")),
    ?assertMatch({error,_}, err("declare")),
    ?assertMatch({error,_}, err("[ALL i=1..3")),
    ?assertMatch({error,_}, err("circuit c(in a; return x) { x = a; ")).

%%%-------------------------------------------------------------------
%%% Corpus:  every .varp file in formulas/ must parse
%%%-------------------------------------------------------------------

%% Files that the current grammar cannot parse.  Each entry is
%% {Basename, Reason} - this is the grammar TODO list.
-define(XFAIL,
	[{"all17.varp",     "ALL used as an ordinary symbol name"},
	 {"and_bug.varp",   "leading && "},
	 {"arith.varp",     "sized variable X:3 inside a logic expression"},
	 {"fib.varp",       "sized variable inside a logic expression"},
	 {"fpga.varp",      "sized variable F(i):3 inside a logic expression"},
	 {"is_square.varp", "sized variable inside a logic expression"},
	 {"plustimes2.varp","sized variable on the left of an assignment"},
	 {"prog1.varp",     "code {} block is not in the grammar"},
	 {"ramsey2.varp",   "quantifier over a set expression"},
	 {"tre.varp",       "sized variable A:6 inside a logic expression"},
	 {"tricky.varp",    "(E n=4) quantifier without brackets"},
	 {"tricky_gt.varp", "FORALL/EXISTS spelled out, and (E x=..) form"},
	 {"wb.varp",        "sized variable inside a logic expression"},
	 {"wsat.varp",      "sized variable inside a logic expression"}
	]).

xfail() -> [N || {N,_} <- ?XFAIL].

corpus_parse_test_() ->
    Files = varp_tc:formula_files("varp", ".varp"),
    ?assert(length(Files) > 50),
    [{filename:basename(F),
      {timeout, 120,
       fun() ->
	       Base = filename:basename(F),
	       {ok,Bin} = file:read_file(F),
	       R = varp_tc:parse_only(binary_to_list(Bin)),
	       case lists:member(Base, xfail()) of
		   true ->
		       ?assertMatch({error,_}, R);
		   false ->
		       ?assertMatch({ok,_}, R)
	       end
       end}} || F <- Files].

%% every entry in the xfail list must exist, so the list cannot rot
xfail_list_is_current_test() ->
    Names = [filename:basename(F) ||
		F <- varp_tc:formula_files("varp", ".varp")],
    ?assertEqual([], xfail() -- Names).
