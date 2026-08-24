%%% Input and output backends: DIMACS cnf, snf, the cnf writer plugin
%%% and the model/clause formatters.
-module(varp_backend_tests).

-include_lib("eunit/include/eunit.hrl").
-include("varp.hrl").

%% .cnf files under formulas/dimacs that are not DIMACS at all
-define(CNF_XFAIL, ["f_1009_503_sym.cnf"]).

-define(SNF,
	"p snf 3 2\n"
	"A !B .\n"
	"B C .\n").

%% .snf files that the snf grammar/loader cannot handle today
-define(SNF_XFAIL,
	["cor5_13.snf",                  %% uses a .. range
	 "factoring_17_13_pure.snf",
	 "factoring_17_13_pure2.snf",
	 "full_adder.snf",
	 "k6.snf",
	 "k6_m1.snf",
	 "prod_2_17_con.snf"]).

%%%-------------------------------------------------------------------
%%% DIMACS
%%%-------------------------------------------------------------------

-define(CNF3,
	"c a small instance\n"
	"p cnf 3 3\n"
	"1 -2 0\n"
	"2 3 0\n"
	"-1 -3 0\n").

detect_test() ->
    ?assertEqual({true,cnf}, varp_dimacs:detect_string(?CNF3)),
    ?assertEqual({true,cnf}, varp_dimacs:detect_data(list_to_binary(?CNF3))),
    ?assertEqual({true,cnf}, varp_dimacs:detect_binary(list_to_binary(?CNF3))),
    ?assertEqual({true,snf}, varp_dimacs:detect_string(?SNF)),
    ?assertEqual(false, varp_dimacs:detect_string("A && B\n")).

parse_cnf_test() ->
    {cnf,{NVars,NClauses,_Sections,CLs}} = parse(?CNF3),
    ?assertEqual(3, NVars),
    ?assertEqual(3, NClauses),
    ?assertEqual([[1,-2],[2,3],[-1,-3]], CLs).

%% a parsed cnf can be handed straight to do_run.
%% (1 or !2) and (2 or 3) and (!1 or !3) has exactly two models
solve_cnf_test() ->
    ?assertEqual(2, length(solve_dimacs(?CNF3))).

%% an unsatisfiable instance
solve_unsat_cnf_test() ->
    Cnf = "p cnf 1 2\n1 0\n-1 0\n",
    ?assertEqual([], solve_dimacs(Cnf)).

%% varp_dimacs:parse/1 takes a binary
parse(Text) when is_list(Text) -> varp_dimacs:parse(list_to_binary(Text));
parse(Bin) when is_binary(Bin) -> varp_dimacs:parse(Bin).

solve_dimacs(Text) ->
    {ok,_} = application:ensure_all_started(varp),
    Formula = parse(Text),
    GOpts = varp:load_option_list([{print,false}]),
    Do = varp:parse_do([{satisfy,[]},{backtrack,[{max,0}]}]),
    case varp:do_run(Do, [], Formula, GOpts) of
	{?INCONSISTENT,_,_} -> [];
	{_,Ms,_} when is_list(Ms) -> Ms
    end.

%% every .cnf under formulas/dimacs must at least parse
dimacs_corpus_test_() ->
    Files = varp_tc:formula_files("dimacs", ".cnf"),
    ?assert(length(Files) > 5),
    [{filename:basename(F),
      {timeout, 60,
       fun() ->
	       {ok,Bin} = file:read_file(F),
	       R = varp_tc:quiet(fun() -> varp_dimacs:parse(Bin) end),
	       case lists:member(filename:basename(F), ?CNF_XFAIL) of
		   true  -> ?assertMatch({error,_}, R);
		   false -> ?assertMatch({cnf,{_,_,_,_}}, R)
	       end
       end}} || F <- Files].

%%%-------------------------------------------------------------------
%%% SNF (symbolic normal form)
%%%-------------------------------------------------------------------

parse_snf_test() ->
    R = varp_tc:quiet(fun() -> parse(?SNF) end),
    ?assertMatch({snf,{_,_,_,_}}, R).

solve_snf_test() ->
    {ok,_} = application:ensure_all_started(varp),
    Formula = varp_tc:quiet(fun() -> parse(?SNF) end),
    GOpts = varp:load_option_list([{print,false}]),
    Do = varp:parse_do([{satisfy,[]},{backtrack,[{max,0}]}]),
    R = varp_tc:quiet(fun() -> varp:do_run(Do, [], Formula, GOpts) end),
    %% (A or !B) and (B or C) has 4 models over A,B,C
    ?assertMatch({_,_,_}, R),
    {_,Ms,_} = R,
    ?assertEqual(4, length(Ms)).

%% every .snf under formulas/ must parse
snf_corpus_test_() ->
    Files = varp_tc:formula_files("dimacs", ".snf") ++
	varp_tc:formula_files("varp", ".snf"),
    [{filename:basename(F),
      {timeout, 120,
       fun() ->
	      {ok,Bin} = file:read_file(F),
	      R = varp_tc:quiet(
		    fun() ->
			    try varp_dimacs:parse(Bin)
			    catch error:Reason -> {error,Reason} end
		    end),
	      case lists:member(filename:basename(F), ?SNF_XFAIL) of
		  true  -> ?assertMatch({error,_}, R);
		  false -> ?assertMatch({snf,{_,_,_,_}}, R)
	      end
       end}} || F <- Files].

%%%-------------------------------------------------------------------
%%% DIMACS output
%%%-------------------------------------------------------------------

%% varp_dimacs:format/1 turns symbolic clauses into DIMACS text that
%% varp_dimacs:parse/1 accepts again
dimacs_round_trip_test() ->
    P = fun(N) -> {p,N,[]} end,
    Clauses = [[P(<<"A">>), {'not',P(<<"B">>)}],
	       [P(<<"B">>), P(<<"C">>)],
	       [{'not',P(<<"A">>)}, {'not',P(<<"C">>)}]],
    Text = lists:flatten(varp_dimacs:format(Clauses)),
    ?assertEqual({true,cnf}, varp_dimacs:detect_string(Text)),
    {cnf,{NVars,NClauses,_,CLs}} = parse(Text),
    ?assertEqual(3, NVars),
    ?assertEqual(3, NClauses),
    %% A=1 B=2 C=3 in first seen order
    ?assertEqual([[1,-2],[2,3],[-1,-3]], CLs).

%% the cnf plugin writes the built formula out as DIMACS
cnf_plugin_test() ->
    Dir = varp_tc:tmpdir(),
    File = filename:join(Dir, "out.cnf"),
    _ = file:delete(File),
    R = varp_tc:quiet(
	  fun() ->
		  varp_tc:run("(A or B) and (!A or C)",
			      [{satisfy,[]},{cnf,[{file,File}]}])
	  end),
    ?assertMatch({_,_,_}, R),
    ?assert(filelib:is_regular(File)),
    {ok,Bin} = file:read_file(File),
    %% it must be readable back as DIMACS
    ?assertMatch({cnf,{_,_,_,_}}, varp_dimacs:parse(Bin)).

%%%-------------------------------------------------------------------
%%% Formatting
%%%-------------------------------------------------------------------

str(IoList) -> binary_to_list(iolist_to_binary(IoList)).

format_symbol_test() ->
    ?assertEqual("A", str(varp_format:format_symbol({p,<<"A">>,[]}))),
    ?assertEqual("A(1,2)", str(varp_format:format_symbol({p,<<"A">>,[1,2]}))),
    ?assertEqual("t", str(varp_format:format_symbol(true))),
    ?assertEqual("f", str(varp_format:format_symbol(false))).

format_internal_symbol_test() ->
    ?assertEqual("A", str(varp_format:format_internal_symbol({<<"A">>,[]}))),
    ?assertEqual("P(1,2)",
		 str(varp_format:format_internal_symbol({<<"P">>,[1,2]}))).

format_binding_test() ->
    ?assertEqual("A", str(varp_format:format_binding({{p,<<"A">>,[]},true}))),
    ?assertEqual("!A", str(varp_format:format_binding({{p,<<"A">>,[]},false}))),
    ?assertEqual("X=5",
		 str(varp_format:format_binding({{p,<<"X">>,[]},
						 {uint,{$1,$0,$1}}}))).

%% varp_circuit:symbol/2 turns a literal back into its source name
circuit_symbol_test() ->
    Vp = varp_nif:new(#{}),
    A = varp_circuit:atom(Vp, <<"A">>),
    {V1,Vn} = varp_nif:add_variables(Vp, 4, true),
    varp_nif:add_symbol(Vp, {<<"W">>,[]}, lists:seq(V1,Vn), uint),
    P = varp_nif:add_variable(Vp, true),
    varp_nif:add_symbol(Vp, {<<"P">>,[1,2]}, P, bool),
    Aux = varp_circuit:var(Vp),
    ?assertEqual("A", varp_circuit:symbol(Vp, A)),
    ?assertEqual("W[0]", varp_circuit:symbol(Vp, V1)),
    ?assertEqual("W[3]", varp_circuit:symbol(Vp, Vn)),
    ?assertEqual("P(1,2)", varp_circuit:symbol(Vp, P)),
    %% an internal variable has no symbol of its own
    ?assertEqual("X("++integer_to_list(Aux)++")",
		 varp_circuit:symbol(Vp, Aux)),
    ?assertEqual("t", varp_circuit:symbol(Vp, true)),
    ?assertEqual("f", varp_circuit:symbol(Vp, false)),
    %% a negative literal is printed with a leading !
    ?assertEqual("!A", varp_circuit:literal(Vp, -A)).

%% format_var/format_lit/format_clause go through varp_circuit:symbol/2
format_var_test() ->
    Bs = varp_formula:new(),
    Vp = element(#bs.vp, Bs),
    A = varp_circuit:atom(Vp, <<"A">>),
    B = varp_circuit:atom(Vp, <<"B">>),
    varp_circuit:clause(Vp, [A,-B]),
    ?assertEqual("A", str(varp_format:format_var(Bs, A))),
    ?assertEqual("!A", str(varp_format:format_lit(Bs, -A))),
    ?assertEqual("1", str(varp_format:format_var(Bs, true))),
    ?assertEqual("0", str(varp_format:format_var(Bs, false))),
    %% with the value appended
    varp_nif:bind(Vp, A),
    ?assertEqual("A=1", str(varp_format:format_var(Bs, A, true))),
    ?assertMatch("A=1@" ++ _, str(varp_format:format_var(Bs, A, level))),
    ?assert(length(str(varp_format:format_clause(Bs, [A,-B]))) > 0).

%%%-------------------------------------------------------------------
%%% Model output formats
%%%-------------------------------------------------------------------

print_format_test_() ->
    [{atom_to_list(Fmt),
      fun() ->
	      Out = capture(
		      fun() ->
			      varp_tc:run("(A or B) and (!A or C)",
					  [{satisfy,[]},{backtrack,[{max,1}]}],
					  #{print => Fmt})
		      end),
	      ?assert(length(Out) > 0)
      end} || Fmt <- [model, literal, erlang, dimacs]].

%% run Fun capturing everything it writes to the group leader
capture(Fun) ->
    Self = self(),
    Collector = spawn(fun() -> collect(Self, []) end),
    Old = group_leader(),
    group_leader(Collector, self()),
    try Fun()
    after
	group_leader(Old, self())
    end,
    Collector ! {done, self()},
    receive {Collector, Data} -> Data after 5000 -> [] end.

collect(_Owner, Acc) ->
    receive
	{io_request, From, ReplyAs, {put_chars,_,Chars}} ->
	    From ! {io_reply, ReplyAs, ok},
	    collect(_Owner, [Acc|Chars]);
	{io_request, From, ReplyAs, {put_chars,_,M,F,As}} ->
	    From ! {io_reply, ReplyAs, ok},
	    collect(_Owner, [Acc|apply(M,F,As)]);
	{io_request, From, ReplyAs, _} ->
	    From ! {io_reply, ReplyAs, ok},
	    collect(_Owner, Acc);
	{done, Pid} ->
	    Pid ! {self(), lists:flatten(Acc)};
	_ ->
	    collect(_Owner, Acc)
    end.
