%%% Command line interface (varp:main/1).
%%%
%%% Every case runs varp:main/1 in its own erl, exactly the way
%%% priv/varp.sh does, so option parsing, exit codes and the printed
%%% result are all covered.
-module(varp_cli_tests).

-include_lib("eunit/include/eunit.hrl").

cli(Args) -> varp_tc:cli(Args).

f(Name) -> filename:join([varp_tc:top(), "formulas", "varp", Name]).
d(Name) -> filename:join([varp_tc:top(), "formulas", "dimacs", Name]).

contains(Out, Text) ->
    string:find(Out, Text) =/= nomatch.

%% NOTE on argument order: options are parsed against the option spec of
%% the plugin they follow, so global options must come before the first
%% plugin name and plugin options must come after it:
%%
%%    varp <global options>* [<plugin> <plugin options>*]* <bindings>* <files>*

%%%-------------------------------------------------------------------
%%% Options
%%%-------------------------------------------------------------------

version_test_() ->
    {timeout, 60,
     fun() ->
	     {Code,Out} = cli(["--version"]),
	     ?assertEqual(0, Code),
	     ?assert(contains(Out, "version")),
	     ?assertMatch({match,_}, re:run(Out, "[0-9]+\\.[0-9]+"))
     end}.

help_test_() ->
    {timeout, 60,
     fun() ->
	     {_Code,Out} = cli(["--help"]),
	     ?assert(contains(Out, "usage")),
	     ?assert(contains(Out, "--timeout")),
	     ?assert(contains(Out, "--print"))
     end}.

plugin_help_test_() ->
    {timeout, 60,
     fun() ->
	     {_Code,Out} = cli(["--help=backjump"]),
	     ?assert(contains(Out, "PLUGIN backjump OPTIONS")),
	     ?assert(contains(Out, "--max"))
     end}.

plugin_h_flag_test_() ->
    %% -h|--help right after a plugin name prints that plugin's options
    {timeout, 60,
     fun() ->
	     {Code1,Out1} = cli(["sat","bj","-h"]),
	     ?assertEqual(0, Code1),
	     ?assert(contains(Out1, "PLUGIN backjump OPTIONS")),
	     ?assert(contains(Out1, "--max-learned")),
	     {Code2,Out2} = cli(["bt","--max","3","--help"]),
	     ?assertEqual(0, Code2),
	     ?assert(contains(Out2, "PLUGIN backtrack OPTIONS"))
     end}.

unknown_option_test_() ->
    {timeout, 60,
     fun() ->
	     {Code,Out} = cli(["--no-such-option"]),
	     ?assertEqual(1, Code),
	     ?assert(contains(Out, "unknown option"))
     end}.

%%%-------------------------------------------------------------------
%%% Formulas on the command line
%%%-------------------------------------------------------------------

formula_option_test_() ->
    {timeout, 60,
     fun() ->
	     {Code,Out} = cli(["-f","A && B","sat","bj"]),
	     ?assertEqual(0, Code),
	     ?assert(contains(Out, "%"))
     end}.

unsat_formula_test_() ->
    {timeout, 60,
     fun() ->
	     {_Code,Out} = cli(["-f","A && !A","sat","bj"]),
	     ?assert(contains(Out, "% 0"))
     end}.

prove_test_() ->
    {timeout, 60,
     fun() ->
	     {_,Out1} = cli(["-f","A || !A","p","bj"]),
	     ?assert(contains(Out1, "% TRUE")),
	     {_,Out2} = cli(["-f","A && B","p","bj"]),
	     ?assert(contains(Out2, "% FALSE"))
     end}.

%%%-------------------------------------------------------------------
%%% Files and bindings
%%%-------------------------------------------------------------------

%% n pigeons into n-1 holes is unsatisfiable, n is bound on the
%% command line as "n=4"
pigeon_file_test_() ->
    {timeout, 120,
     fun() ->
	     {Code,Out} = cli(["sat","bj",f("pigeon.varp"),"n=4"]),
	     ?assertEqual(0, Code),
	     ?assert(contains(Out, "% 0"))
     end}.

%% a satisfiable file
sat_file_test_() ->
    {timeout, 120,
     fun() ->
	     {Code,Out} = cli(["sat","bj",f("send_more.varp")]),
	     ?assertEqual(0, Code),
	     ?assert(contains(Out, "% 1"))
     end}.

dimacs_file_test_() ->
    {timeout, 120,
     fun() ->
	     {Code,Out} = cli(["sat","bj",d("abcd.cnf")]),
	     ?assertEqual(0, Code),
	     ?assert(contains(Out, "%"))
     end}.

%%%-------------------------------------------------------------------
%%% starexec output and exit codes
%%%-------------------------------------------------------------------

starexec_test_() ->
    {timeout, 120,
     fun() ->
	     {Code,Out} = cli(["--starexec=true","sat","bj",
			       f("pigeon.varp"),"n=4"]),
	     ?assert(contains(Out, "s UNSATISFIABLE")),
	     ?assertEqual(20, Code)
     end}.

%%%-------------------------------------------------------------------
%%% Model counting from the command line
%%%-------------------------------------------------------------------

count_test_() ->
    {timeout, 120,
     fun() ->
	     %% all models of a formula with 3 free variables
	     {_Code,Out} = cli(["-f","A || B || C","sat","bt","--max","0"]),
	     ?assert(contains(Out, "% 7"))
     end}.

max_models_test_() ->
    {timeout, 120,
     fun() ->
	     {_Code,Out} = cli(["-f","A || B || C","sat","bt","--max","2"]),
	     ?assert(contains(Out, "% 2"))
     end}.

%%%-------------------------------------------------------------------
%%% Proof output
%%%-------------------------------------------------------------------

proof_file_test_() ->
    {timeout, 120,
     fun() ->
	     Dir = varp_tc:tmpdir(),
	     Path = filename:join(Dir, "cli_proof.out"),
	     _ = file:delete(Path),
	     {_Code,_Out} = cli(["--proof-output","text",
				 "--proof-file","cli_proof.out",
				 "--outdir",Dir,
				 "sat","bj",f("pigeon.varp"),"n=4"]),
	     ?assert(filelib:is_regular(Path)),
	     ?assert(filelib:file_size(Path) > 0)
     end}.

%%%-------------------------------------------------------------------
%%% Errors
%%%-------------------------------------------------------------------

missing_file_test_() ->
    {timeout, 60,
     fun() ->
	     {Code,Out} = cli(["sat","bj","/no/such/file.varp"]),
	     ?assertEqual(1, Code),
	     ?assert(contains(Out, "Unable to read file"))
     end}.

%%%-------------------------------------------------------------------
%%% Several inputs are conjoined
%%%-------------------------------------------------------------------

%% join_f/3 used to build {'and',A,B} where bld/3 wants {lop,'and',A,B},
%% so more than one file, or more than one -f, crashed
several_formulas_test_() ->
    {timeout, 60,
     fun() ->
	     {Code,Out} = cli(["-f","A","-f","B","sat","bt","--max","0"]),
	     ?assertEqual(0, Code),
	     ?assert(contains(Out, "1: A,B")),
	     ?assert(contains(Out, "% 1"))
     end}.

several_files_test_() ->
    {timeout, 60,
     fun() ->
	     Dir = varp_tc:tmpdir(),
	     A = filename:join(Dir, "join_a.varp"),
	     B = filename:join(Dir, "join_b.varp"),
	     ok = file:write_file(A, "A\n"),
	     ok = file:write_file(B, "B\n"),
	     {Code,Out} = cli(["sat","bt","--max","0",A,B]),
	     ?assertEqual(0, Code),
	     ?assert(contains(Out, "1: A,B")),
	     ?assert(contains(Out, "% 1")),
	     %% a file and a command line formula mix too
	     {_,Out2} = cli(["-f","!B","sat","bj",A]),
	     ?assert(contains(Out2, "% 1"))
     end}.

%% --check builds without searching, undeclared symbols are errors
check_test_() ->
    {timeout, 120,
     fun() ->
	     File = filename:join(varp_tc:formula_dir("varp"), "die_hard_system.varp"),
	     {Code, Out} = cli(["--check", "sat", "bj", File]),
	     ?assertEqual(0, Code),
	     ?assert(contains(Out, "% OK")),
	     ?assert(contains(Out, "assuming k=1")),
	     Typo = filename:join(varp_tc:tmpdir(), "typo.varp"),
	     ok = file:write_file(Typo, "declare Connected(a, b, time);\n"
				       "Conected(0,1,0)\n"),
	     {Code2, Out2} = cli(["--check", "sat", "bj", Typo]),
	     ?assertEqual(1, Code2),
	     ?assert(contains(Out2, "'Conected/3' is not declared")),
	     ?assert(contains(Out2, "did you mean 'Connected'"))
     end}.

%% an input module: the .txt file on the command line is the message,
%% the output module prints the digest in hex
md5_io_test_() ->
    {timeout, 300,
     fun() ->
	     Dir = varp_tc:formula_dir("varp"),
	     {Code, Out} = cli(["sat", "bj", filename:join(Dir, "md5.varp"),
				filename:join(Dir, "fox.txt")]),
	     ?assertEqual(0, Code),
	     ?assert(contains(Out, "9e107d9d372bb6826bd81d3542a419d6")),
	     %% --hex prints unsigned vectors in hex in the normal model output
	     {0, Out2} = cli(["--hex", "-f", "declare x:8; x == 255", "sat", "bt"]),
	     ?assert(contains(Out2, "x=0xff"))
     end}.

%% input modules: a data file line (recno picks the line), or the
%% bindings when there is no data file at all
input_module_test_() ->
    {timeout, 300,
     fun() ->
	     Dir = varp_tc:formula_dir("varp"),
	     Md5 = filename:join(Dir, "md5.varp"),
	     %% from the bindings, no data file
	     {0, Out1} = cli(["sat", "bj", "msg=hello world", Md5]),
	     ?assert(contains(Out1, "5eb63bbbe01eeed093cb22bb8f5acdc3")),
	     %% line 2 of a two line file
	     Two = filename:join(varp_tc:tmpdir(), "two.txt"),
	     ok = file:write_file(Two, "first line\nhello world\n"),
	     {0, Out2} = cli(["sat", "bj", "recno=2", Md5, Two]),
	     ?assert(contains(Out2, "5eb63bbbe01eeed093cb22bb8f5acdc3")),
	     {0, Out3} = cli(["sat", "bj", Md5, Two]),
	     ?assert(contains(Out3, "6b4a2b93c7a8ffb1d2a4c6f11e0f6a3c") orelse
		     not contains(Out3, "5eb63bbbe01eeed093cb22bb8f5acdc3")),
	     %% a data file without an input module is an error
	     {1, Out4} = cli(["sat", "bj", filename:join(Dir, "pigeon.varp"), Two]),
	     ?assert(contains(Out4, "no input module"))
     end}.

%% patterns: an unknown byte in the message is found from the digest,
%% and a partial model prints what it knows with * for the rest
pattern_test_() ->
    {timeout, 300,
     fun() ->
	     Md5 = filename:join(varp_tc:formula_dir("varp"), "md5.varp"),
	     H = "5eb63bbbe01eeed093cb22bb8f5acdc3",
	     {0, Out} = cli(["sat", "bj", "msg=hello*world", "digest=" ++ H, Md5]),
	     ?assert(contains(Out, H)),
	     ?assert(contains(Out, "msg=\"hello world\"")),
	     %% a wrong digest for a full message has no model
	     {0, Out2} = cli(["sat", "bj", "msg=hello world", "digest=0" ++ tl(H), Md5]),
	     ?assert(contains(Out2, "% 0")),
	     %% partial: the search is stopped at once, the known half prints
	     {0, Out3} = cli(["--partial", "sat", "bj", "--timeout", "0.2",
			      "mlen=11", "digest=5eb63bbbe01eeed0****************", Md5]),
	     ?assert(contains(Out3, "5eb63bbbe01eeed0")),
	     ?assert(contains(Out3, "*")),
	     {1, Out4} = cli(["sat", "bj", "digest=xyz", Md5]),
	     ?assert(contains(Out4, "digest") orelse contains(Out4, "not_hex"))
     end}.

%% order sorts every variable with five arrays of n elements; md5 has
%% enough variables that they must not go on the scheduler stack
%% (this was a segmentation fault)
order_large_test_() ->
    {timeout, 120,
     fun() ->
	     Md5 = filename:join(varp_tc:formula_dir("varp"), "md5.varp"),
	     H = "5eb63bbbe01eeed093cb22bb8f5acdc3",
	     {0, Out} = cli(["order", "--first=X", "sat", "bj", "msg=hello world", Md5]),
	     ?assert(contains(Out, H))
     end}.
