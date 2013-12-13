%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2010, Tony Rogvall
%%% @doc
%%%    Prover interface
%%% @end
%%% Created :  5 Aug 2010 by Tony Rogvall <tony@rogvall.se>

-module(varp).

-export([main/1]).
-export([run/3]).
-export([run_formula/1, run_formula/2]).
-export([prove_formula/1, prove_formula/2]).
-export([parse/1, parse/2]).
-export([file/1, string/1, file_expand_cnf/2]).


main(Args) ->
    application:start(varp),
    {Mode,Bound,Opts0,Files} = process_args0(Args, none, [], []),
    Opts = [{env,Bound}|Opts0],
    case Files of
	[] when Mode =:= help; Mode =:= version ->
	    run(Mode, undefined, Opts);
	[] ->
	    {ok,Data} = read_in(),
	    case parse("*stdin*", Data) of
		{ok,{Defs,Formula}} ->
		    run(Mode,Formula,[{defs,Defs}|Opts]);
		_Error ->
		    halt(1)
	    end;
	Fs ->
	    {Defs,Formula} = load_files(Fs, 'and'),
	    run(Mode,Formula,[{defs,Defs}|Opts])
    end,
    %% io:format("varp: arguments = ~p\n", [As]),
    halt(0).

run(satisfy, Formula, Opts) ->
    R = run_formula(Formula,Opts++[{value,true}]),
    result(R, satisfy);
run(falsify, Formula, Opts) ->
    R = run_formula(Formula,Opts++[{value,false}]),
    result(R, falsify);
run(prove, Formula, Opts) ->
    R = prove_formula(Formula,Opts),
    result(R, prove);
run(none, Formula, Opts) ->
    R = run_formula(Formula,Opts),
    result(R, none);
run(cnf, Formula, Opts) ->
    %% generate dimacs cnf from a formula
    Bs = proplists:get_value(env,Opts,[]),
    F = form:expand(Formula,Bs),
    %% Cs=clauses and Ls=literals eliminated
    {Cs,_Ls} = cnf:clauses(F),
    Data = cnf:format(Cs),
    case proplists:get_value(output,Opts,"") of
	"" ->
	    io:put_chars(Data);
	FileName ->
	    file:write_file(FileName, Data)
    end,
    ok;
run(help, _Formula, _Opts) ->
    varp_option:usage();
run(version, _Formula, _Opts) ->
    varp_option:version().


result(true,prove) ->
    io:format("TRUE\n", []);
result(false,prove) ->
    io:format("FALSE\n", []);
result(false,_) ->
    io:format("\n", []);
result(N, _) when is_integer(N) ->
    io:format("~w\n", [N]);
result({N,_Mdls}, _) ->
    io:format("~w\n", [N]).


%% load files and form a conjunction over all files
load_files([F|Fs],JoinOp) ->
    Ext = filename:extension(F),
    if Ext =:= ".cnf"; Ext =:= ".snf" ->
	    case dimacs:load(F) of
		{error,_Reason} ->
		    io:format("~s: error: ~p\n", [F,_Reason]),
		    halt(1);
		Cnf = {cnf,{_NVars,_NClauses,_CLs}} ->
		    io:format("loaded: ~s\n", [F]),
		    {Defs0,Formulas} =load_files(Fs,JoinOp),
		    {Defs0,join_f(JoinOp,Cnf,Formulas)}
	    end;
       true ->
	    {ok, Data} = file:read_file(F),
	    case parse(F, Data) of
		{ok,{Defs,Formula}} ->
		    io:format("loaded: ~s\n", [F]),
		    {Defs0,Formulas} =load_files(Fs,JoinOp),
		    {Defs++Defs0,join_f(JoinOp,Formula,Formulas)};
		_Error ->
		    halt(1)
	    end
    end;
load_files([],_JoinOp) ->
    {[],undefined}.

join_f(_JoinOp,undefined,B) -> B;
join_f(_JoinOp,A,undefined) -> A;
join_f(JoinOp,A,B) -> {JoinOp,A,B}.

%% check "base" mode satisfy|falsify|prove
process_args0(["satisfy"|As], _Mode, Opts, Bound) ->
    varp_option:process_args(As, satisfy, Opts, Bound);
process_args0(["falsify"|As], _Mode, Opts, Bound) ->
    varp_option:process_args(As, falsify, Opts, Bound);
process_args0(["prove"|As], _Mode, Opts, Bound) ->
    varp_option:process_args(As, prove, Opts, Bound);
process_args0(["cnf"|As], _Mode, Opts, Bound) ->
    varp_option:process_args(As, cnf, Opts, Bound);
process_args0(["help"|As], _Mode, Opts, Bound) ->
    varp_option:process_args(As, help, Opts, Bound);
process_args0(["version"|As], _Mode, Opts, Bound) ->
    varp_option:process_args(As, version, Opts, Bound);
process_args0(As, Mode, Opts, Bound) ->
    varp_option:process_args(As, Mode, Opts, Bound).


read_in() ->
    collect_in([]).

collect_in(Acc) ->
    case io:get_line('') of
	eof -> 
	    {ok,list_to_binary(lists:reverse(Acc))};
	Line ->
	    collect_in([Line|Acc])
    end.

run_formula(Formula) ->
    run_formula(Formula,[]).
run_formula(Formula,Opts) ->
    prover:run_formula(Formula, Opts).

prove_formula(Formula) ->
    prove_formula(Formula,[]).
prove_formula(Formula,Opts) ->
    prover:prove_formula(Formula, Opts++[{max,2}]).

file(File) ->
    case file:read_file(File) of
	{ok,Binary} ->
	    parse(File,Binary);
	Error ->
	    Error
    end.

parse(String) ->
    parse("*internal*", String).
parse(File, Binary) when is_binary(Binary) ->
    parse(File, binary_to_list(Binary));
parse(File, String) ->
    case varp_scan:string(String) of
	{ok,Ts,_Ln} ->
	    case varp_parse:parse(Ts) of
		{ok,Formula} ->
		    {ok,Formula};
		Error ->
		    io:format("~s: Error: ~p\n", [File,Error]),
		    Error
	    end;
	Error ->
	    io:format("~s: Error: ~p\n", [File, Error]),
	    Error
    end.

string(Binary) when is_binary(Binary) ->
    string(binary_to_list(Binary));
string(String) when is_list(String) ->
    {ok,Ts,_Ln} = varp_scan:string(String),
    varp_parse:parse(Ts).

%% special
file_expand_cnf(File, MetaBind) ->
    case file(File) of
	{ok,F} ->
	    F1 = form:expand(F,MetaBind),
	    {CLs,_Ls} = cnf:clauses(F1),
	    CLs;
	Error ->
	    Error
    end.
