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
-export([scan_file/1]).
-export([file/1, string/1, file_expand_cnf/2]).

main(Args) ->
    application:start(varp),
    {Mode,Bound,Opts0,Files} = process_args0(Args, none, [], []),
    Opts = [{env,Bound}|Opts0],
    {ReadIn,{Defs0,Decls0,Code0,Formula0}} =
	case load_formulas(Opts, undefined, 'and') of
	    {ok,{[],[],[],undefined}} -> {true,{[],[],[],undefined}};
	    {ok,R0} -> {false,R0};
	    __Error -> halt(1)
	end,
    case Files of
	[] when Mode =:= help; Mode =:= version ->
	    run(Mode, undefined, Opts);
	[] when not ReadIn ->
	    run(Mode,Formula0,[{defs,Defs0}|Opts]);
	[] when ReadIn ->
	    case read_in() of
		{ok,<<>>} ->
		    run(Mode,Formula0,[{defs,Defs0}|Opts]);
		{ok,Data} ->
		    case parse("*stdin*", Data) of
			{ok,{Defs,Decls,Code,Formula}} ->
			    Formula1 = join_f('and',Formula0,Formula),
			    run(Mode,Formula1,
				[{defs,Defs0++Defs},
				 {decls,Decls0++Decls},
				 {code,Code0++Code}|Opts]);
			_Error ->
			    halt(1)
		    end;
		_Error ->
		    halt(1)
	    end;
	Fs ->
	    case load_files(Fs,Formula0,Defs0,Decls0,Code0,'and') of
		{ok,{Defs,Decls,Code,Formula}} ->
		    run(Mode,Formula,[{defs,Defs},
				      {decls,Decls},
				      {code,Code} | Opts]);
		_Error ->
		    halt(1)
	    end
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
run(snf, Formula, Opts) ->
    %% generate dimacs snf from a formula
    Bs = proplists:get_value(env,Opts,[]),
    F = varp_expand:formula(Formula,Bs),
    %% Cs=clauses and Ls=literals eliminated
    {Cs,_Ls} = varp_cnf:clauses(F),
    Data = varp_cnf:format(Cs),
    case proplists:get_value(output,Opts,"") of
	"" ->
	    io:put_chars(Data);
	FileName ->
	    file:write_file(FileName, Data)
    end,
    ok;
run(cnf, Formula, Opts) ->
    %% generate dimacs cnf from a formula
    Bs = proplists:get_value(env,Opts,[]),
    F = varp_expand:formula(Formula,Bs),
    %% Cs=clauses and Ls=literals eliminated
    {Cs,_Ls} = varp_cnf:clauses(F),
    Data = varp_dimacs:format(Cs),
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

result(true,prove) ->       io:format("% TRUE\n", []);
result(false,prove) ->      io:format("% FALSE\n", []);
result(undefined,prove) ->  io:format("% UNKNOWN\n", []);
result(undefined,_) ->      io:format("\n", []);
result(N, _) when is_integer(N) -> io:format("% ~w\n", [N]);
result({N,_Mdls}, _) -> io:format("% ~w\n", [N]).


%% load files and form a conjunction over all files
load_files([F|Fs],Formula0,Defs0,Decls0,Code0,JoinOp) ->
    Ext = filename:extension(F),
    if Ext =:= ".cnf"; Ext =:= ".snf" ->
	    case varp_dimacs:load(F) of
		Error={error,_Reason} ->
		    io:format("~s: error: ~p\n", [F,_Reason]),
		    Error;
		Cnf = {cnf,{_NVars,_NClauses,_CLs}} ->
		    io:format("% loaded: ~s\n", [F]),
		    Formula1 = join_f(JoinOp,Cnf,Formula0),
		    load_files(Fs,Formula1,Defs0,Decls0,Code0,JoinOp)
	    end;
       true ->
	    {ok, Data} = file:read_file(F),
	    case parse(F, Data) of
		{ok,{Defs,Decls,Code,Formula}} ->
		    io:format("% loaded: ~s\n", [F]),
		    Formula1 = join_f(JoinOp,Formula,Formula0),
		    load_files(Fs,Formula1,
			       Defs++Defs,
			       Decls++Decls0,
			       Code ++ Code0,
			       JoinOp);
		Error ->
		    Error
	    end
    end;
load_files([],Formula,Defs,Decls,Code,_JoinOp) ->
    {ok,{Defs,Decls,Code,Formula}}.


%% load/parse formulas given on command line like -f "A && B"
load_formulas(Opts, A, JoinOp) ->
    case proplists:get_all_values(formula, Opts) of
	[] -> {ok,{[],[],[],A}};
	Fs -> parse_formulas(Fs,A,[],[],[],JoinOp)
    end.

parse_formulas([F|Fs], Formula,Defs0,Decls0,Code0,JoinOp) ->
    case parse("*command-line*", F) of
	{ok,{Defs,Decls,Code,Formula1}} ->
	    parse_formulas(Fs, join_f(JoinOp, Formula, Formula1),
			   Defs0++Defs,Decls0++Decls,Code0++Code,JoinOp);
	Error ->
	    Error
    end;
parse_formulas([], Formula, Defs, Decls, Code, _JoinOp) ->
    {ok,{Defs,Decls,Code,Formula}}.
    

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
    varp_prover:run_formula(Formula, Opts).

prove_formula(Formula) ->
    prove_formula(Formula,[]).
prove_formula(Formula,Opts) ->
    varp_prover:prove_formula(Formula, [{max,2}|Opts]).

file(File) ->
    case file:read_file(File) of
	{ok,Binary} ->
	    parse(File,Binary);
	Error ->
	    Error
    end.

scan_file(File) ->
    case file:read_file(File) of
	{ok,Binary} ->    
	    tokens(binary_to_list(Binary));
	Error -> Error
    end.

parse(String) ->
    parse("*internal*", String).

parse(File, Binary) when is_binary(Binary) ->
    parse(File, binary_to_list(Binary));
parse(File, String) ->
    case tokens(String) of
	{ok,Ts} ->
	    case varp_parse:parse(Ts) of
		{ok,{Sections,Formula}} ->
		    {Defs,Decls,Code} = split_sections(Sections),
		    {ok,{Defs,Decls,Code,Formula}};
		Error={error,{Ln,Mod,Why}} when 
		      is_integer(Ln), is_atom(Mod) ->
		    Reason = Mod:format_error(Why),
		    io:format("~s:~w: ~s\n", [File,Ln,Reason]),
		    Error;
		Error ->
		    io:format("~s: Error: ~p\n", [File,Error]),
		    Error
	    end;
	Error ->
	    io:format("~s: Error: ~p\n", [File, Error]),
	    Error
    end.

split_sections(Sections) ->
    split_sections(Sections,[],[],[]).

split_sections([{declare,Decls}|Sections], Defs0, Decls0, Code0) ->
    split_sections(Sections, Defs0, Decls0++Decls, Code0);
split_sections([{code,Code}|Sections], Defs0, Decls0, Code0) ->
    split_sections(Sections, Defs0, Decls0, Code0++Code);
split_sections([Def|Sections], Defs0, Decls0, Code0) ->
    split_sections(Sections, Defs0++[Def], Decls0, Code0);
split_sections([], Defs0, Decls0, Code0) ->
    {Defs0, Decls0, Code0}.
    

string(Binary) when is_binary(Binary) ->
    string(binary_to_list(Binary));
string(String) when is_list(String) ->
    {ok,Ts} = tokens(String),
    varp_parse:parse(Ts).

tokens(String) ->
    case varp_scan:string(remove_comments(String)) of
	{ok,Ts,_Ln} -> 
	    %% io:format("tokens=~p\n", [Ts]),
	    {ok,Ts};
	Error -> Error
    end.

%% remove C-style comments from data
remove_comments([$/,$/|Cs]) -> remove_comments(remove_line(Cs));
remove_comments([$/,$*|Cs]) -> remove_comments(remove_block(Cs));
remove_comments([C|Cs]) -> [C|remove_comments(Cs)];
remove_comments([]) -> [].

%% remove until */ but keep all \n
remove_block([$*,$/|Cs]) -> Cs;
remove_block([$\n|Cs]) -> [$\n|remove_block(Cs)];
remove_block([_|Cs]) -> remove_block(Cs);
remove_block([]) -> [].

%% remove until end-of-line (but keep it)
remove_line(Cs=[$\n|_]) -> Cs;
remove_line([_|Cs]) -> remove_line(Cs);
remove_line([]) -> [].


%% special
file_expand_cnf(File, MetaBind) ->
    case file(File) of
	{ok,F} ->
	    F1 = varp_expand:formula(F,MetaBind),
	    {CLs,_Ls} = varp_cnf:clauses(F1),
	    CLs;
	Error ->
	    Error
    end.
