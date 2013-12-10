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
    {Mode,Opts,Files} = process_args0(Args, none, [], []),
    case Files of
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
    ok.


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

usage() ->
    io:format("varp: usage: varp [<Mode>] [Options] [Bindings] [files]\n"),
    io:format("  <Mode> = satisfy|falsify|prove|cnf\n"),
    io:format("Options\n"),
    lists:foreach(
      fun({Opt,_,Spec,Def}) ->
	      io:format("  --~s = ~s (~s)\n",
			[Opt,format_spec(Spec),format_value(Def)])
      end, options()),
    halt(1).

usage(Opt) when is_list(Opt) ->
    io:format("varp: unknown option ~s\n", [Opt]),
    halt(1);    
usage(Opt) when is_atom(Opt) ->
    case lists:keyfind(Opt, 2, options()) of
	false -> 
	    io:format("varp: unknown option '~s'\n", [Opt]),
	    halt(1);
	{OptName,_,Spec,_Def} ->
	    io:format("varp: bad argument to option '--~s', allowed values are ~s\n", 
		      [OptName,format_spec(Spec)]),
	    halt(1)
    end.

format_spec(unsigned) -> "unsigned integer";
format_spec(integer) -> "integer";
format_spec(undefined) -> "undefined";
format_spec(Vs) when is_list(Vs) ->
    string:join([Name || {Name,_Enum} <- Vs], "|").

format_value(N) when is_integer(N) -> integer_to_list(N);
format_value(A) when is_atom(A) -> atom_to_list(A).
    
options() ->
    Level = [{"debug",debug},{"info",info},{"notice",notice},
	     {"warning",warning},{"error",error},{"critical",critical},
	     {"alert",alert},{"emergency",emergency},{"none",none}],
    [{"value", value, [{"true",true},{"false",false},
			 { "none", none}], none},
     {"print", print, [{"true",true},{"literal",literal},
		       {"model",model},{"false",false}], false},
     {"partial", partial, [{"true",true},{"false",false}], false},
     {"method",method,[{"collect", collect}, {"count", count}], collect},
     {"max", max,  unsigned, 0 },  %% (0=all)
     {"order", order, [{"identity",identity},
			 {"reverse", reverse},
			 {"depth",depth},
			 {"occure",occure},
			 {"depth_occure",depth_occure},
			 {"occure_depth",occure_depth}], identify},
     {"bcp", bcp, [{"true",true},{"false",false}], false},
     {"saturate", saturate, unsigned, 0 },
     {"backtrack", backtrack, [{"true",true},{"false",false}], true},
     {"pair", pair, [{"true",true},{"false",false}], true},
     {"assoc", assoc, [{"left",left},{"right",right},{"middle",middle}], left},
     {"threshold", threshold, unsigned, 0 },
     {"carry",carry,[{"true",true},{"false",false},{"ignore",ignore}],ignore},
     {"borrow",borrow,[{"true",true},{"false",false},{"ignore",ignore}],ignore},
     {"divz",divz,[{"true",true},{"false",false},{"ignore",ignore}],false},
     {"log", log, Level, none},
     {"output", output, string, ""},
     {"help", help, undefined, undefined}
    ].


%% check "base" mode satisfy|falsify|prove
process_args0(["satisfy"|As], _Mode, Opts, Bound) ->
    process_args(As, satisfy, Opts, Bound);
process_args0(["falsify"|As], _Mode, Opts, Bound) ->
    process_args(As, falsify, Opts, Bound);
process_args0(["prove"|As], _Mode, Opts, Bound) ->
    process_args(As, prove, Opts, Bound);
process_args0(["cnf"|As], _Mode, Opts, Bound) ->
    process_args(As, cnf, Opts, Bound);
process_args0(As, Mode, Opts, Bound) ->
    process_args(As, Mode, Opts, Bound).

%% process long options and values
process_args(["--"++LongOpt|As],Mode,Opts,Bound) ->
    case match_long_opt(LongOpt,As,options()) of
	false ->
	    usage(LongOpt);
	{{_,help,_,_},_Val,_As1} ->
	    usage();
	{{_,Opt,ValSpec,_Default},Val,As1} ->
	    case match_value(ValSpec,Val) of
		false ->
		    usage(Opt);
		{ok,Value} ->
		    process_args(As1,Mode,[{Opt,Value}|Opts],Bound)
	    end
    end;
process_args(["-"++LongOpt|As],Mode,Opts,Bound) -> %% fixme short opts
    case match_long_opt(LongOpt,As,options()) of
	false ->
	    usage(LongOpt);
	{{_,help,_,_},_Val,_As1} ->
	    usage();
	{{_,Opt,ValSpec,_Default},Val,As1} ->
	    case match_value(ValSpec,Val) of
		false ->
		    usage(Opt);
		{ok,Value} ->
		    process_args(As1,Mode,[{Opt,Value}|Opts],Bound)
	    end
    end;
process_args([Var,"=",Value|As],Mode,Opts,Bound) ->
    V = list_to_atom(Var),
    case string:to_integer(Value) of
	{N,""} -> process_args(As,Mode,Opts,[{V,N}|Bound]);
	_ -> process_args(As,Mode,Opts,[{V,Value}|Bound])
    end;
process_args([A|As],Mode,Opts,Bound) ->
    case string:chr(A,$=) of
	0 -> 
	    {Mode, [{env,Bound}|Opts],[A|As]};
	I ->
	    {Var,"="++Value0} = lists:split(I-1,A),
	    {Value,As1} = 
		if Value0 == "" -> 
			case As of
			    [A2|As2] -> {A2,As2};
			    [] -> {"",[]}
			end;
		   true -> {Value0,As}
		end,
	    V = list_to_atom(Var),
	    case string:to_integer(Value) of
		{N,""} -> process_args(As1,Mode,Opts,[{V,N}|Bound]);
		_ -> process_args(As1,Mode,Opts,[{V,Value}|Bound])
	    end
    end;
process_args([], Mode, Opts, Bound) ->
    {Mode, [{env,Bound}|Opts], []};
process_args(_, _Mode, _Opts, _Bound) ->
    usage().


match_value(integer, Val) ->
    case string:to_integer(Val) of
	{N, ""} -> {ok,N};
	_ -> false
    end;
match_value(unsigned, Val) ->
    case string:to_integer(Val) of
	{N, ""} when N>=0 -> {ok,N};
	_ -> false
    end;
match_value(string, Val) ->
    {ok,Val};
match_value(undefined, "") ->
    {ok, true};
match_value([{Value,Enum}|_Vs], Value) ->
    {ok, Enum};
match_value([_|Vs], Value) ->
    match_value(Vs, Value);
match_value([], _) ->
    false.

match_long_opt(LongOpt,As,[Opt={OptName,_,Spec,_}|Opts]) ->
    case match_string(OptName, LongOpt) of
	false ->
	    match_long_opt(LongOpt,As,Opts);
	"" when Spec == undefined -> %% no value!
	    {Opt,"",As};
	"" ->
	    case As of
		["=",Value|As1] -> {Opt,Value,As1};
		["="++Value|As1] -> {Opt,Value,As1};
		[Value|As1] -> {Opt,Value,As1};
		[] -> {Opt,"",[]}
	    end;
	"=" ->
	    case As of
		[Value|As1] -> {Opt,Value,As1};
		[] -> {Opt,"",[]}
	    end;
	"="++Value1 ->
	    {Opt,Value1,As};
	_ ->
	    usage(LongOpt)
    end;
match_long_opt(LongOpt,_As,[]) ->
    usage(LongOpt).


match_string([C|Cs], [C|Ds]) ->
    match_string(Cs, Ds);
match_string([], Ds) ->
    Ds;
match_string(_, _) ->
    false.

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
    %% MetaBind = proplists:get_value(env, Opts, []),
    %% Opts1    = proplists:delete(env, Opts),
    %% Formula1 = form:expand(Formula,MetaBind),
    prover:run_formula(Formula, Opts).

prove_formula(Formula) ->
    prove_formula(Formula,[]).
prove_formula(Formula,Opts) ->
    %% MetaBind = proplists:get_value(env, Opts, []),
    %% Opts1    = proplists:delete(env, Opts),
    %% Formula1 = form:expand(Formula,MetaBind),
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
