%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2010, Tony Rogvall
%%% @doc
%%%    Prover interface
%%% @end
%%% Created :  5 Aug 2010 by Tony Rogvall <tony@rogvall.se>

-module(varp).

-export([run_formula/1, run_formula/2]).
-export([prove_formula/1, prove_formula/2]).
-export([parse/1, parse/2]).
-export([file/1, string/1, file_expand_cnf/2]).


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
