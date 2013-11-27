%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2010, Tony Rogvall
%%% @doc
%%%    Prover interface
%%% @end
%%% Created :  5 Aug 2010 by Tony Rogvall <tony@rogvall.se>

-module(varp).

-export([satisfy_file/1, satisfy_file/2]).
-export([satisfy_formula/1, satisfy_formula/2]).
-export([falsify_file/1, falsify_file/2]).
-export([falsify_formula/1, falsify_formula/2]).


-compile(export_all).
-define(SCAN_CHUNK_SIZE, 16).  %% small
%% -define(SCAN_CHUNK_SIZE, 2048).
-include_lib("kernel/include/file.hrl").

start() ->
    start([]).

%% require -noshell -noinput? -nouser?
start([]) ->
    P = open_port({fd,0,0}, [in,eof]),
    Res = collect_port_data(P, [], 1000),
    erlang:port_close(P),
    case Res of
	{ok,Data} ->
	    case parse("*stdin*", Data) of
		{ok,Formula} ->
		    satisfy_formula(Formula,[]),
		    stop(0);
		_Error ->
		    stop(1)
	    end;
	Error ->
	    io:format("Error: ~p\n", [Error]),
	    stop(1)
    end;
start([File]) ->
    case file:read_file(File) of
	{ok,Binary} ->
	    case parse(File, Binary) of
		{ok,Formula} ->
		    MetaBind = [], %% fixme: pick form command line
		    satisfy_formula(Formula,MetaBind),
		    stop(0);
		_Error ->
		    stop(1)
	    end;
	Error ->
	    io:format("Error: ~p\n", [Error]),
	    stop(1)
    end.

stop(Code) ->
    erlang:halt(Code).


eval_file(File) ->
    eval_file(File,[]).
eval_file(File,MetaBind) ->
    case file(File) of
	{ok,Formula} ->
	    eval_formula(Formula,MetaBind);
	Error ->
	    Error
    end.

eval_formula(Formula) ->
    eval_formula(Formula,[]).
eval_formula(Formula,MetaBind) ->
    Formula1 = form:expand(Formula,MetaBind),
    %% io:format("Formula1: ~p\n", [Formula1]),
    prover:eval_formula(Formula1, 
			[{value,true},
			 {log, info},
			 {print, true},
			 {method, collect}]).


satisfy_file(File) ->
    satisfy_file(File,[]).
satisfy_file(File,MetaBind) ->
    case file(File) of
	{ok,Formula} ->
	    satisfy_formula(Formula,MetaBind);
	Error ->
	    Error
    end.

satisfy_formula(Formula) ->
    satisfy_formula(Formula,[]).
satisfy_formula(Formula,MetaBind) ->
    Formula1 = form:expand(Formula,MetaBind),
    %% io:format("Formula1: ~p\n", [Formula1]),
    prover:satisfy_formula(Formula1, 
			   [{saturate, 1},
			    %% {eval_bcp, true},
			    {max, 2},
			    {log, info},
			    {print, true},
			    {method, collect}]).

falsify_file(File) ->
    falsify_file(File,[]).
falsify_file(File,MetaBind) ->
    case file(File) of
	{ok,Formula} ->
	    falsify_formula(Formula,MetaBind);
	Error ->
	    Error
    end.

falsify_data(File,Data) ->
    falsify_data(File,Data,[]).
falsify_data(File,Data,MetaBind) ->
    case parse(File, Data) of
	{ok,Formula} ->
	    falsify_formula(Formula,MetaBind),
	    stop(0);
	Error ->
	    io:format("~s: Error: ~p\n", [File, Error]),
	    stop(1)
    end.

falsify_formula(Formula) ->
    falsify_formula(Formula,[]).
falsify_formula(Formula,MetaBind) ->
    Formula1 = form:expand(Formula,MetaBind),
    %% io:format("Formula1: ~p\n", [Formula1]),
    prover:falsify_formula(Formula1, 
			   [{saturate, 1},
			    {max, 2},
			    {log, info},
			    {print, true},
			    {method, collect}]).
    


collect_port_data(P, Acc, Timeout) ->
    receive
	{P,{data,Data}} ->
	    %% io:format("readn_buf: data=~p\n", [Data]),
	    collect_port_data(P, [Data|Acc], Timeout);
	{P, eof} ->
	    {ok, list_to_binary(lists:reverse(Acc))}
    after Timeout ->
	    {error, timeout}
    end.

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

    
