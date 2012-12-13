%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2010, Tony Rogvall
%%% @doc
%%%    Prover interface
%%% @end
%%% Created :  5 Aug 2010 by Tony Rogvall <tony@rogvall.se>

-module(varp).

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
	    run_binary("*stdin*", Data);
	Error ->
	    io:format("Error: ~p\n", [Error]),
	    stop(1)
    end;
start([File]) ->
    case file:read_file(File) of
	{ok,Binary} ->
	    run_binary(File,Binary);
	Error ->
	    io:format("Error: ~p\n", [Error]),
	    stop(1)
    end.

stop(Code) ->
    erlang:halt(Code).

run_binary(_File,Binary) when is_binary(Binary) ->
    case varp_scan:string(binary_to_list(Binary)) of
	{ok,Ts,_Ln} ->
	    case varp_parse:parse(Ts) of
		{ok,Formula} ->
		    run(Formula),
		    stop(0);
		Error ->
		    io:format("~s: Error: ~p\n", [_File,Error]),
		    stop(1)
	    end;
	Error ->
	    io:format("~s: Error: ~p\n", [_File, Error]),
	    stop(1)
    end.

    
run(Formula) ->
    Formula1 = form:expand(Formula),
    io:format("Formula1: ~p\n", [Formula1]),
    prover:satisfy_formula(Formula1, 
			   [{saturate, 1},
			    {max, 2},
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



string(Binary) when is_binary(Binary) ->
    string(binary_to_list(Binary));
string(String) when is_list(String) ->
    {ok,Ts,_Ln} = varp_scan:string(String),
    varp_parse:parse(Ts).

expand(String) ->
    {ok,F} = string(String),
    form:expand(F).
