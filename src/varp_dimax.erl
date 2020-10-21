%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2020, Tony Rogvall
%%% @doc
%%%    Nextgen dimacs parser
%%% @end
%%% Created : 19 Sep 2020 by Tony Rogvall <tony@rogvall.se>

-module(varp_dimax).
-compile(export_all).

-export([load_file/1, load_file/2]).

load_file(Filename) ->
    load_file(Filename, undefined).

load_file(Filename, Vp) ->
    case varp_nc:cat(Filename) of
	undefined ->
	    load_regualar_file(Filename, Vp);
	Cat ->
	    load_nc_file([Cat," ",Filename], Vp)
    end.

load_regualar_file(Filename, Vp) ->
    case file:open(Filename, [read, raw, binary, read_ahead]) of
	{ok, Fd} ->
	    try load_stream(Vp, 1, fun() -> file:read_line(Fd) end) of
		Res -> Res
	    after
		file:close(Fd)
	    end;
	Error ->
	    Error
    end.

load_nc_file(Cmd, Vp) ->
    case varp_nc:open(Cmd) of
	{ok, Fd} ->
	    try load_stream(Vp, 1, fun() -> varp_nc:read_line(Fd) end) of
		Res -> Res
	    after
		varp_nc:close(Fd)
	    end;
	Error ->
	    Error
    end.


load_stream(undefined, Line, LineFun) ->
    load_stream_header(varp_nif:new(#{}), Line, LineFun);
load_stream(Vp, Line, LineFun) ->
    load_stream_header(Vp, Line, LineFun).

load_stream_header(Vp, Line, LineFun) ->
    case LineFun() of
	eof ->
	    {error, bad_format};
	{ok, <<$c,_/binary>>} ->
	    load_stream_header(Vp, Line+1, LineFun);
	{ok, <<"p cnf ",Data/binary>>} ->
	    case dimacs_line(Data) of
		[NVars,NClauses] ->
		    io:format("loading: ~w variables, ~w clauses\n",
			      [NVars, NClauses]),
		    {1,NVars} = varp_nif:add_variables(Vp, NVars),
		    io:format("loading clauses\n"),
		    load_stream_clauses(Vp, Line+1, NClauses, LineFun);
		_ ->
		    {error, bad_problem_line}
	    end;
	{ok,_} ->
	    {error, bad_format}
    end.

load_stream_clauses(Vp, Line, Count, LineFun) ->
    case LineFun() of
	eof ->
	    if Count > 0 ->
		    {error, missing_clauses};
	       true ->
		    {ok,Vp}
	    end;
	{ok, <<$c,_/binary>>} ->
	    load_stream_clauses(Vp, Line+1, Count, LineFun);
	{ok,Data} ->
	    if Line rem 10000 =:= 0 ->
		    io:format("~w lines loaded\n", [Line]);
	       true ->
		    ok
	    end,
	    Clause = dimacs_line(Data),
	    varp_nif:add_clause(Vp, Clause),
	    load_stream_clauses(Vp, Line+1, Count-1, LineFun)
    end.

dimacs_line(Data) ->
    Ts = re:split(Data, <<"\s+|\t+|\n">>),
    %% io:format("tokens = ~p\n", [Ts]),
    dimacs_tokens(Ts).

dimacs_tokens([<<>>]) ->
    [];
dimacs_tokens([<<"0">>,<<>>]) ->
    [];
dimacs_tokens([Lit|Rest]) ->
    [binary_to_integer(Lit) | dimacs_tokens(Rest)].
