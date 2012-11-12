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


parse(File) ->
    case file:open(File, [read]) of
	{ok,Fd} ->
	    set_cont({chars,{"", 1}}),
	    try varp_parse:parse_and_scan({fun scan/1, [Fd]}) of
		Result -> Result
	    %%catch 
	    %%  error:Reason ->
	    %%	    io:format("varp_parse: error ~p\n", [Reason])
	    after
		erase_cont(),
		file:close(Fd)
	    end;
	Error ->
	    Error
    end.
%%
%% scan MUST return 
%%  {ok, Tokens, Endline}
%%  {eof, Endline}
%%  {error, Descriptor, Endline}
%%
scan(Fd) ->
    case get_cont() of
	{chars,Chars} ->
	    scan_chars_fd(Fd, [], Chars, []);
	{cont,Cont} ->
	    scan_cont_fd(Fd,Cont,[])
    end.

scan_chars_fd(Fd, Cont0, {Chars0,Line0}, Acc) ->
    case file:read(Fd, ?SCAN_CHUNK_SIZE) of
	eof when Acc =:= [] -> {eof,Line0};
	eof -> {ok, lists:reverse(Acc), Line0};
	{ok,Chars1} -> scan_chars(Fd,Cont0,{Chars0++Chars1,Line0},Acc);
	Error -> Error
    end.

scan_chars(Fd, Cont0, {Chars0,Line0}, Acc) ->
    case varp_scan:token(Cont0, Chars0, Line0) of
	{more,Cont1} -> 
	    if Acc =:= [] -> scan_cont_fd(Fd,{Cont1,Line0}, Acc);
	       true -> 
		    set_cont({cont,{Cont1,Line0}}),
		    {ok,lists:reverse(Acc),Line0}
	    end;
	{done,{ok,Token,Line1},Chars1} ->
	    scan_chars(Fd,[],{Chars1,Line1},[Token|Acc]);
	{done,{eof,Line1},Chars1} ->
	    set_cont({chars,{Chars1,Line1}}),
	    if Acc =:= [] -> {eof,Line1};
	       true -> {ok,lists:reverse(Acc),Line1}
	    end;
	{done,Error,Chars1} ->
	    set_cont({chars,{Chars1,Line0}}),
	    Error
    end.

scan_cont_fd(Fd, {Cont0,Line0}, Acc) ->
    case file:read(Fd, ?SCAN_CHUNK_SIZE) of
	eof when Acc =:= [] -> {eof,Line0};
	eof -> {ok, lists:reverse(Acc), Line0};
	{ok,Chars1} -> scan_cont_chars(Fd,Cont0,{Chars1,Line0},Acc);
	Error -> Error
    end.

scan_cont_chars(Fd,Cont0,{Chars0,Line0},Acc) ->
    case varp_scan:token(Cont0, Chars0) of
	{more,Cont1} -> 
	    if Acc =:= [] -> scan_cont_fd(Fd,{Cont1,Line0},Acc);
	       true -> 
		    set_cont({cont,{Cont1,Line0}}),
		    {ok,lists:reverse(Acc),Line0}
	    end;
	{done,{ok,Token,Line1},Chars1} ->
	    scan_chars(Fd,[],{Chars1,Line1},[Token|Acc]);
	{done,{eof,Line1},Chars1} ->
	    set_cont({chars,{Chars1,Line1}}),
	    if Acc =:= [] -> {eof,Line1};
	       true ->{ok,lists:reverse(Acc),Line1}
	    end;
	{done,Error,Chars1} ->
	    set_cont({chars,{Chars1,Line0}}),
	    Error
    end.    

get_cont() ->
    case get(varp) of
	undefined -> {chars,{"", 1}};
	Cont -> Cont
    end.

set_cont(Cont) -> put(varp,Cont).

erase_cont() ->
    erase(varp).
    

string(Binary) when is_binary(Binary) ->
    string(binary_to_list(Binary));
string(String) when is_list(String) ->
    {ok,Ts,_Ln} = varp_scan:string(String),
    varp_parse:parse(Ts).

expand(String) ->
    {ok,F} = string(String),
    form:expand(F).

    
    
