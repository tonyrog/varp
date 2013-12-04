%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2010, Tony Rogvall
%%% @doc
%%%    Read the dimacs format files
%%% @end
%%% Created : 20 Aug 2010 by Tony Rogvall <tony@rogvall.se>

-module(dimacs).

-export([file/1]).
-import(lists, [reverse/1]).

file(File) ->
    case file:open(File,[read]) of
	{ok,Fd} ->
	    try load(Fd) of
		Data ->
		    file:close(Fd),
		    Data
	    catch
		_:Reason ->
		    {error,Reason}
	    after
		file:close(Fd)
	    end;
	Error ->
	    Error
    end.

%% File format:
%% c <comment>
%% p <format> <variables> <clauses>
%%
%% <format>=cnf
%% Each line contains literal in form of integers 
%%   (signed are negated variables)
%% Each clause constist of a list of integers and is terminate by number 0
%%
%% Each integer I > 0 is mapped to {p,x,[I]}}
%% ande I < 0 is mapped to {'not',{p,x,[I]}}
%% 
load(Fd) ->
    preamble(Fd,1).

preamble(Fd,L) ->
    case file:read_line(Fd) of
	eof -> [];
	{ok,[$c|Comment]} -> 
	    io:format("~s", [Comment]),
	    preamble(Fd, L+1);
	{ok,[$p|Line]} ->
	    io:format("~s", [Line]),
	    case string:tokens(Line, " \n") of
		["cnf", Variables, Clauses] ->
		    cnf(Fd,L,list_to_integer(Variables),
			list_to_integer(Clauses));
		["sat", Variables] ->
		    sat(Fd,L,list_to_integer(Variables));
		_ ->
		    {error,{L,unknown_format}}
	    end
    end.

%% CNF format
cnf(Fd,L, Vars, Clauses) ->
    case cnf_(Fd,L,[], []) of
	{ok,Cs} ->
	    {cnf,{Vars,Clauses,Cs}};
	Error ->
	    Error
    end.

cnf_(Fd,L,Acc,Cs) ->
    case file:read_line(Fd) of
	eof ->
	    {ok,reverse(Cs)};
	{ok,[$%|_]} ->  %% ????
	    {ok,reverse(Cs)};	    
	{ok,Line} ->
	    case add_literals(string:tokens(Line, " \n"),Acc) of
		{false,Acc1} ->
		    cnf_(Fd,L+1,Acc1,Cs);
		{true,Acc1} ->
		    cnf_(Fd,L+1,[],[reverse(Acc1) | Cs])
	    end
    end.

add_literals([Var|Vs], Acc) ->
    case list_to_integer(Var) of
	0 -> {true,Acc};
	I when I < 0 -> add_literals(Vs, [{'not',{p,x,[-I]}}|Acc]);
	I -> add_literals(Vs, [{p,x,[I]}|Acc])
    end;
add_literals([], Acc) ->
    {false, Acc}.

%% SAT format
sat(_Fd, _L, _Vars) ->
    {error, not_implemented}.


    
    

		

	    

	    
    
				



