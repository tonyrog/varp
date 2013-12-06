%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2010, Tony Rogvall
%%% @doc
%%%    Read the dimacs format files
%%% @end
%%% Created : 20 Aug 2010 by Tony Rogvall <tony@rogvall.se>

-module(dimacs).

-export([load/1, save/2]).
-export([format/1]).
-export([from_cnf/1]).
-import(lists, [reverse/1]).

load(File) ->
    case file:open(File,[read]) of
	{ok,Fd} ->
	    try load_(Fd) of
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
load_(Fd) ->
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
		    to_cnf(Fd,L,list_to_integer(Variables),
			list_to_integer(Clauses));
		["sat", Variables] ->
		    sat(Fd,L,list_to_integer(Variables));
		_ ->
		    {error,{L,unknown_format}}
	    end
    end.

%% CNF format
to_cnf(Fd,L, Vars, Clauses) ->
    case to_cnf_(Fd,L,[], []) of
	{ok,Cs} ->
	    {cnf,{Vars,Clauses,Cs}};
	Error ->
	    Error
    end.

to_cnf_(Fd,L,Acc,Cs) ->
    case file:read_line(Fd) of
	eof ->
	    {ok,reverse(Cs)};
	{ok,[$%|_]} ->  %% ????
	    {ok,reverse(Cs)};	    
	{ok,Line} ->
	    case add_literals(string:tokens(Line, " \n"),Acc) of
		{false,Acc1} ->
		    to_cnf_(Fd,L+1,Acc1,Cs);
		{true,Acc1} ->
		    to_cnf_(Fd,L+1,[],[reverse(Acc1) | Cs])
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

save(File, Cs) ->
    file:write_file(File, format(Cs)).

format(Cs) ->    
    Cs1 = from_cnf(Cs),
    NClauses = length(Cs1),
    Vs = lists:usort(lists:flatten(Cs1)),
    NVars = if hd(Vs) =:= 1 -> length(Vs) -1;
	       true -> length(Vs)
	    end,
    [["c auto generated from <file>\n"],
     ["p cnf ", integer_to_list(NVars), " ", integer_to_list(NClauses), "\n"],
     [[format_clause(CL)," 0","\n"] || CL <- Cs1],
     ["%\n"],
     ["0\n"]].

format_clause([L]) -> [integer_to_list(L)];
format_clause([L|Ls]) -> [integer_to_list(L)," " | format_clause(Ls)].

%%
%% Translate clauses to dimac form 
%%
from_cnf(Cs) ->
    D0 = dict:from_list([{'$fresh',2}]),
    {Cs1, _} = from_cnf_(Cs, [], D0),
    Cs1.

from_cnf_([CL|Cs], Acc, D) ->
    from_cnf_(CL, [], Cs, Acc, D);
from_cnf_([], Acc, D) ->
    {reverse(Acc), D}.

from_cnf_([L|Ls], Acc1, Cs, Acc, D) ->
    case L of
	true  -> from_cnf_(Ls, [1|Acc1], Cs, Acc, D);
	false -> from_cnf_(Ls, [-1|Acc1], Cs, Acc, D);
	{'not',V={p,_V,_Vs}} ->
	    case dict:find(V, D) of
		error -> 
		    N = dict:fetch('$fresh',D),
		    D1 = dict:store(V, N, D),
		    D2 = dict:update_counter('$fresh',1,D1),
		    from_cnf_(Ls, [-N|Acc1], Cs, Acc, D2);
		{ok,N} ->
		    from_cnf_(Ls, [-N|Acc1], Cs, Acc, D)
	    end;
	V={p,_V,_Vs} ->
	    case dict:find(V, D) of
		error -> 
		    N = dict:fetch('$fresh',D),
		    D1 = dict:store(V, N, D),
		    D2 = dict:update_counter('$fresh',1,D1),
		    from_cnf_(Ls, [N|Acc1], Cs, Acc, D2);
		{ok,N} ->
		    from_cnf_(Ls, [N|Acc1], Cs, Acc, D)
	    end
    end;
from_cnf_([], Acc1, Cs, Acc, D) ->
    from_cnf_(Cs, [reverse(Acc1)|Acc], D).
