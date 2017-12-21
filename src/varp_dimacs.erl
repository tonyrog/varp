%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2010, Tony Rogvall
%%% @doc
%%%    Read the dimacs format files
%%% @end
%%% Created : 20 Aug 2010 by Tony Rogvall <tony@rogvall.se>

-module(varp_dimacs).

-export([load/1, save/2]).
-export([parse/1]).
-export([format/1]).
-export([from_cnf/1]).
-import(lists, [reverse/1]).

-define(l2a(X), list_to_atom((X))).

load(File) ->
    case file:read_file(File) of
	{ok,Bin} ->
	    parse(Bin);
	Error -> Error
    end.

%% File format:
%% c <comment>
%% p <format> <variables> <clauses>
%%
%% <format>=cnf
%% Each line contains literal in form of integers 
%%   (signed are negated variables)
%% Each clause consist of a list of integers and is terminate by number 0
%%
%% Each integer I > 0 is mapped to {p,x,[I]}}
%% ande I < 0 is mapped to {'not',{p,x,[I]}}
%%
%% special comment
%% c <chars> 'is' <integer>
%% 
parse(Bin) ->
    preamble(Bin,[],1).

preamble(Bin,Vs,L) ->
    case binary_line(Bin) of
	eof -> [];
	{ok,[$c|Comment],Bin1} ->
	    Vs1 = scan_var(Comment,Vs),
	    preamble(Bin1,Vs1,L+1);
	{ok,[$p|Line],Bin1} ->
	    %% io:format("~s", [Line]),
	    case string:tokens(Line, " \r") of
		["snf", Variables, Clauses] ->
		    to_snf(Bin1,L,list_to_integer(Variables),
			   list_to_integer(Clauses));
		["cnf", Variables, Clauses] ->
		    to_cnf(Bin1,Vs,L,list_to_integer(Variables),
			   list_to_integer(Clauses));
		["sat", Variables] ->
		    sat(Bin1,Vs,L,list_to_integer(Variables));
		_ ->
		    {error,{L,unknown_format}}
	    end
    end.

%% CNF format
to_cnf(Bin,Vs,L,Vars,Clauses) ->
    case to_cnf_(Bin,Vs,L,[], []) of
	{ok,Cs} ->
	    {cnf,{Vars,Clauses,Cs}};
	Error ->
	    Error
    end.

to_cnf_(Bin,Vs,L,Acc,Cs) ->
    case binary_line(Bin) of
	eof ->
	    {ok,reverse(Cs)};
	{ok,[$%|_],_Bin1} ->  %% ????
	    {ok,reverse(Cs)};
	{ok,[$c|Comment],Bin1} -> 
	    Vs1 = scan_var(Comment,Vs),
	    to_cnf_(Bin1,Vs1,L+1,Acc,Cs);
	{ok,Line,Bin1} ->
	    case add_literals(string:tokens(Line, " \n"),Acc) of
		{false,Acc1} ->
		    to_cnf_(Bin1,Vs,L+1,Acc1,Cs);
		{true,Acc1} ->
		    to_cnf_(Bin1,Vs,L+1,[],[reverse(Acc1) | Cs])
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
sat(_Bin,_Vs,_L, _Vars) ->
    {error, not_implemented}.

%% SNF (Symbolc CNF format)
to_snf(Bin,L,Vars,Clauses) ->
    case to_snf_(Bin,L,[], []) of
	{ok,Cs} ->
	    {snf,{Vars,Clauses,Cs}};
	Error ->
	    Error
    end.

%% collect tokens until . is found then call varp_snf parse
to_snf_(Bin,Ln,Ts0,CLs) ->
    case binary_line(Bin) of
	eof ->
	    {ok,reverse(CLs)};
	{ok,[$%|_],_Bin1} ->  %% ????
	    {ok,reverse(CLs)};
	{ok,[$c|_Comment],Bin1} ->
	    to_snf_(Bin1,Ln+1,Ts0,CLs);
	{ok,Line,Bin1} ->
	    case varp_scan:string(Line) of
		{ok,Ts1,Ln1} ->
		    %% io:format("Ts0=~p, Ts1=~p\n", [Ts0,Ts1]),
		    Ts2 = Ts0 ++ Ts1,
		    Eol = lists:keymember('.',1,Ts1),
		    if Eol =:= true ->
			    case varp_snf:parse(Ts2) of
				{ok,CL} ->
				    to_snf_(Bin1,Ln1,[],[CL|CLs]);
				Error ->
				    {error,Ln,Error}
			    end;
		       true ->
			    to_snf_(Bin1,Ln1,Ts2,CLs)
		    end;
		Error ->
		    {error,Ln,Error}
	    end
    end.

save(File, Cs) ->
    file:write_file(File, format(Cs)).

format(Cs) ->
    {Cs1,NVars} = from_cnf(Cs),
    NClauses = length(Cs1),
    [["c auto generated from <file>\n"],
     ["p cnf ", integer_to_list(NVars), " ", integer_to_list(NClauses), "\n"],
     [[format_clause(CL)," 0","\n"] || CL <- Cs1]].
%%     ["%\n"],
%%     ["0\n"]].

format_clause([L]) -> [integer_to_list(L)];
format_clause([L|Ls]) -> [integer_to_list(L)," " | format_clause(Ls)].

%%
%% Translate clauses to dimacs form 
%%
from_cnf(Cs) ->
    D0 = dict:from_list([{'$fresh',1}]),
    {Cs1, D1} = from_cnf_(Cs, [], D0),
    NVars = dict:fetch('$fresh',D1),
    {Cs1,NVars-1}.

from_cnf_([CL|Cs], Acc, D) ->
    from_cnf_(CL, [], Cs, Acc, D);
from_cnf_([], Acc, D) ->
    {reverse(Acc), D}.

from_cnf_([L|Ls], Acc1, Cs, Acc, D) ->
    case L of
	true  -> from_cnf_(Cs, Acc, D);  %% clause is true remove it
	false -> from_cnf_(Ls, Acc1, Cs, Acc, D);
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

binary_line(Bin) ->
    case binary:split(Bin,<<"\n">>) of
	[<<>>] -> eof;
	[<<>>,<<>>] -> eof;
	[<<"\r">>,<<>>] -> eof;
	[Line,Bin1] -> {ok,binary_to_list(Line),Bin1}
    end.

%% look for char+ <blank> is <blank> <integer>
scan_var(Line,Vs) ->
    case string:tokens(Line, " \t\r") of
	[Var,"is",Var] ->
	    try list_to_integer(Var) of
		L -> [{Var,L}|Vs]
	    catch
		error:badarg ->
		    Vs
	    end;
	_ ->
	    Vs
    end.
