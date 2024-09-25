%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2010, Tony Rogvall
%%% @doc
%%%    Read the dimacs format files
%%% @end
%%% Created : 20 Aug 2010 by Tony Rogvall <tony@rogvall.se>

-module(varp_dimacs).

-export([load/1, save/2, detect/1]).
-export([detect_binary/1]).
-export([detect_string/1]).
-export([detect_data/1]).
-export([parse/1]).
-export([format/1]).
-export([from_cnf/1]).
-export([format_error/1]).

-export([order_var_list/2]).

-import(lists, [reverse/1]).

-define(l2a(X), list_to_atom((X))).

-include("varp.hrl").

load(File) ->
    case file:read_file(File) of
	{ok,Bin} ->
	    parse(Bin);
	Error -> Error
    end.

detect(File) ->
    case file:read_file(File) of
	{ok,Bin} ->
	    detect_binary(Bin);
	Error -> Error
    end.

detect_data(Data) when is_binary(Data) ->
    detect_binary(Data);
detect_data(String) when is_list(String) ->
    detect_string(String).

detect_string(String) ->
    case string:split(String, "\n") of
	[[]] ->
	    false;
	[[$c|_Comment] | String1] ->
	    detect_string(String1);
	[[$p,$\s|Line] | _String1] ->
	    case string:tokens(Line, " \r") of
		["snf", _Variables, _Clauses] ->
		    {true,snf};
		["cnf", _Variables, _Clauses] ->
		    {true,cnf};
		["sat", _Variables] ->
		    {true,sat};
		_ ->
		    false
	    end;
	[_|_] ->
	    false
    end.


detect_binary(Bin) ->
    case binary_line(Bin) of
	eof ->
	    false;
	{ok,[$c|_Comment],Bin1} ->
	    detect_binary(Bin1);
	{ok,[$p,$\s|Line],_Bin1} ->
	    case string:tokens(Line, " \r") of
		["snf", _Variables, _Clauses] ->
		    {true,snf};
		["cnf", _Variables, _Clauses] ->
		    {true,cnf};
		["sat", _Variables] ->
		    {true,sat};
		_ ->
		    false
	    end;
	{ok,_, _} ->
	    false
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
%% and I < 0 is mapped to {'not',{p,x,[I]}}
%%
%% special comment
%% c <chars> 'is' <integer>
%% 
parse(Bin) ->
    preamble(Bin, varp:empty_sections(), 1).

preamble(Bin,Sect,L) ->
    case binary_line(Bin) of
	eof -> 
	    [];
	{ok,[$c|Comment],Bin1} ->
	    Sect1 = scan_section(Comment,Sect),
	    preamble(Bin1,Sect1,L+1);
	{ok,[$p,$\s|Line],Bin1} ->
	    %% io:format("~s", [Line]),
	    case string:tokens(Line, " \r") of
		["snf", Variables, Clauses] ->
		    to_snf(Bin1,Sect,L,list_to_integer(Variables),
			   list_to_integer(Clauses));
		["cnf", Variables, Clauses] ->
		    to_cnf(Bin1,Sect,L,list_to_integer(Variables),
			   list_to_integer(Clauses));
		["sat", Variables] ->
		    sat(Bin1,Sect,L,list_to_integer(Variables));
		_ ->
		    {error,{L,?MODULE,unknown_format}}
	    end;
	{ok,_,_Bin} ->
	    {error,{L,?MODULE,unknown_format}}
    end.

%% CNF format
to_cnf(Bin,Sect,L,Vars,Clauses) ->
    case to_cnf_(Bin,Sect,L,[],[]) of
	{ok,Sect1,Cs} ->
	    {cnf,{Vars,Clauses,Sect1,Cs}};
	Error ->
	    Error
    end.

to_cnf_(Bin,Sect,Ln,Acc,Cs) ->
    case binary_line(Bin) of
	eof ->
	    {ok,Sect,reverse(Cs)};
	{ok,[$%|_],_Bin1} ->  %% ????
	    {ok,Sect,reverse(Cs)};
	{ok,[$c|Comment],Bin1} -> 
	    Sect1 = scan_section(Comment,Sect),
	    to_cnf_(Bin1,Sect1,Ln+1,Acc,Cs);
	{ok,Line,Bin1} ->
	    case add_literals(string:tokens(Line, " \r"),Ln,Acc) of
		{false,Acc1} ->
		    to_cnf_(Bin1,Sect,Ln+1,Acc1,Cs);
		{true,Acc1} ->
		    to_cnf_(Bin1,Sect,Ln+1,[],[reverse(Acc1) | Cs]);
		Error={error,_Reason} ->
		    Error
	    end
    end.


add_literals([L|Ls],Ln,Acc) ->
    try list_to_integer(L) of
	0 ->
	    {true,Acc};
	Li ->
	    add_literals(Ls,Ln,[Li|Acc])
    catch
	error:_ ->
	    {error, {Ln,?MODULE,{not_integer_literal,L}}}
    end;
add_literals([],_Ln,Acc) ->
    {false, Acc}.

%% SAT format
sat(_Bin,_Sect, L, _Vars) ->
    {error,{L,?MODULE,not_implemented}}.

%% SNF (Symbolc CNF format)
to_snf(Bin,Sect,L,Vars,Clauses) ->
    case to_snf_(Bin,Sect,L,[],[]) of
	{ok,Sect1,Cs} ->
	    {snf,{Vars,Clauses,Sect1,Cs}};
	Error ->
	    Error
    end.

%% collect tokens until . is found then call varp_snf parse
%% may be terminated by . or 0!
to_snf_(Bin,Sect,Ln,Ts0,CLs) ->
    case binary_line(Bin) of
	eof ->
	    {ok,Sect,reverse(CLs)};
	{ok,[$%|_],_Bin1} ->  %% ????
	    {ok,Sect,reverse(CLs)};
	{ok,[$c|Comment],Bin1} -> 
	    Sect1 = scan_section(Comment,Sect),
	    to_snf_(Bin1,Sect1,Ln+1,Ts0,CLs);
	{ok,Line,Bin1} ->
	    case varp:tokens(Line) of
		{ok,Ts1} ->
		    Ts2 = Ts0 ++ Ts1,
		    case has_eol(Ts2) of
			true ->
			    case varp_snf:parse(Ts2) of
				{ok,CL} ->
				    to_snf_(Bin1,Sect,Ln+1,[],[CL|CLs]);
				{error,{Ln1,Mod,Message}} ->
				    {error,{Ln1-1+Ln,Mod,Message}};
				Error ->
				    Error
			    end;
			false ->
			    %% check if line is terminated by 0
			    case varp_snf:parse(Ts2++[{'.',Ln}]) of
				{ok,CL} ->
				    case lists:last(CL) of
					0 ->
					    to_snf_(Bin1,Sect,Ln,[],
						    [(CL--[0])|CLs]);
					_ ->
					    to_snf_(Bin1,Sect,Ln,Ts2,CLs)
				    end;
				{error,{Ln1,Mod,Message}} ->
				    {error,{Ln1-1+Ln,Mod,Message}};
				Error ->
				    Error
			    end
		    end;
		{error,{Ln1,Mod,Message}} ->
		    {error,{Ln1-1+Ln,Mod,Message}};
		Error ->
		    Error
	    end
    end.

has_eol(Ts) ->
    lists:keymember('.',1,Ts).

save(File, Cs) ->
    file:write_file(File, format(Cs, File)).

format(Cs) ->
    format(Cs, "*input*").

format(Cs, FileName) ->
    {Cs1,NVars} = from_cnf(Cs),
    NClauses = length(Cs1),
    [["c auto generated from ", FileName, "\n"],
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
	?T -> from_cnf_(Cs, Acc, D);  %% clause is true remove it
	?F -> from_cnf_(Ls, Acc1, Cs, Acc, D);
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

%% Fixme: allow blank last lines?
binary_line(Bin) ->
    case binary:split(Bin,<<"\n">>) of
	[<<>>] -> eof;
	[<<>>,<<>>] -> eof;
	[<<"\r">>,<<>>] -> eof;
	[Line,Bin1] -> {ok,binary_to_list(Line),Bin1};
	[Line] -> {ok,binary_to_list(Line),<<>>}
    end.

%% look for:
%%    <name> "is" <integer>
%%    declare <name> ":" <size>/signed
%%    declare <name> ":" <size>/unsigned
%%    order <li> ... .
%% 
scan_section(Line,Sect=#{ decls := Decls, order := Order, syms := Sym }) ->
    case varp:tokens(Line) of
	{ok,Ts=[{symbol,_,_}|_]} ->
	    case parse_symbol(Ts,{identifier,1,"is"}) of
		{Symbol,[{decnum,_,Num}]} ->
		    I = list_to_integer(Num),
		    Sym1 = maps:put(Symbol, I, Sym),
		    Sym2 = maps:put(I, [Symbol], Sym1),
		    Sect#{ syms => Sym2 };
		_ ->
		    Sect
	    end;
	{ok,[{declare,_}|Ts=[{symbol,_,_}|_]]} ->
	    case parse_symbol(Ts,{':',1}) of
		{Symbol,[{decnum,_,Size},{'/',_},{signed,_}]} ->
		    Sz = list_to_integer(Size),
		    Arity = symbol_arity(Symbol),
		    Decls1 = Decls#{ Symbol => {int,Arity,Sz}},
		    Sect#{ declare => Decls1};
		{Symbol,[{decnum,_,Size},{'/',_},{unsigned,_}]} ->
		    Sz = list_to_integer(Size),
		    Arity = symbol_arity(Symbol),
		    Decls1 = Decls#{ Symbol => {uint,Arity,Sz}},
		    Sect#{ declare => Decls1};
		{Symbol,[{decnum,_,Size}]} ->
		    Arity = symbol_arity(Symbol),
		    Sz = list_to_integer(Size),
		    Decls1 = Decls#{ Symbol => {uint,Arity,Sz}},
		    Sect#{ declare => Decls1};
		_ ->
		    Sect
	    end;
	{ok,Ts=[{order,_Ln}|Ts1],_Ln1} ->
	    case order_var_list(Ts1, []) of
		{ok, Order1} ->
		    Sect# { order => Order ++ Order1 };
		error ->
		    io:format("bad order ~w\n", [Ts]),
		    Sect
	    end;
	_Str ->
	    %% io:format("scan = ~p\n", [_Str]),
	    Sect
    end.

symbol_arity({p,_S,Args}) -> length(Args);
symbol_arity({bit_index,Sym,_I}) -> symbol_arity(Sym).

order_var_list([], Acc) ->
    {ok,[{order_list,lists:reverse(Acc)}]};
order_var_list([{',',_Ln}|Ts], Acc) ->
    order_var_list(Ts, Acc);
order_var_list([{decnum,_Ln,Str}|Ts], Acc) ->
    order_var_list(Ts, [list_to_integer(Str)|Acc]);
order_var_list(Ts, Acc) ->
    case parse_symbol(Ts, {',',1}) of
	false -> error;
	{Sym,Ts1} ->
	    order_var_list(Ts1, [Sym|Acc])
    end.

parse_symbol(Ts, Separator) ->
    %% io:format("parse_symbol: ~p (sep = ~p)\n", [Ts, Separator]),
    case lists:takewhile(fun(T) -> T =/= Separator end, Ts) of
	[] -> 
	    false;
	Ts0 ->
	    case varp_snf:parse(Ts0++[{'.',1}]) of
		{ok,[Sym]} ->
		    case lists:dropwhile(fun(T) -> T =/= Separator end, Ts) of
			[] ->
			    {eval_sym(Sym), []};
			[_|Ts1] ->
			    {eval_sym(Sym), Ts1}
		    end;
		{ok,_} ->
		    false;
		_ ->
		    false
	    end
    end.

eval_sym({p,S,Args}) ->
    {p,S,[eval_arg(A)||A<-Args]};
eval_sym({bit_index,Sym,Index}) ->
    {bit_index,eval_sym(Sym),eval_arg(Index)}.

eval_arg(V) when is_integer(V) -> V;
eval_arg({const,V}) -> V.

format_error(Error) ->
    io_lib:format("~p", [Error]).
