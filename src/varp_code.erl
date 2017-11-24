%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2015, Tony Rogvall
%%% @doc
%%%    Lint and generate code
%%% @end
%%% Created :  6 Sep 2015 by Tony Rogvall <tony@rogvall.se>

-module(varp_code).

-export([generate/2]).

-include("varp_bic.hrl").

-record(code,
	{
	  functions = [],
	  decls = [],
	  types = [],
	  bs
	}).

%% input is a list of global objects
%% functions / global variables / declarations ...
%%

generate(Code, Bs) ->
    C = code(Code, #code { bs=Bs }),
    C#code.bs.

code([F=#cfunction{} | Ds], C) ->
    io:format("function = ~p\n", [F]),
    code(Ds, function(F, C));
code([D=#cdecl{} | Ds], C) ->
    io:format("decl = ~p\n", [D]),
    code(Ds, decl(D, C));
code([T=#ctypedef{} | Ds], C) ->
    io:format("type = ~p\n", [T]),
    code(Ds, typedef(T, C));
code([], C) ->
    C.

function(F, C) ->
    Fs = [F | C#code.functions],
    C#code { functions = Fs }.

decl(D, C) ->
    Ds = [D | C#code.decls],
    C#code { decls = Ds }.

typedef(T, C) ->
    Ts = [T | C#code.types],
    C#code { types = Ts }.

