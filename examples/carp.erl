%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2010, Tony Rogvall
%%% @doc
%%%     C language interface using prover backend
%%% @end
%%% Created : 31 Aug 2010 by Tony Rogvall <tony@rogvall.se>

-module(carp).

-compile(export_all).

file(File) ->
    case bic:file(File) of
	{ok,Elements} ->
	    compile(Elements);
	Error ->
	    Error
    end.
%%
%% Structure:
%%
%%  Global variables + Functions
%%  
%%
compile(Elements) ->
    io:format("Elements: ~p\n", [Elements]).

