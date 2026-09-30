%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2026, Tony Rogvall
%%% @doc
%%%    Data for a formula through its input modules.
%%%
%%%    A formula names its input modules, "input sudoku_io;", and a
%%%    file on the command line that is not a formula (a .txt, .dat,
%%%    or anything but .varp/.cnf/.snf) is handed to them.  A module
%%%    exports one or more of
%%%
%%%      file(File, Meta)   the whole file, read by the module itself
%%%      input(Line, Meta)  one line: varp reads the file and hands over
%%%                         line number recno (a meta variable, 1 by
%%%                         default) without its newline
%%%      input(Meta)        no file at all: the data is in the bindings,
%%%                         "varp sat bj msg=hello md5.varp"
%%%
%%%    each returning
%%%
%%%      {ok, Formula}                 a formula to conjoin
%%%      {ok, MetaBindings, Formula}   and meta variables to bind
%%%      skip                          nothing from this module
%%%      {error, Reason}
%%%
%%%    ({true, Formula}, as the old sudoku_io does, is accepted too.)
%%%    Meta is a map of the bindings, Formula is a parse tree such as
%%%    {lop,eq,{p,<<"M">>,[0]},{const,128}}.  The output side is
%%%    output(Fd, Partial, Model), see varp:output_model/3.
%%% @end
-module(varp_input).

-export([file/3, bindings/2]).
-export([lines/1]).

%% a data file through the first module that takes it
file([Mod|Mods], File, Meta) ->
    M = module(Mod),
    case {exported(M, file, 2), exported(M, input, 2)} of
	{true, _} ->
	    result(M:file(File, Meta), Mods, File, Meta);
	{false, true} ->
	    case line(File, Meta) of
		{ok, Line} -> result(M:input(Line, Meta), Mods, File, Meta);
		Error -> Error
	    end;
	{false, false} ->
	    file(Mods, File, Meta)
    end;
file([], File, _Meta) ->
    {error, {no_input_module, File}}.

%% no data file: the modules that take their data from the bindings
bindings([Mod|Mods], Meta) ->
    M = module(Mod),
    case exported(M, input, 1) of
	true -> result(M:input(Meta), Mods, bindings, Meta);
	false -> bindings(Mods, Meta)
    end;
bindings([], _Meta) ->
    skip.

result({ok, Formula}, _Mods, _Src, _Meta) -> {ok, [], Formula};
result({ok, MetaF, Formula}, _Mods, _Src, _Meta) -> {ok, MetaF, Formula};
result({true, Formula}, _Mods, _Src, _Meta) -> {ok, [], Formula};
result({false, _}, _Mods, Src, _Meta) -> {error, {input, Src}};
result(skip, Mods, bindings, Meta) -> bindings(Mods, Meta);
result(skip, Mods, File, Meta) -> file(Mods, File, Meta);
result(Error = {error, _}, _Mods, _Src, _Meta) -> Error.

%% line recno of a text file, 1 based, without the newline
line(File, Meta) ->
    case file:read_file(File) of
	{ok, Bin} ->
	    N = case maps:get(<<"recno">>, Meta, maps:get("recno", Meta, 1)) of
		    I when is_integer(I), I >= 1 -> I;
		    _ -> 1
		end,
	    Lines = lines(Bin),
	    case N =< length(Lines) of
		true -> {ok, lists:nth(N, Lines)};
		false -> {error, {no_such_line, File, N}}
	    end;
	Error ->
	    Error
    end.

%% the lines of a file as strings; a file without a final newline has
%% its last line too, an empty file has one empty line
lines(Bin) ->
    Ls = string:split(binary_to_list(Bin), "\n", all),
    case lists:last(Ls) of
	"" when length(Ls) > 1 -> lists:droplast(Ls);
	_ -> Ls
    end.

module(Name) when is_binary(Name) -> binary_to_atom(Name);
module(Name) when is_atom(Name) -> Name;
module({M,_F,_A}) -> M.

exported(M, F, A) ->
    case code:ensure_loaded(M) of
	{module, M} -> erlang:function_exported(M, F, A);
	_ -> false
    end.
