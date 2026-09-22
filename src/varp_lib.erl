%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2026, Tony Rogvall
%%% @doc
%%%    The circuit library: files of circuits imported once.
%%%
%%%      import op_add;          // lib/default/op_add.varp, or a path
%%%      import "lib/mine/x.varp";
%%%
%%%    A file is looked up in the directories of --lib (default
%%%    lib/default of the installation), parsed in the same process
%%%    with the scanner state of the importing file saved around it,
%%%    and every circuit it defines, including the ones it imports in
%%%    turn, joins the definitions of the importing file.  A file is
%%%    imported once per parse.
%%%
%%%    The scanner also asks autoload/1 for a name it does not know, so
%%%    a library circuit can be used without an import: the file named
%%%    after it is imported.  A circuit the file defines itself wins
%%%    over the library's.
%%%
%%%    The library is how an arithmetic encoding is swapped: another
%%%    directory with the same circuit names, selected with --lib.
%%% @end

-module(varp_lib).

-export([import/1, autoload/1, definitions/0]).
-export([set_path/1, path/0, default_path/0, files/0]).
-export([reset/0, pending_names/0]).

-define(PATH, varp_lib_path).       %% [Dir]
-define(LOADED, varp_lib_loaded).   %% #{ File => true }
-define(DEFS, varp_lib_defs).       %% [{circuit,...}] not yet taken
-define(DEPTH, varp_lib_depth).     %% nesting of imports in progress

-define(SYMBOL_TABLE, varp_symbol_table).
%% the scanner and grammar state that an import must leave untouched
-define(SCANNER_KEYS, [varp_scan_cont, varp_scan_loc, varp_scan_buf,
		       circuit_defs, ?SYMBOL_TABLE]).

%% ------------------------------------------------------------------
%% the search path
%% ------------------------------------------------------------------

path() ->
    case get(?PATH) of
	undefined -> default_path();
	Path -> Path
    end.

default_path() ->
    case application:get_env(varp, lib) of
	{ok, Dirs} when is_list(Dirs), Dirs =/= [] -> Dirs;
	_ ->
	    Top = case code:lib_dir(varp) of
		      {error,_} -> ".";
		      Dir -> Dir
		  end,
	    [filename:join([Top, "lib", "default"])]
    end.

set_path(Dirs) when is_list(Dirs) ->
    put(?PATH, [to_list(D) || D <- Dirs]),
    ok.

to_list(D) when is_binary(D) -> binary_to_list(D);
to_list(D) -> D.

%% the library files on the path, for listings
files() ->
    lists:append([filelib:wildcard(filename:join(Dir, "*.varp"))
		  || Dir <- path()]).

%% ------------------------------------------------------------------
%% per parse state
%% ------------------------------------------------------------------

%% called by the scanner at the start of every parse; an import in
%% progress (depth > 0) keeps the state of the importing file
reset() ->
    case depth() of
	0 ->
	    put(?LOADED, #{}),
	    put(?DEFS, []),
	    %% the circuit names of the previous parse in this process
	    %% would stop the scanner from importing them again
	    put(circuit_defs, #{}),
	    ok;
	_ ->
	    ok
    end.

depth() ->
    case get(?DEPTH) of
	undefined -> 0;
	D -> D
    end.

%% the names of the circuits imported so far in this parse, so that
%% the grammar's reset of the circuit names keeps them (the first
%% token of a file is scanned before the grammar initialises)
pending_names() ->
    maps:from_list([{N, true} || {circuit,N,_,_} <- get_defs()]).

%% the definitions imported since the last call, for the grammar
definitions() ->
    Defs = get_defs(),
    put(?DEFS, []),
    Defs.

get_defs() ->
    case get(?DEFS) of
	undefined -> [];
	Defs -> Defs
    end.

%% ------------------------------------------------------------------
%% importing
%% ------------------------------------------------------------------

%% "import op_add;" or "import "dir/file.varp";" from the grammar
%% -> ok | {error, Reason}
import(Name) when is_binary(Name) ->
    import(binary_to_list(Name));
import(Name) when is_list(Name) ->
    Base = case filename:extension(Name) of
	       ".varp" -> Name;
	       _ -> Name ++ ".varp"
	   end,
    case find(Base, path()) of
	false -> {error, {no_such_library_file, Base}};
	File -> import_file(File)
    end.

%% the scanner: an unknown name that is a library file is a circuit
autoload(Name) when is_binary(Name) ->
    case find(binary_to_list(Name) ++ ".varp", path()) of
	false -> false;
	File ->
	    case import_file(File) of
		ok -> varp_formula:is_circuit_def(Name, false);
		{error, _} -> false
	    end
    end.

find(Base, Dirs) ->
    case filename:pathtype(Base) of
	absolute ->
	    case filelib:is_regular(Base) of
		true -> Base;
		false -> false
	    end;
	_ ->
	    find_(Base, Dirs)
    end.

find_(_Base, []) -> false;
find_(Base, [Dir|Dirs]) ->
    File = filename:join(Dir, Base),
    case filelib:is_regular(File) of
	true -> File;
	false -> find_(Base, Dirs)
    end.

%% parse a library file once, in this process, and register its
%% circuits; the importing file's scanner state is saved around it
import_file(File) ->
    Loaded = case get(?LOADED) of
		 undefined -> #{};
		 L -> L
	     end,
    case maps:is_key(File, Loaded) of
	true ->
	    ok;
	false ->
	    put(?LOADED, Loaded#{ File => true }),
	    Saved = [{K, get(K)} || K <- ?SCANNER_KEYS],
	    put(?DEPTH, depth() + 1),
	    Result = try parse_file(File)
		     after
			 put(?DEPTH, depth() - 1),
			 lists:foreach(fun({K,V}) -> put(K, V) end, Saved)
		     end,
	    case Result of
		{ok, Defs} ->
		    %% known to the scanner from now on, and handed to
		    %% the grammar with the file's own definitions
		    lists:foreach(fun varp_formula:add_circuit_def/1, Defs),
		    put(?DEFS, get_defs() ++ Defs),
		    ok;
		{error, Reason} ->
		    io:format("~s: ~s\n", [File, format(Reason)]),
		    {error, Reason}
	    end
    end.

parse_file(File) ->
    case file:read_file(File) of
	{ok, Bin} ->
	    varp_scan:init(varp:remove_comments(binary_to_list(Bin))),
	    case varp_parse:parse_and_scan({varp_scan, one_token, []}) of
		{ok, {Defs, _Assigns, _Formula}} ->
		    %% Defs holds the file's circuits and, first, the
		    %% ones it imported (varp_parse:file/3 adds them)
		    {ok, [D || D = {circuit,_,_,_} <- Defs]};
		{error, {Ln, Mod, Why}} when is_integer(Ln), is_atom(Mod) ->
		    {error, {Ln, Mod:format_error(Why)}};
		{error, Reason} ->
		    {error, Reason}
	    end;
	{error, Reason} ->
	    {error, Reason}
    end.

format({Ln, Text}) when is_integer(Ln) -> io_lib:format("~w: ~s", [Ln, Text]);
format(Reason) -> io_lib:format("~p", [Reason]).
