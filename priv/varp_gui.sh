#!/usr/bin/env escript
%%% -*- erlang -*-
%%%
%%% Start varp in GUI mode.  Works from anywhere, also through a
%%% symlink on PATH, by locating ebin relative to this script.
%%% Note that $VAR is NOT expanded in an escript %%! line, which is why
%%% the code path is set here instead.

main(Args) ->
    ok = add_ebin(),
    varp:main(["--gui=true"|Args]).

add_ebin() ->
    Ebin = filename:join(filename:dirname(script_dir()), "ebin"),
    case code:add_patha(Ebin) of
	true -> ok;
	{error,bad_directory} ->
	    case code:which(varp) of
		non_existing ->
		    io:format(standard_error,
			      "varp: cannot find ~s\n", [Ebin]),
		    halt(1);
		_ -> ok
	    end
    end.

%% the directory this script lives in, with symlinks resolved
script_dir() ->
    filename:dirname(resolve(filename:absname(escript:script_name()), 16)).

resolve(Path, 0) -> Path;
resolve(Path, N) ->
    case file:read_link(Path) of
	{ok,Target} ->
	    resolve(filename:absname(Target, filename:dirname(Path)), N-1);
	{error,_} ->
	    Path
    end.
