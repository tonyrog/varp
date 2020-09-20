%% Netcat file data
-module(varp_nc).

-export([open/1]).
-export([read_line/1]).
-export([close/1]).
-export([cat/1]).

cat(Filename) ->
    case filename:extension(Filename) of
	".bz2" -> "bzcat";
	".xz" -> "xzcat";
	".z" -> "zcat";
	".gz" -> "zcat";
	_ -> undefined
    end.
    
open(Cmd) ->
    case gen_tcp:listen(0, [binary,{packet,line},{active,false}]) of
	{ok,L} ->
	    {ok,P} = inet:port(L),
	    spawn(
	      fun() ->
		      Nc = ["nc -N 127.0.0.1 ",integer_to_list(P)],
		      CmdNc = [Cmd," | ", Nc],
		      io:format("command: [~s]\n", [CmdNc]),
		      Port = open_port({spawn,CmdNc},[exit_status]),
		      receive
			  {Port, {exit_status,_Status}} ->
			      io:format("port terminated ~w\n",[_Status]),
			      ok
		      end
	      end),
	    case gen_tcp:accept(L) of
		{ok,S} ->
		    gen_tcp:close(L),
		    {ok,S};
		Error ->
		    gen_tcp:close(L),
		    Error
	    end;
	Error ->
	    Error
    end.

read_line(S) ->   
    case gen_tcp:recv(S, 0) of
	{error,closed} -> eof;
	{error,enotconn} -> eof;
	R -> R
    end.

close(S) ->
    gen_tcp:close(S).

    
