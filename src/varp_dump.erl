%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2019, Tony Rogvall
%%% @doc
%%%    Dump clause set plugin
%%% @end
%%% Created : 18 Jun 2019 by Tony Rogvall <tony@rogvall.se>

-module(varp_dump).

-export([run/2]).
-export([options/0]).

-include("varp.hrl").

options() ->
    [ #{ long => "file",
	 short => "f",
	 key  => file,
	 spec => string,
	 default => "",
	 description => "Filename of file to dumped clauses to."
       },
      #{ long => "raw",
	 short => "r",
	 key   => raw,
	 spec => {enum,[?BOOL]},
	 default => false,
	 description => "Dump 'raw' clauses."
       }
    ].

run(Bs, Opts) ->
    dump(Bs, Opts).

%% dump clauses
dump(Bs, Opts) ->
    N = varp_formula:get_info(Bs, number_of_clauses),
    Raw = maps:get(raw, Opts, false),
    case maps:get(file, Opts, "") of
	"" -> 
	    dump_(user, Raw, 0, N, Bs);
	File ->
	    case file:open(File, [write]) of
		{ok,Fd} ->
		    try dump_(Fd, Raw, 0, N, Bs) of
			R -> R
		    after
			file:close(Fd)
		    end;
		Error={error,Reason} ->
		    io:format("dump error: unable to open file ~s (~w)\n",
			      [File, Reason]),
		    Error
	    end
    end.

dump_(_Fd,_Raw,N,N,Bs) ->
    Bs;
dump_(Fd,Raw,I,N,Bs) ->
    case varc:get_clause(Bs#bs.vp, I, undefined, Raw) of
	[] ->
	    dump_(Fd,Raw,I+1,N,Bs);
	CL ->
	    io:put_chars(Fd,[format_snf_clause(Bs,CL),".\n"]),
	    dump_(Fd,Raw,I+1,N,Bs)
    end.

format_snf_clause(Bs,CL) ->
    lists:join(" ", [varp_formula:format_lit(Bs,L,false)||L<-CL]).
