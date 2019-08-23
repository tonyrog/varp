%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2019, Tony Rogvall
%%% @doc
%%%    cnf dump clause set plugin
%%% @end
%%% Created : 18 Jun 2019 by Tony Rogvall <tony@rogvall.se>

-module(varp_cnf).

-export([run/2]).
-export([options/0]).

-include("varp.hrl").

options() ->
    [ #{ long => "type",
	 short => "t",
	 key   => type,
	 spec => {enum,[{"cnf",cnf}, {"snf", snf}]},
	 default => cnf,
	 description => "Dump cnf or symbolc snf format."
       },
      #{ long => "file",
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
    Raw = maps:get(raw, Opts),
    Type = maps:get(type, Opts),
    case maps:get(file, Opts) of
	"" ->
	    dump(user, Type, Raw, Bs);
	File ->
	    case file:open(File, [write]) of
		{ok,Fd} ->
		    try dump(Fd, Type, Raw, Bs) of
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

dump(Fd, Type, Raw, Bs) ->
    N = if Raw ->
		varp_formula:get_info(Bs, number_of_clauses);
	   true ->
		count_number_of_clauses(Bs)
	end,	   
    M = if Raw ->
		varp_formula:get_info(Bs, number_of_variables);
	   true ->
		varp_formula:get_info(Bs, number_of_unbound_variables)
	end,
    case Type of
	cnf ->
	    io:format(Fd, "p cnf ~w ~w\n", [M, N]);
	snf ->
	    io:format(Fd, "p snf ~w ~w\n", [M, N])
    end,
    I = varc:clause_first(Bs#bs.vp),
    dump_(Fd, Type, Raw, I, Bs).

dump_(_Fd,_Type,_Raw,false,Bs) ->
    Bs;
dump_(Fd,Type,Raw,I,Bs) ->
    case varc:get_clause(Bs#bs.vp, I, undefined, Raw) of
	true ->
	    dump_(Fd,Type,Raw,varc:clause_next(Bs#bs.vp,I),Bs);
	[] ->
	    dump_(Fd,Type,Raw,varc:clause_next(Bs#bs.vp,I),Bs);
	CL ->
	    Fmt = case Type of
		      cnf -> format_cnf_clause(Bs,CL); 
		      snf -> format_snf_clause(Bs,CL)
		  end,
	    io:put_chars(Fd,[Fmt,"\n"]),
	    dump_(Fd,Type,Raw,varc:clause_next(Bs#bs.vp,I),Bs)
    end.

format_cnf_clause(_Bs,CL) ->
    [lists:join(" ", [integer_to_list(L)||L<-CL]), " 0"].

format_snf_clause(Bs,CL) ->
    [lists:join(" ", [varp_formula:format_lit(Bs,L,false)||L<-CL]), "."].


%% count number of active clauses
count_number_of_clauses(Bs) ->
    count_number_of_clauses_(Bs, varc:clause_first(Bs#bs.vp), 0).

count_number_of_clauses_(_Bs, false, N) ->
    N;
count_number_of_clauses_(Bs, I, N) ->
    case varc:get_clause(Bs#bs.vp, I, undefined, false) of
	true -> 
	    count_number_of_clauses_(Bs, varc:clause_next(Bs#bs.vp,I),N);
	[] ->
	    count_number_of_clauses_(Bs, varc:clause_next(Bs#bs.vp,I),N);
	_CL ->    
	    count_number_of_clauses_(Bs, varc:clause_next(Bs#bs.vp,I),N+1)
    end.
