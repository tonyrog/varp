%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2019, Tony Rogvall
%%% @doc
%%%    successor cnf
%%% @end
%%% Created : 25 Aug 2019 by Tony Rogvall <tony@rogvall.se>

-module(varp_succ).

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
       }].

run(Bs, Opts) ->
    succ(Bs, Opts).

%% dump clauses
succ(Bs, Opts) ->
    Type = maps:get(type, Opts),
    case maps:get(file, Opts) of
	"" ->
	    succ(user, Type, Bs);
	File ->
	    case file:open(File, [write]) of
		{ok,Fd} ->
		    try succ(Fd, Type, Bs) of
			R -> R
		    after
			file:close(Fd)
		    end;
		Error={error,Reason} ->
		    io:format("succ error: unable to open file ~s (~w)\n",
			      [File, Reason]),
		    Error
	    end
    end.

succ(Fd, Type, Bs) ->
    N = count_number_of_clauses(Bs),
    M = varp_formula:get_info(Bs, number_of_unbound_variables),
    case Type of
	cnf ->
	    io:format(Fd, "p cnf ~w ~w\n", [M, N]);
	snf ->
	    io:format(Fd, "p snf ~w ~w\n", [M, N])
    end,
    I = varc:clause_first(Bs#bs.vp),
    succ_(Fd, Type, I, Bs).

succ_(_Fd,_Type,false,Bs) ->
    Bs;
succ_(Fd,Type,I,Bs) ->
    case varc:get_clause(Bs#bs.vp, I, undefined, false) of
	true ->
	    succ_(Fd,Type,varc:clause_next(Bs#bs.vp,I),Bs);
	[] ->
	    succ_(Fd,Type,varc:clause_next(Bs#bs.vp,I),Bs);
	CL ->
	    Fmt = case Type of
		      cnf -> format_cnf_clause(Bs,CL); 
		      snf -> format_snf_clause(Bs,CL)
		  end,
	    io:put_chars(Fd,[Fmt,"\n"]),
	    succ_(Fd,Type,varc:clause_next(Bs#bs.vp,I),Bs)
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
