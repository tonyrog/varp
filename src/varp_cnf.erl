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
	 description => "Write cnf or symbolic snf format."
       },
      #{ long => "file",
	 short => "f",
	 key  => file,
	 spec => string,
	 default => "",
	 description => "Filename of file to write clauses to."
       },
      #{ long => "raw",
	 short => "r",
	 key   => raw,
	 spec => {enum,[?BOOL,{"debug",debug}]},
	 default => false,
	 description => "output 'raw' clauses."
       }
    ].

run(Bs, Opts) ->
    cnf(Bs, Opts).

%% output cnf clauses
cnf(Bs, Opts) ->
    Raw = maps:get(raw, Opts),
    Type = maps:get(type, Opts),
    case maps:get(file, Opts) of
	"" ->
	    cnf(user, Type, Raw, Bs);
	File ->
	    case file:open(File, [write]) of
		{ok,Fd} ->
		    try cnf(Fd, Type, Raw, Bs) of
			R -> R
		    after
			file:close(Fd)
		    end;
		Error={error,Reason} ->
		    io:format("cnf error: unable to open file ~s (~w)\n",
			      [File, Reason]),
		    Error
	    end
    end.

cnf(Fd, Type, Raw, Bs) ->
    N = if Raw =:= false -> count_number_of_clauses(Bs);
	   true -> varp_formula:get_info(Bs, number_of_clauses)
	end,	   
    M = if Raw =:= false -> 
		varp_formula:get_info(Bs, number_of_unbound_variables);
	   true ->
		varp_formula:get_info(Bs, number_of_variables)
	end,
    case Type of
	cnf ->
	    io:format(Fd, "p cnf ~w ~w\n", [M, N]);
	snf ->
	    io:format(Fd, "p snf ~w ~w\n", [M, N])
    end,
    I = varc:clause_first(Bs#bs.vp),
    cnf_(Fd, Type, Raw, I, Bs).

cnf_(_Fd,_Type,_Raw,false,Bs) ->
    Bs;
cnf_(Fd,Type,Raw,I,Bs) ->
    case varc:get_clause(Bs#bs.vp, I, undefined, Raw=/=false) of
	true ->
	    cnf_(Fd,Type,Raw,varc:clause_next(Bs#bs.vp,I),Bs);
	[] ->
	    cnf_(Fd,Type,Raw,varc:clause_next(Bs#bs.vp,I),Bs);
	CL ->
	    Fmt = case Type of
		      cnf -> format_cnf_clause(Bs,CL,Raw); 
		      snf -> format_snf_clause(Bs,CL,Raw)
		  end,
	    io:put_chars(Fd,[Fmt,"\n"]),
	    cnf_(Fd,Type,Raw,varc:clause_next(Bs#bs.vp,I),Bs)
    end.

format_cnf_clause(_Bs,CL,_) ->
    [lists:join(" ", [integer_to_list(L)||L<-CL]), " 0"].

format_snf_clause(Bs,CL,debug) ->
    [lists:join(" ", [varp_formula:format_lit(Bs,L,true)||L<-CL]), "."];
format_snf_clause(Bs,CL,_) ->
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
