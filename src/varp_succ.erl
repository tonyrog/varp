%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2019, Tony Rogvall
%%% @doc
%%%    successor cnf
%%% @end
%%% Created : 25 Aug 2019 by Tony Rogvall <tony@rogvall.se>

-module(varp_succ).

-export([run/2]).
-export([options/0]).

-compile(export_all).

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
    VarMap = get_var_map(Bs),

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
	    Bn = clause_bn(Bs,CL),
	    Gn = group_bn(Bn),
	    io:put_chars(Fd,[lists:reverse(Bn), 
			     " //", 
			     io_lib:format("~w",[lists:reverse(Gn)]), 
			     "\n"]),
	    case succ_gn(Gn) of
		false ->
		    ok;
		Succ ->
		    lists:foreach(
		      fun(Gi) ->
			      Bi = ungroup_bn(Gi),
			      io:format("~s\n", [lists:reverse(Bi)])
		      end, Succ)
	    end,

%%	    Fmt = case Type of
%%		      cnf -> format_succ_cnf_clause(Bs,Bn); 
%%		      snf -> format_succ_snf_clause(Bs,Bn)
%%		  end,
%%	    io:put_chars(Fd,[Fmt,"\n"]),
	    succ_(Fd,Type,varc:clause_next(Bs#bs.vp,I),Bs)
    end.

%% generate succesor covering from grouped "binary" number
succ_gn([{$*,K},{$0,N}|Bn]) ->
    %% bi=*, 1 <= i <= k-1, bk=0
    if N > 1 -> [ [{$0,K},{$1,1},{$*,N-1}|Bn] ];
       true ->  [ [{$0,K},{$1,1}|Bn] ]
    end;
succ_gn(Bn) ->
    succ_gn_(Bn).

succ_gn_([{$1,K},{$*,N}|Bn]) ->
    case succ_gn_(Bn) of
	false ->
	    [ [{$0,K},{$*,N}|Bn] ];
	BLs ->
	    [ [{$0,K},{$*,N}|Bn] | [ [{$0,K+N} | Bn1 ] || Bn1 <- BLs ] ]
    end;
succ_gn_([{$1,K},{$0,N}|Bn]) ->
    [ [{$0,K+N}|Bn] ];
succ_gn_([{$*,K}|Bn]) ->
    case succ_gn_(Bn) of
	false ->
	    [ [{$*,K}] ];
	BLs ->
	    [ [{$0,K}|Bn] | [ [{$0,K} | Bn1 ] || Bn1 <- BLs ] ]
    end;
succ_gn_([{$0,K}|Bn]) ->
    if K =:= 1 ->
	    [ [{$1,1}|Bn] ];
       true ->
	    [ [{$0,K-1},{$1,1}|Bn] ]
    end;
succ_gn_([]) ->
    [];
succ_gn_([{$1,_K}]) ->
    false.


group_bn([B|Bn]) ->
    group_bn_(Bn,B,1).

group_bn_([B|Bn],B,N) ->
    group_bn_(Bn,B,N+1);
group_bn_([C|Bn],B,N) ->
    [{B,N}|group_bn_(Bn,C,1)];
group_bn_([],B,N) ->
    [{B,N}].

%% ungroup and reverse a grouped Binary number
ungroup_bn([{C,N}|Gn]) ->
    cat(C,N, ungroup_bn(Gn));
ungroup_bn([]) ->
    [].

cat(_C,0,L) -> L;
cat(C,I,L) -> [C|cat(C,I-1,L)].


%% return b1b2..bn!
clause_bn(Bs, CL) ->
    clause_bn_(Bs, varp_formula:first_unbound(Bs), CL, []).

clause_bn_(_Bs, false, _CL, Acc) -> 
    lists:reverse(Acc);
clause_bn_(Bs, {I,Xi}, CL, Acc) ->
    Bi = case lists:member(Xi, CL) of
	     true -> if Xi < 0 -> $1;
			Xi > 0 -> $0
		     end;
	     false ->
		 case lists:member(-Xi, CL) of
		     true ->
			 if Xi > 0 -> $1;
			    Xi < 0 -> $0
			 end;
		     false ->
			 $*
		 end
	 end,
    clause_bn_(Bs, varp_formula:next_unbound(Bs, I), CL, [Bi | Acc]).

%% get unbound mapped to "bit number"
get_var_map(Bs) ->
    get_var_map_(Bs, #{}).

get_var_map_(Bs, Map) ->
    get_var_map_(Bs, varp_formula:first_unbound(Bs), Map, 1).

get_var_map_(_Bs, false, Map, _N) ->
    Map;
get_var_map_(Bs, {I,Xi}, Map, J) ->
    get_var_map_(Bs,varp_formula:next_unbound(Bs,I),maps:put(Xi,J,Map), J+1).

format_succ_cnf_clause(_Bs,CL) ->
    [lists:join(" ", [integer_to_list(L)||L<-CL]), " 0"].

format_succ_snf_clause(Bs,CL) ->
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
