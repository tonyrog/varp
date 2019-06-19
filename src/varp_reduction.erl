%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2018, Tony Rogvall
%%% @doc
%%%    Given a SNF/CNF generate 
%%%    a model reduction defintion 
%%% @end
%%% Created : 25 Apr 2018 by Tony Rogvall <tony@rogvall.se>

-module(varp_reduction).

-export([run/2]).
-export([options/0]).

-compile(export_all).

%% -define(DEBUG, true).
-include("varp.hrl").

options() ->
    [
     #{ long => "size",
	short => "n",
	key => size,
	spec => {union,[unsigned,{enum,[{"all",all}]}]},
	default => 0,
	description => "Number of literal reduction clauses to add."
      },
     #{ long => "reduction-type",
	short => "R",
	key => reduction_type,
	spec => {enum,[{"both",both},{"min",min},{"pos",pos},{"neg",neg}]},
	default => min,
	description => "Type of reductions clauses."
      }].


run(Bs, _Param) ->
    N = varp_formula:number_of_unbound(Bs),
    varp_formula:config(Bs, permanent, 0),
    CMax = varp_formula:get_info(Bs, permanent),
    Type = varp_formula:getopt(Bs, reduction_type),
    case varp_formula:getopt(Bs, reduction) of
	0 ->
	    Bs;
	all ->
	    red(Bs,N,CMax,Type);
	M ->
	    red(Bs,min(N,M),CMax,Type)
    end.

red(Bs,N,CMax,Type) ->
    case varp_formula:first_unbound(Bs) of
	false -> Bs;
	{I,X} -> red(Bs,I,X,N,CMax,Type)
    end.

red(Bs,_I,_X,0,_CMax,_Type) -> Bs;
red(Bs, I, X,N,CMax,Type) ->
    Bs1 = add_var(Bs,X,CMax,Type),
    case varp_formula:next_unbound(Bs1,I) of
	false -> Bs1;
	{I1,X1} -> red(Bs1,I1,X1,N-1,CMax,Type)
    end.

add_var(Bs,V,CMax,Type) ->
    ?dbg("reduction=~s,cmax=~w,type=~w\n",
	 [varp_formula:format_lit(Bs,V),CMax,Type]),
    case Type of
	pos ->
	    Is = get_delta_clauses(Bs,V,CMax),
	    add_lit(Bs,V,Is);
	neg ->
	    Is = get_delta_clauses(Bs,-V,CMax),
	    add_lit(Bs,-V,Is);
	both ->
	    Is1 = get_delta_clauses(Bs,V,CMax),
	    Is2 = get_delta_clauses(Bs,-V,CMax),
	    Bs1 = add_lit(Bs,V,Is1),
	    add_lit(Bs1,-V,Is2);
	min ->
	    Is1 = get_delta_clauses(Bs,V,CMax),
	    Is2 = get_delta_clauses(Bs,-V,CMax),
	    Is1L = length(Is1),
	    Is2L = length(Is2),
	    if Is2L =:= 0 ->
		    add_lit(Bs,V,Is1);
	       Is1L =:= 0 ->
		    add_lit(Bs,-V,Is2);
	       Is1L < Is2L ->
		    add_lit(Bs,V,Is1);
	       true ->
		    add_lit(Bs,-V,Is2)
	    end
    end.

%% extract clauses containing literal l in delta:
%% {l, D1}, {l, D2}, ... {l, Dn} where Di = {di1,..,din}
%% define:   yi = !(Di)  = (!di1 & !di2 .. !dim)
%% encoded (clauses):
%%   {yi,di1,di2,...dim}
%%   {!yi,!di1}
%%   ..
%%   {!yi,!dim}
%% and the clause:
%%   {!l,y1,...yn}
%%

add_lit(Bs,L,Is) ->
    {Ds,Bs1} = clauses(Bs,Is,L,[]),
    %% fixme: add option to emit definition in varp format!
    %% emit_def(Bs, L, Ds),
    lists:foreach(
      fun({Yi,Di}) ->
	      or_clause(Bs1,[Yi|Di]),
	      lists:foreach(
		fun(Dij) ->
			or_clause(Bs1,[-Yi,-Dij])
		end, Di),
	      add_multi(Bs,Yi,Di,Ds)
      end, Ds),
    case [Y || {Y,_} <- Ds] of
	[] ->
	    or_clause(Bs1,[-L]);
	Ys ->
	    or_clause(Bs1,[-L|Ys])
    end.

%% check if ~Di has an intersection with Dj in Ds
%% the add clause {-Yi,-Yj}
add_multi(Bs,Yi,Di,Ds) ->
    NDi = [-L || L <- Di],
    lists:foreach(
      fun({Yj,Dj}) ->
	      case intersect(NDi,Dj) of
		  [] -> ok;
		  _ -> 
		      ?dbg("MULTI\n", []),
		      or_clause(Bs, [-Yi,-Yj])
	      end
      end, Ds).

intersect(A,B) ->
    A -- (A -- B).

or_clause(Bs, CL) ->
    %% add option to add the new clauses?
    %% io:put_chars([varp_formula:format_clause(Bs,CL),"\n"]),
    varp_formula:or_clause(Bs, CL).

emit_def(Bs, Yj, Cs) ->
    io:format("~s == ", [varp_formula:format_lit(Bs,Yj)]),
    lists:foreach(
      fun({_Y,[X1]}) ->
	      io:format("{~s}|",[varp_formula:format_lit(Bs,X1)]);
	 ({_Y,[X1|Xs]}) ->
	      io:format("{~s",[varp_formula:format_lit(Bs,X1)]),
	      lists:foreach(
		fun(Xi) ->
			io:format("&~s", [varp_formula:format_lit(Bs,Xi)])
		end, Xs),
	      io:format("}|")
      end, Cs),
    io:format("\n").
    
%% return list on form [{Y,[Xi]}]
clauses(Bs,[I|Cs],L,Acc) ->
    Fs = varc:get_clause_flags(Bs#bs.vp,I),
    case lists:member(dead, Fs) of
	true ->
	    io:format("DEAD\n"),
	    clauses(Bs, Cs, L, Acc);
	false ->
	    Clause = lists:delete(L, get_clause(Bs,I)),
	    Y = varp_formula:add_variable(Bs),
	    clauses(Bs,Cs,L,[{Y,Clause}|Acc])
    end;
clauses(Bs, [], _L, Acc) ->
    {Acc,Bs}.

get_clause(Bs, I) ->
    varc:get_clause(Bs#bs.vp, I).

%% Return clauses in Delta
get_delta_clauses(Bs, L, CMax) ->
    CLs = varp_formula:get_clauses(Bs,L,literal),
    [I || I <- CLs, I < CMax].
