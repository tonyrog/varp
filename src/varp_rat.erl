%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2018, Tony Rogvall
%%% @doc
%%%    reduce clauses using RAT
%%% @end
%%% Created : 25 Apr 2018 by Tony Rogvall <tony@rogvall.se>

-module(varp_rat).

-export([run/1]).
-compile(export_all).

-include("varp.hrl").

%% -define(DEBUG, true).

-define(dbg0(F,As), ok).
-ifdef(DEBUG).
-define(dbg(F,A), io:format((F),(A))).
-define(dcall(Fun), Fun()).
-else.
-define(dbg(F,A), ok).
-define(dcall(Fun), ok).
-endif.


run(Bs) ->
    N = varp_formula:number_of_unbound(Bs),
    varp_formula:config(Bs, permanent, 0),
    CMax = varp_formula:get_info(Bs, permanent),
    Type = varp_formula:getopt(Bs, rat_type),
    case varp_formula:getopt(Bs, rat) of
	0 ->
	    Bs;
	all ->
	    rat(Bs,N,CMax,Type);
	M ->
	    rat(Bs,min(N,M),CMax,Type)
    end.

rat(Bs,N,CMax,Type) ->
    case varp_formula:first_unbound(Bs) of
	false -> Bs;
	{I,X} -> rat(Bs,I,X,N,CMax,Type)
    end.

rat(Bs,_I,_X,0,_CMax,_Type) -> Bs;
rat(Bs, I, X,N,CMax,Type) ->
    Bs1 = rat_var(Bs,X,CMax,Type),
    case varp_formula:next_unbound(Bs1,I) of
	false -> Bs1;
	{I1,X1} -> rat(Bs1,I1,X1,N-1,CMax,Type)
    end.

rat_var(Bs,V,CMax,Type) ->
    ?dbg("rat=~s,cmax=~w,type=~w\n",
	 [varp_formula:format_lit(Bs,V),CMax,Type]),
    case Type of
	pos ->
	    Is = get_delta_clauses(Bs,V,CMax),
	    rat_lit(Bs,V,Is,CMax);
	neg ->
	    Is = get_delta_clauses(Bs,-V,CMax),
	    rat_lit(Bs,-V,Is,CMax);
	both ->
	    Is1 = get_delta_clauses(Bs,V,CMax),
	    Is2 = get_delta_clauses(Bs,-V,CMax),
	    Bs1 = rat_lit(Bs,V,Is1,CMax),
	    rat_lit(Bs1,-V,Is2,CMax);
	min ->
	    Is1 = get_delta_clauses(Bs,V,CMax),
	    Is2 = get_delta_clauses(Bs,-V,CMax),
	    Is1L = length(Is1),
	    Is2L = length(Is2),
	    if Is2L =:= 0 ->
		    rat_lit(Bs,V,Is1,CMax);
	       Is1L =:= 0 ->
		    rat_lit(Bs,-V,Is2,CMax);
	       Is1L < Is2L ->
		    rat_lit(Bs,V,Is1,CMax);
	       true ->
		    rat_lit(Bs,-V,Is2,CMax)
	    end
    end.

%%
%% Clause = L v D can be removed from Delta
%% if for each ~L v C in Delta
%% ~L,~D,~C is inconsistent
%%

rat_lit(Bs,L,Is,CMax) ->
    {Ds,Bs1} = clauses(Bs,Is,L,[]),
    %% fixme: add option to emit definition in varp format!
    %% emit_def(Bs, L, Ds),
    lists:foreach(
      fun({I,D}) ->
	      Js = get_delta_clauses(Bs,-L,CMax),
	      {Cs,Bs2} = clauses(Bs1,Js,-L,[]),
	      case rat_test(Bs2,Cs,L,D) of
		  true ->
		      io:format("remove clause ~w\n", [I]),
		      varp:del_clause(Bs2#bs.vp, I);
		  false ->
		      ok
	      end
      end, Ds).

rat_test(Bs, [C|Cs], L, D) ->
    Level = 1,
    varp_formula:set_level(Bs,1),
    true = varp_formula:equal(Bs,L,?FALSE),
    lists:foreach(fun(Ci) ->
			  true = varp_formula:equal(Bs,Ci,?FALSE)
		  end, C),
    lists:foreach(fun(Di) ->
			  true = varp_formula:equal(Bs,Di,?FALSE)
		  end, D),
    case varp_formula:eval(Bs) of
	false ->
	    varp_formula:undo_level(Bs,Level),
	    false;
	true ->
	    varp_formula:undo_level(Bs,Level),
	    rat_test(Bs, Cs, L, D)
    end;
rat_test(_Bs, [], _L, _D) ->
    true.


%% Extract clauses and remove the literal L while doing it 
%% (fix me add option to get_clause to remove one literal while extracting)
clauses(Bs,[I|Cs],L,Acc) ->
    Clause = lists:delete(L, get_clause(Bs,I)),
    clauses(Bs,Cs,L,[{I,Clause}|Acc]);
clauses(Bs, [], _L, Acc) ->
    {Acc,Bs}.

get_clause(Bs, I) ->
    varc:get_clause(Bs#bs.vp, I).

%% only extract clauses in Delta (fixme remove dead clauses)
get_delta_clauses(Bs, L, CMax) ->
    CLs = varp_formula:get_clauses(Bs,L,literal),
    [I || I <- CLs, I < CMax].
