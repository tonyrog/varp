%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2018, Tony Rogvall
%%% @doc
%%%    reduce clauses using RAT
%%% @end
%%% Created : 25 Apr 2018 by Tony Rogvall <tony@rogvall.se>

-module(varp_rat).

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
	description => "Number of literal rat clauses to delete."
      },
     #{ long => "type",
	short => "r",
	key => type,
	spec => {enum,[{"both",both},{"min",min},{"pos",pos},{"neg",neg}]},
	default => min,
	description => "Type of rat clauses to try."
      }].

run(Bs, Param) when is_record(Bs,bs), is_map(Param) ->
    N = varp_formula:number_of_unbound(Bs),
    varp_formula:config(Bs, permanent, 0),
    CMax = varp_formula:info(Bs, permanent),
    Type = maps:get(type, Param),
    case maps:get(size, Param) of
	0 ->
	    {?CONTINUE,[],Bs};
	all ->
	    rat(Bs,N,CMax,Type);
	M ->
	    rat(Bs,min(N,M),CMax,Type)
    end.

rat(Bs,N,CMax,Type) ->
    case varp_formula:first_unbound(Bs) of
	false -> {?CONTINUE,[],Bs};
	{I,X} -> rat(Bs,I,X,N,CMax,Type)
    end.

rat(Bs,_I,_X,0,_CMax,_Type) -> 
    {?CONTINUE,[],Bs};
rat(Bs, I, X,N,CMax,Type) ->
    Bs1 = rat_var(Bs,X,CMax,Type),
    case varp_formula:next_unbound(Bs1,I) of
	false -> {?CONTINUE,[],Bs1};
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
    Ds = clauses(Bs,Is,L,[]),
    %% fixme: add option to emit definition in varp format!
    lists:foreach(
      fun({I,D}) ->
	      Js = get_delta_clauses(Bs,-L,CMax),
	      Cs = clauses(Bs,Js,-L,[]),
	      %% io:format("rat_test l=~w, d=~w, cs=~w\n", [L,D,Cs]),
	      varp_formula:set_level(Bs,1),
	      true = varp_formula:bind(Bs,-L),
	      true = neg_bind_all(Bs,D),
	      case rat_test(Bs,Cs) of
		  true ->
		      varp_formula:undo_level(Bs,1),
		      io:format("remove clause ~w = ~w\n", [I,[L|D]]),
		      varp_formula:set_level(Bs,0), %% must be done at level=0!
		      varp_formula:del_clause(Bs, I);
		  false ->
		      varp_formula:undo_level(Bs,1),
		      ok
	      end
      end, Ds),
    Bs.

rat_test(Bs, [{_Cix,C}|Cs]) ->
    Level = 2,
    varp_formula:set_level(Bs,Level),
    case neg_bind_all(Bs,C) of
	false ->
	    varp_formula:undo_level(Bs,Level),
	    false;
	true ->
	    case varp_formula:eval(Bs) of
		false ->
		    varp_formula:undo_level(Bs,Level),
		    false;
		true ->
		    varp_formula:undo_level(Bs,Level),
		    rat_test(Bs, Cs)
	    end
    end;
rat_test(_Bs, []) ->
    true.

%% bind -Xi
neg_bind_all(Bs, [Xi|Xs]) ->
    case varp_formula:bind(Bs,-Xi) of
	false -> false;
	true -> neg_bind_all(Bs,Xs)
    end;
neg_bind_all(_Bs, []) ->
    true.

%% Extract clauses and remove the literal L while doing it 
clauses(Bs,[I|Cs],L,Acc) ->
    case get_clause(Bs,I, L) of
	[] ->
	    clauses(Bs,Cs,L,Acc);
	Clause ->
	    clauses(Bs,Cs,L,[{I,Clause}|Acc])
    end;
clauses(_Bs, [], _L, Acc) ->
    Acc.

get_clause(Bs, I, Skip) ->
    varc:get_clause(Bs#bs.vp, I, Skip).

%% only extract clauses in Delta (fixme remove dead clauses)
get_delta_clauses(Bs, L, CMax) ->
    CLs = varp_formula:get_clauses(Bs,L,literal),
    [I || I <- CLs, I < CMax].
