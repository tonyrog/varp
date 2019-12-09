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
    Type = maps:get(type, Param),
    case maps:get(size, Param) of
	0 ->
	    {?CONTINUE,[],Bs};
	all ->
	    rat(Bs,N,Type);
	M ->
	    rat(Bs,min(N,M),Type)
    end.

rat(Bs,N,Type) ->
    case varp_formula:first_unbound(Bs) of
	false -> {?CONTINUE,[],Bs};
	{I,X} -> rat(Bs,I,X,N,Type)
    end.

rat(Bs,_I,_X,0,_Type) -> 
    {?CONTINUE,[],Bs};
rat(Bs, I, X,N,Type) ->
    Bs1 = rat_var(Bs,X,Type),
    case varp_formula:next_unbound(Bs1,I) of
	false -> {?CONTINUE,[],Bs1};
	{I1,X1} -> rat(Bs1,I1,X1,N-1,Type)
    end.

rat_var(Bs,V,Type) ->
    ?dbg("rat=~s,cmax=~w,type=~w\n",
	 [varp_formula:format_lit(Bs,V),CMax,Type]),
    case Type of
	pos ->
	    Is = get_delta_clauses(Bs,V),
	    rat_lit(Bs,V,Is);
	neg ->
	    Is = get_delta_clauses(Bs,-V),
	    rat_lit(Bs,-V,Is);
	both ->
	    Is1 = get_delta_clauses(Bs,V),
	    Is2 = get_delta_clauses(Bs,-V),
	    Bs1 = rat_lit(Bs,V,Is1),
	    rat_lit(Bs1,-V,Is2);
	min ->
	    Is1 = get_delta_clauses(Bs,V),
	    Is2 = get_delta_clauses(Bs,-V),
	    Is1L = length(Is1),
	    Is2L = length(Is2),
	    if Is2L =:= 0 ->
		    rat_lit(Bs,V,Is1);
	       Is1L =:= 0 ->
		    rat_lit(Bs,-V,Is2);
	       Is1L < Is2L ->
		    rat_lit(Bs,V,Is1);
	       true ->
		    rat_lit(Bs,-V,Is2)
	    end
    end.

%%
%% Clause = L v D can be removed from Delta
%% if for each ~L v C in Delta
%% ~L,~D,~C is inconsistent
%%

rat_lit(Bs,L,Is) ->
    Ds = clauses(Bs,Is,L,[]),
    %% fixme: add option to emit definition in varp format!
    lists:foreach(
      fun({I,D}) ->
	      Js = get_delta_clauses(Bs,-L),
	      Cs = clauses(Bs,Js,-L,[]),
	      %% io:format("rat_test l=~w, d=~w, cs=~w\n", [L,D,Cs]),
	      varc:set_level(Bs#bs.vp, 1),
	      true = varc:bind(Bs#bs.vp,-L),
	      true = neg_bind_all(Bs,D),
	      case rat_test(Bs,Cs) of
		  true ->
		      varc:undo_level(Bs#bs.vp,1),
		      io:format("remove clause ~w = ~w\n", [I,[L|D]]),
		      varc:set_level(Bs#bs.vp,0), %% must be done at level=0!
		      varp_formula:del_clause(Bs, I);
		  false ->
		      varc:undo_level(Bs#bs.vp,1),
		      ok
	      end
      end, Ds),
    Bs.

rat_test(Bs, [{_Cix,C}|Cs]) ->
    Level = 2,
    varc:set_level(Bs#bs.vp,Level),
    case neg_bind_all(Bs,C) of
	false ->
	    varc:undo_level(Bs#bs.vp,Level),
	    false;
	true ->
	    case varc:bcp(Bs#bs.vp) of
		false ->
		    varc:undo_level(Bs#bs.vp,Level),
		    false;
		true ->
		    varc:undo_level(Bs#bs.vp,Level),
		    rat_test(Bs, Cs)
	    end
    end;
rat_test(_Bs, []) ->
    true.

%% bind -Xi
neg_bind_all(Bs, [Xi|Xs]) ->
    case varc:bind(Bs#bs.vp,-Xi) of
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
get_delta_clauses(Bs, L) ->
    get_delta_clauses(Bs, L, varc:clauseset_size(Bs#bs.vp, 0)).

get_delta_clauses(Bs, L, CMax) ->
    CLs = varc:get_clauses(Bs#bs.vp,L,literal),
    [I || I <- CLs, I < CMax].
