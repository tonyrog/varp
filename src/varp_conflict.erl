%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2019, Tony Rogvall
%%% @doc
%%%    Conflict analysis
%%% @end
%%% Created :  3 Dec 2019 by Tony Rogvall <tony@rogvall.se>

-module(varp_conflict).
-export([analyze/3]).

%% -define(DEBUG, true).
-include("varp.hrl").

analyze(Vp, Bump, Minimize) ->
    N = varp_nif:info(Vp, number_of_conflicting_clauses),
    analyze_(Vp, Bump, Minimize, 0, N).

analyze_(_Vp, _Bump, _Minimize, N, N) ->
    [];
analyze_(Vp, Bump, Minimize, I, N) ->
    case varp_nif:conflict(Vp, Bump, I) of
	undefined ->  %% duplicate
	    analyze_(Vp, Bump, Minimize, I+1, N);
	Cix when is_integer(Cix) ->
	    Len0 = varp_nif:clause_info(Vp, Cix, length),
	    case Minimize of
		none ->
		    [{Len0,0,Cix}|
		     analyze_(Vp, Bump, Minimize, I+1, N)];
		Type -> %% local/recursive
		    io:format("minimize ~s Clause[~w]: ~w\n", 
			      [Type, Len0, varp:get_clause(Vp, Cix)]),
		    case varp_nif:minimize(Vp, Cix, Type) of
			undefined -> %% duplicate
			    analyze_(Vp, Bump, Minimize, I+1, N);
			Len ->
			    io:format("Clause'[~w]: save=~w, ~w\n",
				      [Len,Len0-Len,varp:get_clause(Vp, Cix)]),
			    [{Len,Len0-Len,Cix}|
			     analyze_(Vp, Bump, Minimize, I+1, N)]
		    end
	    end
    end.
