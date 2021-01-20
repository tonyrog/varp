%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2019, Tony Rogvall
%%% @doc
%%%    Conflict analysis
%%% @end
%%% Created :  3 Dec 2019 by Tony Rogvall <tony@rogvall.se>

-module(varp_conflict).
-export([analyze/4]).

%% -define(DEBUG, true).
-include("varp.hrl").

analyze(Vp, Level, Bump, Minimize) ->
    N = varp_nif:info(Vp, number_of_conflicting_clauses),
    analyze_(Vp, Level, Bump, Minimize, 0, N).

analyze_(_Vp, _Level, _Bump, _Minimize, N, N) ->
    [];
analyze_(Vp, Level, Bump, Minimize, I, N) ->
    case varp_nif:conflict(Vp, Level, Bump, I) of
	undefined ->  %% duplicate
	    analyze_(Vp, Level, Bump, Minimize, I+1, N);
	Cix when is_integer(Cix) ->
	    Len0 = varp_nif:clause_info(Vp, Cix, length),
	    case Minimize of
		none ->
		    [{Len0,0,Cix}|
		     analyze_(Vp, Level, Bump, Minimize, I+1, N)];
		Type -> %% local/recursive
		    case varp_nif:minimize(Vp, Cix, Type, false) of
			undefined -> %% duplicate
			    analyze_(Vp, Level, Bump, Minimize, I+1, N);
			{UIP,Len} -> %% uip removed?
			    io:format("UIP ~w and ~w literals where removed\n",
				      [UIP, Len0-Len]),
			    io:format("Clause' = ~w\n", [varp:get_clause(Vp, Cix)]),
			    [{Len,Len0-Len,Cix}|
			     analyze_(Vp, Level, Bump, Minimize, I+1, N)];
			Len ->
			    [{Len,Len0-Len,Cix}|
			     analyze_(Vp, Level, Bump, Minimize, I+1, N)]
		    end
	    end
    end.
