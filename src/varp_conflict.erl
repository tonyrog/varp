%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2019, Tony Rogvall
%%% @doc
%%%    Conflict analysis
%%% @end
%%% Created :  3 Dec 2019 by Tony Rogvall <tony@rogvall.se>

-module(varp_conflict).
-export([analyze/3]).
-export([analyze_alpha/3]).

-export([analyze/4]).

-include("varp.hrl").

analyze_alpha(Bs, Level, Bump) ->
    N = varc:info(Bs#bs.vp, number_of_conflicting_clauses),
    [ varc:conflict(Bs#bs.vp, Level, Bump, I) ||
	I <- lists:seq(0, N-1) ].

analyze(Bs, Level, Bump) ->
    Trail = get_bindings(Bs#bs.vp, Level),
    ?dbg("trail: ~s\n", [varp_formula:format_literals(Bs,Trail)]),
    N = varc:info(Bs#bs.vp, number_of_conflicting_clauses),
    analyze_(Bs#bs.vp, Trail, Level, Bump, 0, N).

analyze_(_V,_Trail,_Level,_Bump,N,N) ->
    [];
analyze_(V,Trail,Level,Bump,I,N) ->
    Cix = varc:conflicting_clause(V,I),
    [ analyze_clause_(V,Trail,Cix,Level,Bump) |
      analyze_(V,Trail,Level,Bump,I+1,N) ].

analyze(V, Level, Bump, I) ->
    Trail = get_bindings(V,Level),
    Cix = varc:conflicting_clause(V, I),
    analyze_clause_(V,Trail,Cix,Level,Bump).

analyze_clause_(V,Trail,Cix,Level,Bump) ->
    Conflicting = get_clause(V,Cix,undefined),
    conflict_reason(V,Conflicting,Trail,Level,Bump,#{},0,[]).

conflict_reason(V,[Q|Qs],Trail,Level,Bump,Seen,C,CL) ->
    case is_seen(Q, Seen) of
	true ->
	    conflict_reason(V,Qs,Trail,Level,Bump,Seen,C,CL);
	false ->
	    QLevel = varc:implication_level(V,Q),
	    if QLevel > ?TOP_LEVEL ->
		    varc:bump(V, Q, Bump),
		    Seen1 = set_seen(Q, Seen),
		    if QLevel >= Level ->
			    conflict_reason(V,Qs,Trail,Level,Bump,Seen1,C+1,CL);
		       true ->
			    conflict_reason(V,Qs,Trail,Level,Bump,Seen1,C,[Q|CL])
		    end;
	       true ->
		    conflict_reason(V,Qs,Trail,Level,Bump,Seen,C,CL)
	    end
    end;
conflict_reason(V,[],Trail,Level,Bump,Seen,C,CL) ->
    Trail1= [P|_] = lists:dropwhile(fun(Pi) -> not is_seen(Pi,Seen) end, Trail),
    if C =< 1 ->
	    [-P|CL];
       true ->
	    true = is_seen(P, Seen),
	    Seen1 = clr_seen(P, Seen),
	    Reason = reason(V,P),
	    conflict_reason(V,Reason,Trail1,Level,Bump,Seen1,C-1,CL)
    end.
		    
get_clause(V, ClauseIndex, SkipLiteral) ->
    varc:get_clause(V, ClauseIndex, SkipLiteral).

reason(V,L) ->
    case varc:implication_clause(V,L) of
	-1 -> [];
	Cix ->
	    varc:use_clause(V, Cix),
	    get_clause(V,Cix,L)
    end.

get_bindings(V,Level) ->
    %% fixme: get_bindings(Vp, Level, Reversed=true)
    Bindings = varc:get_bindings(V, Level),
    lists:reverse(Bindings).

%% maps implementing set
set_seen(Q, VarSet) ->
    VarSet#{ abs(Q) => true }.

clr_seen(Q, VarSet) ->
    maps:remove(abs(Q), VarSet).

is_seen(Q, VarSet) ->
    case maps:find(abs(Q), VarSet) of
	error -> false;
	{ok,true} -> true
    end.
