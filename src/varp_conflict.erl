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

%% -define(DEBUG, true).
-include("varp.hrl").

analyze_alpha(Bs, Level, Bump) ->
    N = varc:info(Bs#bs.vp, number_of_conflicting_clauses),
    [ varc:conflict(Bs#bs.vp, Level, Bump, I) ||
	I <- lists:seq(0, N-1) ].

analyze(Bs, Level, Bump) ->
    Trail = get_trail(Bs#bs.vp, Level),
    N = varc:info(Bs#bs.vp, number_of_conflicting_clauses),
    [ begin
	  analyze(Bs#bs.vp, Trail, I, Level, Bump)
      end || I <- lists:seq(0, N-1)].

analyze(V, Level, Bump, I) ->
    analyze(V, get_trail(V, Level), Level, Bump, I).

analyze(V,Trail,I,Level,Bump) ->
    analyze_conflict(V,Trail,varc:conflicting_clause(V,I),Level,Bump).

analyze_conflict(V,Trail,Cix,Level,Bump) ->
    Conflicting = get_clause(V,Cix,undefined),
    ?dbg("trail: decision=~w,clause=~w,trail=~w\n", 
	  [varc:get_decision(V, Level),Conflicting,Trail]),
    analyze_reason(V,Conflicting,Trail,Level,Bump,#{},0,[]).

analyze_reason(V,[Q|Qs],Trail,Level,Bump,Seen,C,CL) ->
    case is_seen(Q, Seen) of
	true ->
	    ?dbg("~w: seen\n", [Q]),
	    analyze_reason(V,Qs,Trail,Level,Bump,Seen,C,CL);
	false ->
	    QLevel = varc:implication_level(V,Q),
	    ?dbg("~w: level ~w\n", [Q, QLevel]),
	    if QLevel > ?TOP_LEVEL ->
		    varc:bump(V, Q, Bump),
		    Seen1 = set_seen(Q, Seen),
		    if QLevel >= Level ->
			    analyze_reason(V,Qs,Trail,Level,Bump,Seen1,C+1,CL);
		       true ->
			    analyze_reason(V,Qs,Trail,Level,Bump,Seen1,C,[Q|CL])
		    end;
	       true ->
		    analyze_reason(V,Qs,Trail,Level,Bump,Seen,C,CL)
	    end
    end;
analyze_reason(V,[],Trail,Level,Bump,Seen,C,CL) ->
    [P|Trail1] = drop_not_seen(Trail, Seen),
    if C =< 1 ->
	    ?dbg("conflict clause ~w\n", [[-P|CL]]),
	    [-P|CL];
       true ->
	    Seen1 = clr_seen(P, Seen),
	    analyze_reason(V,reason(V,P),Trail1,Level,Bump,Seen1,C-1,CL)
    end.

%% dropwhile but with debug output
drop_not_seen(Trail=[P|Trail1], Seen) ->
    case is_seen(P, Seen) of
	true -> 
	    ?dbg("~w: seen\n", [P]),
	    Trail;
	false -> 
	    ?dbg("~w: dropped\n", [P]),
	    drop_not_seen(Trail1, Seen)
    end.
		    
get_clause(V, ClauseIndex, SkipLiteral) ->
    varc:get_clause(V, ClauseIndex, SkipLiteral).

reason(V,L) ->
    case varc:implication_clause(V,L) of
	-1 -> [];
	Cix ->
	    Reason = get_clause(V,Cix,L),
	    ?dbg("~w: implication ~w = ~w\n", 
		  [L,varp_formula:cix(Cix),Reason]),
	    varc:use_clause(V, Cix),
	    Reason
    end.

get_trail(V, Level) ->
    varc:get_bindings(V, Level, false, true).

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
