%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2019, Tony Rogvall
%%% @doc
%%%    Conflict analysis
%%% @end
%%% Created :  3 Dec 2019 by Tony Rogvall <tony@rogvall.se>

-module(varp_conflict).
-export([analyze/4]).
-export([analyze_alpha/4]).

-export([analyze_clause/4]).

%% -define(DEBUG, true).
-include("varp.hrl").

analyze_alpha(Bs, Level, Bump, Minimize) ->
    N = varp_nif:info(Bs#bs.vp, number_of_conflicting_clauses),
    analyze_alpha_(Bs, Level, Bump, Minimize, 0, N).

analyze_alpha_(_Bs, _Level, _Bump, _Minimize, N, N) ->
    [];
analyze_alpha_(Bs, Level, Bump, Minimize, I, N) ->
    case varp_nif:conflict(Bs#bs.vp, Level, Bump, I) of
	undefined ->  %% duplicate
	    %% io:format("clause duplicate\n"),
	    analyze_alpha_(Bs, Level, Bump, Minimize, I+1, N);
	Cix when is_integer(Cix) ->
	    case Minimize of
		true ->
		    case varp_nif:minimize(Bs#bs.vp, Cix) of
			undefined ->
			    %%io:format("clause duplicate after minimize\n"),
			    analyze_alpha_(Bs, Level, Bump, Minimize, I+1, N);
			Len ->
			    [{Len, Cix}|
			     analyze_alpha_(Bs, Level, Bump, Minimize, I+1, N)]
		    end;
		false ->
		    Len = varp_nif:clause_info(Bs#bs.vp, Cix, length),
		    [{Len, Cix}|
		     analyze_alpha_(Bs, Level, Bump, Minimize, I+1, N)]
	    end
    end.

analyze(Bs, Level, Bump, Minimize) ->
    Trail = get_trail(Bs#bs.vp, Level),
    N = varp_nif:info(Bs#bs.vp, number_of_conflicting_clauses),
    [ begin
	  Clause = analyze_clause_(Bs#bs.vp, Trail, I, Level, Bump),
	  if Minimize -> 
		  Clause1 = varp_minimize:clause(Bs, Clause),
		  {length(Clause1), Clause1};
	     true ->
		  {length(Clause),Clause}
	  end
      end || I <- lists:seq(0, N-1)].

analyze_clause(V, Level, Bump, I) ->
    analyze_clause_(V, get_trail(V, Level), I, Level, Bump).

analyze_clause_(V,Trail, I, Level, Bump) ->
    analyze_conflict_(V,Trail,varp_nif:conflicting_clause(V,I),Level,Bump).

analyze_conflict_(V,Trail,Cix,Level,Bump) ->
    Conflicting = varp_nif:get_clause(V,Cix,undefined),
    ?dbg("trail: decision=~w,clause=~w,trail=~w\n", 
	  [varp_nif:get_decision(V, Level),Conflicting,Trail]),
    analyze_reason(V,Conflicting,Trail,Level,Bump,#{},0,[]).

analyze_reason(V,[Q|Qs],Trail,Level,Bump,Seen,C,CL) ->
    case is_seen(Q, Seen) of
	true ->
	    ?dbg("~w: seen\n", [Q]),
	    analyze_reason(V,Qs,Trail,Level,Bump,Seen,C,CL);
	false ->
	    QLevel = varp_nif:implication_level(V,Q),
	    ?dbg("~w: level ~w\n", [Q, QLevel]),
	    if QLevel > ?TOP_LEVEL ->
		    varp_nif:bump(V, Q, Bump),
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
		    
reason(V,L) ->
    case varp_nif:implication_clause(V,L) of
	-1 -> [];
	Cix ->
	    Reason = varp_nif:get_clause(V,Cix,L),
	    ?dbg("~w: implication ~w = ~w\n", 
		  [L,varp_formula:cix(Cix),Reason]),
	    varp_nif:use_clause(V, Cix),
	    Reason
    end.

get_trail(V, Level) ->
    varp:get_bindings_trail(V, Level).

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
