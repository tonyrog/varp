%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2019, Tony Rogvall
%%% @doc
%%%    Conflict analysis
%%% @end
%%% Created :  3 Dec 2019 by Tony Rogvall <tony@rogvall.se>

-module(varp_conflict).
-export([analyze/2, analyze/3]).

-include("varp.hrl").

analyze(Bs, Level) ->
    Trail = [Lit|_] = get_bindings(Bs,Level),
    ?dbg("trail: ~s\n", [varp_formula:format_literals(Bs,Trail)]),
    N = varc:info(Bs#bs.vp, number_of_conflicting_clauses),
    analyze_(Bs, -Lit, Trail, Level, 0, N).

analyze_(_Bs, _Lit, _Trail, _Level, N, N) ->
    [];
analyze_(Bs, Lit, Trail, Level, I, N) ->
    Cix = varc:conflicting_clause(Bs#bs.vp,I),
    [ analyze_clause_(Bs, Lit, Trail, I, Cix, Level) |
      analyze_(Bs, Lit, Trail, Level, I+1, N) ].

analyze(Bs, Level, I) ->
    Trail = [P|_] = get_bindings(Bs,Level),
    Cix = varc:conflicting_clause(Bs#bs.vp, I),
    analyze_clause_(Bs, -P, Trail, I, Cix, Level).

analyze_clause_(Bs, Lit, Trail, _I, Cix, Level) ->
    varc:use_clause(Bs#bs.vp, Cix),
    Conflicting = get_clause(Bs,Cix,Lit),
    ?dbg("reason[~w] cix=~w: ~s,~s\n", 
	 [_I,Cix,format_lit(Bs,Lit),
	  varp_formula:format_literals(Bs,Conflicting)]),
    conflict_reason(Bs,Conflicting,Trail,Level,#{ abs(Lit) => true },1,[]).

conflict_reason(Bs,[Q|Qs],Trail,Level,Seen,C,CL) ->
    AbsQ = abs(Q),
    case Seen of
	#{ AbsQ := true } ->
	    conflict_reason(Bs,Qs,Trail,Level,Seen,C,CL);
	_ ->
	    Seen1 = Seen# { AbsQ => true },
	    QLevel = varc:implication_level(Bs#bs.vp,Q),
	    if QLevel =:= Level ->
		    conflict_reason(Bs,Qs,Trail,Level,Seen1,C+1,CL);
	       QLevel =< ?TOP_LEVEL -> %% filter constants
		    conflict_reason(Bs,Qs,Trail,Level,Seen1,C,CL);
	       true ->
		    conflict_reason(Bs,Qs,Trail,Level,Seen1,C,[Q|CL])
	    end
    end;
conflict_reason(Bs,[],Trail,Level,Seen,C,CL) ->
    conflict_seen(Bs,Trail,Level,Seen,C,CL).

conflict_seen(Bs,[Lit|Trail],Level,Seen,C,CL) ->
    AbsP = abs(Lit),
    case Seen of
	#{ AbsP := true } ->
	    if  C =< 1, CL =:= [] ->
		    [-Lit];
		C =< 1 ->
		    [-Lit|CL];
		true ->
		    conflict_reason(Bs,reason(Bs,Lit),Trail,Level,Seen,C-1,CL)
	    end;
	_ ->
	    conflict_seen(Bs,Trail,Level,Seen,C,CL)
    end.

%% get_clause(Bs, ClauseIndex, SkipLiteral) ->
%%    varc:get_clause(Bs#bs.vp, ClauseIndex) -- [SkipLiteral].
get_clause(Bs, ClauseIndex, SkipLiteral) ->
    varc:get_clause(Bs#bs.vp, ClauseIndex, SkipLiteral).

reason(Bs,Lit) ->
    case varc:implication_clause(Bs#bs.vp,Lit) of
	-1 -> [];
	ClauseIndex -> get_clause(Bs,ClauseIndex,Lit)
    end.

get_bindings(Bs,Level) ->
    %% fixme: get_bindings(Vp, Level, Reversed=true)
    Bindings = varc:get_bindings(Bs#bs.vp, Level),
    lists:reverse(Bindings).
