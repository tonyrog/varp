%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2018, Tony Rogvall
%%% @doc
%%%    Implement the main loop with backjump
%%% @end
%%% Created : 23 Apr 2018 by Tony Rogvall <tony@rogvall.se>

-module(varp_backjump).

-export([backjump/1]).

-include("varp.hrl").

-define(TOP_LEVEL, 0).    %% constants
%% -define(INIT_LEVEL, 1).

-define(dbg0(F,As), ok).
-define(dbg(F,As), ok).
-define(dcall(Fun), ok).
%%-define(dbg(F,As), io:format(F,As)).
%%-define(dcall(Fun), Fun()).

-compile(export_all).
-import(varp_formula, [format_literal/2, format_literal/3]).
-import(varp_formula, [format_var/2]).
-import(varp_formula, [format_clause/2, format_clause/3]).
-import(varp_formula, [format_literals/2]).

backjump(false) ->
    false;
backjump(Bs) ->
    init(Bs).

init(Bs) ->
    loop(Bs,?TOP_LEVEL,varp_formula:first_init(Bs),[]).

loop(Bs,Level,I,Stack) ->
    Eval = varp_formula:eval(Bs),
    ?dbg("loop bindings[~w]\n",[Level]),
    format_bindings(Bs,Level),
    case Eval of
	false ->
	    ?dcall(fun() ->
			   io:format("conflicting clause[~w]: ", [Level]),
			   Cix = varp_formula:conflicting_clause(Bs),
			   get_clause(Bs, Cix),
			   io:format("~s\n",
				     [
				      format_clause(Bs,get_clause(Bs,Cix),
						    true)])
		   end),
	    if Level =:= 0 ->
		    0;
	       true ->
		    contradiction(Bs,Level,I,Stack)
	    end;
	true ->
	    next(Bs,Level,I,Stack)
    end.

contradiction(Bs,Level,_I,Stack) ->
    {JLevel,Clause,_UIP} = conflict_analysis(Bs,Level),
    ?dbg(" level=~w, jlevel=~w, uip=~s\n",
	 [Level,JLevel,format_literal(Bs,_UIP)]),
    ?dcall(fun() -> io:format("stack[~w]: ", [Level]),
		    display_stack_ln(Bs, Stack),
		    io:format("\n", [])
	   end),
    ?dbg("undo[~w]: ~w\n", [Level, JLevel+1]),
    varp_formula:undo(Bs, JLevel+1),
    varp_formula:mark(Bs, JLevel),
    {K,Stack1} = backjump(Bs,Stack,JLevel),
    ?dcall(fun() -> io:format("stack[~w]: ", [JLevel]),
		    display_stack_ln(Bs, Stack1),
		    io:format("\n", [])
	   end),
    ?dbg("conflict clause ~s\n", [format_clause(Bs,Clause,true)]),
    Clause1 = minimize(Bs, Clause),
    ?dbg("minimized conflict clause ~s\n", [format_clause(Bs,Clause1,true)]),
    Clause2 = compress(Bs, Clause1),
    Bs1 = add_conflict_clause(Bs,Clause2),
    loop(Bs1,JLevel,K,Stack1).

backjump(Bs,[{_,_Xk,Level}|Stack],JLevel) when Level > JLevel ->
    backjump(Bs,Stack,JLevel);
backjump(_Bs,Stack=[{K,_Xk,Level}|_],JLevel) when Level =:= JLevel ->
    ?dbg("backjump[~w]: ~s\n", [JLevel, format_literal(_Bs,_Xk)]),
    {K,Stack};
backjump(Bs,[],_JLevel) ->
    {varp_formula:first_init(Bs), []}.

next(Bs,Level,I,Stack) ->
    case varp_formula:next_unbound(Bs,I) of
	false ->
	    model(Bs),
	    display_stat(Bs),
	    1;
	{J,Xj} ->
	    NextLevel = Level+1,
	    varp_formula:mark(Bs,NextLevel),
	    true = varp_formula:equal(Bs,Xj,?TRUE),
	    ?dbg("decision[~w] = ~s\n", [NextLevel,format_literal(Bs,Xj)]),
	    loop(Bs,NextLevel,J,[{J,Xj,NextLevel}|Stack])
    end.


display_stat(Bs) ->
    io:format("num conflict clauses added: ~w\n", 
	      [counters:get(Bs#bs.counters, ?COUNTER_CONFLICT_CLAUSES)]),
    io:format("num ilterals removed: ~w\n",
	      [counters:get(Bs#bs.counters, ?COUNTER_MINIMIZE_COUNT)]),
    io:format("compression saved bits: ~w\n",
	      [counters:get(Bs#bs.counters, ?COUNTER_COMPRESS_CLAUSES)]),
    ok.

model(Bs) ->
    M = varp_formula:model(Bs),
    varp_formula:print(model,1,M).

add_conflict_clause(Bs,[]) ->
    Bs;
add_conflict_clause(Bs,[L]) ->
    ?dbg("~s=1@0(~w)\n", [format_literal(Bs,L),varp_formula:value(Bs,L)]),
    true = varp_formula:equal(Bs,L,?TRUE,?TOP_LEVEL),
    Bs;
add_conflict_clause(Bs,Clause) ->
    Max = varp_formula:get_info(Bs, max_clause_length),
    L = length(Clause),
    if L >= Max ->
	    L2 = L div 2,
	    {CL1,CL2} = lists:split(L2, Clause),
	    {Vi,_Bs1} = varp_formula:fresh_var(Bs),
	    Bs1 = varp_formula:set_var({p,'#',[Vi]}, Vi, Bs),
	    Bs2 = add_conflict_clause(Bs1,[Vi|CL1]),
	    add_conflict_clause(Bs2,[-Vi|CL2]);
       true ->
	    varp_formula:add_clause(Bs, 'or', [?TRUE|Clause]),
	    counters:add(Bs#bs.counters, ?COUNTER_CONFLICT_CLAUSES,1),
	    Bs
    end.

compress(Bs,Clause) ->
    case varp_formula:getopt(Bs,compress) of
	true ->
	    Len = length(Clause),
	    if Len > 2 ->
		    NBits = length(Clause)*32,  %% initial number of bits
		    DeltaCode = compress_(Clause),  %% abs deltas
		    NCompressed = 32 + 
			lists:sum([bit:size(Code)+1||Code<-DeltaCode]),
		    N = NBits - NCompressed,
		    io:format("compress, Clause=~w,delta=~w,NBits=~w,NCompressed=~w,N=~w\n", [Clause, DeltaCode, NBits, NCompressed, N]),
		    if N =< 0 ->
			    ok;
		       true ->
			    counters:add(Bs#bs.counters, ?COUNTER_COMPRESS_CLAUSES,N)
		    end,
		    Clause;
	       true ->
		    Clause
	    end;
	false ->
	    Clause
    end.

compress_([L1|Ls=[L2|_]]) -> [abs(L1)-abs(L2) | compress_(Ls)];
compress_([_Ln]) -> [].

minimize(_Bs,[]) -> [];
minimize(_Bs,Clause=[_]) -> Clause;
minimize(Bs,Clause0) ->
    case varp_formula:getopt(Bs,minimize) of
	true ->
	    Clause = sort_abs_clause(Clause0),
	    %% io:format("minimize: ~p\n", [Clause]),
	    case minimize_(Bs, Clause, Clause, [], 0, 0) of
		{0,_,_} -> 
		    %% io:format("  no change\n", []),
		    Clause;
		{NumRemoved,_InputClauseLength,Clause1} ->
		    counters:add(Bs#bs.counters, ?COUNTER_MINIMIZE_COUNT,
				 NumRemoved),
		    %% io:format("minimize: saved ~.2f%\n", [(NumRemoved / _InputClauseLength)*100]),
		    Clause1
	    end;
	false ->
	    Clause0
    end.

minimize_(Bs, [Li|Ls], Clause, NewClause, Removed, Length) ->
    case implication_clause(Bs, -Li) of
	-1 ->
	    minimize_(Bs, Ls, Clause, [Li|NewClause], Removed, Length+1);
	I ->
	    varp_formula:use_clause(Bs, I),
	    A = get_clause(Bs,I),
	    %% io:format("implication clause of ~w = ~w\n", [-Li, A]),
	    %% if A-{Li} is a subset of Clause then remove Li from clause
	    case is_subclause_abs(A, -Li, Clause) of
		true ->
		    minimize_(Bs, Ls, Clause, NewClause, Removed+1, Length+1);
		false ->
		    minimize_(Bs, Ls, Clause, [Li|NewClause], Removed, Length+1)
	    end
    end;
minimize_(_Bs, [], _Clause, NewClause, Removed, Length) ->
    {Removed,Length,NewClause}.

conflict_analysis(Bs,Level) ->
    Trail= [P|_] = get_literal_bindings(Bs,Level),
    ?dbg("trail: ~s\n", [format_literals(Bs,Trail)]),
    conflict_trail(Bs,-P,varp_formula:conflicting_clause(Bs),
		   conflict_reason(Bs,-P),
		   Trail,Level,sets:from_list([abs(P)]),1,[]).

conflict_trail(Bs,_P,_Ci,Reason,Trail,Level,Seen,C,CL) ->
    ?dbg0("reason ~s:~w = ~s\n", 
	  [format_literal(Bs,_P),_Ci,format_literals(Bs,Reason)]),
    conflict_reason(Bs,Trail,Reason,Level,Seen,C,CL).

conflict_reason(Bs,Trail,[Q|Qs],Level,Seen,C,CL) ->
    case sets:is_element(abs(Q),Seen) of
	false ->
	    Seen1 = sets:add_element(abs(Q),Seen),
	    QLevel = implication_level(Bs,Q),
	    if QLevel =:= Level ->
		    conflict_reason(Bs,Trail,Qs,Level,Seen1,C+1,CL);
	       QLevel =< ?TOP_LEVEL -> %% filter constants
		    conflict_reason(Bs,Trail,Qs,Level,Seen1,C,CL);
	       true ->
		    conflict_reason(Bs,Trail,Qs,Level,Seen1,C,[Q|CL])
	    end;
	true ->
	    conflict_reason(Bs,Trail,Qs,Level,Seen,C,CL)
    end;
conflict_reason(Bs,Trail,[],Level,Seen,C,CL) ->
    conflict_seen(Bs,Trail,Level,Seen,C,CL).

conflict_seen(Bs,[P|Trail],Level,Seen,C,CL) ->
    case sets:is_element(abs(P),Seen) of
	false ->
	    conflict_seen(Bs,Trail,Level,Seen,C,CL);
	true ->
	    if  C =< 1, CL =:= [] ->
		    %% implication_level = decision_level ...
		    ?dcall(fun() ->
				   io:format("level: ~s@~w\n",
					     [format_literal(Bs,P),
					      implication_level(Bs,P)])
			   end),
		    {implication_level(Bs,P)-1,[-P],P};
		C =< 1 ->
		    CM = [-P|CL],
		    ?dcall(fun() ->
				   io:format("level: "),
				   [begin
					io:format("~s@~w ",
						  [format_literal(Bs,I),
						   implication_level(Bs,I)])
				    end || I<-CM],
				   io:format("\n")
			   end),
		    JLevel = lists:max([implication_level(Bs,I)||I<-CL]),
		    {JLevel,CM,P};
	       true ->
		    conflict_trail(Bs,P,implication_clause(Bs,P),
				   reason(Bs,P),
				   Trail,Level,Seen,C-1,CL)
	    end
    end.

reason(Bs,P) ->
    case implication_clause(Bs,P) of
	-1 -> [];
	I -> get_clause(Bs,I) -- [P]
    end.

conflict_reason(Bs,P) ->
    case varp_formula:conflicting_clause(Bs) of
	-1 -> [];
	I -> get_clause(Bs,I) -- [P]
    end.


%% check if As is a subset of Bs
is_subclause(As, Li, Bs) ->
    case (As--[Li])-- Bs of
	[] -> true;
	_ -> false
    end.

sort_abs_clause(Clause) ->
    lists:sort(
      fun(A,A) -> false;
	 (A,B) -> 
	      case abs(A) - abs(B) of
		  0 -> A < 0;
		  R -> R > 0
	      end
      end, Clause).

%% assume clauses are abs sorted in reversed order
is_subclause_abs([Li|As],Li,Bs) ->
    is_subclause_abs(As,Li,Bs);
is_subclause_abs([X|As],Li,[X|Bs]) ->
    is_subclause_abs(As,Li,Bs);
is_subclause_abs(As=[A|_As0],Li,[B|Bs]) ->
    if abs(A) < abs(B) ->
	    is_subclause_abs(As,Li,Bs);
       true ->
	    false
    end;
is_subclause_abs([],_Li,_Bs) ->
    true;
is_subclause_abs(_As,_Li,[]) ->
    false.

implication_clause(Bs,Imp) ->
    {Cix,_,_} = varp_formula:implication_clause(Bs,Imp),
    Cix.

implication_level(Bs,Imp) ->
    {_,_,ImpLev} = varp_formula:implication_clause(Bs,Imp),
    ImpLev.

get_clause(Bs, I) ->
    {'or',[?TRUE|Ls]} = varp_formula:get_clause(Bs,I),
    Ls.

%% -1 - 1 => 0 1
neg01(Val) -> (Val+1) div 2. 
    
val(Xi) when Xi < 0 -> 0;
val(Xi) when Xi > 0 -> 1.

format_bindings(Bs) ->
    format_bindings(Bs,all).

format_bindings(Bs,Level) ->
    Bnd = lists:map(
	    fun({V,Val}) ->
		    {Cix,_,ImpLev} = varp_formula:implication_clause(Bs,V),
		    {ImpLev,V,Val,Cix}
	    end, varp_formula:get_bindings(Bs,0)),
    lists:foreach(
      fun(G) ->
	      [{_Lev,_,_,_}|_] = G,
	      if Level =:= all; Level =:= _Lev ->
		      ?dbg("bindings[~w]: ~s\n",[_Lev,format_group(Bs,G)]);
		 true ->
		      ok
	      end
      end, key_group_list(1,Bnd)).

format_group(Bs,[{_,V,Val,Cix}|G]) ->
    case Cix of
	-1 ->
	    [ [format_binding(Bs,V,Val)," "] | format_group(Bs,G)];
	_ ->
	    [ [format_binding(Bs,V,Val),":",integer_to_list(Cix)," "] |
	      format_group(Bs,G)]
    end;
format_group(_Bs,[]) ->
    [].

%% generate a list of key groups	      
key_group_list(Pos,L) ->
    case lists:keysort(Pos,L) of
	[] -> [];
	[H|T] -> key_group_list(Pos,[H],[],T)
    end.

key_group_list(Pos,Acc=[A|_],Gs,[H|T]) when 
      element(Pos,A) =:= element(Pos,H) ->
    key_group_list(Pos,[H|Acc],Gs,T);
key_group_list(Pos,Acc,Gs,[H|T]) ->
    key_group_list(Pos,[H],[lists:reverse(Acc)|Gs],T);
key_group_list(_Pos,Acc,Gs,[]) ->
    lists:reverse([lists:reverse(Acc)|Gs]).

format_binding(Bs,V,Val) ->
    [format_var(Bs,V),"=",
     case Val of 
	 -1 -> "0";
	 1 -> "1";
	 W -> integer_to_list(W)
     end].


%% get binding list as literal list
get_bindings(Bs, Level) ->
    [if Val < 0 -> -Var; true -> Var end || 
	{Var,Val} <- varp_formula:get_bindings(Bs,Level)].

get_literal_bindings(Bs,Level) ->
    lists:reverse(get_bindings(Bs,Level)).

get_literal_implications(Bs, Level) ->
    case get_bindings(Bs, Level) of
	[] -> [];
	[_|L] -> L
    end.

display_stack_ln(Bs,[{K,Xk,Level}|Stack]) ->
    io:format("~s@~w/~w ", [format_literal(Bs,Xk), Level, K]),
    display_stack_ln(Bs, Stack);
display_stack_ln(_Bs,[]) ->
    ok.
