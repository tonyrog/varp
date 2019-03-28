%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2018, Tony Rogvall
%%% @doc
%%%    Implement the main loop with backjump
%%% @end
%%% Created : 23 Apr 2018 by Tony Rogvall <tony@rogvall.se>

-module(varp_backjump).

-export([backjump/1]).

-include("varp_bic.hrl").
-include("varp.hrl").

-define(dbg(F,As), ok).
%%-define(dbg(F,As), io:format(F,As)).

-define(INITVAL, -1).

backjump(false) ->
    false;
backjump(Bs) ->
    init(Bs).

init(Bs) ->
    case varp_formula:eval(Bs) of
	false ->  0;
	true -> next0(Bs,2,[])
    end.

next0(Bs,Level,Stack) ->
    case varp_formula:first_unbound(Bs) of
	false ->
	    model(Bs), 1;
	{I,Xi} ->
	    %% io:format("next0: i=~w, xi=~w\n", [I,Xi]),
	    loop(Bs,I,Xi,Level,?INITVAL,Stack)
    end.

next(Bs,Level,I,Stack) ->
    case varp_formula:next_unbound(Bs,I) of
	false ->
	    model(Bs), 1; %% pop()
	{J,Xj} ->
	    loop(Bs,J,Xj,Level,?INITVAL,Stack)
    end.

loop(Bs,I,Xi,Level,Val,Stack) ->
    varp_formula:mark(Bs,Level),
    ?dbg(" decision[~w]: ~s=~w\n", [Level,format_var(Bs,Xi),(Val+1) div 2]),
    true = varp_formula:equal(Bs,Xi,Val),
    case varp_formula:eval(Bs) of
	false ->
	    contradiction(Bs,Level,I,Xi,Val,Stack);
	true ->
	    format_all_bindings(Bs),
	    next(Bs,Level+1,I,[{I,Xi,Val,Level}|Stack])
    end.

%% Xi=Val generated conflict
contradiction(Bs,Level,_I,_Xi,_Val,Stack) ->
    ?dbg("contradiction[~w]: xi=~s\n", [Level,format_var(Bs,_Xi)]),
    format_all_bindings(Bs),
    {JLevel,Clause,_UIP} = conflict_analysis(Bs,Level),
    %%io:format("conflict clause s\n", [format_clause(Bs,Clause,true)]),
    ?dbg(" level=~w, jlevel=~w, uip=~s\n",
	 [Level,JLevel,format_literal(Bs,_UIP)]),
    ?dbg("stack=~w\n", [Stack]),
    ?dbg("undo: ~w\n", [Level]),
    varp_formula:undo(Bs, JLevel),
    {K,Stack1} = backjump(Bs,Stack,JLevel),
    ?dbg("stack1=~w\n", [Stack1]),
    Bs1 = add_conflict_clause(Bs,Clause),
    ?dbg(" neg decision: ~s=~w\n", [format_var(Bs1,_Xi),(-_Val+1) div 2]),
    %% true = varp_formula:equal(Bs,_Xi,-_Val),
    case varp_formula:eval(Bs1) of
	false ->
	    ?dbg("decision contradiction\n", []),
	    format_all_bindings(Bs1),
	    case Stack1 of
		[] -> 
		    0;
		[{J,Xj,JVal,_}|Stack2] ->
		    contradiction(Bs1,JLevel,J,Xj,JVal,Stack2)
	    end;
	true ->
	    %% io:format("backjump: i=~w, k=~w\n", [I,K]),
	    %% next0(Bs1,JLevel+1,Stack1)
	    next(Bs1,JLevel+1,K-1,Stack1)
    end.


model(Bs) ->
    M = varp_formula:model(Bs),
    varp_formula:print(model,1,M).

backjump(Bs,[{_,_,_,Level}|Stack],JLevel) when Level > JLevel ->
    backjump(Bs,Stack,JLevel);
backjump(_Bs,Stack=[{K,_,_,Level}|_],JLevel) when Level =:= JLevel ->
    %%varp_formula:mark(Bs, Level),
    {K,Stack};
backjump(_Bs,[],_JLevel) ->
    {2,[]}.

add_conflict_clause(Bs,[L]) ->
    TopLevel = 0, %% install at top level (constant)
    true = varp_formula:equal(Bs,L,1,TopLevel),
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
	    _Cix = varp_formula:add_clause(Bs, 'or', [1|Clause]),
	    if _Cix =:= false -> error(conflict_clause_error);
	       _Cix =:= error -> error(clause_error);
	       true -> ok
	    end,
	    Bs
    end.

conflict_analysis(Bs,Level) ->
    Trail= [P|_] = lists:reverse(get_literal_bindings(Bs,Level)),
    ?dbg("trail: ~s\n", [format_literals(Bs,Trail)]),
    conflict_trail(Bs,-P,varp_formula:conflicting_clause(Bs),
		   conflict_reason(Bs,-P),
		   Trail,Level,sets:from_list([abs(P)]),1,[]).

conflict_trail(Bs,_P,_Ci,Reason,Trail,Level,Seen,C,CL) ->
    ?dbg("reason ~s:~w = ~s\n", 
	 [format_literal(Bs,_P),_Ci,format_literals(Bs,Reason)]),
    conflict_reason(Bs,Trail,Reason,Level,Seen,C,CL).

conflict_reason(Bs,Trail,[Q|Qs],Level,Seen,C,CL) ->
    case sets:is_element(abs(Q),Seen) of
	false ->
	    Seen1 = sets:add_element(abs(Q),Seen),
	    QLevel = implication_level(Bs,Q),
	    if QLevel =:= Level ->
		    conflict_reason(Bs,Trail,Qs,Level,Seen1,C+1,CL);
	       QLevel =< 1 -> %% filter constants
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
		    {1,[-P],P};
		C =< 1 ->
		    CM = [-P|CL],
		    ?dbg("level = ~w\n",[[{I,implication_level(Bs,I)}||I<-CM]]),
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
	I -> 
	    {'or',[1|Ls]} = varp_formula:get_clause(Bs,I),
	    Ls -- [P]
    end.

conflict_reason(Bs,P) ->
    case varp_formula:conflicting_clause(Bs) of
	-1 -> [];
	I ->
	    {'or',[1|Ls]} = varp_formula:get_clause(Bs,I),
	    Ls -- [P]
    end.

format_all_bindings(Bs) ->
    Bnd = lists:map(
	    fun({V,Val}) ->
		    {Cix,_,ImpLev} = varp_formula:implication_clause(Bs,V),
		    {ImpLev,V,Val,Cix}
	    end, varp_formula:get_bindings(Bs,1)),
    lists:foreach(
      fun(G) ->
	      [{_Lev,_,_,_}|_] = G,
	      ?dbg("bindings[~w]: ~s\n",[_Lev,format_group(Bs,G)])
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

format_clause(Bs,CL) ->
    format_clause(Bs,CL,false).

format_clause(Bs,CL,Bound) ->
    List = format_literals(Bs,CL,Bound),
    ["{",List,"}"].

format_literals(Bs,Ls) ->
    format_literals(Bs,Ls,false).

format_literals(Bs,Ls,Bound) ->
    concat([format_literal(Bs,L,Bound)||L<-Ls],",").

format_literal(Bs,X) ->
    format_literal(Bs,X, false).

format_literal(Bs,X,Bound) when X<0 ->
    ["-",format_var(Bs,-X,Bound)];
format_literal(Bs,X,Bound) ->
    format_var(Bs,X,Bound).

format_var(Bs,X) ->
    format_var(Bs,X,false).

format_var(Bs,X,Bound) ->    
    case varp_formula:find_var(X,Bs) of
	error ->
	    format_binding(Bs, X, X, Bound);
	{ok,[Var]} ->
	    format_binding(Bs, X, Var, Bound)
    end.

format_binding(_Bs, _X, Var, false) ->
    format_symbol(Var);
format_binding(Bs, X, Var, _Bound) ->
    L = implication_level(Bs, X), 
    Value = case varp_formula:value(Bs, X) of
		true -> "=1:"++integer_to_list(L);
		false -> "=0:"++integer_to_list(L);
		_ -> ""
	    end,
    format_symbol(Var) ++ Value.

%% get binding list as literal list
get_literal_bindings(Bs,Level) ->
    [if Val < 0 -> -Var; true -> Var end || 
	{Var,Val} <- varp_formula:get_bindings(Bs,Level)].

implication_clause(Bs,Imp) ->
    {Cix,_,_} = varp_formula:implication_clause(Bs,Imp),
    Cix.

implication_level(Bs,Imp) ->
    {_,_,ImpLev} = varp_formula:implication_clause(Bs,Imp),
    ImpLev.

format_symbol(true) -> "true";
format_symbol(false) -> "false";
format_symbol(V) when is_atom(V) -> atom_to_list(V);
format_symbol(I) when is_integer(I) -> [$$|integer_to_list(I)];
format_symbol({bit,V,_N,I}) ->
    format_symbol(V)++"["++integer_to_list(I)++"]";
format_symbol({uint,V,_N,I}) ->
    format_symbol(V)++"["++integer_to_list(I)++"]";
format_symbol({int,V,_N,I}) ->
    format_symbol(V)++"["++integer_to_list(I)++"]";
format_symbol({bit_index,V,I}) ->
    format_symbol(V)++"["++integer_to_list(I)++"]";
format_symbol(Var={p,_,_}) ->
    varp_formula:format_var(Var).

concat([], _) -> [];
concat([H],_) -> [H];
concat([H|T],S) -> [H,S | concat(T,S)].
