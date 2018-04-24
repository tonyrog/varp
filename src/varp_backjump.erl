%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2018, Tony Rogvall
%%% @doc
%%%    Implement the main loop with backjump
%%% @end
%%% Created : 23 Apr 2018 by Tony Rogvall <tony@rogvall.se>

-module(varp_backjump).
-compile(export_all).

-include("varp_bic.hrl").

%% -define(dbg(F,As), ok).
-define(dbg(F,As), io:format(F,As)).

-define(INITVAL, 1).

%%
%%  1. select unassigned variable xi
%%       if not possible the print model, 
%%
%%

satisfy(SNF) ->
    satisfy(SNF,-1).
    
satisfy({snf,{_Nv,_Nc,Decl,Literals,CLs}},N) ->
    satisfy(CLs, Literals, Decl, N);
satisfy({cnf,{_Nv,_Nc,Decl,Literals,CLs}},N) ->
    satisfy(CLs, Literals, Decl, N);
satisfy({CLs, Literals, Decl},N) ->
    satisfy(CLs, Literals, Decl, N).

satisfy(CLs, Ls, _Decl, _N) ->
    Vp = varc:new(),
    Level = 1,
    varc:mark(Vp,Level),
    Vm = add_literals(Vp, Ls, #{}),
    Vm1 = add_clauses(Vp, CLs, Vm),
    case varc:eval(Vp) of
	false -> 
	    ?dbg("contradiction bindings[~w]:  ~s\n", 
		 [Level,format_marked_bindings(Vp,Vm1,Level)]),
	    0;
	true ->
	    %% varc:order_sort(Vp, occur_descending),
	    init(Vp, Vm1)
    end.

init(Vp,Vm) ->
    case varc:eval(Vp) of
	false ->
	    0;
	true ->
	    case varc:order_first(Vp) of
		false ->
		    model(Vp,Vm), 1;
		{I,Xi} ->
		    run(Vp,Vm,I,Xi,2,?INITVAL,[])
	    end
    end.

run(Vp,Vm,I,Xi,Level,Val,Stack) ->
    varc:mark(Vp,Level),
    ?dbg(" decision[~w]: ~s=~w\n", [Level,format_var(Vm,Xi),(Val+1) div 2]),
    true = varc:put(Vp,Xi,Val),
    case varc:eval(Vp) of
	false ->
	    contradiction(Vp,Vm,Xi,Level,Val,Stack);
	true ->
	    format_all_bindings(Vp,Vm),
	    next(Vp,Vm,Level+1,I,[{I,Xi,Val,Level}|Stack])
    end.

%% Xi=Val generated conflict
contradiction(Vp,Vm,Xi,Level,Val,Stack) ->
    ?dbg("contradiction[~w]: xi=~s\n", [Level,format_var(Vm,Xi)]),
    format_all_bindings(Vp,Vm),
    {JLevel,Clause,UIP} = conflict_analysis(Vp,Vm,Level),
    ?dbg("conflict clause=~s\n", [format_clause(Vm,Clause)]),
    ?dbg(" level=~w, jlevel=~w, uip=~s\n",
	 [Level,JLevel,format_literal(Vm,UIP)]),
    io:format("stack=~w\n", [Stack]),
    ?dbg("undo: ~w\n", [Level]),
    varc:undo(Vp, Level),
    {K,Stack1} = backjump(Vp,Vm,Stack,JLevel),
    io:format("stack1=~w\n", [Stack1]),
    add_conflict_clause(Vp,Vm,Clause),
    ?dbg(" neg decision: ~s=~w\n", [format_var(Vm,Xi),(-Val+1) div 2]),
    true = varc:put(Vp,Xi,-Val),
    case varc:eval(Vp) of
	false ->
	    ?dbg("decision contradiction\n", []),
	    format_all_bindings(Vp,Vm),
	    case Stack1 of
		[] -> 
		    0;
		[{_J,Xj,JVal,_}|Stack2] ->
		    contradiction(Vp,Vm,Xj,JLevel,JVal,Stack2)
	    end;
	true ->
	    next(Vp,Vm,Level+1,K,Stack1)
    end.

next(Vp,Vm,Level,I,Stack) ->
    case varc:order_next(Vp,I) of
	false ->
	    model(Vp,Vm), 1; %% pop()
	{J,Xj} ->
	    run(Vp,Vm,J,Xj,Level,?INITVAL,Stack)
    end.

model(Vp,Vm) ->
    M = varp_formula:model(Vp,Vm),
    varp_formula:print(model,1,M).

backjump(Vp,Vm,[{_,_,_,Mark}|Stack],JMark) when Mark > JMark ->
    ?dbg("undo: ~w\n", [Mark]),
    varc:undo(Vp, Mark),
    backjump(Vp,Vm,Stack,JMark);
backjump(_Vp,_Vm,Stack=[{K,_,_,_}|_],_JMark) ->
    {K,Stack};
backjump(_Vp,_Vm,[],_JMark) ->
    {2,[]}.


add_conflict_clause(Vp,Vm,Clause) ->
    L = length(Clause),
    if L >= 64 ->
	    ignore;
       true ->
	    Cix = varc:add_clause(Vp, 'or', [1|Clause]),
	    io:format("add_clause: ~w, ~s\n", [Cix,format_clause(Vm,Clause)])
    end.

add_clauses(Vp, [CL|Clauses], Vm) ->
    {Ls,Vm1} = add_clause(Vp, CL, [], Vm),
    Cix = varc:add_clause(Vp, 'or', [1|Ls]),
    io:format("~w: ~s\n", [Cix, format_clause(Vm1, Ls)]),
    add_clauses(Vp, Clauses, Vm1);
add_clauses(_Vp, [], Vm) ->
    Vm.

add_clause(V, [L|Ls], Acc, Vm) ->
    {Li,Vm1} = add_literal(V,L,Vm),
    add_clause(V, Ls, [Li|Acc], Vm1);
add_clause(_V, [], Acc, Vm) ->
    {lists:reverse(Acc),Vm}.


add_literals(Vp, [L|Ls], Vm) ->
    {Li,Vm1} = add_literal(Vp,L,Vm),
    varc:put(Vp,Li,1),
    add_literals(Vp,Ls,Vm1);
add_literals(_Vp, [], Vm) ->
    Vm.

%% convert literals to internal variables/constants
add_literal(_Vp,false,Vs) -> {-1,Vs};
add_literal(_Vp,true,Vs) -> {1,Vs};
add_literal(Vp,{'not',Var},Vs) ->
    X = eval_var(Var),
    case maps:find(X,Vs) of
	error ->
	    Xv = varc:add_variable(Vp),
	    {-Xv,Vs#{ X => Xv, Xv => [X]}};
	{ok,Xv} ->
	    {-Xv,Vs}
    end;
add_literal(Vp,Var,Vs) ->
    X = eval_var(Var),
    case maps:find(X,Vs) of
	error ->
	    Xv = varc:add_variable(Vp),
	    {Xv,Vs#{ X => Xv, Xv => [X]}};
	{ok,Xv} ->
	    {Xv,Vs}
    end.

eval_var({bit_index,Var,I}) -> 
    {bit_index,eval_p(Var),eval_expr(I)};
eval_var({uint,Var,Size,N}) -> 
    {uint,eval_p(Var),eval_expr(Size),eval_expr(N)};
eval_var({int,Var,Size,N}) -> 
    {int,eval_p(Var),eval_expr(Size),eval_expr(N)};
eval_var(true) -> true;
eval_var(false) -> false;
eval_var(Var) -> eval_p(Var).

eval_p({p,Var,Es}) -> {p,Var,[eval_expr(E)||E<-Es]}.
    

eval_expr(#cconst{value=List,base=Base}) ->
    list_to_integer(List,Base);
eval_expr(E) when is_integer(E) -> E.

	    
conflict_analysis(Vp,Vm,Level) ->
    Trail=[P|_] = lists:reverse(get_literal_bindings(Vp,Level)),
    conflict_trail(Vp,Vm,-P,varc:conflict_clause(Vp),
		   conflict_reason(Vp,-P),
		   Trail,Level,sets:from_list([abs(P)]),1,[]).

conflict_trail(Vp,Vm,P,Ci,Reason,Trail,Level,Seen,C,CL) ->
    io:format("reason ~s:~w = ~s\n", 
	      [format_literal(Vm,P),Ci,
	       format_literals(Vm,Reason)]),
    conflict_reason(Vp,Vm,Trail,Reason,Level,Seen,C,CL).

conflict_reason(Vp,Vm,Trail,[Q|Qs],Level,Seen,C,CL) ->
    case sets:is_element(abs(Q),Seen) of
	false ->
	    Seen1 = sets:add_element(abs(Q),Seen),
	    QLevel = implication_level(Vp,Q),
	    if QLevel =:= Level ->
		    conflict_reason(Vp,Vm,Trail,Qs,Level,Seen1,C+1,CL);
	       QLevel =< 1 -> %% filter constants
		    conflict_reason(Vp,Vm,Trail,Qs,Level,Seen1,C,CL);
	       true ->
		    conflict_reason(Vp,Vm,Trail,Qs,Level,Seen1,C,[Q|CL])
	    end;
	true ->
	    conflict_reason(Vp,Vm,Trail,Qs,Level,Seen,C,CL)
    end;
conflict_reason(Vp,Vm,Trail,[],Level,Seen,C,CL) ->
    conflict_seen(Vp,Vm,Trail,Level,Seen,C,CL).
    
conflict_seen(Vp,Vm,[P|Trail],Level,Seen,C,CL) ->
    case sets:is_element(abs(P),Seen) of
	false ->
	    conflict_seen(Vp,Vm,Trail,Level,Seen,C,CL);
	true ->
	    if  C =< 1, CL =:= [] ->
		    {1,[-P],P};
		C =< 1 ->
		    CM = [-P|CL],
		    ?dbg("level = ~w\n",[[{I,implication_level(Vp,I)}||I<-CM]]),
		    JMark = lists:max([implication_level(Vp,I)||I<-CL]),
		    {JMark,CM,P};
	       true ->
		    conflict_trail(Vp,Vm,P,implication_clause(Vp,P),
				   reason(Vp,P),
				   Trail,Level,Seen,C-1,CL)
	    end
    end.

reason(Vp,P) ->
    case implication_clause(Vp,P) of
	-1 -> [];
	I -> 
	    {'or',[1|Ls]} = varc:get_clause(Vp,I),
	    Ls -- [P]
    end.

conflict_reason(Vp,P) ->
    case varc:conflict_clause(Vp) of
	-1 -> [];
	I ->
	    {'or',[1|Ls]} = varc:get_clause(Vp,I),
	    Ls -- [P]
    end.

format_all_bindings(Vp,Vm) ->
    Bs = lists:map(
	   fun({V,Val}) ->
		   {Cix,_,ImpLev} = varc:implication_clause(Vp,V),
		   {ImpLev,V,Val,Cix}
	   end, varc:get_bindings(Vp,1)),
    lists:foreach(
      fun(G) ->
	      [{Lev,_,_,_}|_] = G,
	      io:format("bindings[~w]: ~s\n",[Lev,format_group(Vm,G)])
      end, key_group_list(1,Bs)).

format_group(Vm,[{_,V,Val,Cix}|G]) ->
    case Cix of
	-1 ->
	    [ [format_binding(Vm,V,Val)," "] | format_group(Vm,G)];
	_ ->
	    [ [format_binding(Vm,V,Val),":",integer_to_list(Cix)," "] |
	      format_group(Vm,G)]
    end;
format_group(_Vm,[]) ->
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

format_marked_bindings(Vp,Vs,Mark) ->
    format_bindings(Vs,varc:get_bindings(Vp,Mark)).

format_bindings(Vm,Bs) ->
    [[format_binding(Vm,V,Val)," "] || {V,Val} <- Bs].

format_binding(Vm,V,Val) ->
    [format_var(Vm,V),"=",
     case Val of 
	 -1 -> "0";
	 1 -> "1"
     end].


format_clause(Vm,CL) ->
    List = format_literals(Vm,CL),
    ["{",List,"}"].

format_literals(Vm,Ls) ->
    concat([format_literal(Vm,L)||L<-Ls],",").

format_literal(Vm,X) when X<0 ->
    ["-",format_var(Vm,-X)];
format_literal(Vm,X) ->
    format_var(Vm,X).

format_var(Vs,X) ->
    case maps:find(X,Vs) of
	error -> 
	    integer_to_list(X);
	{ok,[Var]} ->
	    format_symbol(Var)
    end.

%% get binding list as literal list
get_literal_bindings(Vp,Mark) ->
    [if Val < 0 -> -Var; true -> Var end || 
	{Var,Val} <- varc:get_bindings(Vp,Mark)].

implication_clause(Vp,Imp) ->
    {Cix,_,_} = varc:implication_clause(Vp,Imp),
    Cix.

implication_level(Vp,Imp) ->
    {_,_,ImpLev} = varc:implication_clause(Vp,Imp),
    ImpLev.

format_symbol(true) -> "true";
format_symbol(false) -> "false";
format_symbol(V) when is_atom(V) -> atom_to_list(V);
format_symbol(I) when is_integer(I) -> [$T|integer_to_list(I)];
format_symbol({bit,V,_N,I}) ->
    format_symbol(V)++"["++integer_to_list(I)++"]";
format_symbol({uint,V,_N,I}) ->
    format_symbol(V)++"["++integer_to_list(I)++"]";
format_symbol({int,V,_N,I}) ->
    format_symbol(V)++"["++integer_to_list(I)++"]";
format_symbol({bit_index,V,I}) ->
    format_symbol(V)++"["++integer_to_list(I)++"]";
format_symbol({p,T,[]}) when is_integer(T) -> [$T|integer_to_list(T)];
format_symbol({p,V,[]}) -> atom_to_list(V);
format_symbol({p,V,As}) ->
    [atom_to_list(V),"(", concat([io_lib:format("~w",[X])||X<-As], ","), ")"].

concat([], _) -> [];
concat([H],_) -> [H];
concat([H|T],S) -> [H,S | concat(T,S)].
