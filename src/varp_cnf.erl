%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2010, Tony Rogvall
%%% @doc
%%%   Rewrite formulas into CNF format
%%% @end
%%% Created : 20 Aug 2010 by Tony Rogvall <tony@rogvall.se>

-module(varp_cnf).
-export([rewrite/1]).
-export([clauses/1]).
-export([normalize_clause/1,normalize_clause/2]).
-export([normalize_clauses/1,normalize_clauses/2]).
-export([format/1]).
-compile(export_all).

-include("varp.hrl").

%% -define(dbg(F,As), ok).
-define(dbg(F,As), io:format(F,As)).

%%
%% Special CNF prover
%% backtrack over Clauses 
%% for each variable v:
%%   a) assume v=0 then for each clause C with v as negative literal 
%%      C={..!v..a..!b..} set a=0, b=1 backtrack
%% 
%%   b) assume v=1 then for each clause C with v as positive literal 
%%      C={..v..c..!d..} set c=0, d=1 backtrack
%%   
%%

sat({snf,{_Nv,_Nc,Decl,Literals,CLs}}) ->
    satisfy(CLs, Literals, Decl, 1);
sat({cnf,{_Nv,_Nc,Decl,Literals,CLs}}) ->
    satisfy(CLs, Literals, Decl, 1).

satisfy(SNF) ->
    satisfy(SNF,-1).
    
satisfy({snf,{_Nv,_Nc,Decl,Literals,CLs}},N) ->
    satisfy(CLs, Literals, Decl, N);
satisfy({cnf,{_Nv,_Nc,Decl,Literals,CLs}},N) ->
    satisfy(CLs, Literals, Decl, N).

satisfy(CLs, Ls, _Decl, N) ->
    Vp = varc:new(),
    Mark = 1,
    varc:mark(Vp,Mark),
    Vm = add_literals(Vp, Ls, #{}),
    Vm1 = add_clauses(Vp, CLs, Vm),
    ?dbg("bindings[~w]:  ~s\n", 
	 [Mark,format_marked_bindings(Vp,Vm1,Mark)]),
    case varc:eval(Vp) of
	false -> 
	    0;
	true ->
	    %% varc:order_sort(Vp, occur_descending),
	    bt(Vp,Vm1,
	       fun(Vpi,Acc) ->
		       model(Vpi,Vm1),
		       case Acc+1 of
			   N -> {false,N};
			   Acc1 -> {true,Acc1}
		       end
	       end, 0)
    end.

model(Vp,Vm) ->
    M = varp_formula:model(Vp,Vm),
    varp_formula:print(model,1,M).

%%
%% Explicit recursion version, allow times backtracking
%% mix alogorithms etc.
%%
bt(Vp,Vm,Func,Acc) ->
    case bt_init(Vp,Vm) of
	{model,_Stack} ->
	    {_,Acc1} = Func(Vp,Acc),
	    Acc1;
	{true,Stack} ->
	    bt_loop(Vp,Vm,Stack,Func,Acc);
	false ->
	    Acc
    end.

bt_loop(Vp,Vm,Stack,Func,Acc) ->
    case bt_next(Vp,Vm,Stack) of
	{model,Stack1} ->
	    case Func(Vp,Acc) of
		{true,Acc1} ->
		    bt_undo(Vp,Vm,Stack1),
		    bt_loop(Vp,Vm,Stack1,Func,Acc1);
		{false,Acc1} ->
		    Acc1
	    end;
	{true,Stack1} ->
	    bt_loop(Vp,Vm,Stack1,Func,Acc);
	false ->
	    Acc
    end.

-define(BT_START_MARK, 2).
-define(BT_ORDER, [1,-1]).
-define(BT_FIRST, hd(?BT_ORDER)).
-define(BT_LAST,  hd(tl(?BT_ORDER))).

%% initalise backtrack stack
bt_init(Vp,_Vm) ->
    case varc:order_first(Vp) of
	false  -> {model,[]};
	{I,Xi} -> {true,[{I,Xi,?BT_ORDER,?BT_START_MARK}]}
    end.

bt_next(Vp,Vm,[{_,_,[],_}|Stack1]) ->
    ?dbg("empty next\n", []),
    bt_undo(Vp,Vm,Stack1),
    bt_next(Vp,Vm,Stack1);
bt_next(Vp,Vm,Stack0=[{I,Xi,[V|_Vs],Mark}|_Stack]) ->
    ?dbg("decision[~w]: ~s/~w=~w\n", [Mark,format_var(Vm,Xi),I,(V+1) div 2]),
    varc:mark(Vp,Mark),
    bt_next1(Vp,Vm,Stack0);
bt_next(_Vp,_Vm,[]) ->
    false.

bt_next1(Vp,Vm,Stack0=[{_I,Xi,[V|_Vs],Mark}|_Stack]) ->
    true = varc:put(Vp,Xi,V),
    case varc:eval(Vp) of
	false -> %% conflict
	    bt_conflict(Vp,Vm,Stack0);
	true ->
	    ?dbg("bindings[~w]: ~s\n", 
		 [Mark,format_marked_bindings(Vp,Vm,Mark)]),
	    bt_next_var(Vp,Vm,Stack0)
    end.

bt_conflict(Vp,Vm,[]) ->
    ?dbg("next = ~w\n", [varc:order_first(Vp)]),
    bt_init(Vp,Vm);
bt_conflict(Vp,Vm,Stack0=[{_I,_Xi,[],_Mark}|Stack]) ->
    bt_undo(Vp,Vm,Stack0),
    bt_conflict(Vp,Vm,Stack);
bt_conflict(Vp,Vm,Stack0=[{I,Xi,Vs,Mark}|_Stack]) ->
    ?dbg("xi/~w=~s\n", [I,format_var(Vm,Xi)]),
    format_all_bindings(Vp,Vm),
    {JMark,Clause,UIP} = conflict(Vp,Vm,Mark),
    ?dbg("conflict clause=~s\n", [format_clause(Vm,Clause)]),
    ?dbg(" mark=~w, jmark=~w, uip=~s\n", [Mark,JMark,format_literal(Vm,UIP)]),
    {_J,Stack1} = bt_undo(Vp,Vm,Stack0,JMark),
    add_conflict_clause(Vp,Vm,Clause),
    %% [Vn|_] = tl(Vs),
    Vn = -hd(Vs),
    io:format(" set: ~s=~w\n", [format_var(Vm,Xi),(Vn+1) div 2]),
    true = varc:put(Vp,Xi,Vn),
    case varc:eval(Vp) of
	false -> %% conflict
	    bt_conflict(Vp,Vm,Stack1);
	true ->
	    ?dbg("bindings[~w]: ~s\n", 
		 [JMark,format_marked_bindings(Vp,Vm,JMark)]),
	    bt_next_var(Vp,Vm,Stack1)
    end.


add_conflict_clause(Vp,Vm,Clause) ->
    L = length(Clause),
    if L >= 64 ->
	    ignore;
       true ->
	    Cix = varc:add_clause(Vp, 'or', [1|Clause]),
	    io:format("add_clause: ~w, ~s\n", [Cix,format_clause(Vm,Clause)])
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


bt_continue(Vp,Vm,[]) ->
    ?dbg("RESTART\n",[]),
    bt_init(Vp,Vm);
bt_continue(Vp,_Vm,[{I,Xi,Vs,Mark}|Stack]) ->
    case varc:order_next(Vp,I) of
	false ->
	    {model,[{I,Xi,Vs,Mark}|Stack]};
	{J,Xj} ->
	    {true,[{J,Xj,?BT_ORDER,Mark+1},{I,Xi,Vs,Mark}|Stack]}
    end.

bt_next_var(Vp,Vm,[]) ->
    bt_init(Vp,Vm);
bt_next_var(Vp,Vm,[{I,Xi,[],Mark}|Stack]) ->
    case varc:order_next(Vp,I) of
	false ->
	    ?dbg("next_var: xi/~w=~s, model\n", [I,format_var(Vm,Xi)]),
	    {model,Stack};
	{J,Xj} ->
	    ?dbg("next_var: xi/~w=~s, xj/~w=~s\n", 
		 [I,format_var(Vm,Xi),
		  J,format_var(Vm,Xj)]),
	    {true,[{J,Xj,?BT_ORDER,Mark+1}|Stack]}
    end;
bt_next_var(Vp,Vm,[{I,Xi,[_|Vs],Mark}|Stack]) ->
    case varc:order_next(Vp,I) of
	false ->
	    ?dbg("next_var: xi/~w=~s, model\n", [I,format_var(Vm,Xi)]),
	    {model,[{I,Xi,Vs,Mark}|Stack]};
	{J,Xj} ->
	    ?dbg("next_var: xi/~w=~s, xj/~w=~s\n", 
		 [I,format_var(Vm,Xi),
		  J,format_var(Vm,Xj)]),
	    {true,[{J,Xj,?BT_ORDER,Mark+1},{I,Xi,Vs,Mark}|Stack]}
    end.

bt_undo(Vp,Vm,[{_,_,_,Mark}|Stack],JMark) when Mark > JMark ->
    ?dbg("undo: ~w\n", [Mark]),
    varc:undo(Vp, Mark),
    bt_undo(Vp,Vm,Stack,JMark);
bt_undo(_Vp,_Vm,Stack=[{J,_Xj,_Vs,_Mark}|_],_JMark) ->
    {J,Stack};
bt_undo(_Vp,_Vm,[],_JMark) ->
    {2,[]}.


bt_undo(Vp,_Vm,[{_,_,_,Mark}|_]) ->
    ?dbg("undo: ~w\n", [Mark]),
    varc:undo(Vp, Mark);
bt_undo(_Vp,_Vm,[]) ->
    ok.


conflict(Vp,Vm,Level) ->
    {CVar,CVal} = varc:get_latest_binding(Vp),
    Lit = if CVal < 0 -> -CVar; true -> CVar end,
    case find_first_uip(Vp,Vm,Level,Lit) of
	{ok,[L]} ->
	    {1,[-L],L};
	{ok,CSrc} ->
	    Clause = [-L||L<-CSrc],
	    ?dbg("level = ~w\n", [[{I,implication_level(Vp,I)}||I<-CSrc]]),
	    JMark = lists:max([implication_level(Vp,I)||I<-tl(CSrc)]),
	    {JMark,Clause,hd(CSrc)}
    end.

find_first_uip(Vp,Vm,Level,CLit) ->
    case implication_clause(Vp,CLit) of
	-1 -> %% CLit is probably the decision variable
	    ?dbg("conflict literal=~s, no cut\n",[format_literal(Vm,CLit)]),
	    {ok,[CLit]};
	Cix1 ->
	    Cix2 = varc:conflicting_clause(Vp),
	    ?dbg("conflict literal=~s, Cix1=~w, Cix2=~w\n",
		 [format_literal(Vm,CLit),Cix1,Cix2]),
	    Marks = sets:from_list([CLit,-CLit]),
	    {Q1,Marks1,Num1,CSrc1} =
		enq_imp(Vp,Level,CLit,Cix1,queue:new(),Marks,0,[]),
	    {Q2,Marks2,Num2,CSrc2} =
		enq_imp(Vp,Level,-CLit,Cix2,Q1,Marks1,Num1,CSrc1),
	    find_first_uip_(Vp,Level,Q2,Marks2,Num2,CSrc2)
    end.

find_first_uip_(Vp,Level,Q,Marks,Num,CSrc) ->
    {{value,Imp},Q1} = queue:out(Q),
    case sets:is_element(Imp, Marks) of
	false ->
	    find_first_uip_(Vp,Level,Q1,Marks,Num,CSrc);
	true when Num =:= 1 ->
	    {ok,[Imp|CSrc]};
	true ->
	    Marks1 = sets:del_element(Imp,Marks),
	    Num1 = Num-1,
	    case implication_clause(Vp,Imp) of
		-1 when Num1 =:= 1 ->
		    {ok,[Imp|CSrc]};
		-1 ->
		    find_first_uip_(Vp,Level,Q,Marks1,Num1,CSrc);
		Cix ->
		    {Q2,Marks2,Num2,CSrc1} = 
			enq_imp(Vp,Level,
				Imp,Cix,Q1,Marks1,Num1,CSrc),
		    if Num2 =:= 1 ->
			    {ok,CSrc1};
		       true ->
			    find_first_uip_(Vp,Level,Q2,
					    Marks2,Num2,CSrc1)
		    end
	    end
    end.

enq_imp(Vp,Level,L,Ci,Q,Marks,Num,CSrc) ->
    {'or',[1|Ls]} = varc:get_clause(Vp,Ci),
    enq_imp_(Vp,Level,L,Ls,Q,Marks,Num,CSrc).

enq_imp_(Vp,Level,L,[L|Ls],Q,Marks,Num,CSrc) ->
    enq_imp_(Vp,Level,L,Ls,Q,Marks,Num,CSrc);
enq_imp_(Vp,Level,L,[Li|Ls],Q,Marks,Num,CSrc) ->
    Imp = -Li,
    case sets:is_element(Imp,Marks) of
	true ->
	    enq_imp_(Vp,Level,L,Ls,Q,Marks,Num,CSrc);
	false ->
	    Marks1 = sets:add_element(Imp,Marks),
	    ImpLev = implication_level(Vp,Imp),
	    if  %% ImpLev =:= 1 -> %% constant, do not add to cut
		%%    enq_imp_(Vp,Level,L,Ls,Q,Marks1,Num,CSrc);
		ImpLev < Level ->
		    %% marked but not counted
		    enq_imp_(Vp,Level,L,Ls,Q,Marks1,Num,[Imp|CSrc]);
	       true ->
		    Num1 = Num+1,
		    Q1 = queue:in(Imp, Q),
		    enq_imp_(Vp,Level,L,Ls,Q1,Marks1,Num1,CSrc)
	    end
    end;
enq_imp_(_Vp,_Level,_L,[],Q,Marks,Num,CSrc) ->
    {Q,Marks,Num,CSrc}.

implication_clause(Vp,Imp) ->
    {Cix,_,_} = varc:implication_clause(Vp,Imp),
    Cix.

implication_level(Vp,Imp) ->
    {_,_,ImpLev} = varc:implication_clause(Vp,Imp),
    ImpLev.

%% get binding list as literal list
get_literal_bindings(Vp,Mark) ->
    [if Val < 0 -> -Var; true -> Var end || 
	{Var,Val} <- varc:get_bindings(Vp,Mark)].
    
%% set all literals except L to false
%% return false if contradiction is found or no assignments where done
%%         true if any literal was assigned 
%%
zclause(Vp,L,Ls) ->
    zclause(Vp,L,Ls,false).

zclause(Vp,L,[L|Ls],F) ->
    zclause(Vp,L,Ls,F);
zclause(Vp,L,[M|Ls],F) ->
    %% io:format("ZPUT: ~w = ~w\n",[L,-1]),
    case varc:get(Vp,M) of
	-1 -> zclause(Vp,L,Ls,F);
	1  -> false;
	M  ->
	    case peval(Vp,M,-1) of
		false -> false;
		true -> zclause(Vp,L,Ls,true)
	    end
    end;
zclause(_Vp,_L,[],F) ->
    F.

peval(Vp, Xv, Val) ->
    case varc:put(Vp, Xv, Val) of
	true -> varc:eval(Vp);
	false -> false
    end.

next(Vp, Xv) when Xv < 0 ->
    -varc:class_next(Vp, -Xv);
next(Vp, Xv) ->
    varc:class_next(Vp, Xv).

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

%%
%% Formula to CNF form
%% return {Clauses, Literals}
%%
clauses(A) ->
    %% io:format("A=~p\n", [A]),
    A1 = rewrite(A),
    %% io:format("A1=~p\n", [A1]),
    Cs1 = clause_form(A1),
    %% io:format("Cs1=~p\n", [Cs1]),
    {Cs2,Ls1} = normalize_clauses(Cs1),
    %% io:format("Cs2=~p, Ls1=~p\n", [Cs2,Ls1]),
    Cs3 = subsume_clauses(Cs2),
    %% io:format("Cs3=~p,Ls2=~p\n", [Cs3]),
    {Cs3,Ls1}.

%%
%% Normalize all clauses F
%%
normalize_clauses(F) ->
    normalize_clauses(F,[]).

normalize_clauses(F,Ss) ->
    normalize_clauses_(F,Ss,[],[]).

normalize_clauses_([C|Cs],Ss,Acc,Ss1) ->
    case normalize_clause(C,Ss) of
	[] ->
	    normalize_clauses_(Cs,Ss,Acc,Ss1);
	[L] -> %% clause contain one literal only add to singleton list
	    normalize_clauses_(Cs,Ss,Acc,[L|Ss1]);
	D  ->
	    normalize_clauses_(Cs,Ss,[D|Acc],Ss1)
    end;
normalize_clauses_([],Ss,Acc,[]) ->
    {Acc,Ss};
normalize_clauses_([],Ss,Acc,Ss1) -> %% one more round
    normalize_clauses_(Acc,Ss1++Ss,[],[]).
    
%% Normalize a clause.
%%  Rule (after usort, where multiple literals are removed)
%%  MULT:  .. A .. A .. => [.. A.. ]    remove multiples (usort)
%%  TAUT:  .. !A .. A   => []           clause removed
%%  CONST: .. true ..   => []           clause removed
%%  CONST: .. false     => [..]         constant removed
%%  UNSAT: false        =>              throw(false)
%%
normalize_clause(CL) ->
    normalize_clause(CL,[]).
normalize_clause(CL,Ls) ->
    normalize_clause_(lists:usort(CL),[],Ls).

%% fixme: handle true,false and removed literals !
normalize_clause_([false|As],Acc,Ls) -> normalize_clause_(As,Acc,Ls);
normalize_clause_([true|_],_Acc,_Ls) -> [];
normalize_clause_([L|As],Acc,Ls) ->
    %% UNIT check against singleton clause list
    case lists:member(neg(L), Ls) of
	true ->
	    normalize_clause_(As,Acc,Ls);
	false ->
	    case lists:member(L, Ls) of
		true ->
		    [];
		false ->  
		    normalize_clause_(As,[L|Acc],Ls)
	    end
    end;
normalize_clause_([],CL,_Ls) ->
    CL.

%%
%% Remove sub clauses, return clauses and a lists of
%% removed literals. FIXME record literals removed from 
%% F when clause is deleted!
%%
subsume_clauses(F) ->
    %% make set and sort descending set size
    NCsL = [begin 
		Set = sets:from_list(CL),
		{sets:size(Set), Set}
	    end || CL <- F],
    CsL = [Set || {_,Set} <- lists:sort(fun(A,B) -> A>B end,NCsL)],
    CsL1 = subsume_clauses_(CsL,[]),
    [sets:to_list(CL) || CL <- CsL1].
		  
subsume_clauses_([CL|CLs],Acc) ->
    case has_sub_clause(CL,CLs) of
	true -> subsume_clauses_(CLs,Acc);
	false -> subsume_clauses_(CLs,[CL|Acc])
    end;
subsume_clauses_([],Acc) ->
    Acc.

has_sub_clause(CL, [C|Cs]) ->
    case sets:is_subset(C, CL) of
	true -> true;
	false -> has_sub_clause(CL, Cs)
    end;
has_sub_clause(_CL, []) ->
    false.

%%  CL1=(A,B,C,D)  CL2=(A,B,!C,D)
%%
%% CL3 = intersect(CL1,CL2) = A,B,D
%% if CL1-CL3 == !CL2-CL3


%% PURE A clause can be deleted if it contins L and !L does not
%% occur in F, fixme: to handle models [L,~L] should be added instead
purify(F) ->
    Set = literals(F, sets:new()),
    purify(F, Set).

purify([CL|Cs], Set) ->
    case lists:any(fun(L) -> not sets:is_element(neg(L), Set) end, CL) of
	true -> purify(Cs, Set);
	false -> [CL|purify(Cs,Set)]
    end;
purify([],_Set) ->
    [].

%% build a set of all literals in F    
literals([CL|Cs],Set) ->
    Set1 = lists:foldl(
	     fun(L,Si) -> sets:add_element(L,Si) end,
	     Set, CL),
    literals(Cs, Set1);
literals([], Set) -> Set.


clause_form({'and',A,B}) ->
    clause_form(A) ++ clause_form(B);
clause_form({'or',A,B}) ->
    As = clause_form(A),
    lists:flatmap(fun(Bd) ->
			  lists:map(fun(Ad) -> Ad++Bd end, As)
		  end, clause_form(B));
clause_form({'not',V}) ->
    [[{'not',V}]];
clause_form(V) ->
    [[V]].

%%
%% rewrite into and-or form, also move negation to the literals
%%
rewrite(true)  -> true;
rewrite(1)     -> true;
rewrite(false) -> false;
rewrite(0)     -> false;
rewrite(A={p,_P,_Vs}) -> A;
rewrite(A={'not',{p,_P,_Vs}}) -> A;
rewrite({'not', {'not', A}}) -> rewrite(A);
rewrite({'not', {'and', A, B}}) -> r('or',{'not',A},{'not',B});
rewrite({'not', {'or', A, B}})  -> r('and', {'not',A},{'not',B});
rewrite({'not', F}) -> rewrite(r('not',F));
rewrite({'!', F})  -> rewrite(r('not',F));
rewrite({'and', A, B}) -> r('and', A, B);
rewrite({'&&', A, B}) ->  r('and', A, B);
rewrite({'&', A, B}) ->  r('and', A, B);
rewrite({'or', A, B}) ->  r('or', A, B);
rewrite({'||', A, B}) ->  r('or', A, B);
rewrite({'|', A, B}) ->  r('or', A, B);
rewrite({'imp',A,B}) ->   r('or', {'not', A}, B);
rewrite({'->',A,B}) ->    r('or', {'not', A}, B);
rewrite({'<->',A,B}) ->   rewrite({'equ',A,B});
rewrite({'equ',A,B}) ->
    A1 = rewrite(A), B1 = rewrite(B),
    {'and',
     {'or', rewrite({'not', A1}), B1},
     {'or', rewrite({'not', B1}), A1}};
rewrite({'xor',A,B})    -> rewrite({'not',{'equ',A,B}});

rewrite({'all',Fs})  -> fold('and',true,[rewrite(F) || F <- Fs]);
rewrite({'any',Fs})  -> fold('or',false,[rewrite(F) || F <- Fs]);
rewrite({'none',Fs}) -> fold('and',true,[rewrite({'not',F}) || F <- Fs]);
rewrite({'one',[]})  -> false;
rewrite({'one',[F]}) -> rewrite(F);
rewrite({'one',Fs})  ->
    rewrite({'and', {all, [{'not',{'and',A,B}} || {A,B} <- pairs(Fs)]},
	     {any, Fs}}).

r(Op,A,B) -> {Op,rewrite(A),rewrite(B)}.
r(Op,A)   -> {Op,rewrite(A)}.


fold(_Op,Init,[]) -> Init;
fold(_Op,_Init,[A]) -> A;
fold(Op,Init,[A|As]) -> {Op,A,fold(Op,Init,As)}.

pairs([]) -> [];
pairs([_]) -> [];
pairs([A|As]) -> [{A,Ai} || Ai <- As] ++ pairs(As).

prod(N,File) ->
    {snf,{_Nv,_Nc,Decls,Ls,CLs}} = prod(N),
    file:write_file(File, format(Decls,CLs ++ [[L]||L<-Ls])).

prod(N) when is_integer(N), N>1 ->
    put(next_var, 2), %% FIXME!
    Nv = integer_bits(N),
    Lx  = (length(Nv)+1) div 2,
    Ly  = length(Nv)-1,
    Ix = lists:seq(0,Lx-1),
    Iy = lists:seq(0,Ly-1),
    X  = [{uint,{p,'X',[]},Lx,I}||I<-Ix],
    Y  = [{uint,{p,'Y',[]},Ly,I}||I<-Iy],
    Decls = [{{p,'X',[]},uint,Lx},{{p,'Y',[]},uint,Ly}],
    {Prod,Cs} = multiply(X, Y, []),
    %% Prod=Nv
    Cs1 = assign(Prod,Nv,Cs),
    %% X>1
    Cs2 = gt_1(X,Cs1),
    %% Y>1
    Cs3 = gt_1(Y,Cs2),
    %% X<Y
    Cs4 = lt(X,Y,Cs3),
    %% {Cs4,[],Decls},
    %%
    {Cs5,Ls1} = normalize_clauses(Cs4),
    %% {Cs5,Ls1,Decls}.
    Cs6 = subsume_clauses(Cs5),
    Nvs = length(X)+length(Y)+(get(next_var)-1),
    {snf,{Nvs,length(Cs6),Decls,Ls1,Cs6}}.

sum(N,File) ->
    {CLs,Ls,Decls} = sum(N),
    file:write_file(File, format(Decls,CLs ++ [[L]||L<-Ls])).

sum(N) when is_integer(N), N>1 ->
    put(next_var, 2), %% FIXME!
    Nv = integer_bits(N),
    L  = length(Nv),
    Is = lists:seq(0,L-1),
    X  = [{uint,{p,'X',[]},L,I}||I<-Is],
    Y  = [{uint,{p,'Y',[]},L,I}||I<-Is],
    Decls = [{{p,'X',[]},uint,L},{{p,'Y',[]},uint,L}],
    {Cout,Sum,Cs} = add(X, Y, []),
    %% Prod=Nv
    Cs1 = assign(Sum++[Cout],Nv,Cs),
    %% X>0
    Cs2 = gt_0(X,Cs1),
    %% Y>0
    Cs3 = gt_0(Y,Cs2),
    %%
    {Cs4,Ls1} = normalize_clauses(Cs3),
    {Cs4,Ls1,Decls}.
    %% Cs6 = subsume_clauses(Cs4),
    %% {Cs6,Ls1,Decls}.

integer_bits(N) ->
    [element((I-$0)+1,{false,true})||I<-lists:reverse(integer_to_list(N,2))].

assign([Z|Zs], [true|Vs], Cs) ->
    assign(Zs,Vs,[[Z]|Cs]);
assign([Z|Zs], [false|Vs], Cs) ->
    assign(Zs,Vs,[[{'not',Z}]|Cs]);
assign([Z|Zs],[],Cs) ->
    assign(Zs,[],[[{'not',Z}]|Cs]);
assign([],[],Cs) ->
    Cs.

gt_0(Xs,Cs) ->    
    [Xs|Cs].

gt_1([_|Xs],Cs) ->    
    [Xs | Cs].

%% X<Y == (xn<yn) || (xn=yn)&&(xn-1<yn-1)
lt(X,Y,Cs) ->
    {X1,Y1} = extend(X,Y),
    {Out,Cs1} = lt_(lists:reverse(X1), lists:reverse(Y1), Cs),
    [[Out]|Cs1].

lt_([Xi],[Yi],Cs) ->
    clt(Xi,Yi,Cs);
lt_([Xi|Xs],[Yi|Ys],Cs) ->
    {Lt,Cs1} = clt(Xi,Yi,Cs),
    {Eq,Cs2} = ceq(Xi,Yi,Cs1),
    {Lt1,Cs3} = lt_(Xs,Ys,Cs2),
    {And,Cs4} = cand(Eq,Lt1,Cs3),
    cor(Lt,And,Cs4).

multiply(X, Y, Cs) ->
    multiply_(X,Y,[],[],Cs).

multiply_([Xi|Xs],Y,Prev,Out,Cs) ->
    {M, Cs1} = mult_by_bit(Y,Xi,Cs),
    {Cout,[S1|Sum],Cs2} = add(M,Prev,Cs1),
    Prev1 = Sum++[Cout],
    Out1 = Out++[S1],
    multiply_(Xs,Y,Prev1,Out1,Cs2);
multiply_([],_Y,Prev,Out,Cs) ->
    {Out ++ Prev, Cs}.

mult_by_bit([A|X], B, Cs) ->
    {And,Cs1} = cand(A,B,Cs),
    {As,Cs2} = mult_by_bit(X, B, Cs1),
    {[And|As], Cs2};
mult_by_bit([], _B, Cs) ->
    {[false], Cs}.

%% simple sequential adder
add(X,[],Cs) ->
    {false,X,Cs};
add([],Y,Cs) ->
    {false,Y,Cs};
add(X,Y,Cs) ->
    Cout = create_var(),
    add(X,Y,Cout,Cs).

add(X,Y,Cout,Cs) ->
    {X1,Y1} = extend(X,Y),
    add_(lists:zip(X1,Y1),false,Cout,[],Cs).

add_([{Ai,Bi}],Cin,Cout,Sum,Cs) ->
    S = create_var(),
    {Cout,lists:reverse([S|Sum]),full_adder(Ai,Bi,Cin,S,Cout,Cs)};
add_([{Ai,Bi}|Inputs],Cin,Cout,Sum,Cs) ->
    S = create_var(),
    Cout1 = create_var(),
    Cs1 = full_adder(Ai,Bi,Cin,S,Cout1,Cs),
    add_(Inputs,Cout1,Cout,[S|Sum],Cs1);
add_([],_Cin,Cout,Sum,Cs) ->
    {Cout,lists:reverse(Sum),Cs}.

%% X = Y and Z
cand(Y,Z,Cs) ->
    cand(Y,Z,create_var(),Cs).
cand(Y,Z,X,Cs) ->
    {X,[[X,neg(Y),neg(Z)],[neg(X),Y],[neg(X),Z] | Cs]}.

%%  (X == Y or Z)
cor(Y,Z,Cs) ->
    cor(Y,Z,create_var(),Cs).
cor(Y,Z,X,Cs) ->
    {X,[[neg(X),Y,Z],[X,neg(Y)],[X,neg(Z)] | Cs]}.

%% X == Y -> Z
cimp(Y,Z,Cs) ->
    cimp(Y,Z,create_var(),Cs).
cimp(Y,Z,X,Cs) ->
    {X,[[neg(X),neg(Y),Z],[X,Y],[X,neg(Z)] | Cs]}.

%% X == Y <-> Z
ceq(Y,Z,Cs) ->
    ceq(Y,Z,create_var(),Cs).

ceq(Y,Z,X,Cs) ->
    {X,[[X,Y,Z],[X,neg(Y),neg(Z)],
	[neg(X),Y,neg(Z)],[neg(X),neg(Y),Z] | Cs]}.

%% X == Y < Z
clt(Y,Z,Cs) ->
    clt(Y,Z,create_var(),Cs).

clt(Y,Z,X,Cs) ->
    {X,[[X,Y,neg(Z)],[neg(X),Z],[neg(X),neg(Y)]|Cs]}.

%% full adder in CNF form
%% input A, B, and carry in Cin
%% output S sum, and carry out Cout
%% Cs are list of clauses
%%
full_adder(A,B,Cin,S,Cout,Cs) ->
    [[neg(A), neg(B), neg(Cin), S],
     [neg(A), neg(B), Cout],
     [neg(A), neg(Cin), Cout],
     [neg(A), Cout, S],
     [A, B, Cin, neg(S)],
     [A, B, neg(Cout)],
     [A, Cin, neg(Cout)],
     [A, neg(Cout), neg(S)],
     [neg(B), neg(Cin), Cout],
     [neg(B), Cout, S],
     [B, Cin, neg(Cout)],
     [B, neg(Cout), neg(S)],
     [neg(Cin), Cout, S],
     [Cin, neg(Cout), neg(S)] | Cs].

half_adder(A,B,S,Co,Cs) ->
    [[neg(Co),A], [neg(Co),B], [Co,neg(A),neg(B)],
     [S,neg(A),neg(B)],[S,A,neg(B)],[neg(S),neg(A),neg(B)],[neg(S),A,B] | Cs].

create_var() ->
    case get(next_var) of
	undefined -> put(next_var,3), {p,2,[]};
	V -> put(next_var,V+1), {p,'T',V}
    end.

neg(true) -> false;
neg(false) -> true;
neg({'not',X}) -> X;
neg(X) -> {'not',X}.

%% make bool vector X and Y the same size
extend(X,Y) ->
    Lx = length(X),
    Ly = length(Y),
    if Lx < Ly -> {X++lists:duplicate(Ly-Lx,false),Y};
       Lx > Ly -> {X,Y++lists:duplicate(Lx-Ly,false)};
       true -> {X,Y}
    end.

%% convert boolean to integer
uint1(X) when is_boolean(X) ->
    erlang:phash2(X,31) band 1.

%% generate full adder clauses
%%    A B Cin  Cout S
%%    1 1 1    1    1
%%    1 1 0    1    0
%%    1 0 1    1    0
%%    0 1 1    1    0
%%    0 0 0    0    0
%%    0 0 1    0    1
%%    0 1 0    0    1
%%    1 0 0    0    1
%%
%%    S = (A xor B xor Cin)
%%    Cout = ((A xor B) and Cin) or (A and B)
%%
full_adder() ->
    cclauses_1(
      fun(A,B,Cin,S) ->
	      (S =:= (A xor B xor Cin))
      end, ['A','B','Cin','S']) ++
    cclauses_1(
      fun(A,B,Cin,Cout) ->
	      (Cout =:= ((A xor B) and Cin) or (A and B))
      end, ['A','B','Cin','Cout']).

%% Utility to create CNF clauses from a boolean function
cclauses_1(F) ->
    {arity,N} = erlang:fun_info(F, arity),
    Vars = [list_to_atom("X"++integer_to_list(J))||J<-lists:seq(1,N)],
    cclauses_1_(F, N, 0, (1 bsl N), [], Vars).

cclauses_1(F,Vars) when is_list(Vars) ->
    N = length(Vars),
    cclauses_1_(F, N, 0, (1 bsl N), [], Vars).

cclauses_1_(F, N, I, L, Acc, Vars) when I < L ->
    Args = [(element(J+1,{false,true}))|| <<J:1>> <= <<I:N>>],
    case apply(F,Args) of
	false ->
	    CL = [if A -> {'not',V};
		     true -> V
		  end || {V,A} <- lists:zip(Vars,Args)],
	    cclauses_1_(F,N,I+1,L,[CL|Acc],Vars);
	true ->
	    cclauses_1_(F,N,I+1,L,Acc,Vars)
    end;
cclauses_1_(_F,_N,L,L,Acc,_Vars) ->
    lists:reverse(Acc).


format(CLs) ->
    format([],CLs).

format(Decls,CLs) ->
    NClauses = length(CLs),
    Vars = snf_vars(CLs),
    NVars = length(Vars),
    [["c auto generated from <file>\n"],
     ["p snf ", integer_to_list(NVars), " ", integer_to_list(NClauses), "\n"],
     [[format_decl(D)] || D <- Decls],
     [[format_clause(C)," .","\n"] || C <- CLs]].

snf_vars(CLs) -> snf_vars(CLs,sets:new()).
snf_vars([C|CLs],VSet) ->
    VSet1 = lists:foldl(
	      fun({'not',V}, Si) -> add_var(V,Si);
		 (V,Si) -> add_var(V,Si)
	      end, VSet, C),
    snf_vars(CLs, VSet1);
snf_vars([],VSet) ->
    sets:to_list(VSet).

add_var(true,VSet) -> VSet;
add_var(false,VSet) -> VSet;
add_var(V,VSet) -> sets:add_element(V,VSet).

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

format_decl({Name,int,Sz}) ->
    ["c declare ", format_symbol(Name),":",integer_to_list(Sz),"/signed","\n"];
format_decl({Name,uint,Sz}) ->
    ["c declare ",format_symbol(Name),":",integer_to_list(Sz),"/unsigned","\n"];
format_decl(_) -> [].

format_clause(C) ->
    concat([format_literal(L) || L <- C], " ").

format_literal({'not',V}) -> ["!",format_symbol(V)];
format_literal(V) ->  format_symbol(V).

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
format_symbol(Var={p,_,_}) -> varp_formula:format_var(Var).

concat([], _) -> [];
concat([H],_) -> [H];
concat([H|T],S) -> [H,S | concat(T,S)].
