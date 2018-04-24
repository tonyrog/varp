%%
%% Example from chung-yang
%%

-module(chung_yang).

-export([run/0]).

run() ->
    Vp = varc:new(),
    A = varc:add_variable(Vp),
    B = varc:add_variable(Vp),
    C = varc:add_variable(Vp),
    A1 = varc:add_variable(Vp),
    A2 = varc:add_variable(Vp),
    A3 = varc:add_variable(Vp),
    B1 = varc:add_variable(Vp),
    B2 = varc:add_variable(Vp),
    B3 = varc:add_variable(Vp),
    B4 = varc:add_variable(Vp),
    C1 = varc:add_variable(Vp),
    C2 = varc:add_variable(Vp),
    C3 = varc:add_variable(Vp),
    C4 = varc:add_variable(Vp),
    G = varc:add_variable(Vp),
    Vars = #{ A => "a", B => "b", C => "c",
	      A1 => "a1", A2 => "a2", A3 => "a3",
	      B1 => "b1", B2 => "b2", B3 => "b3", B4 => "b4",
	      C1 => "c1", C2 => "c2", C3 => "c3", C4 => "c4",
	      G => "g"
	    },
    varc:add_clause(Vp, 'or', 1, -A1, -A),
    varc:add_clause(Vp, 'or', 1, A2, -A),
    varc:add_clause(Vp, 'or', 1, A3, -A2, A1),

    varc:add_clause(Vp, 'or', 1, -B1, -A,  B),
    varc:add_clause(Vp, 'or', 1,  B2, A1, B),
    varc:add_clause(Vp, 'or', 1, -B3, -B2),
    varc:add_clause(Vp, 'or', 1,  B4, -A3, B1, B3),
    
    varc:add_clause(Vp, 'or', 1, -C1, C),
    varc:add_clause(Vp, 'or', 1,  C2, C1, B1),
    varc:add_clause(Vp, 'or', 1,  C3, C1),
    varc:add_clause(Vp, 'or', 1, -C4, -A2, -C3),

    varc:add_clause(Vp, 'or', 1, -G, -B4, C4),
    varc:add_clause(Vp, 'or', 1,  G, -C2),

    branch(Vp, Vars, [{A,1},{B,0},{C,0}], 2).

print_bindings(Vp,Vars,Level) ->
    Bs = varc:get_bindings(Vp,Level,true),
    io:format("~p\n", [lookup_vars(Vp,Vars,Bs)]).

%% test code going in a tree branch
branch(Vp,Vars,[{Decision,Value}|Vs],Level) ->
    varc:mark(Vp, Level),
    io:format("~w: ~s/~w\n", [Level,lookup_var(Vars,Decision),Value]),
    varc:put(Vp, Decision, Value),
    case varc:eval(Vp) of
	false ->
	    print_bindings(Vp,Vars,Level),
	    [{CVar,CVal}] = varc:get_latest_binding(Vp),
	    Lit = if CVal < 0 -> -CVar; true -> CVar end,
	    case find_first_uip(Vp,Vars,Level,Lit) of
		{ok,UIP} ->
		    io:format("uip=~p\n", [lookup_list(Vars,UIP)]),
		    {ok,{Lit,UIP}};
		Error={error,_} ->
		    Error
	    end;
	true ->
	    print_bindings(Vp,Vars,Level),
	    branch(Vp,Vars,Vs,Level+1)
    end;
branch(_Vp,_Vars,[],_Level) ->
    true.

find_first_uip(Vp,Vars,Level,CLit) ->
    io:format("conflict: ~s\n", [lookup(Vars,CLit)]),
    {Cix1,_,_} = varc:implication_clause(Vp,CLit),
    Cix2 = varc:conflict_clause(Vp),
    io:format("conflict clause = ~w ~p\n", [Cix2,lookup_clause(Vp,Vars,Cix2)]),
    %% Cix2 = find_conflict_clause(Vp, -CLit),

    Marks = sets:from_list([CLit,-CLit]),
    {Q1,Marks1,Num1,CSrc1} =
	enq_imp(Vp,Vars,Level,CLit,Cix1,queue:new(),Marks,0,[]),
    {Q2,Marks2,Num2,CSrc2} =
	enq_imp(Vp,Vars,Level,-CLit,Cix2,Q1,Marks1,Num1,CSrc1),
    io:format("num = ~w\n", [Num2]),
    find_first_uip_(Vp,Vars,Level,Q2,Marks2,Num2,CSrc2).

find_first_uip_(Vp,Vars,Level,Q,Marks,Num,CSrc) ->
    io:format("Q = ~p\n", [lookup_list(Vars,queue:to_list(Q))]),
    case queue:out(Q) of
	{empty, _Q1} ->
	    {error,not_found};  %% ???
	{{value,Imp},Q1} ->
	    case sets:is_element(Imp, Marks) of
		false ->
		    io:format("~p not marked\n", [lookup(Vars,Imp)]),
		    find_first_uip_(Vp,Vars,Level,Q1,Marks,Num,CSrc);
		true when Num =:= 1 ->
		    io:format("first uip = ~p\n", [lookup(Vars,Imp)]),
		    {ok,[Imp|CSrc]};
		true ->
		    Marks1 = sets:del_element(Imp,Marks),
		    Num1 = Num-1,
		    io:format("unmark(~p) num=~w\n", [lookup(Vars,Imp),Num1]),
		    case varc:implication_clause(Vp,Imp) of
			{-1,-1,_} ->
			    find_first_uip_(Vp,Vars,Level,Q,Marks1,Num1,CSrc);
			{Cix,_Lpos,_Lev} ->
			    {Q2,Marks2,Num2,CSrc1} = 
				enq_imp(Vp,Vars,Level,
					Imp,Cix,Q1,Marks1,Num1,CSrc),
			    find_first_uip_(Vp,Vars,Level,Q2,
					    Marks2,Num2,CSrc1)
		    end
	    end
    end.

%%
%% Scan all literals in Ci (implication sources)
%% add to conflict source.
%%
%% {'or',  1,    x1, .., L, .. xn}   L <- x1/0, .. xn/0
%% {'or',  0,    x1, .., L, .. xn}   L <- x0/0
%% {'or',  L,    x1, .., xi, .. xn}  L/1 <- xi/1 | L/0 <-
%%
%% {'and', 0,    x1, .., L, .. Xn}   L <- x1/1, .. xn/1
%% {'and', x0/0, x1, .., L, .. Xn}   L <- x1/1, .. xn/1
%% {'and', x0/1, x1, .., L, .. xn}   L <- x0/1
%%

enq_imp(Vp,Vars,Level,L,Ci,Q,Marks,Num,CSrc) ->
    {'or',[1|Ls]} = varc:get_clause(Vp,Ci),
    io:format("enq_imp(~p) = ~p\n",
	      [lookup(Vars,L),lookup_list(Vars,[-Li||Li<- (Ls--[L])])]),
    enq_imp_(Vp,Vars,Level,L,Ls,Q,Marks,Num,CSrc).

enq_imp_(Vp,Vars,Level,L,[L|Ls],Q,Marks,Num,CSrc) ->
    enq_imp_(Vp,Vars,Level,L,Ls,Q,Marks,Num,CSrc);
enq_imp_(Vp,Vars,Level,L,[Li|Ls],Q,Marks,Num,CSrc) ->
    Imp = -Li,
    case sets:is_element(Imp,Marks) of
	true ->
	    enq_imp_(Vp,Vars,Level,L,Ls,Q,Marks,Num,CSrc);
	false ->
	    Marks1 = sets:add_element(Imp,Marks),
	    {_,_,ImpLev} = varc:implication_clause(Vp,Imp),
	    if ImpLev < Level ->
		    io:format("add(~p)\n", [lookup(Vars,Imp)]),
		    %% marked but not counted
		    enq_imp_(Vp,Vars,Level,L,Ls,Q,Marks1,Num,[Imp|CSrc]);
	       true ->
		    Num1 = Num+1,
		    Q1 = queue:in(Imp, Q),
		    io:format("mark(~p) num=~w\n", [lookup(Vars,Imp),Num1]),
		    io:format("enq(~s)\n", [lookup(Vars,Imp)]),
		    enq_imp_(Vp,Vars,Level,L,Ls,Q1,Marks1,Num1,CSrc)
	    end
    end;
enq_imp_(_Vp,_Vars,_Level,_L,[],Q,Marks,Num,CSrc) ->
    {Q,Marks,Num,CSrc}.

-ifdef(not_used).
find_conflict_clause(Vp, _ConflictLit) ->
    find_conflict_clause_(Vp, varc:get_clauses(Vp, ConflictLit)).

find_conflict_clause_(_Vp, []) ->
    -1;
find_conflict_clause_(Vp, [Cix|Cs]) ->
    case varc:get_clause(Vp, Cix) of
	{'or',[1|Ls]} -> %% CNF
	    case lists:all(fun(L) -> varc:get(Vp,L) == -1 end, Ls) of
		true -> Cix;
		false -> find_conflict_clause_(Vp, Cs)
	    end;
	{'and',[0|Ls]} -> %% DNF
	    case lists:all(fun(L) -> varc:get(Vp,L) == 1 end, Ls) of
		true -> Cix;
		false -> find_conflict_clause_(Vp, Cs)
	    end
    end.
-endif.

lookup_vars(Vp,Vars,[{V,Val,-1,-1}|Bs]) ->
    W = if Val < 0 -> -V; true -> V end,
    [lookup(Vars,W) | lookup_vars(Vp,Vars,Bs)];
lookup_vars(Vp,Vars,[{V,Val,Li,Ci}|Bs]) ->
    W = if Val < 0 -> -V; true -> V end,
    Clause = lookup_clause(Vp,Vars,Ci),
    [ {lookup(Vars,W),Li,Ci,Clause} |
      lookup_vars(Vp,Vars,Bs)];
lookup_vars(_Vp,_Vars,[]) ->
    [].

lookup_clause(Vp,Vars,Ci) ->
    {Op,Ls} = varc:get_clause(Vp,Ci),
    {Op,lookup_list(Vars,Ls)}.

lookup_list(Vars,Ls) ->
    [lookup(Vars,Vi)||Vi<-Ls].
    
lookup(_Vars,1) -> "1";
lookup(_Vars,-1) -> "0";
lookup(Vars,V) when V < -1 -> maps:get(-V, Vars)++"=0";
lookup(Vars,V) when V > 1 -> maps:get(V, Vars)++"=1".

lookup_var(Vars,V) when V > 1 -> maps:get(V, Vars).
