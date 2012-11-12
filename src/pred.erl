%%% File    : pred.erl
%%% Author  : Tony Rogvall <tony@PBook.local>
%%% Description : Predicate resolution 
%%% Created : 30 Oct 2006 by Tony Rogvall <tony@PBook.local>

-module(pred).

-compile(export_all).

-import(lists, [reverse/1, map/2, flatmap/2]).
%%
%% Representaion:
%% P =
%%    {'&', A, B}      =   A /\ B
%%    {'|',  A, B}     =   A \/ B
%%    {'->',  A, B}    =   A -> B
%%    {'<->', A, B}    =   A <-> B
%%    {'~', A}         =  ~A
%%    {'A',X,P(X)}     =   Axp(X)
%%    {'E',X,P(X)}     =   Exp(X)
%%    {p,P,Ts}         =   P(T1,T2,..Tn)
%%    
%% T = [{v,X}            =  X (X is atom or integer)
%%      {c,C}            =  C (C is any constant)
%%      {u,UC}           =  witness skolem unique constant
%%      {f,F,[T1,..Tn]}  =  F(T1,T2,...Tn) 
%%
%% Transform:
%%
%%     1. Remove implications.
%%              {'->',A,B}   == {or,{not,A},B}
%%              {'<->',A,B}   == {and,{imp,A,B},{imp,B,A}}
%%                            == {and,{or,{not,A},B},{or,{not,B},A}}
%%
%%     2. Move negations
%%               {not, {not, A}}  == A
%%               {not, {and,A,B}} == {or,{not,A},{not,B}}
%%               {not, {or,A,B}}  == {and,{not,A},{not,B}}
%%               {not, {all,X,p(X)}}    == {exists,X,{not,p(X)}}
%%               {not, {exists,X,p(X)}} == {all,X,{not,p(X)}}
%%
%%     3. Uniq variables 
%%               Rename variables so no quantifier use the same variable
%%
%%     4. Remove Exists
%%             Replace {'E',z ..{v,z}}            => z = {u,UC}
%%             Replace {'A',x,..{'E',z, ..{v,Z}}  => z = {f,UF,[X]}
%%
%%     5. Drop all quantifier
%%             {'A',x,P} =>  P
%%
%%     6. Write to clause form (&) [ D1, ..., Dn ]
%%              Di = (|) [~P(Tk), P(Tk)...]
%%        implies moveing '|' inside '&'
%%          (A & B) | C == (A | C) & (B | C)
%%          C | (A & B) == (C | A) & (C & B)
%%
%%     7. Make uniq clause variables
%%          [ [P(x),P(y)]  [P(x),P(y)] ]
%%          => [ [P(x1),P(y1)]  [P(x2),P(y2)] ]
%%
%%  Ax P(x) & Q(x) => Ax P(x) & Ax Q(x)
%%

%% Ax (Ay P(x,y)) -> ~(Ay Q(x,y) => R(x,y))
f(0) ->
    {'A',x,
     {'->',
      {'A',y,{p,'P',[{v,x},{v,y}]}},
      {'~', {'A',y, {'->',{p,'Q',[{v,x},{v,y}]},
		     {p,'R',[{v,x},{v,y}]}}}}}};

%% Ax Ey bar(x,y) => ~ foo(x) & Ax foo(x)
f(1) ->
    {'A',x,
     {'->', 
      {'E',y,{p,bar,[{v,x},{v,y}]}},
      {'~', {'&',{p,foo,[{v,x}]}, 
	       {'A',x,{p,foo,[{v,x}]}}}}
     }};
f(2) ->
    %% Ax p(x) -> Ex p(x)
    {'->', 
     {'A',x,{p,'P',[{v,x}]}},
     {'E',x,{p,'P',[{v,x}]}}
    };
f(3) ->
    %% A | ~((A & B) | C) =>
    %% A | (~(A & B) & ~C) =>
    %% A | ((~A | ~B) & ~C) =>
    %% A | [ [~A,~B],[~C] ] =>
    %% [ [A,~A,~B], [A,~C] ]
    {'|',
     {p,'A',[]},
     {'~',
      {'|', 
       {'&',{p,'A',[]},{p,'B',[]}},
       {p,'C',[]}}}}.

c(0) ->
    [ [{p,xorg,[{c,x1}]}],
      [{p,xorg,[{c,x2}]}],
      [{p,andg,[{c,a1}]}],
      [{p,andg,[{c,a2}]}],
      [{p,org,[{c,o1}]}],
      [{p,conn,[{f,i,[{c,1},{c,f1}]},more]}] ];
c(1) ->
    [ [{f,[{c,art},{c,john}],'+'}],
      [{f,[{c,bob},{c,kim}], '+'}],
      [{f,[{v,x},{v,y}],'-'}, {p,[{v,x},{v,y}],'+'}],
      [{p,[{v,z},{c,jon}],'-'}, {ans,[{v,z}],'+'}] ].
     

test(I) ->
    transform(f(I)).

transform(P) ->
    io:format("P=~s\n",[format(P)]),
    P1 = remove_implications(P),
    io:format("P(1)=~s\n",[format(P1)]),
    P2 = negations_in(P1),
    io:format("P(2)=~s\n",[format(P2)]),
    P3 = uniq_variables(P2),
    io:format("P(3)=~s\n",[format(P3)]),
    P4 = remove_exists(P3),
    io:format("P(4)=~s\n",[format(P4)]),
    P5 = drop_all(P4),
    io:format("P(5)=~s\n",[format(P5)]),
    P6 = clause_form(P5),
    io:format("P(6)=~s\n",[format(P6)]),
    P7 = rename_variables(P6),
    io:format("P(7)=~s\n",[format(P7)]),
    P7.


%% 1. Remove implication
remove_implications(Rule) ->
    case Rule of
	{'->',A,B} ->
	    {'|', {'~', remove_implications(A)}, remove_implications(B)};
	{'<->',A,B} ->
	    A1 = remove_implications(A),
	    B1 = remove_implications(B),
	    {'&', {'|', {'~', A1}, B1},{'|', {'~', B1}, A1}};
	{'&',A,B} ->
	    {'&',remove_implications(A),remove_implications(B)};
	{'|',A,B} ->
	    {'|',remove_implications(A),remove_implications(B)};
	{'~',A} ->
	    {'~',remove_implications(A)};
	{'A',X,P} ->
	    {'A',X,remove_implications(P)};
	{'E',X,P} ->
	    {'E',X,remove_implications(P)};
	{p,P,Ts} when is_atom(P),is_list(Ts) -> Rule
    end.

%% 2. Move negations in to the predicate
negations_in(Rule) ->
    case Rule of
	{'~', {'~', A}} ->
	    negations_in(A);
	{'~', {'&', A, B}} ->
	    {'|', negations_in({'~',A}),negations_in({'~',B})};
	{'~', {'|', A, B}} ->
	    {'&', negations_in({'~',A}),negations_in({'~',B})};
	{'~', {'E',X,P}} ->
	    {'A',X,negations_in({'~', P})};
	{'~', {'A',X,P}} ->
	    {'E',X,negations_in({'~', P})};
	{'&', A, B} ->
	    {'&', negations_in(A), negations_in(B)};
	{'|', A, B} ->
	    {'|', negations_in(A), negations_in(B)};
	{'E', X, P} ->
	    {'E', X, negations_in(P)};
	{'A', X, P} ->
	    {'A', X, negations_in(P)};
	{p,P,Ts} when is_atom(P),is_list(Ts) -> 
	    Rule;
	{'~',{p,P,Ts}} when is_atom(P),is_list(Ts) -> 
	    Rule
    end.

%% 3. Rename variable into unique ones

uniq_variables(Rule) ->
    {Rule1,_} = uniq_variables(Rule,[]),
    Rule1.

uniq_variables(Rule,Bs) ->
    case Rule of
	{'E',X,P} ->
	    case lists:keysearch(X,1,Bs) of
		false ->
		    {P1,Bs1} = uniq_variables(P,[{X,X}|Bs]),
		    {{'E',X,P1},Bs1};
		{value,_} ->
		    U = uid(),
		    {P1,Bs1} = uniq_variables(P,[{X,U}|Bs]),
		    {{'E',U,P1},Bs1}
	    end;
	{'A',X,P} ->
	    case lists:keysearch(X,1,Bs) of
		false ->
		    {P1,Bs1} = uniq_variables(P,[{X,X}|Bs]),
		    {{'A',X,P1},Bs1};
		{value,_} ->
		    U = uid(),
		    {P1,Bs1} = uniq_variables(P,[{X,U}|Bs]),
		    {{'A',U,P1},Bs1}
	    end;
	{'&',A,B} ->
	    {A1,Bs1} = uniq_variables(A,Bs),
	    {B1,Bs2} = uniq_variables(B,Bs1),
	    {{'&',A1,B1},Bs2};
	{'|',A,B} ->
	    {A1,Bs1} = uniq_variables(A,Bs),
	    {B1,Bs2} = uniq_variables(B,Bs1),
	    {{'|',A1,B1},Bs2};
	{'~',A} ->
	    {A1,Bs1} = uniq_variables(A,Bs),
	    {{'~',A1},Bs1};
	{p,P,Ts} when is_atom(P),is_list(Ts) ->
	    {{p,P, map(fun(T) -> pred_mapvar(T, Bs) end, Ts)},Bs}
    end.


%% remap variables in Predicate terms
pred_mapvar([T|Ts], Bs) ->
    [pred_mapvar(T, Bs) |pred_mapvar(Ts, Bs)];
pred_mapvar([], _Bs) ->
    [];
pred_mapvar(C={c,_C}, _Bs) -> C;
pred_mapvar(U={u,_U}, _Bs) -> U;
pred_mapvar({v,X}, Bs) ->
    {value,{X,Y}} = lists:keysearch(X,1,Bs),
    {v,Y};
pred_mapvar({f,F,Ts}, Bs) ->
    {f,F,map(fun(T) -> pred_mapvar(T, Bs) end, Ts)}.


%% 4. Remoce extists by replace with skolem constant/function
remove_exists(Rule) ->
    remove_exists(Rule,[],[]).

remove_exists(Rule, Bs, Map) ->
    case Rule of
	{'E',X,P} ->
	    Sx = if Bs == [] ->
			 {u,uid()};
		    true ->
			 {f,uid(),map(fun(V) -> {v,V} end,Bs)}
		 end,
	    remove_exists(P, Bs, [{X,Sx}|Map]);
	{'A',X,P} ->
	    {'A',X,remove_exists(P,[X|Bs],Map)};
	{'&',A,B} ->
	    A1 = remove_exists(A, Bs, Map),
	    B1 = remove_exists(B, Bs, Map),
	    {'&',A1,B1};
	{'|',A,B} ->
	    A1 = remove_exists(A, Bs, Map),
	    B1 = remove_exists(B, Bs, Map),
	    {'|',A1,B1};
	{'~',{p,P,Ts}} ->
	    {'~',{p,P,subvar(Ts,Map)}};
	{p,P,Ts} ->
	    {p,P,subvar(Ts, Map)}
    end.

%% 5. Drop all quantifier
drop_all(Rule) ->
    case Rule of
	{'A',_X,P} -> drop_all(P);
	{'&',A,B}  -> {'&', drop_all(A), drop_all(B)};
	{'|',A,B} ->  {'|', drop_all(A), drop_all(B)};
	{'~',{p,_P,_Ts}} -> Rule;
	{p,_P,_Ts} -> Rule
    end.

%% 6. Geneate clause form
%%
%% [[x1,x2],[y1]] | [[b1,b2],[c1]] =  
%%   [[x1,x2,b1,b2],[x1,x2,c1], [y1,b1,b2], [y1,c1]]
%%
%% also transform predicate {'~',{p,P,Ts}} => {p,P,'-',Ts}
%%                      and {p,P,Ts}       => {p,P,'+',Ts}
%%
clause_form(Rule) ->
    case Rule of
	{'&',A,B} ->
	    clause_form(A) ++ clause_form(B);
	{'|',A,B} ->
	    As = clause_form(A),
	    flatmap(fun(Bd) ->
			    map(fun(Ad) -> Ad++Bd end, As)
		    end, clause_form(B));
	{'~',{p,P,Ts}} ->
	    [[{P,Ts,'-'}]];
	{p,P,Ts} ->
	    [[{P,Ts,'+'}]]
    end.

%% Rename variables
%% All variables are made unique per clause
rename_variables([Clause|ClauseList]) ->
    Clause1 = rename_variables(Clause, [],[]),
    [Clause1 | rename_variables(ClauseList)];
rename_variables([]) ->
    [].

rename_variables([{P,Ts,S}|Ps], Bs,Acc) ->
    {Ts1,Bs1} = rename_term_list_variables(Ts, Bs, []),
    rename_variables(Ps, Bs1,[{P,Ts1,S}|Acc]);
rename_variables([], _Bs,Acc) ->
    reverse(Acc).

rename_term_list_variables([T|Ts], Bs, Acc) ->
    {T1,Bs1} = rename_term_variables(T, Bs),
    rename_term_list_variables(Ts, Bs1, [T1|Acc]);
rename_term_list_variables([], Bs, Acc) ->
    {reverse(Acc),Bs}.
    
rename_term_variables({v,X}, Bs) ->
    case lists:keysearch(X, 1, Bs) of
	false ->
	    U = uid(),
	    {{v,U},[{X,U}|Bs]};
	{value,{X,NX}} ->
	    {{v,NX},Bs}
    end;
rename_term_variables({c,C}, Bs) ->
    {{c,C},Bs};
rename_term_variables({u,UC}, Bs) ->
    {{u,UC},Bs};
rename_term_variables({f,F,Ts},Bs) ->
    {Ts1,Bs1} = rename_term_list_variables(Ts, Bs, []),
    {{f,F,Ts1},Bs1}.

%% Run resolution 
resolve(Cs) ->
    case ordsets:to_list(Cs) of
	[] -> [];
	[C|CsL] ->
	    resolve1(C, CsL, CsL, ordsets:new(), ordsets:new())
    end.

%% Each pair of clauses try to unify them
resolve1(C, [D|Cs], Cs0, Old, New) ->
    Pairs = [{Cp,Dp} ||
		Cp={P1,_,S1}<-ordsets:to_list(C),
		Dp={P2,_,S2}<-ordsets:to_list(D), P1==P2,S1 =/= S2 ],
    io:format("pairs=~p\n", [Pairs]),
    case unify_pair(Pairs) of
	false ->
	    resolve1(C,Cs,Cs0,Old, New);
	{Cp,Dp,Unifier} ->
	    E1 = app(ordsets:del_element(Cp,C), Unifier),
	    E2 = app(ordsets:del_element(Dp,C), Unifier),
	    E = ordsets:union(E1,E2),
	    resolve1(C,Cs,Cs0,Old,ordsets:add_element(E, New))
    end;
resolve1(C,[],[D|Cs],Old,New) ->
    resolve1(D,Cs,Cs,ordsets:add_element(C, Old),New);
resolve1(C,[],[],Old,New) ->
    {ordsets:add_element(C, Old),New}.

unify_pair([{Cp={_,CTs,_},Dp={_,DTs,_}}|Pairs]) ->
    case mgu(CTs,DTs) of
	false ->
	    io:format("mgu(~p, ~p)=~p\n", [Cp,Dp,false]),
	    unify_pair(Pairs);
	Unifier ->
	    io:format("mgu(~p, ~p)=~p\n", [Cp,Dp,Unifier]),
	    {Cp,Dp,Unifier}
    end;
unify_pair([]) ->
    false.

%% Make the clause list into a clause set
clause_set(Cs) ->
    clause_set(Cs, ordsets:new()).

clause_set([C|Cs], Set) ->
    C1 = ordsets:from_list(C),
    clause_set(Cs, ordsets:add_element(C1,Set));
clause_set([], Set) ->
    Set.

%% Remove tautology clauses from the clause set
tauology_removal(Set) ->
    tauology_removal(ordsets:to_list(Set), Set).

tauology_removal([Clause|Cs], Set) ->
    case is_tautology(ordsets:to_list(Clause)) of
	true -> 
	    tauology_removal(Cs, ordsets:del_element(Clause,Set));
	false ->
	    tauology_removal(Cs, Set)
    end;
tauology_removal([], Set) ->
    Set.

is_tautology([{P,Ts,_S1},{P,Ts,_S2}|_]) ->
    %% NOTE that S1 and S2 MUST be of different signs! and also
    %% always sorted together.
    true;
is_tautology([_|T]) -> is_tautology(T);
is_tautology([]) -> false.
    

%% calculate MGU of terms
mgu(X,X) -> [];
mgu({v,X},Y) -> mguvar(X,Y);
mgu(X,{v,Y}) -> mguvar(Y,X);
mgu({f,F,Ts1},{f,F,Ts2}) ->
    mgu(Ts1, Ts2);
mgu(Ts1, Ts2) when is_list(Ts1), is_list(Ts2) ->
    L1 = length(Ts1),
    L2 = length(Ts2),
    if L1 == L2 ->
	    mgu(Ts1,Ts2,1,L1+1,[]);
       true -> false
    end;    
mgu(_, _) -> false.

mgu(_Xs,_Ys2,N,N,G) ->
    G;
mgu(Xs,Ys,I,N,G) ->
    X = lists:nth(I, Xs),
    Y = lists:nth(I, Ys),
    case mgu(X,Y) of
	false -> false;
	[] -> mgu(Xs,Ys,I+1,N,G);
	S ->
	    G1 = compose(G,S),
	    mgu(subvar(Xs,G1),subvar(Ys,G1),I+1,N,G1)
    end.

mguvar(X, Y) ->
    case incvar(X,Y) of
	true -> false;
	false -> [{X,Y}]
    end.

    
    

format({'A',X,Rule}) ->
    "A("++format_var(X)++")"++ format(Rule);
format({'E',X,Rule}) ->
    "E("++format_var(X)++")"++ format(Rule);
format({'&',A,B}) ->
    "("++format(A)++"&"++format(B)++")";
format({'->',A,B}) ->
    "("++format(A)++"->"++format(B)++")";
format({'<->',A,B}) ->
    "("++format(A)++"<->"++format(B)++")";
format({'|',A,B}) ->
    "("++format(A)++"|"++format(B)++")";
format({'~',A}) ->
    case A of
	{p,_,_} -> "~"++format_pred(A);
	_ ->       "~("++format(A)++")"
    end;
format(A={'p',_P,_Ts}) ->
    format_pred(A);
format(Clauses) when is_list(Clauses) ->
    format_clause_list(Clauses).

format_var(X) when is_atom(X) ->
    atom_to_list(X);
format_var(X) when is_integer(X) ->
    "$"++integer_to_list(X).

format_pred({p,P,[]}) ->
    atom_to_list(P);
format_pred({'~',{P,[]}}) ->    
    "~"++atom_to_list(P);
format_pred({p,P,Ts}) ->
    atom_to_list(P)++"("++format_term_list(Ts) ++ ")";
format_pred({'~',{p,P,Ts}}) ->
    "~"++atom_to_list(P)++"("++format_term_list(Ts) ++ ")".

format_clause_list([D]) ->
    format_clause(D);
format_clause_list([D|Ds]) ->
    format_clause(D) ++ " " ++ format_clause_list(Ds);    
format_clause_list([]) -> "".

format_clause(Ps) ->
    "{" ++ format_clause1(Ps) ++ "}".

format_clause1([P]) ->
    format_cpred(P);
format_clause1([P|Ps]) ->
    format_cpred(P)++","++format_clause1(Ps);
format_clause1([]) ->
    "".

format_cpred({P,[],'+'}) ->
    atom_to_list(P);
format_cpred({P,[],'-'}) ->    
    "~"++atom_to_list(P);
format_cpred({P,Ts,'+'}) ->
    atom_to_list(P)++"("++format_term_list(Ts) ++ ")";
format_cpred({P,Ts,'-'}) ->
    "~"++atom_to_list(P)++"("++format_term_list(Ts) ++ ")".

format_term_list([T]) ->
    format_term(T);
format_term_list([T|Ts]) ->
    format_term(T)++","++format_term_list(Ts);
format_term_list([]) ->
    "".

format_term({v,X}) ->
    format_var(X);
format_term({c,C}) ->
    lists:flatten(io_lib:format("~p", [C]));
format_term({u,UC}) ->
    "#<"++integer_to_list(UC)++">";
format_term({f,F,Ts}) ->
    if is_atom(F) ->
	    atom_to_list(F)++"("++format_term_list(Ts)++")";
       is_integer(F) ->
	    "#<"++integer_to_list(F)++">"++"("++format_term_list(Ts)++")"
    end.

%% kind of uniq!
uid() ->
    case get('$uid') of
	undefined -> 
	    put('$uid',2), 1;
	I ->
	    put('$uid',I+1), I
    end.
%%    {A,B,C} = now(),
%%    ((A*1000000+B)*1000000 + C).

%% Check if variable X is included in Term Y
incvar(_,{c,_}) -> false;
incvar(_,{u,_}) -> false;
incvar(X,{v,Y}) -> X==Y;
incvar(X,{f,_,Ts}) ->
    lists:all(fun(T) -> incvar(X,T) end, Ts).


%% Compose bindings G and S and return an updated G'
compose(G, S) ->
    map(fun({X,Y}) -> {X,subvar(Y, S)} end, G) ++ S.

%% Apply substitutions on a clause
app(Clause, S) ->
    ordsets:from_list(
      map(fun({P,Ts,Sign}) -> {P,subvar(Ts, S),Sign} end,
	  ordsets:to_list(Clause))).
    

%% Substitue variable in Ts with value from mapping Map
subvar([T|Ts], Map) ->
    [subvar(T, Map) | subvar(Ts, Map)];
subvar([], _Map) -> [];
subvar({v,X}, Map) ->
    case lists:keysearch(X, 1, Map) of
	false -> {v,X};
	{value,{_,Z}} -> Z
    end;
subvar(C={c,_},_Map) ->  C;
subvar(C={u,_},_Map) ->  C;
subvar({f,F,Ts}, Map) -> {f,F,subvar(Ts, Map)}.
