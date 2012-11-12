%%% File    : bdd.erl
%%% Author  : Tony Rogvall <tony@iMac.local>
%%% Description : BDD implementation
%%% Created : 20 Jan 2006 by Tony Rogvall <tony@iMac.local>

-module(bdd).

-compile(export_all).

-import(lists, [reverse/1,map/2,member/2]).

f1() -> {'and', {var,x1}, {var, x2}}.

f2() -> {'or', {var,x1}, {var, x2}}.

f3() -> {'xor', {var,x1}, {var, x2}}.

f4() -> {'or', {'and',{var,x1},{var,x2}}, {'and',{var,x1},{var,x3}}}.


f5() -> {'or', {'and',{var,x1},{var,x2}}, 
	 {'or', {'and',{var,x3},{var,x4}}, {'and',{var,x5},{var,x6}}}}.

f6() -> 
    {'or', {'and',{var,x1},{var,x3}}, 
     {'or', {'and',{var,x2},{var,x5}}, {'and',{var,x3},{var,x6}}}}.
    
%%
%% Construct a bbd from Formula F
%% F =  {and,F1,F2}
%%    | {or,F1,F2}
%%    | {not,F1}
%%    | {xor,F1}
%%    | atom(X)
%%    | true
%%    | false
%%
construct(F) ->
    Vs = variables(F),
    construct(Vs, F, 2).

construct(_, 0, Free) ->  {0,Free,[]};
construct(_, 1, Free) ->  {1,Free,[]};
construct([V | Vs], F, Free) ->
    io:format("Free=~p,F=~p\n", [Free, F]),
    F0 = peval(F, V, 0),
    io:format("F[~w/0] =  ~p\n", [V,F0]),
    F1 = peval(F, V, 1),
    io:format("F[~w/1] =  ~p\n", [V,F1]),
    if F0 == 0, F1 == 0 ->  {0,Free,[]};
       F0 == 1, F1 == 1 ->  {1,Free,[]};
       true ->
	    {Ir0,Free1,Vs0} = construct(Vs, F0, Free),
	    {Ir1,Free2,Vs1} = construct(Vs, F1, Free1),
	    Vs2 = [{Free2,V,Ir0,Ir1}]++Vs0++Vs1,
	    Res={Ir2,Free3,Ws}=reduce(Free2,Vs2,Free),
	    io:format("reduce: ~w, Vs0=~999p, Vs1=~999p = ~999p\n", 
		      [{Free2,V,Ir0,Ir1},Vs0,Vs1, Ws]),
	    Res
    end.

%%
%%
%%
reduce(Root, Vs, Free) ->
    Vec = make_vector(Vs),
    D0 = insert(1, 1, dict:new()),
    D1 = insert(0, 0, D0),
    calc(Vs, Vec, D1, Free, Root, []).
    

calc([{Ai,Xi,Bi,Ci}|Vs], Vec, D0, Free, Root, Ws) ->
    case lookup(Ai,D0) of
	error ->
	    {Bj,D1,Free1,Ws1} = calc(Bi,Vec,D0,Free,Ws),
	    {Cj,D2,Free2,Ws2} = calc(Ci,Vec,D1,Free1,Ws1),
	    case lookup({Xi,Bj,Cj}, D2) of
		error ->
		    D3 = insert({Xi,Bj,Cj},Free2,D2),
		    D4 = insert(Ai,Free2,D3),
		    calc(Vs, Vec, D4, Free2+1, Root, [{Free2,Xi,Bj,Cj}|Ws2]);
		{ok, I} ->
		    D3 = insert(Ai,I,D2),
		    calc(Vs, Vec, D3, Free, Root, Ws2)
	    end;
	{ok,Wi} ->
	    calc(Vs, Vec, D0, Free, Root, Ws)
	    %% Bj = fetch(Bi, D0),
	    %% Cj = fetch(Ci, D0),
	    %% calc(Vs, Vec, D0, Free, Root, [{Wi,Xi,Bj,Cj}|Ws])
    end;
calc([], _Vec, D0, Free, Root, Ws) ->
    R1 = fetch(Root, D0),
    {R1,Free, Ws}.

%% recursivly calculate Vi
calc(1, _Vec, D0, Free, Ws) -> {1,D0,Free,Ws};
calc(0, _Vec, D0, Free, Ws) -> {0,D0,Free,Ws};
calc(Vi, Vec, D0, Free, Ws) ->
    %% io:format("calc: ~w\n", [Vi]),
    case lookup(Vi,D0) of
	error ->
	    {Vi,Xi,Bi,Ci} = element(Vi,Vec),
	    {Bj,D1,Free1,Ws1} = calc(Bi, Vec, D0, Free, Ws),
	    {Cj,D2,Free2,Ws2} = calc(Ci, Vec, D1, Free1, Ws1),
	    case lookup({Xi,Bj,Cj}, D2) of
		error ->
		    D3 = insert({Xi,Bj,Cj},Free2,D2),
		    D4 = insert(Vi,Free2,D3),
		    {Free2,D4,Free2+1,[{Free2,Xi,Bj,Cj}|Ws2]};
		{ok, Wi} ->
		    D3 = insert(Vi,Wi,D2),
		    {Wi,D3,Free2,Ws2}
	    end;
	{ok,Wi} ->
	    {Wi, D0, Free, Ws}
    end.

insert(A, B, Dict) ->
    %% io:format("~w => ~w\n", [A, B]),
    dict:store(A, B, Dict).

lookup(A, Dict) ->
    Res = dict:find(A, Dict),
    %% io:format("lookup ~p => ~p\n", [A, Res]),
    Res.

fetch(A, Dict) ->
    %% io:format("fetch: ~p\n", [A]),
    dict:fetch(A, Dict).


make_vector(Vs) ->
    list_to_tuple(fill_vector(1,lists:sort(Vs))).

fill_vector(Ai,[Vi={Ai,_Xi,_Bi,_Cj}|Vs]) ->
    [Vi | fill_vector(Ai+1,Vs)];
fill_vector(Ai,[Vj={Aj,_Xi,_Bi,_Cj}|Vs]) ->
    lists:duplicate((Aj - Ai), []) ++ 
	[Vj | fill_vector(Aj+1,Vs)];
fill_vector(_Ai,[]) -> [].

value(0, _Dict) -> 0;
value(1, _Dict) -> 1;
value(Ix, Dict) -> dict:fetch(Ix, Dict).

%%
%% Substitute and evaluate F [V/Vx] 
%%   
peval({'and',F1,F2}, V, Vx) ->
    case peval(F1, V, Vx) of
	1 -> peval(F2,V,Vx);
	0 -> 0;
	W1 ->
	    case peval(F2,V,Vx) of
		1 -> W1;
		0 -> 0;
		W2 -> {'and',W1,W2}
	    end
    end;
peval({'or',F1,F2}, V, Vx) ->
    case peval(F1, V, Vx) of
	0 -> peval(F2,V,Vx);
	1 -> 1;
	W1 ->
	    case peval(F2,V,Vx) of
		0 -> W1;
		1 -> 1;
		W2 -> {'or',W1,W2}
	    end
    end;
peval({'xor',F1,F2}, V, Vx) ->
    case peval(F1, V, Vx) of
	0 -> peval(F2,V,Vx);
	1 ->  peval({'not',F2},V,Vx);
	W1 ->
	    case peval(F2,V,Vx) of
		0 -> W1;
		1 -> {'not',W1};
		W2 -> {'xor',W1,W2}
	    end
    end;
peval({'not',F},V,Vx) ->
    case peval(F,V,Vx) of
	1 -> 0;
	0 -> 1;
	W -> {'not',W}
    end;
peval({var,V},V,Vx) -> Vx;
peval({var,W},_V,_Vx) -> {var,W};
peval(false,_,_) -> 0;
peval(true,_,_) -> 1.



%%
%% Extract all variables from F
%%
variables(F) ->
    vars(F,ordsets:new()).


vars({'and',F1,F2}, Set) ->  vars(F2, vars(F1,Set));
vars({'or',F1,F2}, Set)  ->  vars(F2, vars(F1,Set));
vars({'xor',F1,F2}, Set) ->  vars(F2, vars(F1,Set));
vars({'not',F},Set) -> vars(F,Set);
vars({var,X}, Set) -> ordsets:add_element(X, Set);
vars(true, Set) -> Set;
vars(false, Set) -> Set.




    
    
    

