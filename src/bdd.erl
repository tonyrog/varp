%%% File    : bdd.erl
%%% Author  : Tony Rogvall <tony@iMac.local>
%%% Description : BDD implementation
%%% Created : 20 Jan 2006 by Tony Rogvall <tony@iMac.local>

-module(bdd).

-compile(export_all).

-import(lists, [reverse/1,map/2,member/2]).

satisfy(F) ->
    {R,_F,Vs} = construct(F),
    models(R, Vs, []).

models({R,_F,Vs}) ->
    models(R,Vs,[]).

models(R, Vs, Model) ->
    {_,V,E0,E1} = lists:keyfind(R,1,Vs),
    if E0 =:= 0 -> 0;
       E0 =:= 1 -> io:format("~w\n", [Model]),1;
       true -> models(E0,Vs,Model)
    end + 
    if E1 =:= 0 -> 0;
       E1 =:= 1 -> io:format("~w\n", [[V|Model]]),1;
       true -> models(E1,Vs,[V|Model])
    end.
    
%%
%% Construct a bbd from Formula F (see form:expand for forms)
%%
%% Return {Root,Free,Nodes}
%% Nodes = [{Vi,Var,E0,E1}]
%%
construct(F) ->
    construct_(form:expand(F)).

construct_(F) ->
    case form:variables(F) of
	[] ->
	    peval(F, undefined, undefined);
	Vs ->
	    construct_(lists:sort(Vs), F, 2)
    end.

construct_(_, 0, Free)     -> {0,Free,[]};
construct_(_, 1, Free)     -> {1,Free,[]};
construct_([V | Vs], F, Free) ->
    F0 = peval(F, V, 0),
    F1 = peval(F, V, 1),
    if F0 == 0, F1 == 0 -> {0,Free,[]};
       F0 == 1, F1 == 1 -> {1,Free,[]};
       true ->
	    {Ir0,Free1,Vs0} = construct_(Vs, F0, Free),
	    {Ir1,Free2,Vs1} = construct_(Vs, F1, Free1),
	    io:format("."),
	    Vs2 = [{Free2,V,Ir0,Ir1}]++Vs0++Vs1,
	    Res = {_R,_Free3,_Vs3} = reduce(Free2,Vs2,Free),
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
	{ok,_Wi} ->
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
peval(false,_,_) -> 0;
peval(true,_,_)  -> 1;
peval(V,V,Vx)    -> Vx;
peval(W={p,_,_},_V,_Vx) -> W;
peval({'&&',F1,F2}, V, Vx) -> peval({'and',F1,F2}, V, Vx);
peval({'||',F1,F2}, V, Vx) -> peval({'or',F1,F2}, V, Vx);
peval({'->',F1,F2}, V, Vx) -> peval({'or',{'not',F1},F2}, V, Vx);
peval({'<->',F1,F2}, V, Vx) -> peval({'not',{'xor',F1,F2}}, V, Vx);
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
peval({all,[]},_V,_Vx) -> 1;
peval({all,[F]},V,Vx) -> peval(F,V,Vx);
peval({all,[F|Fs]},V,Vx) ->
    case peval(F, V, Vx) of
	1 -> peval({all,Fs},V,Vx);
	0 -> 0;
	W1 ->
	    case peval({all,Fs},V,Vx) of
		1 -> W1;
		0 -> 0;
		W2 -> {'and',W1,W2}
	    end
    end;
peval({any,[]},_V,_Vx) -> 0;
peval({any,[F]},V,Vx) -> peval(F,V,Vx);
peval({any,[F|Fs]}, V, Vx) ->
    case peval(F, V, Vx) of
	0 -> peval({any,Fs},V,Vx);
	1 -> 1;
	W1 ->
	    case peval({any,Fs},V,Vx) of
		0 -> W1;
		1 -> 1;
		W2 -> {'or',W1,W2}
	    end
    end;
peval({none,[]},_V,_Vx) -> 1;
peval({none,[F]},V,Vx) -> peval({'not',F},V,Vx);
peval({none,[F|Fs]}, V, Vx) ->
    case peval(F, V, Vx) of
	0 -> peval({none,Fs},V,Vx);
	1 -> 0;
	W1 ->
	    case peval({none,Fs},V,Vx) of
		0 -> 0;
		1 -> {'not',W1};
		W2 -> {'and',{'not',W1},W2}
	    end
    end;


peval({one,[]},_V,_Vx) -> 0;
peval({one,[F]},V,Vx) -> peval(F,V,Vx);
peval({one,[F|Fs]},V,Vx) ->
    case peval(F, V, Vx) of
	0 -> peval({one,Fs},V,Vx);
	1 -> peval({none,Fs},V,Vx);
	W1 ->
	    case peval({one,Fs},V,Vx) of
		0 -> {'and',W1,peval({none,Fs},V,Vx)};
		1 -> {'not',W1};
		W2 -> 
		    W3 = peval({none,Fs},V,Vx),
		    {'or',
		     {'and',W2,{'not',W1}},
		     {'and',{'not',W2},{'and',W1,W3}}}
	    end
    end.
