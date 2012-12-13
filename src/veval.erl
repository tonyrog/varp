%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2012, Tony Rogvall
%%% @doc
%%%    Evaluate
%%% @end
%%% Created :  4 Dec 2012 by Tony Rogvall <tony@rogvall.se>

-module(veval).

-compile(export_all).

%%
%% Ex F(x,x1...xn) == F(F(1,x1...xn),x1...xn)
%% Ax F(x,x1...xn) == F(F(0,x1...xn),x1...xn)
%%
%%

%% Compute canonical valuation for F with N variables
valuation(F, N) when is_integer(N) ->
    valuation(F, lists:duplicate(N, true));  %% Ex1 Ex2 ... Exn
valuation(F,Ns) when is_list(Ns) ->
    N = length(Ns),
    eval(F,0,(1 bsl N)-1,Ns,array:new()).

eval(F,I,M,Ns,R) when I < M ->
    V = apply(F, [as(I,Ns,R)]),
    eval(F,I+1,M,Ns,array:set(I,V,R));
eval(F,I,M,Ns,R) when I =:= M ->
    Ax = as(I,Ns,R),
    V = apply(F, [Ax]),
    {V, Ax}.

%% Arguments when calculating Rj  N are number of variables
%%
%% a(i+1) = true                 when j & 2^i == 0
%% a(i+1) = r(j & ~((2^i)-1)-1)  otherwise
%%
%%

as(_J,[],_R) -> 
    [];
as(J,[V|Ns],R) ->
    N = length(Ns),
    B = (1 bsl N),
    if J band B =:= 0 ->
	    [V | as(J,Ns,R)];
       true ->
	    R1 = J band (bnot (B-1)),
	    Ri = array:get(R1-1, R), %% {r,R1-1},
	    [Ri | as(J,Ns,R)]
    end.

%%
%% pigeon
%%

pigeon_2([P11,P21]) ->
    (P11 and P21) and (not (P11 and P21)).

pigeon_3([P11,P12,P21,P22,P31,P32]) ->
    (P11 or P12) 
	and
    (P21 or P22)
	and
    (P31 or P32)
	and
        (not (P11 and P21)) and
	(not (P11 and P31)) and
	(not (P21 and P31)) and
	(not (P12 and P22)) and
	(not (P12 and P32)) and
	(not (P22 and P32)).

%%
%% Ax1Ey1Ax2Ey2...AxnEyn((x1+y1) & (x2+y2) &...& (xn+yn)) är sann
%%
x1_test(N) ->
    valuation(fun x1/1, lists:append(lists:duplicate(N, [false,true]))).

x1([Xi,Yi|XYs]) -> (Xi xor Yi) and x1(XYs);
x1([]) -> true.

%%
%% Ax1Ey1Ax2Ey2...AxnEynEQn(x1...xn, y1...yn)  
%%    är sann och borde vara svår för alla lösare.
%%
x2_test(N) ->
    valuation(fun (XYs) ->
		      bool_sum(XYs,0) =:= N
	      end, lists:append(lists:duplicate(N, [false,true]))).


%%
%% Ex1Ay1Ex2Ay2...ExnAyn((x1+y1) & (x2+y2) &...& (xn+yn)) är falsk.
%%
x3_test(N) ->
    valuation(fun x3/1, lists:append(lists:duplicate(N, [true,false]))).

x3([Xi,Yi|XYs]) -> (Xi xor Yi) and x3(XYs);
x3([]) -> true.

%%
%% Ex1Ay1Ex2Ay2...ExnAyn((x1 v y1) & (x2 v y2) &...& (xn v yn)) är sann.
%%
x4_test(N) ->
    valuation(fun x4/1, lists:append(lists:duplicate(N, [true,false]))).

x4([Xi,Yi|XYs]) -> (Xi or Yi) and x4(XYs);
x4([]) -> true.


bool_sum([true|Xs],I) -> bool_sum(Xs,1+I);
bool_sum([false|Xs],I) -> bool_sum(Xs,I);
bool_sum([],I) -> I.
