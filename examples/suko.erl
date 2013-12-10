%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2011, Tony Rogvall
%%% @doc
%%%   Suko solver
%%% @end
%%% Created : 26 Aug 2011 by Tony Rogvall <tony@rogvall.se>

-module(suko).

-compile(export_all).
%%
%%   Solve Pussel grid
%%   A, B, C
%%   D, E, F
%%   G, H, I
%%
%%   Given that:
%%      A+B+D+E = K1
%%      B+C+E+F = K2
%%      D+E+G+H = K3
%%      E+F+H+I = K4
%%
%%   Extra condition:
%%      A+B+D   = K5
%%      C+E+F+I = K6
%%      G+H     = K7
%%      1 <= A,B,C,D,E,F,G,H,I <= 9
%%      A != B != C != D != E != F != G != H != I (uniq)
%%


solve(F) ->
    varp:satisfy(F).

between(X, N, K1, K2) when K1 =< K2 ->
    {'and', {'>=',X,{uint,N,K1}},{'<=',X,{uint,N,K2}}}.

formula(Ks) ->
    N = 6,
    A = {uint,N,a},
    B = {uint,N,b},
    C = {uint,N,c},
    D = {uint,N,d},
    E = {uint,N,e},
    F = {uint,N,f},
    G = {uint,N,g},
    H = {uint,N,h},
    I = {uint,N,i},
    Vs = [A,B,C,D,E,F,G,H,I],
    %% Square sums
    X1 = {'+',{'+',A,B},{'+',D,E}},
    X2 = {'+',{'+',B,C},{'+',E,F}},
    X3 = {'+',{'+',D,E},{'+',G,H}},
    X4 = {'+',{'+',E,F},{'+',H,I}},
    %% Extra conditions
    X5 = {'+',{'+',A,B},D},
    X6 = {'+',{'+',C,E},{'+',F,I}},
    X7 = {'+',G,H},

    Xs = [X1,X2,X3,X4,X5,X6,X7],
    {all,  
     %% equations
     [{'==', X, {uint,N,K}} || {X,K} <- lists:zip(Xs, Ks)] ++
	 %% All variables in range 1..9
	 [between(V,N,1,9) || V <- Vs] ++   
	 %% All variables have different values
	 [{'!=', X, Y} || X <- Vs, Y <- Vs, X < Y] ++
	 [] }.

test1() ->
    F = formula([18,22,24,14,14,18,13]),
    solve(F).

test2() ->
    F = formula([17,23,19,23,13,24,8]),
    solve(F).



    

