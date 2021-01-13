%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2013, Tony Rogvall
%%% @doc
%%%    integer math stuff used by varp
%%% @end
%%% Created : 10 Dec 2013 by Tony Rogvall <tony@rogvall.se>

-module(varp_math).

-export([factorial/1]).
-export([binom/2]).
-export([pow/2]).
-export([ilog2/1]).
-export([signed_size/1]).
-export([unsigned_size/1]).
-export([isqrt/1]).
-export([nroot/2]).

factorial(0) -> 1;
factorial(N) when N > 0 -> 
    fac_(N, 1).

fac_(1, X) -> X;
fac_(N, X) -> fac_(N-1, X*N).


binom(N,K) when is_integer(N),is_integer(K),N>=0,K>=0 ->
    if N < K -> 0;
       true -> binom_(N, min(K, N-K), 0, 1)
    end.

binom_(_N, K, I, P) when I >= K -> P;
binom_(N, K, I, P) -> 
    binom_(N, K, I+1, ((N-I)*P) div (I+1)).

pow(A, B) when is_integer(A), is_integer(B), B >= 0 ->
    if A == 1 ->  1;
       true -> pow_(A, B, 1)
    end.

pow_(A, 1, Prod) ->
    A*Prod;
pow_(_A, 0, Prod) ->
    Prod;
pow_(A, B, Prod)  ->
    B1 = B bsr 1,
    A1 = A*A,
    if B - B1 == B1 ->
	    pow_(A1, B1, Prod);
       true ->
	    pow_(A1, B1, (A*Prod))
    end.

ilog2(N) when is_integer(N), N>0 ->
    unsigned_size(N)-1.
    
%% smallest number of bits needed to represent a
%% signed integer X (including sign bit)
signed_size(X) when is_integer(X) ->
    if X < 0 -> unsigned_size(-X - 1)+1;
       true -> unsigned_size(X)+1
    end.

%% smallest number of bits needed to represent an
%% unsigned integer X

unsigned_size(X) when is_integer(X), X >= 0 ->
    size_(X).

size_(0) ->
    1;
size_(X) when is_integer(X), X > 0 ->
    size32_(X,0).

size32_(X, I) ->
    if X > 16#FFFFFFFF -> size32_(X bsr 32, I+32);
       true -> size8_(X, I)
    end.

size8_(X, I) ->
    if X > 16#FF -> size8_(X bsr 8, I+8);
       X >= 2#10000000 -> I+8;
       X >= 2#1000000 -> I+7;
       X >= 2#100000 -> I+6;
       X >= 2#10000 -> I+5;
       X >= 2#1000 -> I+4;
       X >= 2#100 -> I+3;
       X >= 2#10 -> I+2;
       X >= 2#1 -> I+1;
       true -> I
    end.

%%
%% Integer square root
%%
%%  Xk+1 = (1/2)(Xk + A/Xk)
%%  using X0 = A / 2
%%

isqrt(0) -> 0;
isqrt(1) -> 1;
isqrt(A) when is_integer(A), A >= 2 ->
    X0 = A div 2,
    isqrt_(A div X0, X0, A).

isqrt_(Ak,Xk,A) when Ak < Xk ->
    Xk1 = (Xk+Ak) div 2,
    isqrt_(A div Xk1, Xk1, A);
isqrt_(_, Xk, _) -> Xk.

%%
%% integer nth root  A^(1/N)
%%
%%    Xk+1 = (1/N)*((N-1)*Xk + A/(Xk^N-1))
%%
nroot(0,_N) -> 0;
nroot(1,_N) -> 1;
nroot(X,1) -> X;
nroot(A,2) -> isqrt(A);
nroot(A,N) when N > 0 ->
    X0 = A div 2, 
    nroot(A div pow(X0,N-1), X0, A, N).

nroot(Ak,Xk,A,N) when Ak < Xk ->
    Xk1 = ((N-1)*Xk+Ak) div N,
    nroot(A div pow(Xk1, N-1), Xk1, A, N);
nroot(_, Xk, _A, _N) -> 
    Xk.
