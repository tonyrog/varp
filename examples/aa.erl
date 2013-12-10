%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2012, Tony Rogvall
%%% @doc
%%%    aa all and any forms
%%% @end
%%% Created :  5 Sep 2012 by Tony Rogvall <tony@rogvall.se>

-module(aa).

-export([rewrite/1]).
-compile(export_all).

-import(lists, [map/2,reverse/1]).

rewrite(F) ->
    b(F,[]).

%%
%% Rewrite a formula into an all and any form (+ one equ form)
%% meaning that we translate all expression
%% into multi-leveled clause form containing 
%%
%% xi = {all,[y1,...,yn]}
%% xj = {any,[z1,...,zm]}
%% xk = {equ,[t1,t2]}  ?..tn
%% where x1 ... xn are literals (integer)
%%
b(A,_Bs) when is_atom(A) -> A;
b({var,A},Bs) -> {var,expand_meta(A,Bs)};
b({'not',A},Bs) -> c('not',b(A,Bs));
b({'and',A,B},Bs) -> c('and',b(A,Bs),b(B,Bs));
b({'or',A,B},Bs)  -> c('or',b(A,Bs),b(B,Bs));
b({'equ',A,B},Bs) -> c('equ',b(A,Bs),b(B,Bs));
b({'xor',A,B},Bs) -> b({'not',{'equ',A,B}},Bs);
b({'imp',A,B},Bs) -> b({'or',{'not',A},B},Bs);
b({'all',As},Bs)    -> c('all',map(fun (Ai) -> b(Ai,Bs) end, As));
b({'any',As},Bs)    -> c('any',map(fun (Ai) -> b(Ai,Bs) end, As));
b({{all,[{'=',X,{range,A,B}}]},F}, Bs) 
  when is_integer(A), is_integer(B), A=<B ->
    c('all', bs(F,X,lists:seq(A,B,1),[],Bs));
b({{any,[{'=',X,{range,A,B}}]},F}, Bs) 
  when is_integer(A), is_integer(B), A=<B ->
    c('any', bs(F,X,lists:seq(A,B,1),[],Bs)).

bs(F,X,[Xi|Xs],Acc,Bs) ->
    bs(F,X,Xs,[b(F,[{X,Xi}|Bs])|Acc],Bs);
bs(_F,_X,[],Acc,_Bs) ->
    reverse(Acc).


c('and',{all,Xs},{all,Ys}) -> {all,Xs++Ys};
c('and',{all,Xs},B) -> {all,Xs++[B]};
c('and',A,{all,Ys}) -> {all,[A]++Ys};
c('and',A,B) -> {all,[A,B]};

c('or',{any,Xs},{any,Ys}) -> {any,Xs++Ys};
c('or',{any,Xs},B) -> {any,Xs++[B]};
c('or',A,{any,Ys}) -> {any,[A]++Ys};
c('or',A,B) -> {any,[A,B]};

c('equ',A,B) -> {'equ',A,B}.

c('not',{all,As})  -> {any,map(fun (Ai) -> c('not',Ai) end, As)};
c('not',{any,As})  -> {all,map(fun (Ai) -> c('not',Ai) end, As)};
c('not',{equ,A,B}) -> {equ,c('not',A),B};
c('not',{'not',A}) -> A;
c('not',{var,A}) -> {'not',{var,A}};
c('not',A) when is_atom(A) -> {'not',A};
c('all',As) -> cs('all',As,[]);
c('any',As) -> cs('any',As,[]).

cs(C,[{C,Xs}|As],Acc) -> cs(C,As,Acc++Xs);
cs(C,[X|As],Acc) ->  cs(C,As,Acc++[X]);
cs(C,[],Acc) -> {C,Acc}.

%%
%%  {q,x,y} => {q,meta(x),meta(y)}
%%
expand_meta(T,Bs) when is_tuple(T) ->
    [P|Vs] = tuple_to_list(T),
    list_to_tuple(
      [P| map(
	    fun(V) ->
		    case lists:keyfind(V,1,Bs) of
			false -> V;
			{_,W} -> W
		    end
	    end, Vs)]);
expand_meta(V,_Bs) -> V.
