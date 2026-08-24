%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2023, Tony Rogvall
%%% @doc
%%%    bit vectors builders
%%% @end
%%% Created :  6 Jan 2023 by Tony Rogvall <tony@rogvall.se>

-module(varp_bitvec).

-export([new/2]).
-export([from_unsigned/1, from_unsigned/2]).
-export([from_signed/1, from_signed/2]).
-export([from_bitstring/1, from_bitstring/2]).
-export([bitwise_not/2, bitwise_not/3]).
-export([bitwise_or/3, bitwise_or/4]).
-export([bitwise_and/3, bitwise_and/4]).
-export([bitwise_xor/3, bitwise_xor/4]).
-export([bitwise_equ/3, bitwise_equ/4]).
-export([bitwise1/3, bitwise1/4]).
-export([bitwise2/4, bitwise2/5]).
-export([foldl_op/4, foldr_op/4, fold_op/4, fold_op/5]).

-define(bool(Y), element((Y)+1,{false,true})).

%% construct bit vector from unsigned integer (msb first)
from_unsigned(X) when is_integer(X), X >= 0 ->
    from_unsigned_(X, varp_math:unsigned_size(X)).
from_unsigned(X, N) when is_integer(X), X >= 0, is_integer(N), N > 0 ->
    from_unsigned_(X, N).
from_unsigned_(X, N) ->
    {uint,N,lists:reverse([?bool(Y) || <<Y:1>> <= <<X:N>>])}.

%% construct bit vector from signed integer (msb first)
from_signed(X) when is_integer(X) ->
    from_signed_(X, varp_math:signed_size(X)).
from_signed(X, N) when is_integer(X), is_integer(N), N > 0 ->
    from_signed_(X, N).
from_signed_(X, N) ->
    {int,N,lists:reverse([?bool(Y) || <<Y:1>> <= <<X:N/signed>>])}.

from_bitstring(Bin) when is_bitstring(Bin) ->
    N = bit_size(Bin),
    {bit,N,lists:reverse([?bool(Y) || <<Y:1>> <= Bin])}.
from_bitstring(Bin,N) when is_bitstring(Bin), is_integer(N), N > 0 ->
    M = bit_size(Bin),
    if N =< M ->
	    K = M - N,
	    <<_:K,Bin1/bitstring>> = Bin,
	    Bits = [?bool(Y) || <<Y:1>> <= Bin1],
	    {bit,N,lists:reverse(Bits)};
       true ->
	    K = N - M,
	    Bits = [?bool(Y) || <<Y:1>> <= <<0:K,Bin/bitstring>>],
	    {bit,N,lists:reverse(Bits)}
    end.

new(Vp,N) when is_integer(N), N > 0 ->
    {First,Last} = varp_nif:add_variables(Vp, N, _IsAtom=true),
    lists:seq(First, Last).

bitwise_not(Vp, Ys) ->
    N = length(Ys),
    bitwise1(Vp,'not',new(Vp,N),Ys).

bitwise_not(Vp, Xs, Ys) ->
    bitwise1(Vp,'not',Xs,Ys).

bitwise_and(Vp, Ys, Zs) ->
    bitwise_and(Vp, undefined, Ys, Zs).

bitwise_and(Vp, undefined, Ys, Zs) when is_list(Ys), is_list(Zs) ->
    N = min(length(Ys), length(Zs)),
    bitwise2(Vp,'and',new(Vp,N),Ys,Zs);
bitwise_and(Vp, Xs, Ys, Zs) when is_list(Xs), is_list(Ys), is_list(Zs) ->
    bitwise2(Vp,'and',Xs,Ys,Zs).

bitwise_or(Vp, Ys, Zs) ->
    bitwise_or(Vp, undefined, Ys, Zs).
bitwise_or(Vp, undefined, Ys, Zs) when is_list(Ys), is_list(Zs) ->
    N = min(length(Ys), length(Zs)),
    bitwise2(Vp,'or',new(Vp,N),Ys,Zs);
bitwise_or(Vp,Xs,Ys,Zs) ->
    bitwise2(Vp,'or',Xs,Ys,Zs).

bitwise_xor(Vp, Ys, Zs) ->
    bitwise_xor(Vp, undefined, Ys, Zs).
bitwise_xor(Vp, undefined, Ys, Zs) when is_list(Ys), is_list(Zs) ->
    N = min(length(Ys), length(Zs)),
    bitwise2(Vp,'xor',new(Vp,N),Ys,Zs);    
bitwise_xor(Vp,Xs,Ys,Zs) ->
    bitwise2(Vp,'xor',Xs,Ys,Zs).

bitwise_equ(Vp, Ys, Zs) ->
    bitwise_equ(Vp, undefined, Ys, Zs).
bitwise_equ(Vp, undefined, Ys, Zs) when is_list(Ys), is_list(Zs) ->
    N = min(length(Ys), length(Zs)),
    bitwise2(Vp,'equ',new(Vp,N),Ys,Zs);    
bitwise_equ(Vp,Xs,Ys,Zs) ->
    bitwise2(Vp,'equ',Xs,Ys,Zs).

bitwise1(Vp,Op,Ys) when is_list(Ys) ->
    N = length(Ys),
    bitwise1(Vp,Op,new(Vp,N),Ys).

bitwise1(Vp,Op,Xs,Ys) when is_list(Xs), is_list(Ys) ->
    bitwise1_(Vp,Op,Xs,Ys,[]);
bitwise1(Vp,Op,Xs,Y)  when is_boolean(Y); is_integer(Y) ->
    bitwisey_(Vp,Op,Xs,Y,[]).

bitwise1_(Vp,Op,[X|Xs],[Y|Ys],As) ->
    A = varp_circuit:gate(Vp,Op,X,Y),
    bitwise1_(Vp,Op,Xs,Ys,[A|As]);
bitwise1_(_Vp,_Op,[],[],As) ->
    lists:reverse(As).

%% Apply same operator on two vectors
bitwise2(Vp,Op,Ys,Zs) when is_list(Ys), is_list(Zs) ->
    N = min(length(Ys), length(Zs)),
    bitwise2(Vp,Op,new(Vp,N),Ys,Zs);
bitwise2(Vp,Op,Ys,Z) when is_boolean(Z); is_integer(Z) ->
    bitwisez_(Vp,Op,Ys,Z,[]).

bitwise2(Vp,Op,Xs,Ys,Zs) when is_list(Xs), is_list(Ys), is_list(Zs) ->
    bitwise2_(Vp,Op,Xs,Ys,Zs,[]);
bitwise2(Vp,Op,Xs,Ys,Z)  when is_boolean(Z); is_integer(Z) ->
    bitwisez_(Vp,Op,Xs,Ys,Z,[]).

bitwise2_(Vp,Op,[X|Xs],[Y|Ys],[Z|Zs],As) ->
    A = varp_circuit:gate(Vp,Op,X,Y,Z),
    bitwise2_(Vp,Op,Xs,Ys,Zs,[A|As]);
bitwise2_(_Vp,_Op,[],[],[],As) ->
    lists:reverse(As).

%%map_op_(Vp,Op,[Y|Ys],[Z|Zs],Xs) ->
%%    X = varp_circuit:gate(Vp,Op,Y,Z),
%%    map_op_(Vp,Op,Ys,Zs,[X|Xs]);
%%map_op_(_Vp,_Op,[],[],Xs) ->
%%    lists:reverse(Xs).

bitwisez_(Vp,Op,[Y|Ys],Z,As) ->
    X = varp_circuit:gate(Vp,Op,Y,Z),
    bitwisez_(Vp,Op,Ys,Z,[X|As]);
bitwisez_(_Vp,_Op,[],_Z,As) ->
    lists:reverse(As).

bitwisez_(Vp,Op,[X|Xs],[Y|Ys],Z,As) ->
    X1 = varp_circuit:gate(Vp,Op,X,Y,Z),
    bitwisez_(Vp,Op,Xs,Ys,Z,[X1|As]);
bitwisez_(_Vp,_Op,[],[],_Z,As) ->
    lists:reverse(As).


bitwisey_(Vp,Op,[X|Xs],Y,As) ->
    X1 = varp_circuit:gate(Vp,Op,X,Y),
    bitwisey_(Vp,Op,Xs,Y,[X1|As]);
bitwisey_(_Vp,_Op,[],_Y,As) ->
    lists:reverse(As).

fold_op(Vp, Op, D, As) ->
    foldl_op(Vp, Op, D, As).

%% Fold operator Op over a variable vector
foldl_op(_Vp,_Op,D,[]) -> D;
foldl_op(Vp,Op,_D,[A|As]) -> foldl_op_(Vp,Op,A,As).

foldl_op_(Vp,Op,A1,[A2|As]) ->
    A = varp_circuit:gate(Vp,Op,A1,A2),
    %% io:format("~w = ~w ~s ~w\n", [A, A1, Op, A2]),
    foldl_op_(Vp,Op,A,As);
foldl_op_(_Vp,_Op,A,[]) ->
    A.

%% Fold operator Op over a variable vector
foldr_op(_Vp,_Op,D,[]) -> D;
foldr_op(_Vp,_Op,_D,[A]) -> A;
foldr_op(Vp,Op,_D,As) -> foldr_op_(Vp,Op,As).

foldr_op_(Vp,Op,[A1,A2]) ->    
    varp_circuit:gate(Vp,Op,A1,A2);
foldr_op_(Vp,Op,[A1|As]) ->
    A2 = foldr_op_(Vp,Op,As),
    varp_circuit:gate(Vp,Op,A1,A2).

%% Fold operator Op over a variable vector assign X
fold_op(Vp,Op,X,D,As) ->
    foldl_op(Vp,Op,X,D,As).

%% Fold operator Op over a variable vector
foldl_op(Vp,_Op,X,D,[]) -> varp_circuit:set(Vp,X,D);
foldl_op(Vp,_Op,X,_D,[A]) -> varp_circuit:set(Vp,X,A);
foldl_op(Vp,Op,X,_D,[A|As]) -> foldl_op_(Vp,Op,X,A,As).

foldl_op_(Vp,Op,X,A1,[A2]) ->
    varp_circuit:gate(Vp,Op,X,A1,A2);
foldl_op_(Vp,Op,X,A1,[A2|As]) ->
    A = varp_circuit:gate(Vp,Op,A1,A2),
    foldl_op_(Vp,Op,X,A,As).

