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
-export([bitwise_not/2]).
-export([bitwise_or/3]).
-export([bitwise_and/3]).
-export([bitwise_xor/3]).
-export([map_op/4]).
-export([foldl_op/4, foldr_op/4, fold_op/4]).

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
    {First,Last} = varp_nif:add_variables(Vp, N, _IsAtom=true, _IsUsed=true),
    lists:seq(First, Last).

bitwise_not(_Vp, Ys) ->
    [varp_circuit:inv(Yi) || Yi <- Ys].

bitwise_and(Vp, [Y|Ys], [Z|Zs]) ->
    X = varp_circuit:and_gate(Vp, Y, Z),
    [X | bitwise_and(Vp, Ys, Zs)];
bitwise_and(_Vp, [], []) ->
    [].

bitwise_or(Vp, [Y|Ys], [Z|Zs]) ->
    X = varp_circuit:or_gate(Vp, Y, Z),
    [X | bitwise_or(Vp, Ys, Zs)];
bitwise_or(_Vp, [], []) ->
    [].

bitwise_xor(Vp, [Y|Ys], [Z|Zs]) ->
    X = varp_circuit:xor_gate(Vp, Y, Z),
    [X | bitwise_xor(Vp, Ys, Zs)];
bitwise_xor(_Vp, [], []) ->
    [].

%% Apply same operator on two vectors
map_op(Vp,Op,Ys,Zs) when is_list(Zs) ->
    map_op_(Vp,Op,Ys,Zs,[]);
map_op(Vp,Op,Ys,Z) when is_boolean(Z); is_integer(Z) ->
    map_opz_(Vp,Op,Ys,Z,[]).

map_op_(Vp,Op,[Y|Ys],[Z|Zs],Xs) ->
    X = varp_circuit:gate(Vp,Op,Y,Z),
    map_op_(Vp,Op,Ys,Zs,[X|Xs]);
map_op_(_Vp,_Op,[],[],Xs) ->
    lists:reverse(Xs).

map_opz_(Vp,Op,[Y|Ys],Z,Xs) ->
    X = varp_circuit:gate(Vp,Op,Y,Z),
    map_opz_(Vp,Op,Ys,Z,[X|Xs]);
map_opz_(_Vp,_Op,[],_Z,Xs) ->
    lists:reverse(Xs).

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
