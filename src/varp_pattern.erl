%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2026, Tony Rogvall
%%% @doc
%%%    Patterns of partly known bytes, for input modules and partial
%%%    models.
%%%
%%%    A text pattern is a string where `*' (or `_') is an unknown
%%%    byte: "hello*world".  A hex pattern is a string of hex digits
%%%    where `*' is an unknown nibble: "5eb6****e01e".  Both parse to
%%%    lists of known values and the atom free.
%%%
%%%    The other way, a model's bit vector (a tuple of $0, $1 and $*
%%%    for an unbound bit, most significant first) formats as hex with
%%%    `*' for a nibble that is not fully known, or as text with `*'
%%%    for a byte that is not.
%%% @end
-module(varp_pattern).

-export([text/1, hex/1]).
-export([format_hex/1, format_text/1]).
-export([bit_values/1]).

%% "hello*world" -> [104,101,...,free,...]
text(Pattern) when is_binary(Pattern) -> text(binary_to_list(Pattern));
text(Pattern) when is_list(Pattern) ->
    [case C of
	 $* -> free;
	 $_ -> free;
	 _ -> C
     end || C <- Pattern].

%% "5eb6**e0" -> {ok,[5,14,11,6,free,free,14,0]} | {error,Reason}
hex(Pattern) when is_binary(Pattern) -> hex(binary_to_list(Pattern));
hex(Pattern) when is_list(Pattern) ->
    try {ok, [nibble(C) || C <- Pattern]}
    catch throw:Reason -> {error, Reason}
    end.

nibble($*) -> free;
nibble($_) -> free;
nibble(C) when C >= $0, C =< $9 -> C - $0;
nibble(C) when C >= $a, C =< $f -> C - $a + 10;
nibble(C) when C >= $A, C =< $F -> C - $A + 10;
nibble(C) -> throw({not_hex, [C]}).

%% the bits of a model vector as integers, unknown ones as free
bit_values(Bits) when is_tuple(Bits) ->
    [case B of $0 -> 0; $1 -> 1; _ -> free end || B <- tuple_to_list(Bits)].

%% a vector as hex, most significant nibble first; a nibble with an
%% unknown bit is *
format_hex(Bits) when is_tuple(Bits) ->
    Vs = bit_values(Bits),
    Pad = (4 - length(Vs) rem 4) rem 4,
    [nibble_char(N) || N <- groups(lists:duplicate(Pad, 0) ++ Vs, 4)].

nibble_char(Bs) ->
    case lists:member(free, Bs) of
	true -> $*;
	false -> element(1+lists:foldl(fun(B,A) -> A*2+B end, 0, Bs),
			 {$0,$1,$2,$3,$4,$5,$6,$7,$8,$9,$a,$b,$c,$d,$e,$f})
    end.

%% a vector as text, most significant byte first; a byte with an
%% unknown bit is *, one that does not print is \xNN
format_text(Bits) when is_tuple(Bits) ->
    Vs = bit_values(Bits),
    Pad = (8 - length(Vs) rem 8) rem 8,
    lists:append([byte_chars(B) || B <- groups(lists:duplicate(Pad, 0) ++ Vs, 8)]).

byte_chars(Bs) ->
    case lists:member(free, Bs) of
	true -> "*";
	false ->
	    V = lists:foldl(fun(B,A) -> A*2+B end, 0, Bs),
	    if V >= 32, V < 127, V =/= $* -> [V];
	       true -> io_lib:format("\\x~2.16.0b", [V])
	    end
    end.

groups([], _N) -> [];
groups(L, N) ->
    {G, Rest} = lists:split(min(N, length(L)), L),
    [G | groups(Rest, N)].
