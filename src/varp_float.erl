%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2026, Tony Rogvall
%%% @doc
%%%    IEEE 754 numbers as bits, the pure part: the formats, encoding
%%%    a number with round to nearest even, decoding and printing.
%%%    A format is {E,M}: a sign bit, E exponent bits and M fraction
%%%    bits, float754(32) is {8,23}.  Light semantics: normal numbers
%%%    and zero; a number below the normal range is flushed to zero,
%%%    one above it is an error, NaN does not exist.  The circuits are
%%%    in varp_formula (the float754 section).
%%% @end
-module(varp_float).

-export([standard/1, bias/1, type_atom/2, type_of_atom/1]).
-export([encode/3, encode_scaled/4]).
-export([fields/3, value/3, to_float/3, format/3, exact_decimal/2]).

%% the standard sizes
standard(16) -> {5,10};
standard(32) -> {8,23};
standard(64) -> {11,52};
standard(128) -> {15,112};
standard(N) -> error({float754_size, N}).

bias(E) -> (1 bsl (E-1)) - 1.

%% the symbol table atom of a format, f8_23
type_atom(E, M) ->
    list_to_atom("f" ++ integer_to_list(E) ++ "_" ++ integer_to_list(M)).

%% back from the atom: {float,E,M}, {fix,F} or undefined
type_of_atom(A) when is_atom(A) ->
    try
	case atom_to_list(A) of
	    "fix" ++ Ds -> {fix, list_to_integer(Ds)};
	    [$f|Rest] ->
		[Es,Ms] = string:split(Rest, "_"),
		{float, list_to_integer(Es), list_to_integer(Ms)};
	    _ -> undefined
	end
    catch
	error:_ -> undefined
    end.

%%--------------------------------------------------------------------
%% encode
%%--------------------------------------------------------------------

%% a float or an integer as the bits of the format, round to nearest
%% even; {error,{float754_range,..}} above the normal range
encode(V, E, M) when is_integer(V) ->
    encode_scaled(V, 0, E, M);
encode(V, E, M) when is_float(V) ->
    <<S:1,Eb:11,Mb:52>> = <<V:64/float>>,
    if Eb =:= 0, Mb =:= 0 ->
	    {ok, S bsl (E+M)};                      %% a signed zero
       Eb =:= 0 ->
	    encode_(S, Mb, -1074, E, M);            %% a subnormal double
       Eb =:= 2047 ->
	    {error, {float754_not_a_number, V}};
       true ->
	    encode_(S, (1 bsl 52) bor Mb, Eb - 1075, E, M)
    end.

%% the exact value I * 2^Shift, I an integer of any size
encode_scaled(I, Shift, E, M) when I < 0 ->
    encode_(1, -I, Shift, E, M);
encode_scaled(I, Shift, E, M) ->
    encode_(0, I, Shift, E, M).

encode_(_S, 0, _Shift, _E, _M) ->
    {ok, 0};
encode_(S, A, Shift, E, M) ->
    L = bit_length(A),              %% the leading one is bit L-1
    Exp = L - 1 + Shift,            %% the unbiased exponent
    {Sig, Exp1} = round_to(A, L, M, Exp),
    Eb = Exp1 + bias(E),
    if Eb =< 0 ->
	    {ok, S bsl (E+M)};         %% below the normal range: zero
       Eb >= (1 bsl E) - 1 ->
	    {error, {float754_range, {E,M}, {S,A,Shift}}};
       true ->
	    {ok, (S bsl (E+M)) bor (Eb bsl M) bor (Sig band ((1 bsl M)-1))}
    end.

%% A with its leading one at bit L-1 as an M+1 bit significand, round
%% to nearest even; the exponent moves up when the rounding carries out
round_to(A, L, M, Exp) when L =< M+1 ->
    {A bsl (M+1-L), Exp};
round_to(A, L, M, Exp) ->
    Drop = L - (M+1),
    Q = A bsr Drop,
    R = A band ((1 bsl Drop) - 1),
    Half = 1 bsl (Drop-1),
    Q1 = if R > Half -> Q+1;
	    R =:= Half -> Q + (Q band 1);
	    true -> Q
	 end,
    if Q1 =:= (1 bsl (M+1)) -> {Q1 bsr 1, Exp+1};
       true -> {Q1, Exp}
    end.

bit_length(0) -> 0;
bit_length(A) -> 1 + bit_length(A bsr 1).

%%--------------------------------------------------------------------
%% decode
%%--------------------------------------------------------------------

%% {Sign, BiasedExponent, Fraction}
fields(Bits, E, M) ->
    {(Bits bsr (E+M)) band 1, (Bits bsr M) band ((1 bsl E)-1),
     Bits band ((1 bsl M)-1)}.

%% the exact value: {zero,S} | {inf,S} | nan | {S,Int,Shift} for
%% Int * 2^Shift.  A subnormal pattern reads as its IEEE value.
value(Bits, E, M) ->
    {S, Eb, Mb} = fields(Bits, E, M),
    Max = (1 bsl E) - 1,
    if Eb =:= 0, Mb =:= 0 -> {zero, S};
       Eb =:= 0 -> {S, Mb, 1 - bias(E) - M};
       Eb =:= Max, Mb =:= 0 -> {inf, S};
       Eb =:= Max -> nan;
       true -> {S, (1 bsl M) bor Mb, Eb - bias(E) - M}
    end.

%% as an Erlang float (the tests compare with it), light: a pattern
%% with every exponent bit set is a number like any other
to_float(Bits, E, M) ->
    {S0, Eb, Mb} = fields(Bits, E, M),
    Light = if Eb =:= (1 bsl E) - 1 -> {S0, (1 bsl M) bor Mb, Eb - bias(E) - M};
	       true -> value(Bits, E, M)
	    end,
    case Light of
	{zero,0} -> 0.0;
	{zero,1} -> -0.0;
	{S,I,Sh} ->
	    F = if Sh >= 0 -> (I bsl Sh) * 1.0;
		   true -> I / (1 bsl -Sh)
		end,
	    if S =:= 1 -> -F; true -> F end
    end.

%%--------------------------------------------------------------------
%% print
%%--------------------------------------------------------------------

%% the shortest decimal that reads back as the same bits for the
%% standard formats, the exact value for the others
format(Bits, E, M) ->
    case value(Bits, E, M) of
	{zero,0} -> "0.0";
	{zero,1} -> "-0.0";
	{inf,0} -> "inf";
	{inf,1} -> "-inf";
	nan -> "nan";
	{S,I,Sh} ->
	    Sign = if S =:= 1 -> "-"; true -> "" end,
	    case {E,M} of
		{11,52} ->
		    <<F:64/float>> = <<Bits:64>>,
		    float_to_list(F, [short]);
		{8,23} ->
		    <<F:32/float>> = <<Bits:32>>,
		    Sign ++ shortest(erlang:abs(F), Bits band 16#7fffffff, E, M);
		{5,10} ->
		    <<F:16/float>> = <<Bits:16>>,
		    Sign ++ shortest(erlang:abs(F), Bits band 16#7fff, E, M);
		_ when Sh >= 0 ->
		    Sign ++ integer_to_list(I bsl Sh) ++ ".0";
		_ ->
		    Sign ++ exact_decimal(I, -Sh)
	    end
    end.

%% the fewest significant digits that encode back to Bits (F is the
%% magnitude as a double, which is exact for the small formats)
shortest(F, Bits, E, M) ->
    shortest(F, Bits, E, M, 0).

shortest(F, Bits, E, M, P) when P =< 17 ->
    Str = with_point(float_to_list(F, [{scientific,P}])),
    case encode(list_to_float(Str), E, M) of
	{ok,Bits} -> plain(Str);
	_ -> shortest(F, Bits, E, M, P+1)
    end;
shortest(F, _Bits, _E, _M, _P) ->
    float_to_list(F, [short]).

%% "2e+00" -> "2.0e+00": list_to_float wants the point
with_point(Str) ->
    case lists:member($., Str) of
	true -> Str;
	false ->
	    [Mant,Exp] = string:split(Str, "e"),
	    Mant ++ ".0e" ++ Exp
    end.

%% "1.5e+02" -> "150.0" when the exponent is moderate
plain(Str) ->
    [Mant,ExpS] = string:split(Str, "e"),
    Exp = list_to_integer(ExpS),
    Digits = [C || C <- Mant, C =/= $.],
    if Exp < -4; Exp > 15 ->
	    %% like float_to_list(F, [short]): 3.0e38, 1.0e-30
	    Mant ++ "e" ++ integer_to_list(Exp);
       true ->
	    %% the point after the first digit moves Exp steps
	    Point = 1 + Exp,
	    Ds = if Point > length(Digits) ->
			 Digits ++ lists:duplicate(Point - length(Digits), $0);
		    true -> Digits
		 end,
	    {Int,Frac0} = if Point =< 0 ->
				  {"0", lists:duplicate(-Point, $0) ++ Ds};
			     true ->
				  lists:split(Point, Ds)
			  end,
	    Frac = case string:trim(Frac0, trailing, "0") of
		       "" -> "0";
		       Fr -> Fr
		   end,
	    Int ++ "." ++ Frac
    end.

%% I / 2^K as an exact decimal, 2^K divides 10^K
exact_decimal(I, K) ->
    Scale = 1 bsl K,
    Int = I div Scale,
    Frac = I rem Scale,
    Digits = if Frac =:= 0 -> "0";
		true ->
		    D = Frac * varp_math:pow(10, K) div Scale,
		    Ds = lists:flatten(io_lib:format("~*..0w", [K, D])),
		    string:trim(Ds, trailing, "0")
	     end,
    integer_to_list(Int) ++ "." ++ Digits.
