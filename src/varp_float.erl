%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2026, Tony Rogvall
%%% @doc
%%%    IEEE 754 numbers as bits, the pure part: the formats, encoding
%%%    a number with round to nearest even, decoding and printing.
%%%    A format is {E,M}: a sign bit, E exponent bits and M fraction
%%%    bits, float754(32) is {8,23}.  Two modes: ieee rounds a number
%%%    below the normal range to a subnormal (gradual underflow), ftz
%%%    (light, flush to zero) makes it zero; a number above the range
%%%    is an error when it is a literal and inf when it is a result.
%%%    The circuits are in varp_formula (the float754 section).
%%% @end
-module(varp_float).

-export([standard/1, bias/1, type_atom/2, type_of_atom/1]).
-export([encode/3, encode/4, encode_scaled/4, encode_scaled/5, encode_status/5]).
-export([fields/3, value/3, light_value/3, to_float/3, format/3, exact_decimal/2]).
-export([mul_bits/4, add_bits/4, div_bits/4, inf_bits/3, nan_bits/2]).
-export([mul_bits/5, add_bits/5, div_bits/5]).
-export([mul_fold/5, add_fold/5, div_fold/5]).

-type mode() :: ieee | ftz.

%% the standard sizes; 8 is E5M2, the one that follows the IEEE rules
%% (E4M3 has no inf and one NaN: float754(3) for its bits, read as
%% IEEE does)
standard(8) -> {5,2};
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
encode(V, E, M) ->
    encode(V, E, M, ieee).

-spec encode(number(), integer(), integer(), mode()) ->
	  {ok, integer()} | {error, term()}.
encode(V, E, M, Mode) when is_integer(V) ->
    encode_scaled(V, 0, E, M, Mode);
encode(V, E, M, Mode) when is_float(V) ->
    <<S:1,Eb:11,Mb:52>> = <<V:64/float>>,
    if Eb =:= 0, Mb =:= 0 ->
	    {ok, S bsl (E+M)};                      %% a signed zero
       Eb =:= 0 ->
	    strip(encode_(S, Mb, -1074, E, M, Mode)); %% a subnormal double
       Eb =:= 2047 ->
	    {error, {float754_not_a_number, V}};
       true ->
	    strip(encode_(S, (1 bsl 52) bor Mb, Eb - 1075, E, M, Mode))
    end.

strip({ok, Bits, _Underflow}) -> {ok, Bits};
strip(Error) -> Error.

%% the exact value I * 2^Shift, I an integer of any size
encode_scaled(I, Shift, E, M) ->
    encode_scaled(I, Shift, E, M, ieee).

encode_scaled(I, Shift, E, M, Mode) ->
    strip(encode_status(I, Shift, E, M, Mode)).

%% {ok, Bits, Underflow}: Underflow is true when the value is tiny
%% (below the normal range before rounding) and the bits do not hold it
%% exactly, the IEEE underflow exception; in ftz every tiny nonzero
-spec encode_status(integer(), integer(), integer(), integer(), mode()) ->
	  {ok, integer(), boolean()} | {error, term()}.
encode_status(I, Shift, E, M, Mode) when I < 0 ->
    encode_(1, -I, Shift, E, M, Mode);
encode_status(I, Shift, E, M, Mode) ->
    encode_(0, I, Shift, E, M, Mode).

encode_(_S, 0, _Shift, _E, _M, _Mode) ->
    {ok, 0, false};
encode_(S, A, Shift, E, M, Mode) ->
    L = bit_length(A),              %% the leading one is bit L-1
    Exp = L - 1 + Shift,            %% the unbiased exponent
    Eb0 = Exp + bias(E),
    if Eb0 =< 0, Mode =:= ieee ->
	    %% a subnormal: the value in units of the smallest one,
	    %% 2^(1-bias-M), rounded to nearest even; 2^M is the
	    %% smallest normal, which the raw pattern already is
	    K = Shift + bias(E) + M - 1,
	    {Q, Inexact} = if K >= 0 -> {A bsl K, false};
			      true -> round_shift(A, -K)
			   end,
	    {ok, (S bsl (E+M)) bor Q, Inexact};
       true ->
	    {Sig, Exp1} = round_to(A, L, M, Exp),
	    Eb = Exp1 + bias(E),
	    if Eb =< 0 ->
		    %% ftz: below the normal range after rounding
		    {ok, S bsl (E+M), true};
	       Eb >= (1 bsl E) - 1 ->
		    {error, {float754_range, {E,M}, {S,A,Shift}}};
	       true ->
		    {ok, (S bsl (E+M)) bor (Eb bsl M) bor (Sig band ((1 bsl M)-1)),
		     false}
	    end
    end.

%% A / 2^Drop rounded to nearest even, and whether anything was lost
round_shift(A, Drop) ->
    Q = A bsr Drop,
    R = A band ((1 bsl Drop) - 1),
    Half = 1 bsl (Drop-1),
    Q1 = if R > Half -> Q+1;
	    R =:= Half -> Q + (Q band 1);
	    true -> Q
	 end,
    {Q1, R =/= 0}.

%% A with its leading one at bit L-1 as an M+1 bit significand, round
%% to nearest even; the exponent moves up when the rounding carries out
round_to(A, L, M, Exp) when L =< M+1 ->
    {A bsl (M+1-L), Exp};
round_to(A, L, M, Exp) ->
    {Q1, _} = round_shift(A, L - (M+1)),
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

%% the light reading: the IEEE value (a subnormal pattern is read as
%% it is), except that every exponent bit set is a number like any
%% other; {zero,S} or {S,Int,Shift}
light_value(Bits, E, M) ->
    {S, Eb, Mb} = fields(Bits, E, M),
    if Eb =:= (1 bsl E) - 1 -> {S, (1 bsl M) bor Mb, Eb - bias(E) - M};
       true -> value(Bits, E, M)
    end.

%% the overflow pattern: every exponent bit set, prints as inf
inf_bits(S, E, M) ->
    (S bsl (E+M)) bor (((1 bsl E) - 1) bsl M).

%% the quiet NaN pattern: every exponent bit and the top fraction bit
nan_bits(E, M) ->
    (((1 bsl E) - 1) bsl M) bor (1 bsl (M-1)).

%% the sign of an IEEE value (a NaN has none that matters)
sign_of({zero,S}) -> S;
sign_of({inf,S}) -> S;
sign_of(nan) -> 0;
sign_of({S,_,_}) -> S.

%% the bits of an operation, and bits with the underflow flag, which
%% the constant folding in varp_formula hands to --underflow
mul_bits(A, B, E, M) -> mul_bits(A, B, E, M, ieee).
add_bits(A, B, E, M) -> add_bits(A, B, E, M, ieee).
div_bits(A, B, E, M) -> div_bits(A, B, E, M, ieee).
mul_bits(A, B, E, M, Mode) -> element(1, mul_fold(A, B, E, M, Mode)).
add_bits(A, B, E, M, Mode) -> element(1, add_fold(A, B, E, M, Mode)).
div_bits(A, B, E, M, Mode) -> element(1, div_fold(A, B, E, M, Mode)).

%% a * b on bit patterns: IEEE for NaN, inf and zero, the exact product
%% rounded otherwise, subnormal or zero (ftz) below the normal range
%% and inf_bits above it
mul_fold(A, B, E, M, Mode) ->
    Va = value(A, E, M), Vb = value(B, E, M),
    S = sign_of(Va) bxor sign_of(Vb),
    case {Va, Vb} of
	{nan,_} -> {nan_bits(E, M), false};
	{_,nan} -> {nan_bits(E, M), false};
	{{inf,_},{zero,_}} -> {nan_bits(E, M), false};
	{{zero,_},{inf,_}} -> {nan_bits(E, M), false};
	{{inf,_},_} -> {inf_bits(S, E, M), false};
	{_,{inf,_}} -> {inf_bits(S, E, M), false};
	{{zero,_},_} -> {S bsl (E+M), false};
	{_,{zero,_}} -> {S bsl (E+M), false};
	{{_,Ia,Sha},{_,Ib,Shb}} ->
	    I = if S =:= 1 -> -(Ia*Ib); true -> Ia*Ib end,
	    fold_result(encode_status(I, Sha+Shb, E, M, Mode), S, E, M)
    end.

fold_result({ok,Bits,Underflow}, _S, _E, _M) -> {Bits, Underflow};
fold_result({error,_}, S, E, M) -> {inf_bits(S, E, M), false}.

%% a + b on bit patterns: IEEE for NaN, inf and zero, the exact sum
%% rounded otherwise, inf_bits above the range.  A zero sum is -0 only
%% when both terms are -0.
add_fold(A, B, E, M, Mode) ->
    Va = value(A, E, M),
    Vb = value(B, E, M),
    case {Va, Vb} of
	{nan,_} -> {nan_bits(E, M), false};
	{_,nan} -> {nan_bits(E, M), false};
	{{inf,S},{inf,S}} -> {inf_bits(S, E, M), false};
	{{inf,_},{inf,_}} -> {nan_bits(E, M), false};
	{{inf,S},_} -> {inf_bits(S, E, M), false};
	{_,{inf,S}} -> {inf_bits(S, E, M), false};
	{{zero,Sa},{zero,Sb}} -> {(Sa band Sb) bsl (E+M), false};
	_ ->
	    {Ia,Sha} = signed_scaled(Va),
	    {Ib,Shb} = signed_scaled(Vb),
	    Sh = erlang:min(Sha, Shb),
	    I = (Ia bsl (Sha-Sh)) + (Ib bsl (Shb-Sh)),
	    if I =:= 0 -> {0, false};
	       true ->
		    fold_result(encode_status(I, Sh, E, M, Mode),
				if I < 0 -> 1; true -> 0 end, E, M)
	    end
    end.

%% a / b on bit patterns: IEEE for NaN, inf and zero (x/0 is inf, as
%% --fdivz ignore gives it), the exact quotient rounded otherwise: it
%% is taken with enough bits, a nonzero remainder becomes a sticky bit
div_fold(A, B, E, M, Mode) ->
    Va = value(A, E, M), Vb = value(B, E, M),
    S = sign_of(Va) bxor sign_of(Vb),
    case {Va, Vb} of
	{nan,_} -> {nan_bits(E, M), false};
	{_,nan} -> {nan_bits(E, M), false};
	{{zero,_},{zero,_}} -> {nan_bits(E, M), false};
	{{inf,_},{inf,_}} -> {nan_bits(E, M), false};
	{{inf,_},_} -> {inf_bits(S, E, M), false};
	{_,{inf,_}} -> {S bsl (E+M), false};
	{_,{zero,_}} -> {inf_bits(S, E, M), false};
	{{zero,_},_} -> {S bsl (E+M), false};
	{{_,Ia,Sha},{_,Ib,Shb}} ->
	    %% enough quotient bits for any subnormal result too
	    K = 2*M + E + 4 + bit_length(Ib),
	    Q0 = (Ia bsl K) div Ib,
	    {Q, K1} = case (Ia bsl K) rem Ib of
			  0 -> {Q0, K};
			  _ -> {(Q0 bsl 1) bor 1, K+1}
		      end,
	    I = if S =:= 1 -> -Q; true -> Q end,
	    fold_result(encode_status(I, Sha - Shb - K1, E, M, Mode), S, E, M)
    end.

signed_scaled({zero,_}) -> {0, 0};
signed_scaled({1,I,Sh}) -> {-I, Sh};
signed_scaled({0,I,Sh}) -> {I, Sh}.

%% as an Erlang float (the tests compare with it)
to_float(Bits, E, M) ->
    case light_value(Bits, E, M) of
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
