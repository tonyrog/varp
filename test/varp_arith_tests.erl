%%% Arithmetic circuit library (varp_arith) self test.
-module(varp_arith_tests).

-include_lib("eunit/include/eunit.hrl").

arith_library_test_() ->
    {timeout, 900, fun() -> ?assertEqual(ok, varp_arith:test()) end}.

%% varp_bitvec is exercised through varp_arith, this only checks the
%% pure conversions.  Bit vectors are least significant bit first.
bitvec_test() ->
    ?assertEqual({uint,3,[false,false,true]}, varp_bitvec:from_unsigned(4,3)),
    ?assertEqual({uint,3,[true,false,true]},  varp_bitvec:from_unsigned(5,3)),
    ?assertEqual({uint,3,[false,false,false]},varp_bitvec:from_unsigned(0,3)),
    ?assertEqual({uint,3,[true,true,true]},   varp_bitvec:from_unsigned(7,3)),
    ?assertEqual({int,4,[true,true,true,true]}, varp_bitvec:from_signed(-1,4)),
    %% a wider vector is zero extended
    ?assertEqual({uint,4,[true,false,true,false]}, varp_bitvec:from_unsigned(5,4)).

math_test() ->
    ?assertEqual(1, varp_math:unsigned_size(0)),
    ?assertEqual(1, varp_math:unsigned_size(1)),
    ?assertEqual(2, varp_math:unsigned_size(3)),
    ?assertEqual(3, varp_math:unsigned_size(4)),
    ?assertEqual(4, varp_math:unsigned_size(8)),
    ?assert(varp_math:signed_size(-1) >= 1),
    ?assert(varp_math:signed_size(-8) >= 4).
