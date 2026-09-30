%%% varp_pattern: partly known bytes in, partly known vectors out

-module(varp_pattern_tests).
-include_lib("eunit/include/eunit.hrl").

text_test() ->
    ?assertEqual([104,105,free,33], varp_pattern:text("hi*!")),
    ?assertEqual([free,free], varp_pattern:text(<<"_*">>)),
    ?assertEqual([], varp_pattern:text("")).

hex_test() ->
    ?assertEqual({ok,[5,14,11,6,free,free,14,0]}, varp_pattern:hex("5eb6**e0")),
    ?assertEqual({ok,[10,15]}, varp_pattern:hex(<<"AF">>)),
    ?assertMatch({error,{not_hex,"x"}}, varp_pattern:hex("5x")).

format_test() ->
    Bits = fun(S) -> list_to_tuple(S) end,
    ?assertEqual("5e", varp_pattern:format_hex(Bits("01011110"))),
    ?assertEqual("5*", varp_pattern:format_hex(Bits("0101111*"))),
    ?assertEqual("a", varp_pattern:format_hex(Bits("1010"))),
    ?assertEqual("0a", varp_pattern:format_hex(Bits("001010"))),   %% padded to nibbles
    ?assertEqual("hi", varp_pattern:format_text(Bits("0110100001101001"))),
    ?assertEqual("h*", varp_pattern:format_text(Bits("01101000*1101001"))),
    ?assertEqual("\\x00", varp_pattern:format_text(Bits("00000000"))),
    ?assertEqual([0,1,free], varp_pattern:bit_values({$0,$1,$*})).
