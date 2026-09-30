%%% varp_input: the protocol between varp and the input modules of a
%%% formula, see the module documentation.

-module(varp_input_tests).
-include_lib("eunit/include/eunit.hrl").

lines_test() ->
    ?assertEqual(["a","b"], varp_input:lines(<<"a\nb\n">>)),
    ?assertEqual(["a","b"], varp_input:lines(<<"a\nb">>)),
    ?assertEqual([""], varp_input:lines(<<>>)),
    ?assertEqual(["", "x"], varp_input:lines(<<"\nx\n">>)).

%% md5_io exports input/2 (a line) and input/1 (the bindings)
protocol_test() ->
    File = filename:join(varp_tc:tmpdir(), "lines.txt"),
    ok = file:write_file(File, "one\ntwo\n"),
    {ok, [{<<"mlen">>,3}], _} = varp_input:file([md5_io], File, #{}),
    {ok, [{<<"mlen">>,3}], F2} = varp_input:file([md5_io], File, #{<<"recno">> => 2}),
    %% "two": each known byte pins its bit range of a message word
    Byte = fun(P, B) -> {lop,eq,{bitrange,{p,<<"M">>,[P div 4]},8*(P rem 4),8*(P rem 4)+7,1},{const,B}} end,
    ?assert(conjunct(Byte(0, $t), F2)),
    ?assert(conjunct(Byte(2, $o), F2)),
    ?assert(conjunct(Byte(3, 16#80), F2)),
    ?assertEqual({error,{no_such_line,File,3}},
		 varp_input:file([md5_io], File, #{<<"recno">> => 3})),
    ?assertEqual({error,{no_input_module,File}}, varp_input:file([], File, #{})),
    ?assertMatch({ok, [{<<"mlen">>,5}], _}, varp_input:bindings([md5_io], #{<<"msg">> => "hello"})),
    ?assertEqual(skip, varp_input:bindings([md5_io], #{})),
    %% a module without any input function is skipped
    ?assertEqual(skip, varp_input:bindings([lists, md5_io], #{})).

conjunct(X, {lop,'and',A,B}) -> conjunct(X, A) orelse conjunct(X, B);
conjunct(X, X) -> true;
conjunct(_, _) -> false.
