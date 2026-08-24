%%% GUI (varp_wx).
%%%
%%% The window itself is only started when a display is available, the
%%% rest is checked without one.  Under a headless CI run the display
%%% case is skipped, run it with
%%%
%%%    xvfb-run -a make test
%%%
%%% to cover it.
-module(varp_wx_tests).

-include_lib("eunit/include/eunit.hrl").

-export([collect_model/4]).

%%%-------------------------------------------------------------------
%%% Plugin contract
%%%-------------------------------------------------------------------

%% varp_wx is also registered as the "wx" plugin
plugin_contract_test() ->
    ?assertMatch({module,varp_wx}, code:ensure_loaded(varp_wx)),
    ?assert(erlang:function_exported(varp_wx, options, 0)),
    ?assert(erlang:function_exported(varp_wx, run, 2)),
    ?assert(is_list(varp_wx:options())).

%%%-------------------------------------------------------------------
%%% Pure helpers
%%%-------------------------------------------------------------------

format_time_test() ->
    S = fun(Ms) -> lists:flatten(varp_wx:format_time(Ms)) end,
    ?assertEqual("00.001", S(1)),
    ?assertEqual("01.000", S(1000)),
    ?assertEqual("01.500", S(1500)),
    ?assertEqual("01:00.000", S(60*1000)),
    ?assertEqual("01:00:00.000", S(60*60*1000)),
    ?assertEqual("1d 00:00:00.000", S(24*60*60*1000)),
    ?assertEqual("1d 01:01:01.001", S(((24+1)*3600 + 61)*1000 + 1)).

%%%-------------------------------------------------------------------
%%% The output callback the GUI installs into varp:do_run/4
%%%-------------------------------------------------------------------

%% The GUI does not print models itself, it passes an
%%   output => [{varp_wx,output_model,[State]}]
%% callback to do_run.  This checks that the callback protocol still
%% works and that the model reaches it in the expected shape.
output_callback_test() ->
    {ok,_} = application:ensure_all_started(varp),
    Opts = varp:load_option_list([]),
    {ok,{Sections,_A,F}} =
	varp:parse("*test*", "declare V:4; (A or B) && (V == 3)", Opts),
    GOpts0 = varp:section_opts(Sections, Opts),
    Self = self(),
    GOpts = GOpts0#{ meta => #{},
		     output => [{?MODULE,collect_model,[Self]}] },
    Do = varp:parse_do([{satisfy,[]},{backtrack,[{max,0}]}]),
    {_R,_Ms,_Bs} = varp_tc:quiet(fun() -> varp:do_run(Do, [], F, GOpts) end),
    Models = drain([]),
    ?assertEqual(3, length(Models)),
    %% every model has V bound to 3 and at least one of A,B true
    lists:foreach(
      fun(Text) ->
	      ?assertNotEqual(nomatch, string:find(Text, "V=3")),
	      ?assert(string:find(Text,"A") =/= nomatch orelse
		      string:find(Text,"B") =/= nomatch)
      end, Models).

%% same shape as varp_wx:output_model/4
collect_model(_Fd, Partial, Model, Owner) ->
    List = [ varp_format:format_binding(B) ||
	       B <- varp_formula:filter_bindings(Model),
	       Partial orelse (element(2,B) =/= false) ],
    Owner ! {model, lists:flatten(lists:join(",", List))},
    ok.

drain(Acc) ->
    receive {model,M} -> drain([M|Acc])
    after 0 -> lists:reverse(Acc)
    end.

%%%-------------------------------------------------------------------
%%% Starting the window
%%%-------------------------------------------------------------------

%% Starting the window is opt-in: it opens a real window on whatever
%% display is in use, so "make test" leaves it alone.  Run
%%
%%    make test-gui
%%
%% to include it (that target starts an Xvfb of its own).
start_window_test_() ->
    case os:getenv("VARP_TEST_GUI") of
	false ->
	    {"window not started, set VARP_TEST_GUI=1 to include it",
	     fun() -> ok end};
	_ ->
	    {timeout, 120, fun start_window/0}
    end.

%% run it in its own erl so that a wx crash cannot take the test node
%% with it
start_window() ->
    {Code,Out} =
	varp_tc:erl_eval(
	  "P = varp_wx:start([]),"
	  "timer:sleep(3000),"
	  "case erlang:is_process_alive(P) of"
	  "  true -> io:format(\"WINDOW OK~n\"), halt(0);"
	  "  false -> io:format(\"WINDOW GONE~n\"), halt(1)"
	  "end"),
    ?assertEqual({0,true}, {Code, string:find(Out,"WINDOW OK") =/= nomatch}).
