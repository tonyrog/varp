%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2026, Tony Rogvall
%%% @doc
%%%    Common helpers for the varp eunit test suites.
%%%
%%%    The module is deliberately NOT named *_tests so that eunit does
%%%    not try to run it as a test module.
%%% @end

-module(varp_tc).

%% parsing
-export([tokens/1, tokens/2]).
-export([parse/1, parse/2]).
-export([parse_result/1, parse_result/2]).
-export([parse_only/1, parse_only/2]).
-export([formula/1, formula/2]).
-export([sections/1]).

%% building / solving
-export([run/2, run/3]).
-export([models/1, models/2]).
-export([count/1, count/2]).
-export([is_sat/1, is_sat/2]).
-export([is_unsat/1, is_unsat/2]).
-export([is_tautology/1, is_tautology/2]).

%% command line
-export([cli/1, cli/2]).
-export([erl_eval/1, erl_eval/2]).

%% misc
-export([top/0, formula_dir/1, formula_files/2]).
-export([tmpfile/1, tmpdir/0]).
-export([quiet/1, capture/1]).

-include("varp.hrl").

%%%-------------------------------------------------------------------
%%% Parsing
%%%-------------------------------------------------------------------

tokens(Text) -> tokens(Text, #{}).
tokens(Text, Opts) ->
    ICase = maps:get(icase, Opts, false),
    {ok,Ts} = varp:tokens(Text, ICase),
    Ts.

%% parse and fail loudly on error
parse(Text) -> parse(Text, #{}).
parse(Text, Opts) ->
    case parse_result(Text, Opts) of
	{ok,R} -> R;
	Error -> erlang:error({parse_failed, Error})
    end.

%% parse and return {ok,_} | {error,_} without printing anything
parse_result(Text) -> parse_result(Text, #{}).
parse_result(Text, Opts) ->
    quiet(fun() ->
		  try varp:parse("*test*", Text, gopts(Opts)) of
		      R -> R
		  catch
		      error:Reason -> {error,Reason}
		  end
	  end).

%% Raw scan+parse only, no section processing.  This is what the
%% syntax tests use: it does not evaluate declaration sizes, so a
%% formula with unbound meta variables still parses.
parse_only(Text) -> parse_only(Text, false).
parse_only(Text, ICase) ->
    Scan = if ICase -> varp_scani; true -> varp_scan end,
    quiet(fun() ->
		  varp_formula:init_circuit_def(),
		  Scan:init(varp:remove_comments(Text)),
		  try varp_parse:parse_and_scan({Scan, one_token, []}) of
		      R -> R
		  catch
		      error:Reason -> {error,Reason}
		  end
	  end).

%% just the main formula of a source text
formula(Text) -> formula(Text, #{}).
formula(Text, Opts) ->
    {_Sections,_Assignments,F} = parse(Text, Opts),
    F.

%% just the section map
sections(Text) ->
    {Sections,_Assignments,_F} = parse(Text),
    Sections.

%%%-------------------------------------------------------------------
%%% Building and solving
%%%-------------------------------------------------------------------

%% Do is a plugin list on varp:parse_do/1 form, e.g.
%%    [{satisfy,[]},{backtrack,[{max,0}]}]
run(Text, Do) -> run(Text, Do, #{}).
run(Text, Do, Opts) ->
    {ok,_} = application:ensure_all_started(varp),
    GOpts0 = gopts(Opts),
    {Sections,Assignments,Formula} = parse(Text, Opts),
    GOpts = varp:section_opts(Sections, GOpts0),
    GDo = varp:parse_do(Do),
    %% a misspelled plugin silently disappears from the list, which would
    %% make every test report "no models"
    length(Do) =:= length(GDo) orelse erlang:error({unknown_plugin, Do}),
    varp:do_run(GDo, Assignments, Formula, GOpts).

%% all models of a formula, normalised and sorted
models(Text) -> models(Text, #{}).
models(Text, Opts) ->
    Do = [{satisfy,[]},{backtrack,[{max,0}]}],
    case run(Text, Do, Opts) of
	{?INCONSISTENT,_,_} -> [];
	{_R,Ms,_Bs} when is_list(Ms) ->
	    lists:sort([norm_model(M) || M <- Ms]);
	Other ->
	    erlang:error({unexpected_result, Other})
    end.

count(Text) -> count(Text, #{}).
count(Text, Opts) -> length(models(Text, Opts)).

is_sat(Text) -> is_sat(Text, #{}).
is_sat(Text, Opts) -> models(Text, Opts) =/= [].

is_unsat(Text) -> is_unsat(Text, #{}).
is_unsat(Text, Opts) -> models(Text, Opts) =:= [].

%% a formula is a tautology when its negation has no model,
%% which is what the 'prove' plugin reports as INCONSISTENT
is_tautology(Text) -> is_tautology(Text, #{}).
is_tautology(Text, Opts) ->
    Do = [{prove,[]},{backtrack,[{max,1}]}],
    case run(Text, Do, Opts) of
	{?INCONSISTENT,_,_} -> true;
	_ -> false
    end.

%% Model is [{{p,Name,Args},Value}], normalise into [{NameString,Value}]
norm_model(M) ->
    lists:sort([{sym_name(X), sym_value(V)} || {X,V} <- M]).

sym_name({p,Name,[]}) ->
    binary_to_list(Name);
sym_name({p,Name,Args}) ->
    binary_to_list(
      iolist_to_binary([Name,"(",
			lists:join(",", [io_lib:format("~w",[A]) || A <- Args]),
			")"]));
sym_name({Name,Args}) ->
    sym_name({p,Name,Args}).

sym_value(true) -> true;
sym_value(false) -> false;
sym_value(undefined) -> undefined;
sym_value({uint,Vec}) -> vec_value(Vec, false);
sym_value({int,Vec})  -> vec_value(Vec, true);
sym_value({bit,Vec})  -> tuple_to_list(Vec);
sym_value(V) -> V.

%% bit tuples are ascii $0/$1/$* MSB first
vec_value(Vec, Signed) ->
    Cs = tuple_to_list(Vec),
    case lists:member($*, Cs) of
	true -> Cs;   %% partially bound, keep the bit pattern
	false ->
	    U = list_to_integer(Cs, 2),
	    if Signed, hd(Cs) =:= $1 ->
		    -(((bnot U) band ((1 bsl length(Cs))-1))+1);
	       true ->
		    U
	    end
    end.

%%%-------------------------------------------------------------------
%%% Command line
%%%-------------------------------------------------------------------

%% Run varp:main/1 in its own erl and return {ExitCode, Output}
cli(Args) -> cli(Args, 120000).
cli(Args, Timeout) ->
    erl_eval(lists:flatten(io_lib:format("varp:main(~w)", [Args])), Timeout).

%% Evaluate an expression in its own erl and return {ExitCode, Output}
erl_eval(Expr) -> erl_eval(Expr, 120000).
erl_eval(Eval, Timeout) ->
    Ebin = filename:join(top(), "ebin"),
    Erl = os:find_executable("erl"),
    Port = erlang:open_port(
	     {spawn_executable, Erl},
	     [{args, ["-noshell", "-pa", Ebin, "-eval", Eval]},
	      stream, in, eof, hide, exit_status, stderr_to_stdout]),
    collect(Port, [], undefined, Timeout).

collect(Port, Acc, Status, Timeout) ->
    receive
	{Port,{data,Data}} ->
	    collect(Port, [Acc|Data], Status, Timeout);
	{Port,{exit_status,Code}} ->
	    collect(Port, Acc, Code, Timeout);
	{Port,eof} ->
	    case Status of
		undefined ->
		    receive
			{Port,{exit_status,Code}} ->
			    finish(Port, Acc, Code)
		    after 5000 ->
			    finish(Port, Acc, undefined)
		    end;
		_ ->
		    finish(Port, Acc, Status)
	    end
    after Timeout ->
	    catch erlang:port_close(Port),
	    erlang:error({cli_timeout, lists:flatten(Acc)})
    end.

finish(Port, Acc, Code) ->
    catch erlang:port_close(Port),
    {Code, lists:flatten(Acc)}.

%%%-------------------------------------------------------------------
%%% Misc
%%%-------------------------------------------------------------------

%% top of the varp source tree
top() ->
    case code:lib_dir(varp) of
	{error,_} ->
	    filename:dirname(filename:dirname(code:which(varp)));
	Dir ->
	    Dir
    end.

formula_dir(Sub) ->
    filename:join([top(), "formulas", Sub]).

formula_files(Sub, Ext) ->
    filelib:wildcard(filename:join(formula_dir(Sub), "*"++Ext)).

tmpdir() ->
    Dir = filename:join(["/tmp", "varp_test_"++os:getpid()]),
    ok = filelib:ensure_dir(filename:join(Dir,"x")),
    Dir.

tmpfile(Name) ->
    filename:join(tmpdir(), Name).

%% run Fun and return everything it wrote to the group leader
capture(Fun) ->
    Old = group_leader(),
    Collector = spawn(fun() -> capture_loop([]) end),
    group_leader(Collector, self()),
    try Fun()
    after
	group_leader(Old, self())
    end,
    Collector ! {done, self()},
    receive {Collector, Data} -> Data after 5000 -> [] end.

capture_loop(Acc) ->
    receive
	{io_request, From, ReplyAs, {put_chars,_,Chars}} ->
	    From ! {io_reply, ReplyAs, ok},
	    capture_loop([Acc|Chars]);
	{io_request, From, ReplyAs, {put_chars,_,M,F,As}} ->
	    From ! {io_reply, ReplyAs, ok},
	    capture_loop([Acc|apply(M,F,As)]);
	{io_request, From, ReplyAs, _} ->
	    From ! {io_reply, ReplyAs, ok},
	    capture_loop(Acc);
	{done, Pid} ->
	    Pid ! {self(), lists:flatten(Acc)};
	_ ->
	    capture_loop(Acc)
    end.

%% run Fun with all io from this process thrown away
quiet(Fun) ->
    Old = group_leader(),
    Sink = spawn(fun sink/0),
    group_leader(Sink, self()),
    try Fun()
    after
	group_leader(Old, self()),
	Sink ! stop
    end.

sink() ->
    receive
	stop -> ok;
	{io_request,From,ReplyAs,_Request} ->
	    From ! {io_reply,ReplyAs,ok},
	    sink();
	_ ->
	    sink()
    end.

%%%-------------------------------------------------------------------

gopts(Opts) when is_list(Opts) ->
    gopts(maps:from_list(Opts));
gopts(Opts) when is_map(Opts) ->
    Meta = maps:get(meta, Opts, #{}),
    Rest = maps:to_list(maps:remove(meta, Opts)),
    %% undeclared warnings are off unless a case asks for them, so that
    %% they do not pollute the output of every other case
    G = varp:load_option_list([{print,false},{undeclared,none}|Rest]),
    G#{ meta => Meta }.
