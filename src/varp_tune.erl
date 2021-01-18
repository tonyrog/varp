%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2021, Tony Rogvall
%%% @doc
%%%    Parameter tuning
%%% @end
%%% Created : 11 Jan 2021 by Tony Rogvall <tony@rogvall.se>

-module(varp_tune).

-export([run/1]).
-export([run/2]).

-export([demo/0]).
-export([demo_factor/0]).
-export([emit_csv/1, emit_csv/2]).
-export([write_csv/1, write_csv/2]).

-compile(export_all).

%% -define(DEBUG, true).
-include("varp.hrl").

%% -define(TUNE_TIMEOUT, (60*5)).  %% 5 minutes
-define(TUNE_TIMEOUT, (10)).  %% 10 seconds

-type range() :: {From::number(), To::number()}.
-type value() :: number() | atom().
-type value_range() :: value() | range().
-type domain() :: value_range() | [value_range()].

-type spec() :: [{Key::atom(), Domain::domain()}].

%% declare range of all parameters that need tuning
-spec global_spec() -> spec().
global_spec() ->
    [
     {phase, [false, true, undefined]},  %% init-phase
     {use_phase, [true, false]}
    ].

%% specifiy parameter range used
-spec backjump_spec() -> spec().
backjump_spec() ->
    [
     {minimize, [none,local,global,recursive]},
     {stumble,  {0,10}},
     {olle,     {0.0, 10.0}},
     {stumble_olle, [false, true]},
     {max_conflicts, {1,10}},
     {max_learned_factor, [0,{1.0,10.0}]},  %% 0=no-max
     {max_learned_inc,    [0,{1.0,2.0}]},   %% 0=1.0=no-inc
     {keep_factor,        {0.0,1.0}},
     {min_keep_clauses,   {0,1000000000}},
     {restart_counter,    {0,1000000}},     %% 0=off
     {restart_interval,   [infinity,{0.01,float(?TUNE_TIMEOUT)}]},
     {bump,               [none,next,log2,log10,rank,
			   {1,1000},{0.001, 1.0}]}
     %% add "reorder" options
    ].


%% sample one parameter
select_samples(Param, global, MaxSamples) ->
    select_samples(Param, global_spec(), MaxSamples);
select_samples(Param, backjump, MaxSamples) ->
    select_samples(Param, backjump_spec(), MaxSamples);
select_samples(Param, Spec, MaxSamples) ->
    Range = proplists:get_value(Param, Spec),
    sample(MaxSamples, Range).

sample(MaxSample, Range) ->
    sample_(MaxSample, Range, []).

sample_(0, _Range, Acc) -> Acc;
sample_(_I, Value, Acc) when is_atom(Value) -> [Value|Acc];
sample_(_I, Value, Acc) when is_number(Value) -> [Value|Acc];
sample_(I, [Value|Range], Acc) when is_atom(Value) ->
    sample_(I-1, Range, [Value|Acc]);
sample_(I, [Value|Range], Acc) when is_number(Value) ->
    sample_(I-1, Range, [Value|Acc]);
sample_(I, {A,B}, Acc) when is_float(A), is_float(B), A =< B ->
    sample_float_range_(I, A, B, Acc);
sample_(I, {A,B}, Acc) when is_integer(A), is_integer(B), A =< B ->
    sample_integer_range_(I, A, B, Acc);

sample_(I, [{A,B}|Range], Acc) when is_float(A), is_float(B), A =< B ->
    N = round(I / (1+length(Range))),
    sample_(I-N, Range, sample_float_range_(N, A, B, Acc));
sample_(I, [{A,B}|Range], Acc) when is_integer(A), is_integer(B), A =< B ->
    N = round(I / (1+length(Range))),
    sample_(I-N, Range, sample_integer_range_(N, A, B, Acc));

sample_(I, [Value|Range], Acc) when is_atom(Value) ->
    sample_(I-1, Range, [Value|Acc]);
sample_(_I, [], Acc) -> 
    Acc.

sample_float_range(N, A, B) when is_integer(N), N >=0,
				 is_float(A), is_float(B), A =< B ->
    sample_float_range_(N, A, B, []).
sample_float_range_(N, A, B, Acc) ->
    sample_float_range_(N, A, B, (B - A) / (N+1), Acc).
sample_float_range_(0, _A, _B, _Step, Acc) -> Acc;
sample_float_range_(I, A, B, Step, Acc) when is_integer(I), I>0, A =< B ->
    A1 = A+Step,
    sample_float_range_(I-1, A1, B, Step, [A1|Acc]).

sample_integer_range(N, A, B) when is_integer(N), N>=0,
				   is_integer(A), is_integer(B), A =< B ->
    sample_integer_range_(N, A, B, []).
sample_integer_range_(N, A, B, Acc) ->
    Step = ((B-A)+1) / N,
    sample_integer_range_(N, A, A, B, Step, Acc).
sample_integer_range_(0, _A0, _A, _B, _Step, Acc) -> Acc;
sample_integer_range_(I, A0, A, B, Step, Acc)  when is_integer(I), I>0 ->
    A1 = A0+Step,
    AA = trunc(A1),
    if  AA > A, AA =< B ->
	    sample_integer_range_(I-1, A1, AA, B, Step, [A|Acc]);
	AA =:= A ->
	    sample_integer_range_(I, A1, A, B, Step, Acc);
	true ->
	    Acc
    end.

global_params() ->
    [{print,[false]},
     {xref, [true]},
     {seed, [1]},
     {timeout, [?TUNE_TIMEOUT]},
     {phase, [true, undefined]},  %% true, false
     {use_phase, [true, false]}].

backjump_params() ->
    [
     %% {max, [1]}  %% default
     {minimize, [none,local,recursive]},
     {bump,[10,0.001,0.01]},  %% none,next,log2,rank
     {max_conflicts, [1]},       %% 2,3
     {max_learned_factor, [1.2]},  %% 1.0,1.2,1.8,2.0
     {max_learned_inc,    [1.2]},  %% 1.0,1.2,1.8,2.0
     {keep_factor,        [0.2]},
     {restart_counter,    [0, 10, 100]},
     {restart_interval,   [infinity, 0.1, 1.0]}
    ].

statistics(Bs, T0) ->
    T1 = erlang:monotonic_time(),
    Time = erlang:convert_time_unit(T1-T0,native,microsecond),
    Ts = Time/1000000,
    ConflictCounter = varp:info(Bs#bs.vp, conflict_counter),
    BcpCounter = varp:info(Bs#bs.vp, bcp_counter),
    %% number of clauses create...?
    {{statistics,
      [{conflicts,ConflictCounter},
       {bcp,BcpCounter}]}, Ts}.

varp_filename(File) ->
    filename:join([code:lib_dir(varp),"formulas","varp",File]).

demo() ->
    run("pigeon.varp", [{"n",8}]).

demo_factor() ->
    run("is_prime.varp", [{"n", 8014003}]).

demo_factor2() ->
    run("is_prime.varp", [{"n", 2225513363}]).

save(_File, Error={error,_}) ->
    Error;
save(File, {N,ResList}) ->
    io:format("total results = ~w\n", [N]),
    NumSave = 10,
    io:format("save ~w fastest\n", [NumSave]),
    ResList1 = 
	lists:filter(fun(Res) ->
			     not lists:member({result,timeout}, Res)
		     end, ResList),
    %% sort according to best runtime
    ResList2 = lists:sort(fun(A, B) ->
				  proplists:get_value(time, A, time) < 
				      proplists:get_value(time, B)
			  end, ResList1),
    Len = length(ResList2),
    if Len =< NumSave ->
	    save_runs(File, ResList2);
       true ->
	    {ResList3,_} = lists:split(NumSave, ResList2),
	    save_runs(File, ResList3)
    end.

save_runs(File, ResList) ->
    case file:open(File, [write]) of
	{ok,Fd} ->
	    try save_runs_(Fd, ResList) of
		_ -> ok
	    after
		file:close(Fd)
	    end;
	Error ->
	    Error
    end.

save_runs_(Fd, Rs) ->
    [ io:format(Fd, "~p.\n", [R]) || R <- Rs ].


run(File) ->
    run(File, []).
run(File, Meta) when is_list(Meta) ->
    run(File, maps:from_list(Meta));
run(File, Meta) when is_map(Meta) ->
    application:ensure_all_started(varp), %% load plugins etc
    {ok,Bin} = file:read_file(varp_filename(File)),
    case parse(binary_to_list(Bin), Meta) of
	{ok,{Sections,Form}} ->
	    lists2:gfold(
	      fun(Params, {I,ResList}) ->
		      io:format("RUN ~w: ", [I]),
		      %% FIXME: save each result in a file 
		      %% so we do not loose results in case of crash
		      case run1(Sections,Form,Meta,Params) of
			  [] -> {I,ResList};
			  Res ->
			      Res1 = [{run,I}|Res]++Params,
			      {I+1,[Res1|ResList]}
		      end
	      end,
	      {1,[]},
	      [{global,global_params()},
	       {backjump,backjump_params()}]);
	{error, {Ln,Mod,Message}} when is_integer(Ln), is_atom(Mod) ->
	    Text = (catch apply(Mod, format_error, [Message])),
	    io:format("~s\n", [Text]),
	    {error, parse};

	{error, {Ln,Mod,Message}, _EndLn} when is_integer(Ln), is_atom(Mod) ->
	    Text = (catch apply(Mod, format_error, [Message])),
	    io:format("~s\n", [Text]),
	    {error, parse};

	{error, Message} ->
	    io:format("~s\n", [varp:format_error(Message)]),
	    {error, Message}
    end.

%% Run one configuration
run1(Sections, Form, Meta, [{global,Global},{backjump,BjParams}]) ->
    GOpts = varp:load_option_list(Global),
    GOpts1 = varp:section_opts(Sections, GOpts),
    Do = 
	[{satisfy,[]},
	 %% {saturate, SaturateParams}
	 %% {order, OrderParams}
	 {backjump,BjParams}],
    GDo = varp:parse_do(Do),
    GOpts2 = GOpts1#{ meta => Meta },
    T0 = erlang:monotonic_time(),
    try varp:do_run(GDo,Form,GOpts2) of
	{?INCONSISTENT,_,Bs} ->
	    {Stat,Time} = statistics(Bs, T0),
	    io:format("UNSAT time=~fs\n", [Time]),
	    [{result,unsat},{time,Time},Stat];
	{?DONE, _, Bs} -> %% one model
	    {Stat,Time} = statistics(Bs, T0),
	    io:format("SAT  time=~fs\n", [Time]),
	    [{result,sat},{time,Time},Stat];
	{?CONTINUE, _, Bs} -> %% one or more models
	    {Stat,Time} = statistics(Bs, T0),
	    io:format("SAT  time=~fs\n", [Time]),
	    [{result,sat},{time,Time},Stat];
	{?TIMEOUT,_,Bs} ->
	    {Stat,Time} = statistics(Bs, T0),
	    io:format("TIMEOUT  time=~fs\n", [Time]),
	    [{result,timeout},{time,Time},Stat];
	{?CANCEL,_,_} ->
	    io:format("USER ABORT\n"),
	    [];
	{?ERROR,_,_} ->
	    io:format("ERROR\n"),
	    [];
	Res ->
	    io:format("unexpected ~p\n",[Res]),
	    []
    catch
	?EXCEPTION(error,Reason,Trace) ->
	    io:format("~s\n", [varp:format_error(Reason)]),
	    io:format("exception:~w\n~p\n", [Reason,?GET_STACK(Trace)]),
	    []
    end.


parse(String, Meta) ->
    case varp:tokens(String) of
	{ok,[{identifier,_,"c"}|_Ts]} ->
	    parse_dimacs(String);
	{ok,[{identifier,_,"p"}|_Ts]} ->
	    parse_dimacs(String);
	{ok,Ts} ->
	    case varp_parse:parse(Ts) of
		{ok,{Sections,Formula}} ->
		    GOpts = #{ meta => Meta },
		    try varp:split_sections(Sections,GOpts) of
			{ok, SectionMap} ->
			    {ok,{SectionMap,Formula}};
			Error ->
			    Error
		    catch
			error:Reason ->
			    {error,Reason}
		    end;
		Error -> Error
	    end;
	Error -> Error
    end.

parse_dimacs(String) ->
    Bin = list_to_binary(String), %% utf?
    case varp_dimacs:parse(Bin) of
	Form={cnf,{_Var,_Clause,SectionMap,_Cs}} ->
	    {ok,{SectionMap,Form}};
	Form={snf,{_Var,_Clause,SectionMap,_Cs}} ->
	    {ok,{SectionMap,Form}};
	Error ->
	    Error
    end.

write_csv(Result) ->
    write_csv("tune.csv", Result).

write_csv(Filename, Result) ->
    case file:open(Filename, [write]) of
	{ok,Fd} ->
	    try emit_csv(Fd, Result) of
		_ -> ok
	    after
		file:close(Fd)
	    end;
	Error ->
	    Error
    end.

emit_csv(Result) ->
    emit_csv(user, Result).
     
emit_csv(Fd, Result) ->
    emit_header(Fd, hd(Result)), io:put_chars(Fd, "\n"),
    [begin emit_row(Fd, Ent), io:put_chars(Fd, "\n") end || 
	Ent <- lists:reverse(Result)].

emit_header(Fd,[{_Key,Value}|Tail]) when is_list(Value) ->
    emit_header(Fd, Value), emit_header(Fd, Tail);
emit_header(Fd, [{Key,_Value}|Tail]) ->
    io:format(Fd, "\"~s\"; ", [Key]), emit_header(Fd, Tail);
emit_header(_Fd, []) ->
    ok.

emit_row(Fd, [{_Key,Value}|Tail]) when is_list(Value) ->
    emit_row(Fd, Value), emit_row(Fd, Tail);
emit_row(Fd, [{_Key,Value}|Tail]) ->
    if is_float(Value) ->
	    io:format(Fd, "~s; ", [io_lib_format:fwrite_g(Value)]);
       true ->
	    io:format(Fd, "~p; ", [Value])
    end,
    emit_row(Fd, Tail);
emit_row(_Fd, []) ->
    ok.


    

    
    
    
