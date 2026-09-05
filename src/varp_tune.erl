%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2021, Tony Rogvall
%%% @doc
%%%    Parameter tuning over a ladder of instance sets.
%%%
%%%    run(Ladder, Spec, Opts) samples configurations from Spec, runs
%%%    every configuration on the first stage of Ladder, keeps the best
%%%    fraction, runs those on the next stage and so on.  The winner is
%%%    printed as a varp command line.
%%%
%%%    Ladder   :: [Stage], Stage :: [Instance]      (small instances first)
%%%    Instance :: {File,Meta} | {File,Meta,TimeoutSeconds}
%%%                File is absolute or relative to formulas/varp
%%%    Spec     :: [{global,Params} | {Plugin,Params}]
%%%                Plugin is the long plugin name (backjump, order, ...)
%%%                and the plugins run in the listed order after satisfy.
%%%    Params   :: [{Key,Domain}]
%%%    Domain   :: [Value | Range] | Range
%%%    Range    :: {From,To} | {log,From,To}   (integers give integers)
%%%                {value,V} is the literal V (use it when V is a list)
%%%
%%%    Opts (map):
%%%      samples   number of random configurations, or all for a grid (96)
%%%      baseline  also run the plugin defaults as configuration #0 (true)
%%%      keep      fraction of configurations that survive a stage (0.25)
%%%      min_keep  never keep fewer than this (4)
%%%      parallel  number of concurrent runs (3)
%%%      final_parallel  concurrent runs in the last stage (1): sequential
%%%                runs give comparable times
%%%      timeout   default timeout per run in seconds (10)
%%%      seed      seed for the configuration sampler (1)
%%%      center    a configuration to search around; samples are then
%%%                mutations of it (default: none, sample the whole Spec)
%%%      mutations parameters changed per sample when center is set (2)
%%%      interval  seconds between progress lines (10)
%%%      grace     seconds past twice the timeout before a run is killed (10)
%%%      log       file that gets everything printed, appended (none)
%%%      csv       file that gets one row per run (none)
%%%      fixed     global options every run gets ([{print,false},{xref,true},{seed,1}])
%%%
%%%    Score of a configuration on a stage is the sum of run times,
%%%    where a timeout or error counts as twice the timeout (PAR2).
%%% @end
%%% Created : 11 Jan 2021 by Tony Rogvall <tony@rogvall.se>

-module(varp_tune).

-export([run/2, run/3]).
-export([ladder/0, ladder/1, demo/0]).
-export([search_e4/0, search_e4/1, e4_center/0, e4_spec/0]).
-export([default_spec/0, default_ladder/0, default_opts/0]).
-export([configs/2, command_line/1]).
-export([emit_csv/1, emit_csv/2]).
-export([write_csv/1, write_csv/2]).

-compile(export_all).

-include("varp.hrl").

-define(DEFAULT_TIMEOUT, 10).

%%% ------------------------------------------------------------------
%%% Defaults: the is_prime ladder
%%% ------------------------------------------------------------------

default_spec() ->
    [{global, [{qtype,     [lifo,fifo]},
	       {phase,     [true,false,undefined]},
	       {use_phase, [true,false]}]},
     {backjump, [{minimize,           [none,local,recursive]},
		 {bump,               [1,none,rank,{log,0.001,1.0}]},
		 {max_conflicts,      [1,{1,4}]},
		 {max_learned_factor, [0,{1.0,4.0}]},
		 {max_learned_inc,    [0,{1.0,2.0}]},
		 {keep_factor,        {0.1,0.9}},
		 {restart_counter,    [0,{log,1000,1000000}]}]}].

%% pairs of (p*q, prime) at 24, 28, 32 and 36 bits
default_ladder() ->
    [[prime(14777863,10),    prime(14777897,10)],
     [prime(164275543,30),   prime(164275547,30)],
     [prime(2635481573,90),  prime(2635481581,90)],
     [prime(38879389247,400),prime(38879389271,400)]].

prime(N, Timeout) ->
    {"is_prime.varp", [{<<"n">>,N}], Timeout}.

default_opts() ->
    #{ samples  => 96,
       baseline => true,
       keep     => 0.25,
       min_keep => 4,
       parallel => 3,
       final_parallel => 1,
       timeout  => ?DEFAULT_TIMEOUT,
       seed     => 1,
       mutations => 2,
       interval => 10,
       grace    => 10,
       log      => undefined,
       csv      => undefined,
       fixed    => [{print,false},{xref,true},{seed,1}]
     }.

%% Neighbourhood search around the best known recipe for is_prime
%% (2026-09-05, "E4"), with saturate and order in the chain.
e4_center() ->
    [{global,   [{qtype,fifo},{use_phase,true}]},
     {order,    [{sort,[identity]}]},
     {saturate, [{level,1},{laps,1},{timeout,2.0}]},
     {backjump, [{minimize,recursive},{max_learned_factor,2.0},
		 {max_learned_inc,1.2},{keep_factor,0.5},
		 {restart_counter,100000}]}].

e4_spec() ->
    [{global,   [{qtype,     [fifo,lifo]},
		 {phase,     [undefined,true,false]},
		 {use_phase, [true,false]}]},
     {order,    [{sort, [{value,[identity]},{value,[random]},{value,[degree]},
			 {value,['-degree']},{value,[rank]},{value,['-rank']}]}]},
     {saturate, [{level,   [1,2]},
		 {laps,    [1,2]},
		 {r,       [0,1,2,4]},
		 {q,       [0,1,2]},
		 {f,       [0,1,2]},
		 {timeout, [1.0,3.0]}]},
     {backjump, [{minimize,           [recursive,local,none]},
		 {bump,               [1,none,{log,0.01,1.0}]},
		 {max_learned_factor, {1.0,4.0}},
		 {max_learned_inc,    {1.0,1.6}},
		 {keep_factor,        {0.2,0.8}},
		 {restart_counter,    [0,{log,3000,1000000}]},
		 {restart_interval,   [infinity,{log,0.02,2.0}]}]}].

%% 24, 28 and 32 bit only; 36 bit is for confirming a winner by hand
search_e4() -> search_e4(#{}).
search_e4(Opts) ->
    Ladder = lists:sublist(default_ladder(), 3),
    run(Ladder, e4_spec(),
	maps:merge(#{ center => e4_center(), samples => 120,
		      mutations => 2, keep => 0.25, min_keep => 6 }, Opts)).

ladder() -> ladder(#{}).
ladder(Opts) -> run(default_ladder(), default_spec(), Opts).

%% quick smoke test: first stage only, few samples
demo() ->
    run([hd(default_ladder())], default_spec(),
	#{ samples => 8, parallel => 2 }).

%%% ------------------------------------------------------------------
%%% Main loop
%%% ------------------------------------------------------------------

run(Ladder, Spec) -> run(Ladder, Spec, #{}).
run(Ladder, Spec, Opts0) when is_list(Ladder), is_list(Spec), is_map(Opts0) ->
    application:ensure_all_started(varp),
    Log = open_file(maps:get(log, Opts0, undefined)),
    Csv = open_file(maps:get(csv, Opts0, undefined)),
    Opts = maps:merge(default_opts(), Opts0#{ log_fd => Log }),
    Configs = configs(Spec, Opts),
    NStages = length(Ladder),
    T0 = erlang:monotonic_time(),
    Progress = progress_start(maps:get(interval, Opts), Log, T0),
    log(Log, "tune: ~w configurations, ~w stages, parallel ~w\n",
	[length(Configs), NStages, maps:get(parallel, Opts)]),
    csv_header(Csv),
    try run_stages(Ladder, 1, NStages, Configs, Opts, Progress, Log, Csv, [])
    of
	Stages ->
	    [{_,Best}|_] = lists:last(Stages),
	    {Id,Score,Config,_} = Best,
	    log(Log, "winner: #~w score ~s\n", [Id, fmt_time(Score)]),
	    log(Log, "winner: ~s\n", [command_line(Config)]),
	    log(Log, "done: ~s\n", [fmt_time(elapsed(T0))]),
	    #{ best => Best, stages => Stages }
    catch
	?EXCEPTION(Class,Reason,Trace) ->
	    log(Log, "error: ~p:~p\n~p\n", [Class,Reason,?GET_STACK(Trace)]),
	    erlang:raise(Class,Reason,?GET_STACK(Trace))
    after
	progress_stop(Progress),
	close_file(Log),
	close_file(Csv)
    end.

run_stages([], _S, _N, _Configs, _Opts, _Progress, _Log, _Csv, Acc) ->
    lists:reverse(Acc);
run_stages([Stage|Ladder], S, N, Configs, Opts, Progress, Log, Csv, Acc) ->
    Instances = [load_instance(I, Opts) || I <- Stage],
    NRuns = length(Configs)*length(Instances),
    log(Log, "stage ~w/~w: ~w configurations x ~w instances (~s)\n",
	[S, N, length(Configs), length(Instances),
	 string:join([instance_name(I) || I <- Instances], ", ")]),
    progress_set(Progress, #{ stage => S, stages => N,
			      runs => 0, nruns => NRuns, best => none }),
    Parallel = case Ladder of
		   [] -> maps:get(final_parallel, Opts);
		   _ -> maps:get(parallel, Opts)
	       end,
    Results0 =
	pmap(fun({Id,Config}) ->
		     Rs = [run1(Id, Config, I, Opts, Progress) || I <- Instances],
		     Score = score(Rs),
		     csv_rows(Csv, S, Id, Config, Instances, Rs),
		     progress_result(Progress, Id, Score),
		     {Id, Score, Config, Rs}
	     end, Configs, Parallel),
    Results = lists:sort(fun({_,A,_,_},{_,B,_,_}) -> A =< B end, Results0),
    Ranked = lists:zip(lists:seq(1,length(Results)), Results),
    stage_table(Log, Ranked),
    Keep = max(maps:get(min_keep, Opts),
	       round(maps:get(keep, Opts) * length(Results))),
    Survivors = [{Id,Config} || {_,{Id,_,Config,_}} <-
				    lists:sublist(Ranked, Keep)],
    log(Log, "stage ~w/~w: done in ~s, keeping ~w: ~s\n",
	[S, N, fmt_time(progress_elapsed(Progress)), length(Survivors),
	 string:join(["#"++integer_to_list(Id) || {Id,_} <- Survivors], " ")]),
    run_stages(Ladder, S+1, N, Survivors, Opts, Progress, Log, Csv,
	       [Ranked|Acc]).

%% one run: configuration on instance.  The solver runs in its own
%% process under a hard wall-clock limit; a run that ignores its
%% timeout gets its stack logged, is killed and scores as a timeout.
run1(Id, Config, Inst, Opts, Progress) ->
    #{ timeout := Timeout } = Inst,
    Hard = trunc((2*Timeout + maps:get(grace, Opts))*1000),
    Log = maps:get(log_fd, Opts, undefined),
    T0 = erlang:monotonic_time(),
    {Pid,Ref} = spawn_monitor(fun() -> exit({run1, do_run1(Config, Inst, Opts)}) end),
    R = receive
	    {'DOWN',Ref,process,Pid,{run1,Res}} ->
		Res;
	    {'DOWN',Ref,process,Pid,Reason} ->
		#{ result => error, reason => Reason, time => elapsed(T0),
		   score => 2*Timeout, conflicts => 0, bcp => 0 }
	after Hard ->
		Info = process_info(Pid, [current_function, current_stacktrace,
					  message_queue_len, reductions]),
		log(Log, "hung: #~w ~s after ~s (timeout ~ws)\n~p\n~s\n",
		    [Id, instance_name(Inst), fmt_time(elapsed(T0)), Timeout,
		     Info, string:join(params_string(Config), " ")]),
		exit(Pid, kill),
		receive {'DOWN',Ref,process,Pid,_} -> ok end,
		#{ result => hung, reason => Info, time => elapsed(T0),
		   score => 2*Timeout, conflicts => 0, bcp => 0 }
	end,
    progress_run(Progress, Id),
    R#{ instance => instance_name(Inst) }.

do_run1(Config, Inst, Opts) ->
    #{ sections := Sections, form := Form, meta := Meta,
       timeout := Timeout } = Inst,
    Global = maps:get(fixed, Opts) ++ [{timeout,Timeout}] ++
	proplists:get_value(global, Config, []),
    Do = [{satisfy,[]} | [{P,Ps} || {P,Ps} <- Config, P =/= global]],
    T0 = erlang:monotonic_time(),
    try
	GOpts = varp:load_option_list(Global),
	GOpts1 = varp:section_opts(Sections, GOpts),
	GDo = varp:parse_do(Do),
	GOpts2 = GOpts1#{ meta => Meta },
	case varp:do_run(GDo, Form, GOpts2) of
	    {?INCONSISTENT,_,Bs} -> result(unsat, Bs, T0, Timeout);
	    {?DONE,_,Bs}         -> result(sat, Bs, T0, Timeout);
	    {?CONTINUE,_,Bs}     -> result(sat, Bs, T0, Timeout);
	    {?TIMEOUT,_,Bs}      -> result(timeout, Bs, T0, Timeout);
	    {Other,_,_} ->
		#{ result => error, reason => Other, time => elapsed(T0),
		   score => 2*Timeout, conflicts => 0, bcp => 0 }
	end
    catch
	?EXCEPTION(Class,Reason,_Trace) ->
	    #{ result => error, reason => {Class,Reason},
	       time => elapsed(T0), score => 2*Timeout,
	       conflicts => 0, bcp => 0 }
    end.

result(What, Bs, T0, Timeout) ->
    Time = elapsed(T0),
    Score = case What of
		timeout -> 2*Timeout;
		_ -> Time
	    end,
    #{ result => What, time => Time, score => Score,
       conflicts => varp_nif:getstat(Bs#bs.vp, conflict_counter),
       bcp => varp_nif:getstat(Bs#bs.vp, bcp_counter) }.

score(Rs) ->
    lists:sum([maps:get(score, R) || R <- Rs]).

elapsed(T0) ->
    erlang:convert_time_unit(erlang:monotonic_time()-T0,
			     native, microsecond) / 1000000.

%%% ------------------------------------------------------------------
%%% Instances
%%% ------------------------------------------------------------------

load_instance({File,Meta}, Opts) ->
    load_instance({File,Meta,maps:get(timeout,Opts)}, Opts);
load_instance({File,Meta0,Timeout}, _Opts) ->
    Meta = if is_list(Meta0) -> maps:from_list(Meta0); true -> Meta0 end,
    Filename = varp_filename(File),
    {ok,Bin} = file:read_file(Filename),
    case parse(binary_to_list(Bin), Meta) of
	{ok,{Sections,Form}} ->
	    #{ file => File, meta => Meta, timeout => Timeout,
	       sections => Sections, form => Form };
	Error ->
	    erlang:error({parse,Filename,Error})
    end.

instance_name(#{ file := File, meta := Meta }) ->
    Base = filename:rootname(filename:basename(File)),
    Base ++ lists:concat([[$\s,binary_to_list(K),$=,fmt(V)]
			  || {K,V} <- maps:to_list(Meta)]).

varp_filename(File) ->
    case filename:pathtype(File) of
	absolute -> File;
	_ ->
	    case filelib:is_file(File) of
		true -> File;
		false ->
		    filename:join([code:lib_dir(varp),"formulas","varp",File])
	    end
    end.

%%% ------------------------------------------------------------------
%%% Configurations
%%% ------------------------------------------------------------------

%% -> [{Id, [{Group,[{Key,Value}]}]}]
configs(Spec, Opts) ->
    Seed = maps:get(seed, Opts),
    rand:seed(exsss, {Seed, Seed*7919, Seed*104729}),
    Center = maps:get(center, Opts, undefined),
    Cs = case maps:get(samples, Opts) of
	     all -> grid(Spec);
	     N when is_integer(N), Center =:= undefined ->
		 random_configs(N, Spec);
	     N when is_integer(N) ->
		 [Center | mutations(N, Center, Spec, maps:get(mutations, Opts))]
	 end,
    %% plugin groups run in Spec order; a group absent from a
    %% configuration is not run at all
    Cs1 = dedup([[{G,proplists:get_value(G,C)} || {G,_} <- Spec,
					     lists:keymember(G,1,C)]
		 || C <- Cs]),
    Baseline = [[{G,[]} || {G,_} <- Spec]],
    All = case maps:get(baseline, Opts) of
	      true -> Baseline ++ (Cs1 -- Baseline);
	      false -> Cs1
	  end,
    Start = case maps:get(baseline, Opts) of true -> 0; false -> 1 end,
    lists:zip(lists:seq(Start, Start+length(All)-1), All).

%% Neighbourhood of Center: each sample changes M randomly chosen
%% parameters of Center to random values from their domains.  A
%% parameter in Spec that Center lacks is added with its sampled value.
mutations(N, Center, Spec, M) ->
    All = [{G,K,D} || {G,Params} <- Spec, {K,D} <- Params],
    [mutate(Center, pick_n(M, All)) || _ <- lists:seq(1,N)].

mutate(Config, Changes) ->
    lists:foldl(
      fun({G,K,D}, Cfg) ->
	      Params = proplists:get_value(G, Cfg, []),
	      Old = proplists:get_value(K, Params, undefined),
	      Params1 = lists:keystore(K, 1, Params, {K,pick_other(D, Old)}),
	      lists:keystore(G, 1, Cfg, {G,Params1})
      end, Config, Changes).

%% a value from Domain that differs from Old, if the domain allows it
pick_other(Domain, Old) -> pick_other(Domain, Old, 10).
pick_other(Domain, _Old, 0) -> pick(Domain);
pick_other(Domain, Old, I) ->
    case pick(Domain) of
	Old -> pick_other(Domain, Old, I-1);
	V -> V
    end.

pick_n(M, L) when M >= length(L) -> L;
pick_n(M, L) ->
    Shuffled = [X || {_,X} <- lists:sort([{rand:uniform(),X} || X <- L])],
    lists:sublist(Shuffled, M).

%% remove duplicates, keep first occurrences in order (the center
%% must stay first so it becomes configuration #1)
dedup(L) -> dedup(L, #{}, []).
dedup([], _Seen, Acc) -> lists:reverse(Acc);
dedup([X|Xs], Seen, Acc) ->
    case maps:is_key(X, Seen) of
	true -> dedup(Xs, Seen, Acc);
	false -> dedup(Xs, Seen#{X => true}, [X|Acc])
    end.

random_configs(N, Spec) ->
    [[{G,[{K,pick(D)} || {K,D} <- Params]} || {G,Params} <- Spec]
     || _ <- lists:seq(1,N)].

pick({value,V}) ->  %% literal value, needed when the value is a list
    V;
pick(Domain) when is_list(Domain) ->
    pick(lists:nth(rand:uniform(length(Domain)), Domain));
pick({log,A,B}) when is_number(A), is_number(B), A > 0, A =< B ->
    V = math:exp(math:log(A) + rand:uniform()*(math:log(B)-math:log(A))),
    if is_integer(A), is_integer(B) -> round(V);
       true -> round3(V)
    end;
pick({A,B}) when is_integer(A), is_integer(B), A =< B ->
    A + rand:uniform(B-A+1) - 1;
pick({A,B}) when is_number(A), is_number(B), A =< B ->
    round3(A + rand:uniform()*(B-A));
pick(Value) ->
    Value.

%% three significant digits keeps tables and command lines readable
round3(V) when V == 0 -> 0.0;
round3(V) ->
    E = math:floor(math:log10(abs(V))),
    M = math:pow(10, 2-E),
    round(V*M)/M.

%% full cartesian product; ranges are not allowed here
grid(Spec) ->
    grid_groups(Spec, []).

grid_groups([], Acc) -> [lists:reverse(Acc)];
grid_groups([{G,Params}|Spec], Acc) ->
    lists:append([grid_groups(Spec, [{G,Ps}|Acc]) || Ps <- grid_params(Params)]).

grid_params([]) -> [[]];
grid_params([{K,Domain}|Params]) ->
    Values = if is_list(Domain) -> Domain; true -> [Domain] end,
    [[{K,V}|Ps] || V <- Values, Ps <- grid_params(Params)].

%%% ------------------------------------------------------------------
%%% Output
%%% ------------------------------------------------------------------

%% configuration as a varp command line
command_line(Config) ->
    string:join(["varp"] ++ params_string(Config) ++ ["<file> [<bindings>]"], " ").

params_string(Config) ->
    G = ["--"++hyphen(K)++"="++fmt(V)
	 || {K,V} <- proplists:get_value(global, Config, [])],
    Ps = lists:append(
	   [[atom_to_list(P) | lists:append([["--"++hyphen(K), fmt(V)]
					     || {K,V} <- Params])]
	    || {P,Params} <- Config, P =/= global]),
    G ++ ["sat"] ++ Ps.

hyphen(Key) ->
    lists:map(fun($_) -> $-; (C) -> C end, atom_to_list(Key)).

fmt(undefined) -> "undefined";
fmt(V) when is_atom(V) -> atom_to_list(V);
fmt(V) when is_integer(V) -> integer_to_list(V);
fmt(V) when is_float(V) -> io_lib_format:fwrite_g(V);
fmt(V) when is_binary(V) -> binary_to_list(V);
fmt(V) when is_list(V) -> string:join([fmt(X) || X <- V], ",");
fmt(V) -> lists:flatten(io_lib:format("~p", [V])).

fmt_time(T) when is_number(T) ->
    lists:flatten(io_lib:format("~.2fs", [T*1.0])).

stage_table(Log, Ranked) ->
    lists:foreach(
      fun({Rank,{Id,Score,Config,Rs}}) ->
	      log(Log, "~4w #~-3w ~9s  ~s  ~s\n",
		  [Rank, Id, fmt_time(Score),
		   string:join([run_string(R) || R <- Rs], " "),
		   string:join(params_string(Config), " ")])
      end, Ranked).

run_string(#{ result := error, reason := Reason }) ->
    lists:flatten(io_lib:format("error(~p)", [Reason]));
run_string(#{ result := hung, time := T }) ->
    lists:flatten(io_lib:format("hung ~s", [fmt_time(T)]));
run_string(#{ result := What, time := T, conflicts := C }) ->
    lists:flatten(io_lib:format("~s ~s/~wc", [What, fmt_time(T), C])).

log(undefined, Fmt, Args) ->
    io:format(Fmt, Args);
log(Fd, Fmt, Args) ->
    io:format(Fmt, Args),
    io:format(Fd, Fmt, Args).

open_file(undefined) -> undefined;
open_file(File) ->
    {ok,Fd} = file:open(File, [append]),
    Fd.

close_file(undefined) -> ok;
close_file(Fd) -> file:close(Fd).

csv_header(undefined) -> ok;
csv_header(Fd) ->
    io:format(Fd, "stage;config;instance;result;time;conflicts;bcp;parameters\n", []).

csv_rows(undefined, _S, _Id, _Config, _Instances, _Rs) -> ok;
csv_rows(Fd, S, Id, Config, _Instances, Rs) ->
    Params = string:join(params_string(Config), " "),
    lists:foreach(
      fun(R) ->
	      io:format(Fd, "~w;~w;~s;~w;~s;~w;~w;~s\n",
			[S, Id, maps:get(instance,R), maps:get(result,R),
			 io_lib_format:fwrite_g(maps:get(time,R)*1.0),
			 maps:get(conflicts,R), maps:get(bcp,R), Params])
      end, Rs).

%%% ------------------------------------------------------------------
%%% Progress: one line every Interval seconds
%%% ------------------------------------------------------------------

progress_start(Interval, Log, T0) ->
    spawn_link(fun() ->
		       progress_loop(#{ stage => 0, stages => 0,
					runs => 0, nruns => 0,
					best => none, t0 => T0,
					stage_t0 => T0 },
				     trunc(Interval*1000), Log)
	       end).

progress_stop(Pid) ->
    Pid ! stop.

progress_set(Pid, Map) ->
    Pid ! {set, Map#{ stage_t0 => erlang:monotonic_time() }}.

progress_run(Pid, Id) ->
    Pid ! {run, Id}.

progress_result(Pid, Id, Score) ->
    Pid ! {result, Id, Score}.

progress_elapsed(Pid) ->
    Pid ! {elapsed, self()},
    receive {elapsed, Pid, T} -> T end.

progress_loop(St, Interval, Log) ->
    Timer = erlang:start_timer(Interval, self(), tick),
    progress_loop_(St, Interval, Log, Timer).

progress_loop_(St, Interval, Log, Timer) ->
    receive
	stop ->
	    ok;
	{set, Map} ->
	    progress_loop_(maps:merge(St, Map), Interval, Log, Timer);
	{run, _Id} ->
	    progress_loop_(St#{ runs => maps:get(runs,St)+1 },
			   Interval, Log, Timer);
	{result, Id, Score} ->
	    Best = case maps:get(best, St) of
		       none -> {Id,Score};
		       {_,S0} when Score < S0 -> {Id,Score};
		       B -> B
		   end,
	    progress_loop_(St#{ best => Best }, Interval, Log, Timer);
	{elapsed, From} ->
	    From ! {elapsed, self(), elapsed(maps:get(stage_t0, St))},
	    progress_loop_(St, Interval, Log, Timer);
	{timeout, Timer, tick} ->
	    #{ stage := S, stages := N, runs := R, nruns := NR,
	       best := Best, t0 := T0 } = St,
	    BestS = case Best of
			none -> "-";
			{Id,Score} ->
			    "#"++integer_to_list(Id)++" "++fmt_time(Score)
		    end,
	    log(Log, "progress: stage ~w/~w runs ~w/~w elapsed ~s best ~s\n",
		[S, N, R, NR, fmt_time(elapsed(T0)), BestS]),
	    progress_loop(St, Interval, Log)
    end.

%%% ------------------------------------------------------------------
%%% Parallel map with at most N workers, order preserved
%%% ------------------------------------------------------------------

pmap(F, L, N) when N =< 1 ->
    lists:map(F, L);
pmap(F, L, N) ->
    Parent = self(),
    %% Tag is unique per call: a worker's last {ready,..} from a previous
    %% pmap may still sit in our mailbox and must not be taken for a
    %% worker of this round.
    Tag = make_ref(),
    Jobs = lists:zip(lists:seq(1,length(L)), L),
    Workers = [spawn_link(fun() -> pmap_worker(Parent, Tag, F) end)
	       || _ <- lists:seq(1, min(N, length(L)))],
    Results = pmap_loop(Tag, Jobs, Workers, length(L), []),
    [R || {_,R} <- lists:keysort(1, Results)].

pmap_loop(Tag, Jobs, Workers, Left, Acc) when Left > 0 ->
    receive
	{ready, Tag, W} ->
	    case Jobs of
		[Job|Jobs1] ->
		    W ! {job, Tag, Job},
		    pmap_loop(Tag, Jobs1, Workers, Left, Acc);
		[] ->
		    W ! {stop, Tag},
		    pmap_loop(Tag, [], Workers, Left, Acc)
	    end;
	{result, Tag, I, R} ->
	    pmap_loop(Tag, Jobs, Workers, Left-1, [{I,R}|Acc])
    end;
pmap_loop(Tag, _Jobs, Workers, 0, Acc) ->
    lists:foreach(fun(W) -> W ! {stop, Tag} end, Workers),
    %% drop the ready messages of workers that finished last
    lists:foreach(fun(_) -> receive {ready, Tag, _} -> ok after 0 -> ok end end,
		  Workers),
    Acc.

pmap_worker(Parent, Tag, F) ->
    Parent ! {ready, Tag, self()},
    receive
	{job, Tag, {I,X}} ->
	    Parent ! {result, Tag, I, F(X)},
	    pmap_worker(Parent, Tag, F);
	{stop, Tag} ->
	    ok
    end.

%%% ------------------------------------------------------------------
%%% Parsing and the old CSV helpers
%%% ------------------------------------------------------------------


parse(String, Meta) ->
    parse(String, Meta, false).

parse(String, Meta, ICase) ->
    Scan = if ICase -> varp_scani;
	      true -> varp_scan
	   end,
    case varp_dimacs:detect_data(String) of
	false ->
	    Scan:init(varp:remove_comments(String)),
	    case varp_parse:parse_and_scan({Scan, one_token, []}) of
		{ok,{Sections,_Assignments,Formula}} ->
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
	{ok,_CnfType} ->
	    parse_dimacs(String)
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
    io:format(Fd, "\"~s\"; ", [uppercase(Key)]), 
    emit_header(Fd, Tail);
emit_header(_Fd, []) ->
    ok.

uppercase(Key) when is_atom(Key) ->
    string:uppercase(atom_to_list(Key));
uppercase(Key) when is_list(Key) ->
     string:uppercase(Key).

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


grid_search(Run, GrpList) ->
    gfold(fun(Params,{I,ResList}) ->
		  case Run(I,Params) of
		      [] -> {I,ResList};
		      Res ->
			  Res1 = [{run,I}|Res]++Params,
			  {I+1,[Res1|ResList]}
		  end
	  end,
	  {1,[]},
	  GrpList).

%% gfold (multi/grouped/zip)
%% fold over group of keyvalues lists
%%   
%%  gfold(Fun, Acc, [{Group::key(),[{Key::key(),[Value::term()]}]}])
%%
%%  gfold(Fun, Acc, [{a,[{x,[1,2]},{y,[3]}]}, {b,[{u,[4,5]}]}])
%%
%%  callback on:
%%     [{a,[{x,1},{y,3}]},{b,[{u,4}]}]
%%     [{a,[{x,1},{y,3}]},{b,[{u,5}]}]
%%     [{a,[{x,2},{y,3}]},{b,[{u,4}]}]
%%     [{a,[{x,2},{y,3}]},{b,[{u,5}]}]
%%
gfold(Fun, Acc, GrpList) ->
    gfold(Fun, Acc, GrpList, [], []).

gfold(Fun, Acc, [{Grp,[{Key,[Value]}|KVs]} | GrpList], Acc1, Acc2) ->
    gfold(Fun, Acc, [{Grp,KVs}|GrpList], [{Key,Value}|Acc1], Acc2);

gfold(Fun, Acc, [{Grp,[{Key,[Value|Vs]}|KVs]} | GrpList], Acc1, Acc2) ->
    Ai = gfold(Fun, Acc, [{Grp,KVs}|GrpList], [{Key,Value}|Acc1], Acc2),
    gfold(Fun, Ai, [{Grp,[{Key,Vs}|KVs]}|GrpList], Acc1, Acc2);
gfold(Fun, Acc, [{Grp,[{_Key,[]}|KVs]} | GrpList], Acc1, Acc2) ->
    gfold(Fun, Acc, [{Grp,KVs} | GrpList], Acc1, Acc2);

gfold(Fun, Acc, [{Grp,[]} | GrpList], Acc1, Acc2) ->
    gfold(Fun, Acc, GrpList, [], [{Grp,lists:reverse(Acc1)}|Acc2]);

gfold(Fun, Acc, [], [], Acc2) ->
    Fun(lists:reverse(Acc2), Acc).
