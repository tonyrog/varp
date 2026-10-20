%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2026, Tony Rogvall
%%% @doc
%%%    varp plugin: run the rest of the chain in N cloned instances
%%%
%%%    varp sat parallel --clones 8 bj formula.varp
%%%
%%%    Every clone is a copy of the built formula (varp_nif:clone) in a
%%%    process of its own, with a seed of its own and, after the first
%%%    clone, a random variable order.  The first clone to finish wins,
%%%    the others are killed.
%%%
%%%    A distributor process subscribes to the permanent (level 0)
%%%    bindings and substitutions of every clone and hands each new one
%%%    to all clones, which import them at their next restart (see the
%%%    import hook in varp_backjump) or between two probes (saturate),
%%%    and to the original instance, so a monitor on it sees them and
%%%    the formula keeps what the race found.  A fact one clone learns
%%%    is sound for the formula, so every clone may use it.
%%%
%%%    Short clauses learned by backjump in one clone go to the others
%%%    through a ring: an ETS table with a sequence number per clause,
%%%    which every clone reads from its own cursor at a restart (see
%%%    the export and import_clauses hooks in varp_backjump). Old
%%%    entries are dropped as the ring moves on; a clone far behind
%%%    misses them, which is no harm, they are learned clauses.
%%%
%%%    A saturate in the chain is divided: clone i probes segment i of
%%%    the variables (see --segment in varp_saturate), so the clones
%%%    together probe every vector once and share what they find. The
%%%    segment of a variable is that of its equivalence class (the
%%%    substitutions shared so far, kept as a union-find per clone):
%%%    probing one member of a class is probing them all, and which
%%%    member is the free one differs between the clones, so the class
%%%    must have one owner whichever member stands for it.
%%%
%%%    The first clone with a decisive result (models, inconsistent, an
%%%    abort) answers; a clone that just continues (saturate at its
%%%    fixpoint, no models) is waited out, and when every clone does
%%%    that the answer is continue with the original instance, which
%%%    then holds all the shared facts.
%%% @end
%%% Created : 19 Oct 2026 by Tony Rogvall <tony@rogvall.se>

-module(varp_parallel).
-behaviour(varp_plugin).

-export([options/0, run/2]).
-export([drain_facts/0, drain_now/0, idle/1]).

-include("varp.hrl").

%% facts are imported in batches: when this many are pending, or when
%% the oldest pending fact is this old (ms), so a trickle of single
%% facts does not restart the search every time
-define(IMPORT_BATCH, 32).
-define(IMPORT_AGE, 200).

%% the clause ring: entries older than this many clauses are dropped,
%% every so many exports
-define(RING_SIZE, 65536).
-define(RING_SWEEP, 4096).

%% the ring, in the clone's Param
%% the cube queue of the driver
-record(cq, {queue, acc, max}).

-record(ring, {tab, seq, len}).

%% the distributor's state (see the distributor below)
-record(dist, {
	  driver,          %% gets the facts too, for the original
	  ref,             %% tags the messages to the driver
	  clones = [],     %% the subscribed clone processes
	  seen = #{},      %% the facts sent, once each
	  n = 0,           %% number of facts sent
	  idle = #{},      %% clones idle on all n facts
	  done = #{}       %% clones past saturate, never waited for
	 }).

options() ->
    [#{ long => "clones",
	short => "n",
	key => clones,
	spec => unsigned,
	default => erlang:system_info(schedulers_online),
	description => "Number of clones (default: online schedulers)."
      },
     #{ long => "seed",
	key => seed,
	spec => integer,
	default => -1,
	description => "Base seed, clone i gets seed+i (-1: the formula's)."
      },
     #{ long => "shuffle",
	key => shuffle,
	spec => {enum,[?BOOL]},
	default => true,
	description => "Random variable order in every clone but the first."
      },
     #{ long => "share",
	key => share,
	spec => {enum,[?BOOL]},
	default => true,
	description => "Share permanent bindings and substitutions between the clones."
      },
     #{ long => "cubes",
	key => cubes,
	spec => unsigned,
	default => 0,
	description => "Split the search instead of repeating it: cubes over "
		       "the first N variables of the order, handed to the "
		       "clones from a queue (0: every clone searches everything)."
      },
     #{ long => "share-len",
	key => share_len,
	spec => unsigned,
	default => 8,
	description => "Share learned clauses up to this length (0: none)."
      },
     #{ long => "stat",
	key => stat,
	spec => {enum,[?BOOL]},
	default => false,
	description => "Report the winner, what was shared and every clone's counters."
      }].

%% the chain after parallel comes in Param (varp:do/3 puts it there)
run(Bs, Param) when is_record(Bs, bs), is_map(Param) ->
    case maps:get(chain, Param, []) of
	[] ->
	    io:format("parallel: no solver after parallel, nothing to run\n"),
	    {?CONTINUE, [], Bs};
	Chain ->
	    N = max(1, maps:get(clones, Param)),
	    run_clones(Bs, Param, Chain, N)
    end.

run_clones(Bs, Param, Chain, N) ->
    Vp = Bs#bs.vp,
    %% the messages to the driver carry a reference of this run: the
    %% driver may be a long-lived process (a shell, a test) and a clone
    %% that finished just as the winner did leaves its result behind
    Ref = make_ref(),
    Seed0 = case maps:get(seed, Param) of
		-1 -> varp_nif:getopt(Vp, seed);
		S -> S
	    end,
    Share = maps:get(share, Param),
    %% the cubes are made on the original before anything else happens
    %% to it; no cube at all means propagation refutes every assignment
    case cube_mode(Vp, Param, Chain) of
	{cubes, [], _} ->
	    stat(Param, "parallel: no cube survives propagation\n", []),
	    varp:no_models(Bs);
	Mode ->
	    run_clones(Bs, Param, Chain, N, Mode, Ref, Seed0, Share)
    end.

run_clones(Bs, Param, Chain, N, Mode, Ref, Seed0, Share) ->
    Vp = Bs#bs.vp,
    Driver = self(),
    case Mode of
	{cubes, Cubes, _} ->
	    stat(Param, "parallel: ~w cubes over ~w variables\n",
		 [length(Cubes), maps:get(cubes, Param)]);
	portfolio ->
	    ok
    end,
    Dist = case Share of
	       true -> spawn_link(fun() -> distributor(#dist{driver=Driver, ref=Ref}) end);
	       false -> undefined
	   end,
    %% substitutions go into the original with subst, which needs the
    %% cross reference; it is put back as it was afterwards
    Xref = varp_nif:getopt(Vp, xref),
    Share andalso varp_nif:setopt(Vp, xref, true),
    Ring = case Share andalso maps:get(share_len, Param) > 0 of
	       true ->
		   #ring{tab = ets:new(varp_shared_clauses,
				       [ordered_set, public,
					{write_concurrency, true},
					{read_concurrency, true}]),
			 seq = atomics:new(1, []),
			 len = maps:get(share_len, Param)};
	       false ->
		   undefined
	   end,
    Chain1 = clause_chain(import_chain(Chain, Dist), Ring),
    %% the instances are cloned here so that the driver can read their
    %% counters at the end, also from the clones that were killed; the
    %% counters start as the original's (varp_nif:clone copies them)
    Instances = [begin
		     W = varp_nif:clone(Vp, #{level => 0, set => [alpha,beta,gamma,delta]}),
		     {I, W, snapshot(W)}
		 end || I <- lists:seq(0, N-1)],
    Clones = [{I, spawn_link(fun() ->
				     clone(I, N, Bs#bs{vp = W}, Param, Chain1,
					   Seed0+I, Dist, Driver, Ref, Mode)
			     end)} || {I, W, _} <- Instances],
    T0 = erlang:monotonic_time(millisecond),
    Result = case Mode of
		 portfolio ->
		     wait_result(Bs, Ref, Dist, Clones, []);
		 {cubes, Cubes0, Max} ->
		     Q = #cq{queue = Cubes0, max = Max, acc = acc0(Vp)},
		     wait_cubes(Bs, Ref, Dist, Clones, Q, [])
	     end,
    T1 = erlang:monotonic_time(millisecond),
    Shared = stop_distributor(Dist),
    import_original(Bs, drain_all(Ref)),
    flush_results(Ref),
    varp_nif:setopt(Vp, xref, Xref),
    SharedClauses = stop_ring(Ring),
    case Result of
	{Winner, {R, Acc, BsW}} ->
	    stat(Param, "parallel: clone ~w finished first (~.2fs), ~w facts and ~w clauses shared\n",
		 [Winner, (T1-T0)/1000, Shared, SharedClauses]),
	    clone_summary(Param, Instances, Winner),
	    output_models(Bs, BsW, Acc),
	    {R, Acc, BsW};
	{cubes, Acc} ->
	    %% every cube searched: the models of all of them, or none
	    stat(Param, "parallel: all cubes searched (~.2fs), ~w facts and ~w clauses shared\n",
		 [(T1-T0)/1000, Shared, SharedClauses]),
	    clone_summary(Param, Instances, none),
	    case Acc of
		_ when Acc =:= []; Acc =:= 0 ->
		    varp:no_models(Bs);
		_ ->
		    output_models(Bs, Bs, Acc),
		    {?DONE, Acc, Bs}
	    end;
	{all, Results} ->
	    stat(Param, "parallel: all ~w clones finished (~.2fs), ~w facts and ~w clauses shared\n",
		 [N, (T1-T0)/1000, Shared, SharedClauses]),
	    clone_summary(Param, Instances, none),
	    %% the original has every shared fact; without sharing the
	    %% facts are in the clones, so the first one answers
	    case Share of
		true ->
		    {?CONTINUE, [], Bs};
		false ->
		    {_, {_, _, Bs0}} = lists:keyfind(0, 1, Results),
		    {?CONTINUE, [], Bs0}
	    end;
	{Winner, Other} ->
	    io:format("parallel: clone ~w failed: ~p\n", [Winner, Other]),
	    {?ERROR, [], Bs}
    end.

%% the solvers in the chain get the import hook: backjump takes the
%% facts in batches at a restart, saturate takes them all between two
%% probes (its lap stands at level 0, so there is nothing to undo)
import_chain(Chain, undefined) ->
    Chain;
import_chain(Chain, _Dist) ->
    [case P of
	 varp_backjump -> {P, Prm#{import => fun ?MODULE:drain_facts/0}};
	 varp_saturate -> {P, Prm#{import => fun ?MODULE:drain_now/0,
				   idle => fun ?MODULE:idle/1}};
	 _ -> {P, Prm}
     end || {P, Prm} <- Chain].

%% the backjump plugins in the chain get the clause ring
clause_chain(Chain, undefined) ->
    Chain;
clause_chain(Chain, Ring) ->
    [case P of
	 varp_backjump ->
	     {P, Prm#{export => fun(Lits) -> export_clause(Ring, Lits) end,
		      import_clauses => fun() -> import_clauses(Ring) end,
		      share_len => Ring#ring.len}};
	 _ -> {P, Prm}
     end || {P, Prm} <- Chain].

%% the clauses shared, and the ring is gone
stop_ring(undefined) ->
    0;
stop_ring(#ring{tab=Tab, seq=Seq}) ->
    N = atomics:get(Seq, 1),
    ets:delete(Tab),
    N.

%% the export hook, run in the clone process on a short learned
%% clause: into the ring under the next sequence number, and now and
%% then the oldest entries are dropped
export_clause(#ring{tab=Tab, seq=Seq}, Lits) ->
    N = atomics:add_get(Seq, 1, 1),
    ets:insert(Tab, {N, self(), Lits}),
    case N rem ?RING_SWEEP of
	0 when N > ?RING_SIZE ->
	    ets:select_delete(Tab, [{{'$1', '_', '_'}, [{'<', '$1', N - ?RING_SIZE}], [true]}]);
	_ ->
	    ok
    end.

%% the import hook, run in the clone process at a restart: the clauses
%% of the others since the clone's cursor, in batches like the facts
import_clauses(#ring{tab=Tab, seq=Seq}) ->
    N = atomics:get(Seq, 1),
    Cursor = case get(clause_cursor) of
		 undefined -> N;      %% nothing before the clone started
		 C -> C
	     end,
    Now = erlang:monotonic_time(millisecond),
    Since = case get(clause_import_time) of
		undefined -> put(clause_import_time, Now), Now;
		T -> T
	    end,
    if N - Cursor >= ?IMPORT_BATCH; N > Cursor, Now - Since >= ?IMPORT_AGE ->
	    put(clause_cursor, N),
	    put(clause_import_time, Now),
	    Self = self(),
	    ets:select(Tab, [{{'$1', '$2', '$3'},
			      [{'>', '$1', Cursor}, {'=<', '$1', N}, {'=/=', '$2', Self}],
			      ['$3']}]);
       true ->
	    []
    end.

%% clone I of N probes segment I when it saturates (when the clones
%% share what they find, that is; without sharing each probes it all):
%% the variables whose equivalence class, by its lowest member, is
%% I modulo N
segment_chain(Chain, _I, _N, undefined) ->
    Chain;
segment_chain(Chain, I, N, _Dist) ->
    Mine = fun(X) -> class_of(abs(X)) rem N =:= I end,
    [case P of
	 varp_saturate -> {P, Prm#{segment => Mine}};
	 _ -> {P, Prm}
     end || {P, Prm} <- Chain].

%% the equivalence classes of the substitutions this clone has
%% received, a union-find in the process dictionary keyed by variable:
%% the class is named by its lowest variable
class_of(X) ->
    case get({class, X}) of
	undefined -> X;
	Y -> class_of(Y)
    end.

note_fact({X, Y}) ->
    case {class_of(abs(X)), class_of(abs(Y))} of
	{C, C} -> ok;
	{Cx, Cy} when Cx < Cy -> put({class, Cy}, Cx);
	{Cx, Cy} -> put({class, Cx}, Cy)
    end;
note_fact(_X) ->
    ok.

%% the first clone with a decisive answer wins, the rest are killed
%% (unlinked first, a linked kill would take the driver with it); a
%% clone that just continues is noted, and when all do, that is the
%% answer. Meanwhile the facts the clones share go into the original
wait_result(Bs, Ref, Dist, Clones, Done) ->
    receive
	{result, Ref, I, Pid, Result} ->
	    case decisive(Result) of
		true ->
		    kill_clones([P || {_, P} <- Clones, P =/= Pid]),
		    unlink(Pid),
		    {I, Result};
		false ->
		    unlink(Pid),
		    %% the others need not wait for this one at a fixpoint
		    Dist =/= undefined andalso (Dist ! {done, Pid}),
		    Done1 = [{I, Result}|Done],
		    case length(Done1) =:= length(Clones) of
			true -> {all, Done1};
			false -> wait_result(Bs, Ref, Dist, Clones, Done1)
		    end
	    end;
	{fact, Ref, Fact} ->
	    import_original(Bs, [Fact]),
	    wait_result(Bs, Ref, Dist, Clones, Done)
    end.

%% --cubes K: the search is split instead of repeated. A cube is an
%% assignment of the first K unbound variables of the order that
%% propagation does not refute; the clones take cubes from the queue
%% here and search under them as assumptions (backtrack and backjump
%% take assume in Param; what they learn never depends on the
%% assumptions, so facts and clauses are still shared). The models of
%% the cubes are disjoint, so counting adds up; the first model wins
%% when max is 1, and max models in all end it otherwise. A cube
%% without models is DONE with nothing, just the next cube;
%% INCONSISTENT is a contradiction at level 0, the formula has no
%% models at all (and the instance is spent), so it ends everything.
%% The part of the chain before the search (saturate, order) runs
%% once in every clone.
cube_mode(Vp, Param, Chain) ->
    case maps:get(cubes, Param) of
	0 ->
	    portfolio;
	K ->
	    case [Prm || {P, Prm} <- Chain, is_search(P)] of
		[] ->
		    io:format("parallel: --cubes needs backtrack or backjump "
			      "in the chain, every clone searches everything\n"),
		    portfolio;
		[SearchParam|_] ->
		    {cubes, cubes(Vp, K), maps:get(max, SearchParam, 1)}
	    end
    end.

is_search(varp_backtrack) -> true;
is_search(varp_backjump) -> true;
is_search(_) -> false.

%% the cubes as literal lists, in the order of a depth first walk; a
%% variable the cube so far already binds is left out of it
cubes(Vp, K) ->
    Vars = lists:sublist(varp:order_all(Vp), K),
    Level = varp_nif:level(Vp),
    Cubes = cubes_(Vp, Vars, [], []),
    varp_nif:pop(Vp, Level),
    lists:reverse(Cubes).

cubes_(_Vp, [], Cube, Acc) ->
    [lists:reverse(Cube)|Acc];
cubes_(Vp, [X|Xs], Cube, Acc) ->
    case varp_nif:value(Vp, X) of
	undefined ->
	    Acc1 = cube_branch(Vp, X, Xs, Cube, Acc),
	    cube_branch(Vp, -X, Xs, Cube, Acc1);
	_ ->
	    cubes_(Vp, Xs, Cube, Acc)
    end.

cube_branch(Vp, L, Xs, Cube, Acc) ->
    Level = varp_nif:level(Vp),
    varp_nif:push(Vp),
    Acc1 = case varp_nif:bind(Vp, L) andalso varp_nif:bcp(Vp) of
	       true -> cubes_(Vp, Xs, [L|Cube], Acc);
	       false -> Acc
	   end,
    varp_nif:pop(Vp, Level),
    Acc1.

acc0(Vp) ->
    case varp_nif:getopt(Vp, method) of
	count -> 0;
	_ -> []
    end.

%% the driver in cube mode: hands out cubes, adds up what comes back
wait_cubes(Bs, Ref, Dist, Clones, Q, Done) ->
    receive
	{next_cube, Ref, Pid} ->
	    case Q#cq.queue of
		[C|Cs] ->
		    Pid ! {cube, Ref, C},
		    wait_cubes(Bs, Ref, Dist, Clones, Q#cq{queue = Cs}, Done);
		[] ->
		    Pid ! {cube, Ref, done},
		    wait_cubes(Bs, Ref, Dist, Clones, Q, Done)
	    end;
	{cube_result, Ref, I, _Pid, Result} ->
	    case Result of
		{?INCONSISTENT, _, BsW} ->
		    kill_clones([P || {_, P} <- Clones]),
		    {I, {?INCONSISTENT, Q#cq.acc, BsW}};
		{R, Acc1, BsW} when R =:= ?DONE; R =:= ?CONTINUE ->
		    Acc = varp:combine_result(Q#cq.acc, Acc1),
		    case enough(Acc, Q#cq.max) of
			true ->
			    %% the winner keeps asking for cubes, so it goes too
			    kill_clones([P || {_, P} <- Clones]),
			    {I, {?DONE, Acc, BsW}};
			false ->
			    wait_cubes(Bs, Ref, Dist, Clones, Q#cq{acc = Acc}, Done)
		    end;
		{What, Acc1, BsW} ->
		    kill_clones([P || {_, P} <- Clones]),
		    {I, {What, varp:combine_result(Q#cq.acc, Acc1), BsW}};
		Other ->
		    kill_clones([P || {_, P} <- Clones]),
		    {I, Other}
	    end;
	{result, Ref, I, Pid, Result} ->
	    %% the chain before the search was decisive, or the clone
	    %% found the queue empty
	    case decisive(Result) of
		true ->
		    kill_clones([P || {_, P} <- Clones, P =/= Pid]),
		    unlink(Pid),
		    {I, Result};
		false ->
		    unlink(Pid),
		    Dist =/= undefined andalso (Dist ! {done, Pid}),
		    Done1 = [{I, Result}|Done],
		    case length(Done1) =:= length(Clones) of
			true -> {cubes, Q#cq.acc};
			false -> wait_cubes(Bs, Ref, Dist, Clones, Q, Done1)
		    end
	    end;
	{fact, Ref, Fact} ->
	    import_original(Bs, [Fact]),
	    wait_cubes(Bs, Ref, Dist, Clones, Q, Done)
    end.

enough(_Acc, 0) -> false;
enough(Acc, Max) when is_integer(Acc) -> Acc >= Max;
enough(Acc, Max) -> length(Acc) >= Max.

%% the losers are killed and waited for, so that nobody touches an
%% instance when its counters are read; a clone that has already
%% finished is gone, which the monitor reports just the same
kill_clones(Pids) ->
    Mons = [begin
		unlink(P),
		M = monitor(process, P),
		exit(P, kill),
		M
	    end || P <- Pids],
    [receive {'DOWN', M, process, _, _} -> ok after 5000 -> ok end || M <- Mons],
    ok.

%% the counters of an instance when its clone starts; the clone adds
%% to them, so the difference at the end is the clone's own work
snapshot(W) ->
    {varp_nif:getstat(W, conflict_counter), varp_nif:getstat(W, bcp_counter)}.

%% with --stat: one line per clone and the sum, the way to see what
%% all the clones did and not only the winner
clone_summary(Param, Instances, Winner) ->
    case maps:get(stat, Param) of
	false ->
	    ok;
	true ->
	    Rows = [{I,
		     varp_nif:getstat(W, conflict_counter) - C0,
		     varp_nif:getstat(W, bcp_counter) - B0,
		     varp_nif:getstat(W, number_of_clauses),
		     varp_nif:getstat(W, number_of_dead_clauses)}
		    || {I, W, {C0, B0}} <- Instances],
	    [io:format("parallel: clone ~3w: #conflict:~w, bcp:~w, #clauses:~w, #dead:~w~s\n",
		       [I, C, B, Nc, Nd, case I of Winner -> " *"; _ -> "" end])
	     || {I, C, B, Nc, Nd} <- Rows],
	    io:format("parallel: total: #conflict:~w, bcp:~w\n",
		      [lists:sum([C || {_, C, _, _, _} <- Rows]),
		       lists:sum([B || {_, _, B, _, _} <- Rows])])
    end.

%% continue without models is what saturate at its fixpoint, or a
%% search that just ran out, says: nothing to answer with yet
decisive({?CONTINUE, [], _Bs}) -> false;
decisive({?CONTINUE, 0, _Bs}) -> false;
decisive(_) -> true.

%% a fact goes into the original at level 0; a contradiction means the
%% formula has no models, which the clones report on their own, so the
%% original is just left as it is
import_original(_Bs, []) ->
    ok;
import_original(Bs, Facts) ->
    Vp = Bs#bs.vp,
    case varp_nif:level(Vp) of
	0 -> _ = varp:import_facts(Vp, Facts), ok;
	_ -> ok
    end.

drain_all(Ref) ->
    receive
	{fact, Ref, Fact} -> [Fact|drain_all(Ref)]
    after 0 ->
	[]
    end.

%% the results of clones that finished as the winner did
flush_results(Ref) ->
    receive
	{result, Ref, _I, _Pid, _Result} -> flush_results(Ref);
	{cube_result, Ref, _I, _Pid, _Result} -> flush_results(Ref);
	{next_cube, Ref, _Pid} -> flush_results(Ref)
    after 0 ->
	ok
    end.

stop_distributor(undefined) ->
    0;
stop_distributor(Dist) ->
    Dist ! {stop, self()},
    receive
	{shared, Dist, N} -> N
    after 5000 -> 0
    end.

stat(Param, Fmt, Args) ->
    case maps:get(stat, Param) of
	true -> io:format(Fmt, Args);
	false -> ok
    end.

%% the clones solve with printing off, the winner's models are printed
%% here, once
output_models(Bs, BsW, Models) when is_list(Models) ->
    Flavour = varp_nif:getopt(Bs#bs.vp, print),
    varp_nif:setopt(BsW#bs.vp, print, Flavour, user),
    lists:foldl(fun(Model, I) ->
			varp:output_model(BsW, false, I, Model),
			I+1
		end, 1, lists:reverse(Models)),
    ok;
output_models(_Bs, _BsW, _Count) ->
    ok.

%%--------------------------------------------------------------------
%% the clone process
%%--------------------------------------------------------------------

%% Bs holds the clone's own instance (cloned by the driver)
clone(I, N, Bs, Param, Chain0, Seed, Dist, Driver, Ref, Mode) ->
    process_flag(trap_exit, false),
    put(distributor, Dist),
    Chain = offset_chain(segment_chain(Chain0, I, N, Dist), I),
    W = Bs#bs.vp,
    varp_nif:setopt(W, seed, Seed),
    varp_nif:setopt(W, print, false, user),
    case I > 0 andalso maps:get(shuffle, Param) of
	true -> varp_nif:order_sort(W, random, Seed);
	false -> ok
    end,
    subscribe(Dist, W),
    BsW = Bs#bs{ counters = counters:new(?NUM_COUNTERS, []),
		 d1 = counters:new(1024, []),
		 d2 = counters:new(1024, []),
		 clen = counters:new(1024, []) },
    put(output_model_header, false),  %% the driver prints the header
    Result = try search(Mode, Chain, BsW, Driver, Ref, I)
	     catch ?EXCEPTION(Class, Reason, Trace) ->
		     {crashed, {Class, Reason, ?GET_STACK(Trace)}}
	     end,
    Driver ! {result, Ref, I, self(), Result}.

search(portfolio, Chain, Bs, _Driver, _Ref, _I) ->
    varp:do(Chain, [], Bs);
search({cubes, _, _}, Chain, Bs, Driver, Ref, I) ->
    {Prefix, Search} = lists:splitwith(fun({P, _}) -> not is_search(P) end, Chain),
    case varp:do(Prefix, [], Bs) of
	{?CONTINUE, Acc, Bs1} when Acc =:= []; Acc =:= 0 ->
	    %% a pass line and a counter block per cube is too much
	    Opt = Bs1#bs.option,
	    Log = min(maps:get(log, Opt, ?LOG_LEVEL_NONE), ?LOG_LEVEL_WARNING),
	    cube_loop(Search, Bs1#bs{option = Opt#{log => Log}}, Driver, Ref, I);
	Decisive ->
	    Decisive
    end.

%% one cube at a time from the driver, the search under it as
%% assumptions; the instance is back at level 0 before the next
cube_loop(Search, Bs, Driver, Ref, I) ->
    Driver ! {next_cube, Ref, self()},
    receive
	{cube, Ref, done} ->
	    {?CONTINUE, [], Bs};
	{cube, Ref, Cube} ->
	    Result = varp:do(assume_chain(Search, Cube), [], Bs),
	    varp_nif:pop(Bs#bs.vp, 0),
	    Driver ! {cube_result, Ref, I, self(), Result},
	    cube_loop(Search, Bs, Driver, Ref, I)
    end.

assume_chain(Chain, Cube) ->
    [case is_search(P) of
	 true -> {P, Prm#{assume => Cube}};
	 false -> {P, Prm}
     end || {P, Prm} <- Chain].

%% clone I takes step I of a backjump restart strategy (--restart)
%% first, so that the clones try different things
offset_chain(Chain, I) ->
    [case P of
	 varp_backjump -> {P, Prm#{restart_offset => I}};
	 _ -> {P, Prm}
     end || {P, Prm} <- Chain].

%% the distributor must be the subscriber (the nif sends to the caller
%% of subscribe), and the search waits until it listens
subscribe(undefined, _W) ->
    ok;
subscribe(Dist, W) ->
    Dist ! {subscribe, self(), W},
    receive
	{subscribed, Dist} -> ok
    end.

%% the import hook, run by backjump at its restart point in the clone
%% process: the facts the distributor sent, in batches
drain_facts() ->
    Pending = drain(get(pending_facts)),
    Now = erlang:monotonic_time(millisecond),
    case Pending of
	{[], _} ->
	    [];
	{Lits, Since} when length(Lits) >= ?IMPORT_BATCH; Now - Since >= ?IMPORT_AGE ->
	    erase(pending_facts),
	    Lits;
	_ ->
	    put(pending_facts, Pending),
	    []
    end.

drain(undefined) ->
    drain({[], erlang:monotonic_time(millisecond)});
drain({Facts, Since}) ->
    receive
	{fact, Fact} -> count_fact(Fact), drain({[Fact|Facts], Since})
    after 0 ->
	{Facts, Since}
    end.

%% the import hook for saturate: everything that has arrived, at once
drain_now() ->
    {Facts, _Since} = drain(get(pending_facts)),
    erase(pending_facts),
    Facts.

%% the facts this clone has received, so the distributor can tell an
%% idle report that has seen everything it sent from one that has not;
%% a substitution also goes into the classes
count_fact(Fact) ->
    note_fact(Fact),
    put(fact_count, fact_count() + 1).

fact_count() ->
    case get(fact_count) of
	undefined -> 0;
	N -> N
    end.

%% the idle hook for saturate, run in the clone process. At its
%% fixpoint (true) the clone tells the distributor, then waits for
%% facts from the others to lap on again, or for finish when every
%% clone is there. Leaving saturate another way (laps, timeout) it
%% says it is done, so the others do not wait for it.
idle(true) ->
    get(distributor) ! {idle, self(), fact_count()},
    receive
	{fact, Fact} -> count_fact(Fact), [Fact|drain_now()];
	finish -> finish
    end;
idle(false) ->
    get(distributor) ! {done, self()},
    finish.

%%--------------------------------------------------------------------
%% the distributor: one subscriber for every clone, each permanent
%% binding X and substitution {X,Y} goes to all clones and the driver
%% once (an instance that has it already ignores it, so nothing echoes)
%%
%% It also keeps the saturating clones together at the fixpoint: a
%% clone that has nothing more to find says idle with the number of
%% facts it has received, a fact sent out puts everyone back to work,
%% and when every clone is idle on everything sent (or done with
%% saturate) they all get finish. The messages from a clone (its
%% facts, then its idle) and to it (facts, then finish) are each in
%% order, so a clone counted idle has seen every fact there is.
%%--------------------------------------------------------------------

distributor(D=#dist{driver=Driver, ref=Ref, clones=Clones, seen=Seen, n=N}) ->
    receive
	{subscribe, Pid, W} ->
	    ok = varp_nif:subscribe(W, variable),
	    Pid ! {subscribed, self()},
	    distributor(D#dist{clones=[Pid|Clones]});
	{varp, Fact, _Info} ->
	    case maps:is_key(Fact, Seen) of
		true ->
		    distributor(D);
		false ->
		    Driver ! {fact, Ref, Fact},
		    [Pid ! {fact, Fact} || Pid <- Clones],
		    distributor(D#dist{seen=Seen#{Fact => true}, n=N+1, idle=#{}})
	    end;
	{idle, Pid, N} ->  %% idle on everything sent so far
	    finish(D#dist{idle=(D#dist.idle)#{Pid => true},
			  done=maps:remove(Pid, D#dist.done)});
	{idle, _Pid, _Behind} ->
	    distributor(D);
	{done, Pid} ->
	    finish(D#dist{done=(D#dist.done)#{Pid => true},
			  idle=maps:remove(Pid, D#dist.idle)});
	{stop, From} ->
	    From ! {shared, self(), N}
    end.

finish(D=#dist{clones=Clones, idle=Idle, done=Done}) ->
    case map_size(Idle) + map_size(Done) >= length(Clones) of
	true ->
	    [Pid ! finish || Pid <- maps:keys(Idle)],
	    distributor(D#dist{idle=#{}});
	false ->
	    distributor(D)
    end.
