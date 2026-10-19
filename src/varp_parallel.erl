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
%%%    bindings of every clone and hands each new one to all clones,
%%%    which import them at their next restart (see the import hook in
%%%    varp_backjump).  A fact one clone learns is sound for the
%%%    formula, so every clone may use it.
%%% @end
%%% Created : 19 Oct 2026 by Tony Rogvall <tony@rogvall.se>

-module(varp_parallel).
-behaviour(varp_plugin).

-export([options/0, run/2]).
-export([drain_facts/0]).

-include("varp.hrl").

%% facts are imported in batches: when this many are pending, or when
%% the oldest pending fact is this old (ms), so a trickle of single
%% facts does not restart the search every time
-define(IMPORT_BATCH, 32).
-define(IMPORT_AGE, 200).

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
	description => "Share permanent bindings between the clones."
      },
     #{ long => "stat",
	key => stat,
	spec => {enum,[?BOOL]},
	default => false,
	description => "Report the winner and the facts shared."
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
    Driver = self(),
    Seed0 = case maps:get(seed, Param) of
		-1 -> varp_nif:getopt(Vp, seed);
		S -> S
	    end,
    Dist = case maps:get(share, Param) of
	       true -> spawn_link(fun() -> distributor([], #{}, 0) end);
	       false -> undefined
	   end,
    Chain1 = import_chain(Chain, Dist),
    Clones = [{I, spawn_link(fun() ->
				     clone(I, Bs, Param, Chain1, Seed0+I, Dist, Driver)
			     end)} || I <- lists:seq(0, N-1)],
    T0 = erlang:monotonic_time(millisecond),
    Result = wait_result(Clones),
    T1 = erlang:monotonic_time(millisecond),
    Shared = stop_distributor(Dist),
    case Result of
	{Winner, {R, Acc, BsW}} ->
	    stat(Param, "parallel: clone ~w finished first (~.2fs), ~w facts shared\n",
		 [Winner, (T1-T0)/1000, Shared]),
	    output_models(Bs, BsW, Acc),
	    {R, Acc, BsW};
	{Winner, Other} ->
	    io:format("parallel: clone ~w failed: ~p\n", [Winner, Other]),
	    {?ERROR, [], Bs}
    end.

%% the backjump plugins in the chain get the import hook
import_chain(Chain, undefined) ->
    Chain;
import_chain(Chain, _Dist) ->
    [case P of
	 varp_backjump -> {P, Prm#{import => fun ?MODULE:drain_facts/0}};
	 _ -> {P, Prm}
     end || {P, Prm} <- Chain].

%% the first clone to answer wins, the rest are killed (unlinked
%% first, a linked kill would take the driver with it)
wait_result(Clones) ->
    receive
	{result, I, Pid, Result} ->
	    [begin unlink(P), exit(P, kill) end || {_, P} <- Clones, P =/= Pid],
	    unlink(Pid),
	    {I, Result}
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

clone(I, Bs, Param, Chain, Seed, Dist, Driver) ->
    process_flag(trap_exit, false),
    W = varp_nif:clone(Bs#bs.vp, #{level => 0, set => [alpha,beta,gamma,delta]}),
    varp_nif:setopt(W, seed, Seed),
    varp_nif:setopt(W, print, false, user),
    case I > 0 andalso maps:get(shuffle, Param) of
	true -> varp_nif:order_sort(W, random, Seed);
	false -> ok
    end,
    subscribe(Dist, W),
    BsW = Bs#bs{ vp = W,
		 counters = counters:new(?NUM_COUNTERS, []),
		 d1 = counters:new(1024, []),
		 d2 = counters:new(1024, []),
		 clen = counters:new(1024, []) },
    put(output_model_header, false),  %% the driver prints the header
    Result = try varp:do(Chain, [], BsW)
	     catch ?EXCEPTION(Class, Reason, Trace) ->
		     {crashed, {Class, Reason, ?GET_STACK(Trace)}}
	     end,
    Driver ! {result, I, self(), Result}.

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
drain({Lits, Since}) ->
    receive
	{fact, L} -> drain({[L|Lits], Since})
    after 0 ->
	{Lits, Since}
    end.

%%--------------------------------------------------------------------
%% the distributor: one subscriber for every clone, each permanent
%% binding goes to all clones once (a clone that has it already
%% ignores it, so nothing echoes)
%%--------------------------------------------------------------------

distributor(Clones, Seen, N) ->
    receive
	{subscribe, Pid, W} ->
	    ok = varp_nif:subscribe(W, variable),
	    Pid ! {subscribed, self()},
	    distributor([Pid|Clones], Seen, N);
	{varp, X, _Info} when is_integer(X) ->
	    case maps:is_key(X, Seen) of
		true ->
		    distributor(Clones, Seen, N);
		false ->
		    [Pid ! {fact, X} || Pid <- Clones],
		    distributor(Clones, Seen#{X => true}, N+1)
	    end;
	{varp, {_X,_Y}, _Info} ->
	    %% substitutions are not shared (yet)
	    distributor(Clones, Seen, N);
	{stop, From} ->
	    From ! {shared, self(), N}
    end.
