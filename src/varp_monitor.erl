%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2019, Tony Rogvall
%%% @doc
%%%    varp plugin to monitor permament assignments and print them
%%% @end
%%% Created : 18 Jun 2019 by Tony Rogvall <tony@rogvall.se>

-module(varp_monitor).
-behaviour(varp_plugin).
-export([options/0, run/2]).
%% special sync stop call
-export([stop/0]).

-include("varp.hrl").

options() ->
    [].

run(Bs, _Param) ->
    case get(monitor_pid) of
	undefined ->
	    start_monitor(Bs);
	Pid when is_pid(Pid) ->
	    io:format("monitor ~p already started\n", [Pid]),
	    {?CONTINUE,[],Bs}
    end.

stop() ->
    case get(monitor_pid) of
	undefined ->
	    ok;
	Pid when is_pid(Pid) ->
	    Mon = erlang:monitor(process, Pid),
	    Pid ! stop,
	    receive
		{'DOWN',Mon,process,Pid,Reason} ->
		    io:format("monitor stopped ~p\n", [Reason]),
		    ok
	    after 3000 ->
		    io:format("monitor timeout\n", []),
		    timeout
	    end
    end.


start_monitor(Bs) ->
    SELF = self(),
    Info = [atom,variable,number_of_variables,number_of_bound_variables,
	    number_of_clauses, number_of_dead_clauses,
	    number_of_conflicts, number_of_propagations,
	    number_of_decisions, number_of_bcps],
    Ref = make_ref(),
    {Pid,Mon} = 
	spawn_monitor(
	  fun() ->
		  io:format("monitor ~p started\n", [self()]),
		  varp_nif:subscribe(Bs#bs.vp, Info),
		  Mon = monitor(process, SELF),
		  SELF ! {ack,Ref},
		  loop(Bs, Mon)
	  end),
    receive
	{ack,Ref} ->
	    put(monitor_pid, Pid),
	    erlang:demonitor(Mon);
	{'DOWN', Mon, process, Pid, _Reason} ->
	    ok
    after 3000 ->
	    io:format("need to wait longer?\n"),
	    timeout
    end,
    {?CONTINUE,[],Bs}.


loop(Bs, Mon) ->
    receive
	{'DOWN', Mon, process, _Pid, _Reason} ->
	    done;
	{varp, {X,Y}, _Info} ->
	    io:format("monitor: substitut (~w=>~w) ~s => ~s\n", 
		      [Y,X,
		       varp_format:format_lit(Bs,Y),
		       varp_format:format_lit(Bs,X)
		      ]),
	    loop(Bs, Mon);
	{varp, X, _Info} ->
	    io:format("monitor: permanent ~s\n", 
		      [varp_format:format_lit(Bs,X)]),
	    loop(Bs, Mon);
	stop ->
	    ok;
	Other ->
	    io:format("monitor: got ~p\n", [Other]),
	    loop(Bs, Mon)
    end.
