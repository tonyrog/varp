%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2019, Tony Rogvall
%%% @doc
%%%    varp plugin to monitor permament assignments and print them
%%% @end
%%% Created : 18 Jun 2019 by Tony Rogvall <tony@rogvall.se>

-module(varp_monitor).
-export([options/0, run/2]).

-include("varp.hrl").

options() ->
    [].

run(Bs, _Param) ->
    SELF = self(),
    Info = [atom,variable,number_of_variables,number_of_bound_variables,
	    number_of_clauses, number_of_dead_clauses],
    Ref = make_ref(),
    {Pid,Mon} = 
	spawn_monitor(
	  fun() ->
		  io:format("monitor ~p started\n", [self()]),
		  varc:subscribe(Bs#bs.vp, Info),
		  Mon = monitor(process, SELF),
		  SELF ! {ack,Ref},
		  loop(Bs, Mon)
	  end),
    receive
	{ack,Ref} ->
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
		       varp_formula:format_lit(Bs,Y),
		       varp_formula:format_lit(Bs,X)
		      ]),
	    loop(Bs, Mon);
	{varp, X, _Info} ->
	    io:format("monitor: permanent (~w=1) ~s = ~w\n", 
		      [X,varp_formula:format_lit(Bs,X), ?T]),
	    loop(Bs, Mon);
	Other ->
	    io:format("monitor: got ~p\n", [Other]),
	    loop(Bs, Mon)
    end.
