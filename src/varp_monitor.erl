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
    spawn(
      fun() ->
	      io:format("monitor ~p started\n", [self()]),
	      varc:subscribe(Bs#bs.vp, atom),
	      Mon = monitor(process, SELF),
	      loop(Bs, Mon)
      end),
    {?CONTINUE,[],Bs}.

loop(Bs, Mon) ->
    receive
	{'DOWN', Mon, process, _Pid, _Reason} ->
	    done;
	{varp, {X,Y}} ->
	    io:format("monitor: substitut (~w=>~w) ~s => ~s\n", 
		      [Y,X,
		       varp_formula:format_lit(Bs,Y),
		       varp_formula:format_lit(Bs,X)]),
	    loop(Bs, Mon);
	{varp, X} ->
	    io:format("monitor: permanent (~w=1) ~s = ~w\n", 
		      [X,varp_formula:format_lit(Bs,X), 1]),
	    loop(Bs, Mon);
	Other ->
	    io:format("monitor: got ~p\n", [Other]),
	    loop(Bs, Mon)
    end.
