%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2019, Tony Rogvall
%%% @doc
%%%    varp plugin to set formula variable to TRUE
%%% @end
%%% Created : 18 Jun 2019 by Tony Rogvall <tony@rogvall.se>

-module(varp_satisfy).
-export([options/0, run/2]).

-include("varp.hrl").

options() ->
    [].

run(Bs, _Param) ->
    case Bs#bs.main of
	undefined ->
	    io:format("error: missing main variable\n"),
	    error;
	Main ->
	    varp_formula:set_level(Bs,?TOP_LEVEL),
	    case varp_formula:bind(Bs, Main) of
		false -> false;
		true ->
		    case varp_formula:eval(Bs) of
			false -> false;
			true -> Bs
		    end
	    end
    end.
