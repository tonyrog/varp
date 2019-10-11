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

run(Bs, Param)  when is_record(Bs,bs), is_map(Param) ->
    case Bs#bs.main of
	undefined ->
	    io:format("error: missing main variable\n"),
	    {?ERROR, "missing main variable",Bs};
	?F ->
	    {?INCONSISTENT,[],Bs};
	?T ->
	    case varp_formula:eval(Bs) of
		false -> 
		    {?INCONSISTENT,[],Bs};
		true -> 
		    {?CONTINUE,[],Bs}
	    end;
	Main ->
	    varp_formula:set_level(Bs,?TOP_LEVEL),
	    case varp_formula:bind(Bs, Main) of
		false -> 
		    {?INCONSISTENT,[],Bs};
		true ->
		    case varp_formula:eval(Bs) of
			false ->
			    {?INCONSISTENT,[],Bs};
			true ->
			    {?CONTINUE,[],Bs}
		    end
	    end
    end.
