%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2019, Tony Rogvall
%%% @doc
%%%    varp clean-up module 
%%% @end
%%% Created : 25 Aug 2019 by Tony Rogvall <tony@rogvall.se>

-module(varp_clean).
-export([options/0, run/2]).

-include("varp.hrl").

options() ->
    [#{ long  => "edges",
	short => "e",
	key   => edges,
	spec  => {enum,[?BOOL]},
	default => false,
	description => "remove edges that are constant."
      },
     #{ long  => "clauses",
	short => "c",
	key   => clauses,
	spec  => {enum,[?BOOL]},
	default => false,
	description => "remove clauses that are dead."
      }
    ].

run(Bs, Param) ->
    Bs1 = 
	case maps:get(clauses, Param, false) of
	    false -> Bs;
	    true -> varp_formula:clean_clauses(Bs)
	end,
    Bs2 = 
	case maps:get(literals, Param, false) of
	    false -> Bs1;
	    true -> varp_formula:clean_literals(Bs1)
	end,
    Bs2.
