%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2019, Tony Rogvall
%%% @doc
%%%    varp plugin to order variables
%%% @end
%%% Created : 18 Jun 2019 by Tony Rogvall <tony@rogvall.se>

-module(varp_order).
-export([options/0, run/2]).

-include("varp.hrl").

options() ->
    [#{ long => "sort",
	key => sort,
	spec => {list,{enum,[?ORDER]}},
	default => [identity],
	description => "Specifiy variable order."
      },
     #{ long => "first",
	short => "f",
	key => first,
	spec => {list,literal},
	default => [],
	description => "Literals sorted first."
      },
     #{ long => "last",
	short => "l",
	key => last,
	spec => {list,literal},
	default => [],
	description => "Literals sorted last."
      },
     #{ long => "display",
	short => "d",
	key => display,
	spec => {enum,[?BOOL]},
	default => false,
	description => "Display declared variable order."
      }].

run(Bs, Param) when is_record(Bs, bs), is_map(Param) ->
    order_literals(Bs, Param).

order_literals(Bs, Param) ->
    Seed = varp_formula:getopt(Bs,seed),
    case maps:get(sort,Param) of
	[Key1,Key2] ->
	    varp_formula:order_sort(Bs,Key1,Key2,Seed);
	[Key1] ->
	    varp_formula:order_sort(Bs,Key1,undefined,Seed)
    end,
    Bs1 = case maps:get(first,Param) of
	      [] -> Bs;
	      First -> varp_formula:order_sort_first(Bs,First)
	  end,
    Bs2 = case maps:get(last,Param) of
	      [] -> Bs1;
	      Last -> varp_formula:order_sort_last(Bs1,Last)
	  end,
    display_order(Bs2,Param),
    {?CONTINUE,[],Bs2}.
    
display_order(Bs,Param) ->
    case maps:get(display,Param) of
	false ->
	    ok;
	true ->
	    Order = collect_order(Bs,varp_formula:first_init(Bs),[]),
	    lists:foreach(fun(V) ->
				  io:format("~s ",[varp_formula:fmt_var(Bs,V)])
			  end, Order),
	    io:format("\n")
    end.

collect_order(Bs,I,Acc) ->
    case varp_formula:next_unbound(Bs,I) of
	false -> lists:reverse(Acc);
	{J,Xj} -> collect_order(Bs,J,[Xj|Acc])
    end.
