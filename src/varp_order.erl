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
	default => [?ORDER_IDENTITY],
	description => "Specifiy variable order."
      },
      #{ long => "seed",
	 key => seed,
	 spec => integer,
	 default => -1,
	 description => "Random seed."
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
     #{ override => "override",
	short => "x",
	key => override,
	spec => {enum,[{"file",file},{"cmdline",cmdline}]},
	default => cmdline,
	description => "Selected order from command line or file"
      },
     #{ long => "display",
	short => "d",
	key => display,
	spec => {enum,[?BOOL]},
	default => false,
	description => "Display declared variable order."
      }].

run(Bs, Param0) when is_record(Bs, bs), is_map(Param0) ->
    ?dbg("file order=~p\n", [maps:get(order,Bs#bs.option,[])]),
    case maps:get(override, Param0) of
	file ->
	    FileOrder = maps:get(order, Bs#bs.option, []),
	    Param1 = case proplists:get_value(first, FileOrder) of
			 undefined -> Param0;
			 First -> maps:put(first, First, Param0)
		     end,
	    Param2 = case proplists:get_value(last, FileOrder) of
			 undefined -> Param1;
			 Last -> maps:put(last, Last, Param1)
		     end,
	    Param3 = case proplists:get_value(sort, FileOrder) of
			 undefined -> Param2;
			 Sort -> maps:put(sort, Sort, Param2)
		     end,
	    order_literals(Bs, Param3);
	cmdline ->
	    order_literals(Bs, Param0)
    end.

order_literals(Bs, Param) ->
    ?dbg1("order params=~p\n", [Param]),
    Seed = case maps:get(seed,Param) of
	       -1 -> varp_formula:getopt(Bs,seed);
	       S0 -> S0
	   end,
    ?dbg("Seed = ~w\n", [Seed]),
    case maps:get(sort,Param) of
	[Key1,Key2] ->
	    varp_formula:order_sort(Bs,Key1,Key2,Seed);
	[Key1] ->
	    varp_formula:order_sort(Bs,Key1,?ORDER_UNDEFINED,Seed)
    end,
    Bs1 = case maps:get(first,Param) of
	      [] -> Bs;
	      First -> varp_formula:order_first(Bs,First)
	  end,
    Bs2 = case maps:get(last,Param) of
	      [] -> Bs1;
	      Last -> varp_formula:order_last(Bs1,Last)
	  end,
    display_order(Bs2,Param),
    {?CONTINUE,[],Bs2}.
    
display_order(Bs,Param) ->
    case maps:get(display,Param) of
	false ->
	    ok;
	true ->
	    Order = varc:order_all(Bs#bs.vp),
	    lists:foreach(fun(V) ->
				  io:format("~s ",[varp_formula:fmt_var(Bs,V)])
			  end, Order),
	    io:format("\n")
    end.
