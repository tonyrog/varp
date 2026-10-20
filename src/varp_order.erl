%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2019, Tony Rogvall
%%% @doc
%%%    varp plugin to order variables
%%% @end
%%% Created : 18 Jun 2019 by Tony Rogvall <tony@rogvall.se>

-module(varp_order).
-behaviour(varp_plugin).

-export([options/0, run/2]).

-include("varp.hrl").

options() ->
    [#{ long => "sort",
	key => sort,
	spec => {list,{enum,[?ORDER]}},
	default => [identity],
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
     #{ long => "ignore-file",
	key => ignore_file,
	spec => {enum,[?BOOL]},
	default => false,
	description => "Ignore the order section in the file."
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
    case maps:get(ignore_file, Param0) of
	true -> order_literals(Bs, Param0);
	false -> order_literals(Bs, file_order(Bs, Param0))
    end.

%% the order section in the file fills in what the command line did not
%% give: --first, --last and --sort each win over the file on their own
file_order(Bs, Param0) ->
    FileOrder = maps:get(order, Bs#bs.option, []),
    lists:foldl(
      fun({Key, Default}, Param) ->
	      case {maps:get(Key, Param, Default),
		    proplists:get_value(Key, FileOrder)} of
		  {_, undefined} -> Param;
		  {Default, Value} -> maps:put(Key, Value, Param);
		  {_, _} -> Param
	      end
      end, Param0, [{first, []}, {last, []}, {sort, [identity]}]).

order_literals(Bs, Param) ->
    ?dbg("order params=~p\n", [Param]),
    Seed = case maps:get(seed,Param) of
	       -1 -> varp_nif:getopt(Bs#bs.vp,seed);
	       S0 -> S0
	   end,
    ?dbg("Seed = ~w\n", [Seed]),
    case maps:get(sort,Param) of
	[Key1,Key2] ->
	    varp_nif:order_sort(Bs#bs.vp,Key1,Key2,Seed);
	[Key1] ->
	    varp_nif:order_sort(Bs#bs.vp,Key1,Seed);
	Key1 when is_atom(Key1) ->
	    varp_nif:order_sort(Bs#bs.vp,Key1,Seed)
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
	    Order = varp:order_all(Bs#bs.vp),
	    lists:foreach(fun(V) ->
				  io:format("~s ",
					    [varp_format:format_var(Bs,V)])
			  end, Order),
	    io:format("\n")
    end.
