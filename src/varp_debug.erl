%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2020, Tony Rogvall
%%% @doc
%%%    varp debug module
%%% @end
%%% Created : 24 Feb 2020 by Tony Rogvall <tony@rogvall.se>

-module(varp_debug).

-behaviour(varp_plugin).
-export([options/0, run/2]).

-include("varp.hrl").

options() ->
    [#{ long  => "rank",
	short => "r",
	key   => rank,
	spec  => {enum,[?BOOL]},
	default => false,
	description => "show variable rank."
      }
    ].

run(Bs, Param) when is_record(Bs, bs), is_map(Param) ->
    Rank = maps:get(rank, Param, false),
    if Rank -> show_rank(Bs); true -> ok end,
    {?CONTINUE, [], Bs}.

%% enable xref and calculate rank (via xref)
show_rank(Bs) ->
    varp_nif:setopt(Bs#bs.vp, xref, true),
    N = varp:get_number_of_variables(Bs#bs.vp),
    DMap = degree_map(Bs#bs.vp, 1, N, #{}),
    DList = maps:to_list(DMap),
    SList = lists:reverse(lists:keysort(2, DList)),
    lists:foreach(
      fun({Li,Rank}) ->
	      io:format("~w: ~s\n", 
			[Rank, varp_formula:format_lit(Bs, Li)])
      end, lists:sublist(SList, 20)).


degree_map(Vp, I, N, Map) when I =< N ->
    D0 = varp_nif:literal_info(Vp, -I, degree),
    D1 = varp_nif:literal_info(Vp, I, degree),
    degree_map(Vp, I+1, N, Map#{ I => D1, -I => D0 });
degree_map(_Vp, _I, _N, Map) ->
    Map.
