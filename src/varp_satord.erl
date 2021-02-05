%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2021, Tony Rogvall
%%% @doc
%%%    Find variable order by saturation
%%% @end
%%% Created :  5 Feb 2021 by Tony Rogvall <tony@rogvall.se>

-module(varp_satord).

-behaviour(varp_plugin).

-export([run/2]).
-export([options/0]).

-define(DEBUG, true).
%% -compile(export_all).

-include("varp.hrl").

options() ->
    [#{ long  => "timeout",
	short => "t",
	key   => timeout,
	spec  => {union,[float,{enum,[{"infinity",infinity}]}]},
	default => infinity,
	description => "Timeout in seconds"
      },
     #{ long => "size",
	short => "s",
	key => size,
	spec => unsigned, 
	default => 10,
	description => "Variable selection size"
      },
     #{ long  => "iterations",
	short => "n",
	key   => iter,
	spec  => unsigned,
	default => 1000,
	description => "Number of samples"
      }].

run(Bs, Param) when is_record(Bs, bs), is_map(Param) ->
    Timeout = maps:get(timeout, Param, infinity),
    Size = maps:get(size, Param, 10),
    N = maps:get(iter, Param, 1000),
    Vt = list_to_tuple(varp:vec_extend_rand(Bs#bs.vp, [], Size)),
    Map = loop(Bs#bs.vp, N, Vt, #{}),
    %% Assumed = update_list(Map), 
    Assumed = [-Li || Li <- update_list(Map)],
    ?dbg0("Satord = ~w\n", [Assumed]),
    varp:order_first(Bs#bs.vp, Assumed),
    {?CONTINUE,[],Bs}.

loop(_Vp, 0, _Vt, Map) ->
    Map;
loop(Vp, I, Vt, Map) ->
    J = rand:uniform(tuple_size(Vt)),
    Vj = varp:vtl(Vp, J, Vt),
    L = varp_nif:push(Vp),
    case varp_nif:vbcp(Vp, Vj, true) of
	true ->
	    Ei = varp_nif:get_bindings(Vp, L+2, false, _AsTuple=false),
	    ?dbg0("Vj ~w -> Ei ~w\n", [Vj, Ei]),
	    varp_nif:pop(Vp, L),
	    Map1 = update(Ei, Map),
	    loop(Vp, I-1, Vt, Map1);
	_ -> %% false or contradiction
	    ?dbg0("Vj ~w -> false\n", [Vj]),
	    varp_nif:pop(Vp, L),
	    loop(Vp, I-1, Vt, Map)
    end.

%% literal Li state
%%   Li => N       seen N times
%%   Li => false   -Li seen
%%
update([Li|Ls], Map) ->
    case maps:find(Li, Map) of
	error ->
	    case maps:find(-Li, Map) of
		{ok,false} ->
		    error(internal);
		{ok,_N} -> 
		    update(Ls, Map#{ Li => false });
		error ->
		    update(Ls, Map#{ Li => 1 })
	    end;
	{ok,false} ->
	    update(Ls, Map);
	{ok,N} ->
	    update(Ls, Map#{ Li => N + 1})
    end;
update([], Map) ->
    Map.

update_list(Map) ->
    Ls = maps:fold(fun(_, false, Acc) -> Acc;
		      (Li, N, Acc) -> [{N,Li}|Acc]
		   end, [], Map),
    Ls1 = lists:reverse(lists:sort(Ls)),
    [Li || {_N,Li} <- Ls1].
