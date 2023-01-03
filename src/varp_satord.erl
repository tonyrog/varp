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

-define(DEFAULT_TIMEOUT, infinity).
-define(DEFAULT_SIZE,    10).
-define(DEFAULT_ROUNDS,  2).
-define(DEFAULT_ITER,    1000).
-define(DEFAULT_MODE,    sat).

options() ->
    [#{ long  => "timeout",
	short => "t",
	key   => timeout,
	spec  => {union,[float,{enum,[{"infinity",infinity}]}]},
	default => ?DEFAULT_TIMEOUT,
	description => "Timeout in seconds"
      },
     #{ long => "size",
	short => "v",
	key => size,
	spec => unsigned, 
	default => ?DEFAULT_SIZE,
	description => "Variable selection vector size"
      },
     #{ long => "rounds",
	short => "r",
	key => rounds,
	spec => unsigned, 
	default => ?DEFAULT_ROUNDS,
	description => "Number of selections"
      },
     #{ long  => "iterations",
	short => "n",
	key   => iter,
	spec  => unsigned,
	default => ?DEFAULT_ITER,
	description => "Number of samples per round"
      },
     #{ long  => "mode",
	short => "m",
	key   => mode,
	spec  => {enum, [{"s", sat}, {"sat", sat},
			 {"u", unsat}, {"unsat", unsat}]},
	default => ?DEFAULT_MODE,
	description => "Select negation (unsat) or not (sat, default)"
      }
    ].

run(Bs, Param) when is_record(Bs, bs), is_map(Param) ->
    _Timeout = maps:get(timeout, Param, ?DEFAULT_TIMEOUT),
    Size = maps:get(size, Param, ?DEFAULT_SIZE),
    N = maps:get(iter, Param, ?DEFAULT_ITER),
    %% N should not be > 2^Size
    if (N >= (1 bsl Size)) ->
	    io:format("n > 2^v! use saturate?", []);
       true ->
	    ok
    end,
    R = maps:get(rounds, Param, ?DEFAULT_ROUNDS),
    Mode = maps:get(mode, Param, ?DEFAULT_MODE),
    Map = rounds(Bs#bs.vp, R, Size, N, #{}),
    Ls0 = literal_list(Map),   %% get probable literals
    Ls = [ Li || {_Ln,Li} <- Ls0, %% Ln > R, 
		 varp_nif:isatom(Bs#bs.vp, Li)],
    ?dbg1("kept ~w\n", [Ls]),
    Assumed = case Mode of
		  sat -> Ls;
		  unsat -> [-Li || Li <- Ls]
	      end,
    varp:order_first(Bs#bs.vp, Assumed),
    {?CONTINUE,[],Bs}.

rounds(_Vp, 0, _Size, _N, Map) ->
    Map;
rounds(Vp, R, Size, N, Map) ->
    %% new random selection
    Vt = list_to_tuple(varp:vec_extend_rand(Vp, [], Size)),
    Map1 = loop(Vp, N, Vt, Map),
    rounds(Vp, R-1, Size, N, Map1).

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
	    Map1 = intersect(Ei, Map),
	    loop(Vp, I-1, Vt, Map1);
	_ -> %% false or contradiction (map hold for all)
	    ?dbg0("Vj ~w -> false\n", [Vj]),
	    varp_nif:pop(Vp, L),
	    loop(Vp, I-1, Vt, Map)
    end.

%% literal Li state
%%   Li => N       seen N times
%%   Li => false   -Li seen
%%
intersect([Li|Ls], Map) ->
    case maps:find(Li, Map) of
	error ->
	    case maps:find(-Li, Map) of
		{ok,false} ->
		    error(internal);
		{ok,_N} -> 
		    intersect(Ls, Map#{ Li => false, -Li => false });
		error ->
		    intersect(Ls, Map#{ Li => 1 })
	    end;
	{ok,false} ->
	    intersect(Ls, Map);
	{ok,N} ->
	    intersect(Ls, Map#{ Li => N + 1})
    end;
intersect([], Map) ->
    Map.

literal_list(Map) ->
    NRemoved = maps:fold(fun(_, false, N) -> N+1;
			    (_Li, _, N) -> N
			 end, 0, Map),
    ?dbg1("literals not constant (removed) = ~w\n", [NRemoved]),
    Ls = maps:fold(fun(_, false, Acc) -> Acc;
		      (Li, N, Acc) -> [{N,Li}|Acc]
		   end, [], Map),
    lists:reverse(lists:sort(Ls)).
