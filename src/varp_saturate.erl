%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2017, Tony Rogvall
%%% @doc
%%%    Run saturation
%%% @end
%%% Created : 19 Dec 2017 by Tony Rogvall <tony@rogvall.se>

-module(varp_saturate).

-behaviour(varp_plugin).

-export([run/2]).
-export([options/0]).
-export([saturate/5]).
-export([saturate/7]).

%% -define(DEBUG, true).
%% -compile(export_all).

-include("varp.hrl").

-define(CHECK_INTERVAL, 1000).
-define(COUNT, 16#1ff).

options() ->
    [#{ long  => "timeout",
	short => "t",
	key   => timeout,
	spec  => {union,[float,{enum,[{"infinity",infinity}]}]},
	default => infinity,
	description => "Timeout in seconds"
      },
     #{ long => "level",
	short => "k",
	key => level,
	spec => unsigned, 
	default => 1,
	description => "Saturation level"
      },
     #{ long => "seq",
	short => "q",
	key => q,
	spec => unsigned,
	default => 0,
	description => "Add q consecutive variables during saturation"
      },
     #{ long => "random",
	short => "r",
	key => r,
	spec => unsigned,
	default => 0,
	description => "Add r random variables during saturation"
      },
     #{ long => "threshold",
	key => threshold,
	spec => unsigned,
	default => 0,
	description => "Threshold for #bound variables during saturation round"
      },
     #{ long  => "laps",
	short => "l",
	key   => laps,
	spec  => unsigned,
	default => 0,
	description => "Max saturation lap count"
      }
     ].

run(Bs, Param) when is_record(Bs, bs), is_map(Param) ->
    varp_formula:config(Bs, max_conflicting, 1),
    K = maps:get(level, Param, 1),
    Q = maps:get(q, Param, 1),
    R = maps:get(r, Param, 1),
    Timeout = maps:get(timeout, Param, infinity),
    Threshold = maps:get(threshold, Param, 0),
    Laps = maps:get(laps, Param, infinity),
    ?dbg0("k=~w,q=~w,r=~w,laps=~w\n", [K,Q,R,Laps]),
    saturate(Bs,K,Q,R,Timeout,Laps,Threshold).

saturate(Bs,K,Timeout,MaxLaps,Threshold) ->
    saturate(Bs,K,0,0,Timeout,MaxLaps,Threshold).

saturate(Bs,K,Q,R,Timeout,MaxLaps,Threshold) ->
    varc:config(Bs#bs.vp, xref, true),
    Bs1 = varp:set_local_timeout(Bs, Timeout),
    Level = ?TOP_LEVEL,
    N = varp_formula:number_of_bound(Bs),
    FriendMap = varc:make_friend_map(Bs#bs.vp),
    %% io:format("FriendMap = ~w\n", [FriendMap]),
    case loop(Bs1,K,Q,R,N,Level,MaxLaps,Threshold,FriendMap) of
	false ->
	    {?INCONSISTENT,[],Bs1};
	{Reason,Bs1} -> 
	    varc:config(Bs#bs.vp, xref, false),
	    ?dbg("saturate limit ~w\n", [Reason]),
	    {Reason,[],Bs1#bs{ t_local = undefined }}
    end.

loop(Bs,K,Q,R,N,Level,Laps,Threshold,FriendMap) ->
    ?dbg1("Laps=~w n=~w\n", [Laps, N]),
    case lap(Bs, K, Q, R, FriendMap) of
	true ->
	    N1 = varp_formula:number_of_bound(Bs),
	    Laps1 = Laps-1,
	    if N1 - N =< Threshold ->
		    loop_done(?THRESHOLD,Laps,Bs);
	       Laps1 =:= 0 ->
		    loop_done(?ITERATIONS,Laps,Bs);
	       true ->
		    loop(Bs,K,Q,R,N1,Level,Laps1,Threshold,FriendMap)
	    end;
	Result -> Result
    end.

loop_done(Reason, _Laps, Bs) ->
    {Reason,Bs}.

%% Run one lap over all variables given 
%% K number of variables, Q number of extra variables
%% R number of randomly selected variables
%% Variables in every eval is K+Q+R

lap(Bs, K, Q, R, FriendMap) ->
    case varc:vec_create(Bs#bs.vp, varc:next_unbound(Bs#bs.vp), K) of
	[] -> true;
	Vec0 -> lap_(Bs, Vec0, Q, R, 1, FriendMap)
    end.

lap_(Bs, Vec0, Q, R, Count, FriendMap) when Count band ?COUNT =:= 0 ->
    case varp:check_timeout_or_cancel(Bs,?COUNTER_ST_BCP_COUNTER,
				      ?CHECK_INTERVAL) of
	{true,What} ->
	    {What, Bs};
	false ->
	    lap__(Bs, Vec0, Q, R, Count, FriendMap)
    end;
lap_(Bs, Vec0, Q, R, Count, FriendMap) ->
    lap__(Bs, Vec0, Q, R, Count, FriendMap).

lap__(Bs, Vec0, Q, R, Count, FriendMap) ->
    case varc:vec_sat(Bs#bs.vp, Vec0, Q, R, FriendMap) of
	false -> false;
	true ->
	    case varc:vec_step(Bs#bs.vp, Vec0) of
		false -> true;
		Vec1 -> lap_(Bs, Vec1, Q, R, Count+1, FriendMap)
	    end
    end.

-ifdef(DEBUG).
indent(D) -> lists:duplicate(D, $>).
-endif.

