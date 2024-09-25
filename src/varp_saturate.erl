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
-export([saturate/5, saturate/6]).
-export([saturate/8, saturate/9]).

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
     #{ long => "friend",
	short => "f",
	key => f,
	spec => unsigned,
	default => 0,
	description => "Add f friend variables during saturation"
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
      },
     #{ long  => "subst",
	short => "s",
	key   => subst,
	spec  =>  {enum,[?BOOL]},
	default => true,
	description => "Enable substitution"
      }
     ].

run(Bs, Param) when is_record(Bs, bs), is_map(Param) ->
    varp_nif:setopt(Bs#bs.vp, max_conflicting, 1),
    K = maps:get(level, Param, 1),
    Q = maps:get(q, Param, 1),
    F = maps:get(f, Param, 1),
    R = maps:get(r, Param, 1),
    Timeout = maps:get(timeout, Param, infinity),
    Threshold = maps:get(threshold, Param, 0),
    Laps = maps:get(laps, Param, infinity),
    Subst = maps:get(laps, Param, infinity),
    ?dbg0("k=~w,q=~w,f=~w,r=~w,laps=~w\n", [K,Q,F,R,Laps]),
    saturate(Bs,K,Q,F,R,Timeout,Laps,Threshold,Subst).

saturate(Bs,K,Timeout,MaxLaps,Threshold) ->
    saturate(Bs,K,Timeout,MaxLaps,Threshold,true).

saturate(Bs,K,Timeout,MaxLaps,Threshold,Subst) ->
    saturate(Bs,K,0,0,0,Timeout,MaxLaps,Threshold,Subst).

saturate(Bs,K,Q,F,R,Timeout,MaxLaps,Threshold) ->
    saturate(Bs,K,Q,F,R,Timeout,MaxLaps,Threshold, true).

saturate(Bs,K,Q,F,R,Timeout,MaxLaps,Threshold,Subst) ->
    varp_nif:setopt(Bs#bs.vp, xref, true),
    Bs1 = varp:set_local_timeout(Bs, Timeout),
    N = varp:get_number_of_bound_variables(Bs#bs.vp),
    FriendMap = if F =:= 0 ->
			undefined;  %% not needed
		   true ->
			varp:make_friend_map(Bs#bs.vp)
		end,
    %% io:format("FriendMap = ~w\n", [FriendMap]),
    case loop(Bs1,K,Q,F,R,N,MaxLaps,Threshold,Subst,FriendMap) of
	false ->
	    {?INCONSISTENT,[],Bs1};
	{Reason,Bs2} -> 
	    varp_nif:setopt(Bs2#bs.vp, xref, false),
	    ?dbg0("saturate limit ~w\n", [Reason]),
	    {Reason,[],Bs2}
    end.

loop(Bs,K,Q,F,R,N,Laps,Threshold,Subst,FriendMap) ->
    case lap(Bs,K,Q,F,R,Subst,FriendMap) of
	true ->
	    N1 = varp:get_number_of_bound_variables(Bs#bs.vp),
	    ?dbg0("Laps=~w n=~w\n", [Laps, N]),
	    Laps1 = Laps-1,
	    if N1 - N =< Threshold ->
		    loop_done(?THRESHOLD,Laps,Bs);
	       Laps1 =:= 0 ->
		    loop_done(?ITERATIONS,Laps,Bs);
	       true ->
		    loop(Bs,K,Q,F,R,N1,Laps1,Threshold,Subst,FriendMap)
	    end;
	Result -> Result
    end.

loop_done(Reason, _Laps, Bs) ->
    {Reason,Bs}.

%% Run one lap over all variables given 
%% K number of variables, Q number of extra variables
%% R number of randomly selected variables
%% Variables in every eval is K+Q+R

lap(Bs,K,Q,F,R,Subst,FriendMap) ->
    case varp:vec_create(Bs#bs.vp, varp_nif:next_unbound(Bs#bs.vp), K) of
	[] -> true;
	Vec0 -> lap_(Bs,Vec0,Q,F,R,1,Subst,FriendMap)
    end.

lap_(Bs,Vec0,Q,F,R,Count,Subst,FriendMap) when Count band ?COUNT =:= 0 ->
    case varp:check_timeout_or_cancel(Bs,?COUNTER_ST_BCP_COUNTER,
				      ?CHECK_INTERVAL) of
	{true,?TIMEOUT} ->
	    Bs1 = varp:clear_local_timeout(Bs),
	    case varp:is_local_timeout(Bs) of
		true ->
		    {true, Bs1};
		false ->
		    {?TIMEOUT, Bs1}
	    end;
	{true,What} ->
	    {What, Bs};
	false ->
	    lap__(Bs,Vec0,Q,F,R,Count,Subst,FriendMap)
    end;
lap_(Bs,Vec0,Q,F,R,Count,Subst,FriendMap) ->
    lap__(Bs,Vec0,Q,F,R,Count,Subst,FriendMap).

lap__(Bs,Vec0,Q,F,R,Count,Subst,FriendMap) ->
    case varp:vec_sat(Bs#bs.vp,Vec0,Q,F,R,Subst,FriendMap) of
	false -> false;
	true ->
	    case varp:vec_step(Bs#bs.vp, Vec0) of
		false -> true;
		Vec1 -> lap_(Bs,Vec1,Q,F,R,Count+1,Subst,FriendMap)
	    end
    end.
