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
-export([saturate/8, saturate/9, saturate/10]).

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
      },
     #{ long  => "model",
	key   => model,
	spec  =>  {enum,[?BOOL]},
	default => true,
	description => "Stop with the model when an assignment binds every variable"
      },
     #{ long  => "warn",
	key   => warn,
	spec  =>  {enum,[?BOOL]},
	default => true,
	description => "Warn when the main variable is unbound (no sat/unsat/prove before)"
      }
     ].

run(Bs, Param) when is_record(Bs, bs), is_map(Param) ->
    maps:get(warn, Param, true) andalso warn_unbound_main(Bs),
    varp_nif:setopt(Bs#bs.vp, max_conflicting, 1),
    K = maps:get(level, Param, 1),
    Q = maps:get(q, Param, 1),
    F = maps:get(f, Param, 1),
    R = maps:get(r, Param, 1),
    Timeout = maps:get(timeout, Param, infinity),
    Threshold = maps:get(threshold, Param, 0),
    Laps = maps:get(laps, Param, infinity),
    Subst = maps:get(subst, Param, true),
    Model = maps:get(model, Param, true),
    ?dbg0("k=~w,q=~w,f=~w,r=~w,laps=~w\n", [K,Q,F,R,Laps]),
    saturate(Bs,K,Q,F,R,Timeout,Laps,Threshold,Subst,Model).

%% probing propagates from what is bound; without the main variable
%% (sat, unsat or prove before saturate) nothing much is. Saturating
%% just the clauses is a use as well, --warn=false then
warn_unbound_main(Bs) ->
    case Bs#bs.main of
	Main when is_integer(Main), Main =/= ?T, Main =/= ?F ->
	    case varp_nif:value(Bs#bs.vp, Main) of
		undefined ->
		    io:format("saturate: the main variable is not bound, "
			      "put sat, unsat or prove before saturate "
			      "(--warn=false if that is intended)\n");
		_ ->
		    ok
	    end;
	_ ->
	    ok
    end,
    ok.

saturate(Bs,K,Timeout,MaxLaps,Threshold) ->
    saturate(Bs,K,Timeout,MaxLaps,Threshold,true).

saturate(Bs,K,Timeout,MaxLaps,Threshold,Subst) ->
    saturate(Bs,K,0,0,0,Timeout,MaxLaps,Threshold,Subst).

saturate(Bs,K,Q,F,R,Timeout,MaxLaps,Threshold) ->
    saturate(Bs,K,Q,F,R,Timeout,MaxLaps,Threshold, true).

saturate(Bs,K,Q,F,R,Timeout,MaxLaps,Threshold,Subst) ->
    saturate(Bs,K,Q,F,R,Timeout,MaxLaps,Threshold,Subst,true).

%% Model: report a model when an assignment of a vector binds every
%% variable (a search plugin after saturate finds it as well, but this
%% is the assignment just made, at once)
saturate(Bs,K,Q,F,R,Timeout,MaxLaps,Threshold,Subst,Model) ->
    varp_nif:setopt(Bs#bs.vp, xref, true),
    Bs1 = varp:set_local_timeout(Bs, Timeout),
    N = varp:get_number_of_bound_variables(Bs#bs.vp),
    FriendMap = if F =:= 0 ->
			undefined;  %% not needed
		   true ->
			varp:make_friend_map(Bs#bs.vp)
		end,
    %% io:format("FriendMap = ~w\n", [FriendMap]),
    OnModel = if Model -> fun() -> varp:output_model(Bs1, false, 1) end;
		 true -> undefined
	      end,
    case loop(Bs1,K,Q,F,R,N,MaxLaps,Threshold,Subst,FriendMap,OnModel) of
	false ->
	    {?INCONSISTENT,[],Bs1};
	{model, Found} ->
	    %% one assignment of a vector bound every variable
	    varp_nif:setopt(Bs1#bs.vp, xref, false),
	    Acc = case varp_nif:getopt(Bs1#bs.vp, method) of
		      collect -> [Found];
		      count -> 1
		  end,
	    {?DONE,Acc,Bs1};
	{Reason,Bs2} -> 
	    varp_nif:setopt(Bs2#bs.vp, xref, false),
	    ?dbg0("saturate limit ~w\n", [Reason]),
	    {Reason,[],Bs2}
    end.

loop(Bs,K,Q,F,R,N,Laps,Threshold,Subst,FriendMap,OnModel) ->
    case lap(Bs,K,Q,F,R,Subst,FriendMap,OnModel) of
	true ->
	    N1 = varp:get_number_of_bound_variables(Bs#bs.vp),
	    ?dbg0("Laps=~w n=~w\n", [Laps, N]),
	    Laps1 = Laps-1,
	    if N1 - N =< Threshold ->
		    loop_done(?THRESHOLD,Laps,Bs);
	       Laps1 =:= 0 ->
		    loop_done(?ITERATIONS,Laps,Bs);
	       true ->
		    loop(Bs,K,Q,F,R,N1,Laps1,Threshold,Subst,FriendMap,OnModel)
	    end;
	Result -> Result
    end.

loop_done(Reason, _Laps, Bs) ->
    {Reason,Bs}.

%% Run one lap over all variables given 
%% K number of variables, Q number of extra variables
%% R number of randomly selected variables
%% Variables in every eval is K+Q+R

lap(Bs,K,Q,F,R,Subst,FriendMap,OnModel) ->
    case varp:vec_create(Bs#bs.vp, varp_nif:next_unbound(Bs#bs.vp), K) of
	[] -> true;
	Vec0 -> lap_(Bs,Vec0,Q,F,R,1,Subst,FriendMap,OnModel)
    end.

lap_(Bs,Vec0,Q,F,R,Count,Subst,FriendMap,OnModel) when Count band ?COUNT =:= 0 ->
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
	    lap__(Bs,Vec0,Q,F,R,Count,Subst,FriendMap,OnModel)
    end;
lap_(Bs,Vec0,Q,F,R,Count,Subst,FriendMap,OnModel) ->
    lap__(Bs,Vec0,Q,F,R,Count,Subst,FriendMap,OnModel).

lap__(Bs,Vec0,Q,F,R,Count,Subst,FriendMap,OnModel) ->
    case varp:vec_sat(Bs#bs.vp,Vec0,Q,F,R,Subst,FriendMap,OnModel) of
	false -> false;
	{model, _} = Found -> Found;
	true ->
	    case varp:vec_step(Bs#bs.vp, Vec0) of
		false -> true;
		Vec1 -> lap_(Bs,Vec1,Q,F,R,Count+1,Subst,FriendMap,OnModel)
	    end
    end.
