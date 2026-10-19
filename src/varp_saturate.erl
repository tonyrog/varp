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
-export([saturate/8, saturate/9, saturate/10, saturate/12]).

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
     #{ long  => "segment",
	key   => segment,
	spec  => unsigned,
	default => 0,
	description => "Probe segment i of --segments: the variables with index i modulo n"
      },
     #{ long  => "segments",
	key   => segments,
	spec  => unsigned,
	default => 1,
	description => "Number of segments the variables are divided in"
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

%% the constants of a lap
-record(lap, {
	  k,          %% vector size
	  q, f, r,    %% extra variables: next, friend, random
	  subst,      %% substitute equal literals
	  friend_map,
	  on_model,   %% fun called with a model in place, or undefined
	  segment,    %% fun(X) -> boolean(): probe the vectors led by
		      %% the variables X it says yes to (undefined: all)
	  import,     %% fun() -> [fact], facts from other instances to
		      %% take in between the probes, or undefined
	  idle        %% fun(Fixpoint) -> finish | [fact]: at the fixpoint
		      %% wait for more facts from the other instances or
		      %% for the word that all are there, or undefined
	 }).

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
    Segment = segment(maps:get(segment, Param, 0), maps:get(segments, Param, 1)),
    Hooks = {maps:get(import, Param, undefined), maps:get(idle, Param, undefined)},
    ?dbg0("k=~w,q=~w,f=~w,r=~w,laps=~w,segment=~w\n", [K,Q,F,R,Laps,Segment]),
    saturate(Bs,K,Q,F,R,Timeout,Laps,Threshold,Subst,Model,Segment,Hooks).

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

saturate(Bs,K,Q,F,R,Timeout,MaxLaps,Threshold,Subst,Model) ->
    saturate(Bs,K,Q,F,R,Timeout,MaxLaps,Threshold,Subst,Model,undefined,{undefined,undefined}).

%% --segment i --segments n: the variables i, i+n, i+2n, ... (a fun
%% from varp_parallel instead divides by equivalence class, see there)
segment(Fun, _N) when is_function(Fun, 1) ->
    Fun;
segment(_I, N) when N =< 1 ->
    undefined;
segment(I, N) ->
    fun(X) -> X rem N =:= I end.

%% Model: report a model when an assignment of a vector binds every
%% variable (a search plugin after saturate finds it as well, but this
%% is the assignment just made, at once)
%% Segment: only the vectors led by the variables the fun says yes to
%% are probed; n instances with the segments 0..n-1 together probe
%% every vector once, and what they find they share (varp_parallel),
%% with the hooks {Import,Idle} of the #lap record
saturate(Bs,K,Q,F,R,Timeout,MaxLaps,Threshold,Subst,Model,Segment,{Import,Idle}) ->
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
    Lap = #lap{k=K, q=Q, f=F, r=R, subst=Subst, friend_map=FriendMap,
	       on_model=OnModel, segment=Segment, import=Import, idle=Idle},
    case loop(Bs1,Lap,N,MaxLaps,Threshold) of
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

%% laps until a lap binds nothing (more than Threshold) or the laps
%% run out; imported facts count as bound, so an instance keeps
%% lapping while the others still find things
loop(Bs,Lap,N,Laps,Threshold) ->
    case lap(Bs,Lap) of
	true ->
	    N1 = varp:get_number_of_bound_variables(Bs#bs.vp),
	    ?dbg0("Laps=~w n=~w\n", [Laps, N]),
	    Laps1 = Laps-1,
	    if N1 - N =< Threshold ->
		    fixpoint(Bs,Lap,Laps,Threshold);
	       Laps1 =:= 0 ->
		    loop_done(?ITERATIONS,Lap,Bs);
	       true ->
		    loop(Bs,Lap,N1,Laps1,Threshold)
	    end;
	false -> false;
	{model,_} = Found -> Found;
	{Reason,Bs1} -> loop_done(Reason,Lap,Bs1)   %% timeout, cancel
    end.

%% at the fixpoint an instance of a group waits for facts from the
%% others, and laps again on them, or for the word that all are there
fixpoint(Bs,#lap{idle=undefined},_Laps,_Threshold) ->
    {?THRESHOLD,Bs};
fixpoint(Bs,Lap=#lap{idle=Idle},Laps,Threshold) ->
    case Idle(true) of
	finish ->
	    {?THRESHOLD,Bs};
	Facts ->
	    case varp:import_facts(Bs#bs.vp, Facts) of
		false -> false;
		true ->
		    N = varp:get_number_of_bound_variables(Bs#bs.vp),
		    loop(Bs,Lap,N,Laps,Threshold)
	    end
    end.

%% leaving before the fixpoint: the group is told not to wait
loop_done(Reason, #lap{idle=undefined}, Bs) ->
    {Reason,Bs};
loop_done(Reason, #lap{idle=Idle}, Bs) ->
    _ = Idle(false),
    {Reason,Bs}.

%% Run one lap over all variables given 
%% K number of variables, Q number of extra variables
%% R number of randomly selected variables
%% Variables in every eval is K+Q+R

lap(Bs,Lap) ->
    case import(Bs, Lap) of
	false -> false;
	true ->
	    case segment_vec(Bs#bs.vp, varp:vec_create(Bs#bs.vp, Lap#lap.k), Lap) of
		[] -> true;
		Vec0 -> lap_(Bs,Vec0,1,Lap)
	    end
    end.

lap_(Bs,Vec0,Count,Lap) when Count band ?COUNT =:= 0 ->
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
	    lap__(Bs,Vec0,Count,Lap)
    end;
lap_(Bs,Vec0,Count,Lap) ->
    lap__(Bs,Vec0,Count,Lap).

lap__(Bs,Vec0,Count,Lap) ->
    #lap{q=Q, f=F, r=R, subst=Subst, friend_map=FriendMap, on_model=OnModel} = Lap,
    case import(Bs, Lap) andalso
	varp:vec_sat(Bs#bs.vp,Vec0,Q,F,R,Subst,FriendMap,OnModel) of
	false -> false;
	{model, _} = Found -> Found;
	true ->
	    case segment_vec(Bs#bs.vp, varp:vec_step(Bs#bs.vp, Vec0), Lap) of
		[] -> true;
		Vec1 -> lap_(Bs,Vec1,Count+1,Lap)
	    end
    end.

%% The vector as the lap steps it, moved on to the segment: the lead
%% variable (the last of the list, the slowest to step) must be in
%% it, so the lap skips to the next lead that is, and starts a fresh
%% vector from there. [] when the lap is over.
segment_vec(_Vp, false, _Lap) ->
    [];
segment_vec(_Vp, [], _Lap) ->
    [];
segment_vec(_Vp, Vec, #lap{segment=undefined}) ->
    Vec;
segment_vec(Vp, Vec, Lap=#lap{segment=Mine, k=K}) ->
    Lead = lists:last(Vec),
    case Mine(Lead) of
	true -> Vec;
	false ->
	    case next_lead(Vp, Lead, Mine) of
		false -> [];
		Lead1 -> segment_vec(Vp, varp:vec_create(Vp, Lead1, K), Lap)
	    end
    end.

next_lead(Vp, X, Mine) ->
    case varp_nif:next_unbound(Vp, X) of
	false -> false;
	X1 ->
	    case Mine(X1) of
		true -> X1;
		false -> next_lead(Vp, X1, Mine)
	    end
    end.

%% facts from the other instances go in between the probes, at level
%% 0 where the lap stands; false when one contradicts this instance
import(_Bs, #lap{import=undefined}) ->
    true;
import(Bs, #lap{import=Import}) ->
    case Import() of
	[] -> true;
	Facts -> varp:import_facts(Bs#bs.vp, Facts)
    end.
