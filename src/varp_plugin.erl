%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2019, Tony Rogvall
%%% @doc
%%%    VARP plugin template
%%% @end
%%% Created : 30 Sep 2019 by Tony Rogvall <tony@rogvall.se>

-module(varp_plugin).

-export([run/2]).
-export([options/0]).

-include("varp.hrl").

options() ->
    [ #{ long => "long-option-name",
	 short => "o",
	 key   => internal_atom_name,
	 spec => {enum,[{"true",true}, {"false", false}]},  %% see varp_option
	 default => true,
	 description => "Option format."
       }
      %% ...
    ].

-spec run(Bs::#bs{}, Opts::map()) ->
		 {Status::inconsistent|timeout|cancel|continue,
		  Model::integer()|list(), Bs::#bs{}}.

%% ?INCONSISTENT means that clause set is found inconsistent and
%%   proving must be terminated.
%% 
%% ?CONTINUE means that proving may be continued.
%%
%% ?DONE means that proving is done all models are found.
%%
%% ?CANCEL means that proving was stopped by user.
%%
%% ?TIMEOUT  means that proving was timedout, and may, if
%%  local timeout, continue with an other step. 
%%  But if global timeout then proving is stopped.
%% 

run(Bs, Param) when is_record(Bs,bs), is_map(Param) ->
    {?CONTINUE, [], Bs}.
