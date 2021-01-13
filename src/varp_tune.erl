%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2021, Tony Rogvall
%%% @doc
%%%    Parameter tuning
%%% @end
%%% Created : 11 Jan 2021 by Tony Rogvall <tony@rogvall.se>

-module(varp_tune).

-export([run/1]).
-export([run/2]).

-export([demo/0]).
-export([demo_factor/0]).
-export([emit_csv/1, emit_csv/2]).
-export([write_csv/1, write_csv/2]).

%% -define(DEBUG, true).
-include("varp.hrl").

%% -define(TUNE_TIMEOUT, (60*5)).  %% 5 minutes
-define(TUNE_TIMEOUT, (10)).  %% 10 seconds

global_params() ->
    [{print,[false]},
     {xref, [true]},
     {seed, [1]},
     {timeout, [?TUNE_TIMEOUT]},
     {phase, [true, undefined]},  %% true, false
     {use_phase, [true, false]}].

backjump_params() ->
    [
     {minimize, [none,local,recursive]},
     {bump,[10,0.001,0.01,0.5,log10]},  %% none,next,log2,rank
     {max_conflicts, [1]},       %% 2,3
     {max_learned_factor, [1.2]},  %% 1.0,1.2,1.8,2.0
     {max_learned_inc,    [1.2]},  %% 1.0,1.2,1.8,2.0
     {keep_factor,        [0.2]},
     {restart_counter,    [0, 10, 100, 1000]},
     {restart_interval,   [infinity, 0.1, 10.0]}
    ].

statistics(Bs, T0) ->
    T1 = erlang:monotonic_time(),
    Time = erlang:convert_time_unit(T1-T0,native,microsecond),
    Ts = Time/1000000,
    ConflictCounter = varp:info(Bs#bs.vp, conflict_counter),
    BcpCounter = varp:info(Bs#bs.vp, bcp_counter),
    %% number of clauses create...?
    {{statistics,
      [{conflicts,ConflictCounter},
       {bcp,BcpCounter}]}, Ts}.

demo() ->
    run("pigeon.varp", [{"n",8}]).

demo_factor() ->
    run("is_prime.varp", [{"n", 8014003}]).

demo_factor2() ->
    run("is_prime.varp", [{"n", 2225513363}]).

run(File) ->
    run(File, []).
run(File, Meta) when is_list(Meta) ->
    run(File, maps:from_list(Meta));
run(File, Meta) when is_map(Meta) ->
    application:ensure_all_started(varp), %% load plugins etc
    {ok,Bin} = file:read_file(File),
    case parse(binary_to_list(Bin), Meta) of
	{ok,{Sections,Form}} ->
	    lists2:gfold(
	      fun([{global,Global},{backjump,BjParams}],
		  {I,ResList}) ->
		      io:format("RUN ~w: ", [I]),
		      GOpts = varp:load_option_list(Global),
		      GOpts1 = varp:section_opts(Sections, GOpts),
		      Do = 
			  [{satisfy,[]},
			   %% {saturate, SaturateParams}
			   %% {order, OrderParams}
			   {backjump,BjParams}],
		      GDo = varp:parse_do(Do),
		      GOpts2 = GOpts1#{ meta => Meta },
		      T0 = erlang:monotonic_time(),
		      try varp:do_run(GDo,Form,GOpts2) of
			  {?INCONSISTENT,_,Bs} ->
			      {Stat,Time} = statistics(Bs, T0),
			      io:format("UNSAT time=~fs\n", [Time]),

			      Res = [{run,I},{result,unsat},{time,Time},
				     Stat,
				     {global,Global},
				     {backjump,BjParams}],
			      {I+1,[Res|ResList]};
			  {?DONE, _, _Bs} ->
			      io:format("UNKNOWN\n"),
			      {I+1,ResList};
			  {?CONTINUE, _, Bs} ->
			      {Stat,Time} = statistics(Bs, T0),
			      io:format("SAT  time=~fs\n", [Time]),
			      Res = [{run,I},{result,sat},{time,Time},
				     Stat,
				     {global,Global},
				     {backjump,BjParams}],
			      {I+1,[Res|ResList]};
			  {?TIMEOUT,_,Bs} ->
			      {Stat,Time} = statistics(Bs, T0),
			      io:format("TIMEOUT  time=~fs\n", [Time]),
			      Res = [{run,I},{result,timeout},{time,Time},
				     Stat,
				     {global,Global},
				     {backjump,BjParams}],
			      {I+1,[Res|ResList]};
			  {?CANCEL,_,_} ->
			      io:format("USER ABORT\n"),
			      {I,ResList};
			  {?ERROR,_,_} ->
			      io:format("ERROR\n"),
			      {I,ResList};
			  Res ->
			      io:format("unexpected ~p\n",[Res]),
			      {I,ResList}
		      catch
			  ?EXCEPTION(error,Reason,Trace) ->
			      io:format("~s\n", [varp:format_error(Reason)]),
			      io:format("exception:~w\n~p\n", [Reason,?GET_STACK(Trace)]),
			      {I,ResList}
		      end
	      end,
	      {1,[]},
	      [{global,global_params()},
	       {backjump,backjump_params()}]);
	{error, {Ln,Mod,Message}} when is_integer(Ln), is_atom(Mod) ->
	    Text = (catch apply(Mod, format_error, [Message])),
	    io:format("~s\n", [Text]);

	{error, {Ln,Mod,Message}, _EndLn} when is_integer(Ln), is_atom(Mod) ->
	    Text = (catch apply(Mod, format_error, [Message])),
	    io:format("~s\n", [Text]);

	{error, Message} ->
	    io:format("~s\n", [varp:format_error(Message)])
    end.


parse(String, Meta) ->
    case varp:tokens(String) of
	{ok,[{identifier,_,"c"}|_Ts]} ->
	    parse_dimacs(String);
	{ok,[{identifier,_,"p"}|_Ts]} ->
	    parse_dimacs(String);
	{ok,Ts} ->
	    case varp_parse:parse(Ts) of
		{ok,{Sections,Formula}} ->
		    GOpts = #{ meta => Meta },
		    try varp:split_sections(Sections,GOpts) of
			{ok, SectionMap} ->
			    {ok,{SectionMap,Formula}};
			Error ->
			    Error
		    catch
			error:Reason ->
			    {error,Reason}
		    end;
		Error -> Error
	    end;
	Error -> Error
    end.

parse_dimacs(String) ->
    Bin = list_to_binary(String), %% utf?
    case varp_dimacs:parse(Bin) of
	Form={cnf,{_Var,_Clause,SectionMap,_Cs}} ->
	    {ok,{SectionMap,Form}};
	Form={snf,{_Var,_Clause,SectionMap,_Cs}} ->
	    {ok,{SectionMap,Form}};
	Error ->
	    Error
    end.

write_csv(Result) ->
    write_csv("tune.csv", Result).

write_csv(Filename, Result) ->
    case file:open(Filename, [write]) of
	{ok,Fd} ->
	    try emit_csv(Fd, Result) of
		_ -> ok
	    after
		file:close(Fd)
	    end;
	Error ->
	    Error
    end.

emit_csv(Result) ->
    emit_csv(user, Result).
     
emit_csv(Fd, Result) ->
    emit_header(Fd, hd(Result)), io:put_chars(Fd, "\n"),
    [begin emit_row(Fd, Ent), io:put_chars(Fd, "\n") end || 
	Ent <- lists:reverse(Result)].

emit_header(Fd,[{_Key,Value}|Tail]) when is_list(Value) ->
    emit_header(Fd, Value), emit_header(Fd, Tail);
emit_header(Fd, [{Key,_Value}|Tail]) ->
    io:format(Fd, "\"~s\"; ", [Key]), emit_header(Fd, Tail);
emit_header(_Fd, []) ->
    ok.

emit_row(Fd, [{_Key,Value}|Tail]) when is_list(Value) ->
    emit_row(Fd, Value), emit_row(Fd, Tail);
emit_row(Fd, [{_Key,Value}|Tail]) ->
    if is_float(Value) ->
	    io:format(Fd, "~s; ", [io_lib_format:fwrite_g(Value)]);
       true ->
	    io:format(Fd, "~p; ", [Value])
    end,
    emit_row(Fd, Tail);
emit_row(_Fd, []) ->
    ok.


    

    
    
    
