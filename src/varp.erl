%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2010, Tony Rogvall
%%% @doc
%%%    Prover interface
%%% @end
%%% Created :  5 Aug 2010 by Tony Rogvall <tony@rogvall.se>

-module(varp).

-export([start/0, start0/0]).
-export([main/1]).
-export([do_run/3]).

-export([tokens/1]).
-export([parse/1, parse/2]).
-export([scan_file/1]).
-export([file/1, string/1]).
-export([archive_path/1]).
-export([output_model/3]).
-export([empty_sections/0]).
-export([split_sections/1, split_sections/2]).
-export([section_opts/2]).
-export([load_plugins/0]).
-export([load_do/0, load_do/1]).
-export([parse_do/1, parse_do/2]).

-export([load_options/0, load_options/1, load_options/2]).
-export([load_option_list/1, load_option_list/3]).

-export([default_options/0]).
-export([read_timer/1]).
-export([set_local_timeout/2]).
-export([set_global_timeout/2]).
-export([is_local_timeout/1]).
-export([is_global_timeout/1]).
-export([is_timeout/1]).
-export([is_timeout_or_was_canceled/1]).
-export([check_timeout_or_cancel/3]).
-export([decision_clause/1, decision_clause/2]).
-export([block_clause/1]).
-export([make_psym/2]).
-export([format_error/1]).

-include_lib("stdlib/include/zip.hrl").

%% -define(DEBUG, true).
-include("varp.hrl").

-record(stat,
	{
	 clause_n_counter,
	 clause_2_counter,
	 clause_3_counter,
	 clause_d_counter,
	 bcp_count,
	 conflict_count,
	 bound,
	 clauses,
	 dead_clauses
	}).

global_options() ->
    [
     #{ long => "phase",
	key => phase,
	spec => {enum,[?BOOL]},
	default => true,
	description => "Fixed phase selection."
      },
     #{ long => "use-phase",
	key => use_phase,
	spec => {enum,[?BOOL]},
	default => false,
	description => "Use variable phase saving."
      },
     #{ long => "turbo",
	key => turbo,
	spec => {enum,[?BOOL]},
	default => false,
	description => "Use turbo rule."
      },
     #{ long => "starexec",
	key => starexec,
	spec =>  {enum,[?BOOL]},
	default => false,
	description => "Report result in starexec format"
      },
     #{ long => "outdir",
	key => outdir,
	spec =>  string,
	default => "",
	description => "Output directory for various output files."
      },
     #{ long => "proof-output",
	key => proof_output,
	spec =>  {enum,
		  [{"none", none},
		   {"user", user},
		   {"text", text},
		   {"binary", binary}]},
	default => none,
	description => "Proof output type."
      },
     #{ long => "proof-file",
	key => proof_file,
	spec => string,
	default => "proof.out",
	description => "Proof output file name."
      },
     #{ long => "method",
	key => method,
	spec => {enum,
		 [{"collect", collect},
		  {"count", count}]},
	default => collect,
	description => "Count or collect models."
      },
     #{ long => "print",
	short => "p",
	key => print,
	spec => {enum,
		 [?BOOL,
		  {"literal",literal},
		  {"erlang",erlang},
		  {"model",model},
		  {"dimacs",dimacs}
		 ]},
	default => model,
	description => "Print models when found."
      },
     #{ long => "partial",
	key => partial,
	spec => {enum,[?BOOL]},
	default => false,
	description => "Print partial models when possible."
      },
     #{ long => "compress",
	 short => "g",
	 key => compress,
	 spec => {enum,[?BOOL]},
	 default => false,
	 description => "Compress clauses."
       },
      #{ long => "seed",
	 key => seed,
	 spec => integer,
	 default => -1,
	 description => "Random seed."
       },
      #{ long => "assoc",
	 key => assoc,
	 spec => {enum,
		  [{"left",left},
		   {"right",right},
		   {"balanced",balanced},
		   {"none", none}
		  ]},
	 default => none,
	 description => "Specify the order how all and any are built."
       },
      #{ long => "adder",
	 key => adder,
	 spec => {enum,
		  [{"plain",plain},
		   {"fast",fast}
		  ]},
	 default => plain,
	 description => "Specify style of adder to use."
       },
      #{ long  => "timeout",
	 short => "t",
	 key   => timeout,
	 spec  => {union,[float,{enum,[{"infinity",infinity}]}]},
	 default => infinity,
	 description => "Max time to run in seconds"
       },
      #{ long => "carry",
	 key => carry,
	 spec => {enum,[?BOOL,{"ignore",ignore}]},
	 default => ignore,
	 description => "How to handle carry in addition."
       },
      #{ long => "borrow",
	 key => borrow,
	 spec => {enum,[?BOOL,{"ignore",ignore}]},
	 default => ignore,
	 description => "How to handle borrow in subtraction."
       },
      #{ long => "overflow",
	 key => overflow,
	 spec => {enum,[?BOOL,{"ignore",ignore}]},
	 default => ignore,
	 description => "How to handle overflow in addition."
       },
      #{ long => "divz",
	 key => divz,
	 spec => {enum,[?BOOL,{"ignore",ignore}]},
	 default => false,
	 description => "How to handle divide by zero."
       },
      #{ long => "log",
	 key => log,
	 spec => {enum,
		  [{"debug",?LOG_LEVEL_DEBUG},
		   {"info",?LOG_LEVEL_INFO},
		   {"notice",?LOG_LEVEL_NOTICE},
		   {"warning",?LOG_LEVEL_WARNING},
		   {"error",?LOG_LEVEL_ERROR},
		   {"critical",?LOG_LEVEL_CRITICAL},
		   {"alert",?LOG_LEVEL_ALERT},
		   {"emergency",?LOG_LEVEL_EMERGENCY},
		   {"none",?LOG_LEVEL_NONE}]},
	 default => ?LOG_LEVEL_NONE,
	 description => "Output log level."
       },
      #{ long => "out",
	 short => "o",
	 key => out,
	 spec => string, 
	 default => "",
	 description => "Output file name."
       },
      #{ long => "formula",
	 short => "f",
	 key => formula,
	 spec => {multiple,string},
	 default => [],
	 description => "Command line formula."
       },
      #{ long => "qtype",
	 key => qtype,
	 spec => {enum,[{"fifo",fifo},{"lifo",lifo},{"recursive",recursive}]},
	 default => recursive,
	 description => "lifo, fifo or depth first queue type."
       },
      #{ long => "hash",
	 key => hash,
	 spec =>  {enum,[?BOOL]},
	 default => false,
	 description => "use clause hash, speed up validate."
       },
      #{ long => "xref",
	 key => xref,
	 spec =>  {enum,[?BOOL]},
	 default => false,
	 description => "enable xref from start."
       },
      #{ long => "version",
	 short => "V", 
	 key => version,
	 spec => string,
	 default => vsn(),
	 description => "Report current version."
       },
     #{ long => "cprof",
	key => cprof,
	spec =>  {enum,[?BOOL]},
	default => false,
	description => "Use Call Count Profiling"
      },
     #{ long => "fprof",
	key => fprof,
	spec =>  {enum,[?BOOL]},
	default => false,
	description => "Use Time Profiling"
      },
      #{ long => "help",
	 short => "h", 
	 key => help,
	 spec => void,
	 default => undefined,
	 description => "This help."
       }
    ].

internal_options() -> %% needed?
    [
     #{ key => meta,
	spec => {set,{string,term}},
	default => #{},
	description => "Internal list of meta variables and values"},
     #{ key => defs,
	spec => {set,{pred,term}},
	default => #{},
	description => "Internal list of all definitions"},
     #{ key => decls,
	spec => {set,{predpat,atom,term}},
	default => #{},
	description => "Internal list of all declarations"},     
     #{ key => literals,
	spec => {set,atom},
	default => #{},
	description => "Internal list of all literals"},
     #{ key => assert,
	spec => {list,term},
	default => [],  %% list
	description => "Internal list of all assertions"},
     #{ key => input,
	spec => {list,term},
	default => [],  %% list
	description => "Internal list of input modules"},
     #{ key => output,
	spec => {list,term},
	default => [],  %% list
	description => "Internal list of output modules"},
     #{ key => syms,
	spec => map,
	default => #{},  %% map
	description => "Internal map of symbols" }
    ].
    

vsn() ->
    case application:get_key(varp,vsn) of
	{ok,V} -> V;
	undefined -> "undefined"
    end.

%% call with erl ... -extra "$@"
start() ->
    main(init:get_plain_arguments()).

start0() ->
    %% dummy start for servator when generating application
    application:ensure_all_started(varp),
    ok.

main(Args) ->
    %% ?dbg1("main: arguments = ~p\n", [Args]),
    application:ensure_all_started(varp),

    Plugins = load_plugins(),
    %% ?dbg1("main: plugins = ~p\n", [Plugins]),

    GlobalOptionSpec = global_option_spec(),
    GOpts0 = default_options(),

    %% ?dbg1("options0 = ~p\n", [GOpts0]),
    GOpts1 = load_options(GlobalOptionSpec, GOpts0),
    %% ?dbg1("main: options1 = ~p\n", [GOpts1]),
    Do0 = load_do(Plugins),

    {Do1,Files,GOpts2,Bound0} =
	process_args(Args, Plugins, [], [], GlobalOptionSpec, GOpts1, []),
    Bound = maps:from_list(Bound0),

    Do = if Do1 =/= [] -> Do1;
	    true -> Do0
	 end,
    %% io:format("main: do = ~p\n", [Do]),
    %% io:format("files = ~p\n", [Files]),
    %% io:format("options2 = ~p\n", [GOpts2]),
    %% io:format("bound = ~p\n", [Bound]),

    {ReadIn,{Sections0,Formula0}} =
	try load_formulas(maps:get(formula,GOpts2,[]), undefined, 'and',
			  GOpts2) of
	    {ok,{S0,undefined}}-> {true,{S0,undefined}};
	    {ok,R0} -> {false,R0}
	catch
	    ?EXCEPTION(error,Error0,_Trace0) ->
		io:format("~s\n", [format_error(Error0)]),
		?dbg("~p\n", [?GET_STACK(_Trace0)]),
		halt(1)
	end,

    GOpts3 = section_opts(Sections0, GOpts2#{ meta => Bound }),

    case Files of
	[] when not ReadIn ->
	    varp_run(Do, Formula0, GOpts3);
	[] when ReadIn ->
	    case read_in() of
		{ok,<<>>} ->
		    varp_run(Do, Formula0, GOpts3);
		{ok,Data} ->
		    try parse("*stdin*", Data, GOpts3) of
			{ok,{Sections1,Formula}} ->
			    Formula1 = join_f('and',Formula0,Formula),
			    Sections = append_sections(Sections0,Sections1),
			    GOpts4 = section_opts(Sections,GOpts3),
			    varp_run(Do,Formula1,GOpts4)
		    catch
			?EXCEPTION(error,Error1,_Trace1) ->
			    io:format("~s\n", [format_error(Error1)]),
			    ?dbg("~p\n", [?GET_STACK(_Trace1)]),
			    halt(1)
		    end;
		_Error ->
		    halt(1)
	    end;
	[F] -> %% check if batch mode, run tar/zip over all formulas
	    case archive_type(F) of
		undefined ->
		    try load_files([F],Formula0,Sections0,'and',GOpts3) of
			{ok,{Sections1,Formula,GOpts4}} ->
			    GOpts5 = section_opts(Sections1, GOpts4),
			    varp_run(Do,Formula,GOpts5);
			_Error ->
			    halt(1)
		    catch
			?EXCEPTION(error,Error2,_Trace2) ->
			    io:format("~s\n", [format_error(Error2)]),
			    ?dbg("~p\n", [?GET_STACK(_Trace2)]),
			    halt(1)
		    end;
		Type -> %% with formula?
		    run_batch(Do,Type,F,GOpts3)
	    end;
	Fs ->
	    try load_files(Fs,Formula0,Sections0,'and',GOpts3) of
		{ok,{Sections1,Formula,GOpts4}} ->
		    GOpts5 = section_opts(Sections1, GOpts4),
		    varp_run(Do,Formula,GOpts5);
		_Error ->
		    halt(1)
	    catch
		?EXCEPTION(error,Error3,_Trace3) ->
		    io:format("~s\n", [format_error(Error3)]),
		    ?dbg("~p\n", [?GET_STACK(_Trace3)]),
		    halt(1)
	    end
    end,
    halt(get(exit_code)).

global_option_spec() ->
    GlobalOptionList = global_options(),
    varp_option:options_spec(GlobalOptionList).

default_options() ->
    varp_option:default_opts(global_options() ++ internal_options()).

load_options() ->
    load_options(default_options()).

load_options(GOpts) ->
    load_options(global_option_spec(), GOpts).

load_options(OptionSpec,GOpts) ->
    case application:get_env(varp, options) of
	undefined -> GOpts;
	{ok,OptionList} ->
	    load_option_list(OptionSpec,GOpts,OptionList)
    end.

load_option_list(OptionList) when is_list(OptionList) ->
    load_option_list(global_option_spec(), default_options(), OptionList).

load_option_list(OptionSpec,OptMap,[{Key,Value}|Opts]) ->
    OptMap1 = varp_option:setopt(Key,Value,OptMap,OptionSpec),
    load_option_list(OptionSpec,OptMap1,Opts);
load_option_list(_OptionSpec,OptMap,[]) ->
    OptMap.


%% load the do config
load_do() ->
    load_do(load_plugins()).

load_do(Plugins) ->
    case application:get_env(varp, do) of
	undefined -> [];
	{ok,Do} ->
	    %% convert all option lists info maps
	    %% for all plugins
	    parse_do_(Do, Plugins, [])
    end.

parse_do(Do) when is_list(Do) ->
    parse_do_(Do, load_plugins(), []).

parse_do(Do, PluginMap) when is_list(Do), is_map(PluginMap) ->
    parse_do_(Do, PluginMap, []).

parse_do_([{P, OptionList}|Ps], PluginMap, Acc) ->
    case maps:get(P, PluginMap, undefined) of
	undefined ->
	    io:format("plugin ~s does not exist\n", [P]),
	    parse_do_(Ps, PluginMap, Acc);
	Mod ->
	    OptionInfoList = Mod:options(),
	    OptionSpec = varp_option:options_spec(OptionInfoList),
	    OptMap = varp_option:default_opts(OptionInfoList),
	    OptMap1 =
		lists:foldl(
		  fun({Key,Value}, Mi) ->
			  ?dbg("setopt(~p, ~p)\n", [Key,Value]),
			  varp_option:setopt(Key,Value,Mi,OptionSpec)
		  end, OptMap, OptionList),
	    parse_do_(Ps, PluginMap, [{Mod, OptMap1}|Acc])
    end;
parse_do_([], _PluginMap, Acc) ->
    lists:reverse(Acc).


%% load a map of plugins Name => Module | Atom => Module
load_plugins() ->
    case application:get_env(varp, plugins) of
	undefined -> #{};
	{ok,Ps} ->
	    lists:foldl(
	      fun({ShortName,LongName,Mod},Plugins) ->
		      case load_plugin(Mod) of
			  true ->
			      Plugins#{ ShortName => Mod,
					list_to_atom(ShortName) => Mod,
					LongName => Mod,
					list_to_atom(LongName) => Mod };
			  false ->
			      Plugins
		      end
	      end, #{}, Ps)
    end.
		
load_plugin(Mod) ->
    case code:ensure_loaded(Mod) of
	{module,Mod} ->
	    case erlang:function_exported(Mod, options, 0) of
		false ->
		    io:format("error: options/0 not exported by ~s\n", [Mod]),
		    false;
		true ->
		    true
	    end 
		and
	    case erlang:function_exported(Mod, run, 2) of
		false ->
		    io:format("error: run/2 not exported by ~s\n",[Mod]),
		    false;
		true ->
		    true
	    end;
	{error,Reason} ->
	    io:format("error: unabled to load plugin ~p\n", 
		      [Reason]),
	    false
    end.

run_batch(Do,ArchiveType,ArchiveFile,GOpts) ->
    {ok,Fs} = archive_file_list(ArchiveType,ArchiveFile),
    lists:foreach(
      fun(F) ->
	      AFile = filename:join(ArchiveFile,F),
	      case load_files([AFile],true,empty_sections(),'and',GOpts) of
		  {ok,{Sections,Formula,GOpts1}} ->
		      varp_run(Do,Formula, section_opts(Sections, GOpts1));
		  Error ->
		      io:format("~s: error ~p\n", [F,Error]),
		      ok
	      end
      end, Fs).

%% command line - display errors and exception as well as results
varp_run(Do, Formula, GOpts) ->
    put(exit_code, 0),
    start_cprof(GOpts),
    start_fprof(GOpts),
    R = (catch do_run(Do, Formula, GOpts)),
    case R of
	{'EXIT',{Error, _Where}} ->
	    io:format("~s\n", [format_error(Error)]),
	    ?dbg("~p\n", [_Where]),
	    stop_cprof(GOpts, false),
	    stop_fprof(GOpts, false),
	    ok;
	_ ->
	    stop_cprof(GOpts, true),
	    stop_fprof(GOpts, true),
	    R
    end.

start_cprof(GOpts) ->
    case maps:get(cprof, GOpts) of
	false ->
	    ok;
	true ->
	    cprof:start()
    end.
    
stop_cprof(GOpts, Analyse) ->
    case maps:get(cprof, GOpts) of
	false ->
	    ok;
	true ->
	    if Analyse ->
		    CProf = cprof:analyse(),
		    display_cprof(CProf);
	       true ->
		    ok
	    end,
	    cprof:stop()
    end.

start_fprof(GOpts) ->
    case maps:get(fprof, GOpts) of
	false ->
	    ok;
	true ->
	    fprof:start(),
	    fprof:trace(start)
    end.

stop_fprof(GOpts, Analys) ->
    case maps:get(fprof, GOpts) of
	false ->
	    ok;
	true ->
	    fprof:trace(stop),
	    if Analys ->
		    %% FIXME output in file...?
		    fprof:profile(),
		    ok = fprof:analyse();
	       true ->
		    ok
	    end,
	    fprof:stop()
    end.    

display_cprof({TCalls,Ms}) ->    
    io:format("total calls: ~w\n", [TCalls]),
    lists:foreach(
      fun({Mod,MCalls,Fs}) when MCalls > 1 ->
	      io:format("  ~s calls: ~w\n", [Mod,MCalls]),
	      lists:foreach(
		fun({{_Mod,Fun,Ari},FCalls}) when FCalls > 1 ->
			io:format("    ~s/~w: ~w\n", [Fun,Ari,FCalls]);
		   (_) ->
			ok
		end, Fs);
	 (_) ->
	      ok
      end, Ms).

format_error(Err) ->
    case Err of
	{unbound,Var} ->
	    ["Variable ", Var, " is unbound\n"];
	{var_out_of_range,Var} ->
	    VarName = varp_formula:format_symbol(Var),
	    ["Variable ",VarName," is out of range\n"];
	{empty_clause, _Where} ->
	    ["Empty clause not allowed\n"];
	{arity_mismatch,Var} ->
	    VarName = varp_formula:format_symbol(Var),
	    ["Variable ",VarName, " can only have ", "one arity"];
	{bitsize_mismatch,Var} ->
	    VarName = varp_formula:format_symbol(Var),
	    ["Variable ",VarName, " can only have one size"];
	{shift_not_constant,B} ->
	    BStr = varp_formula:format_symbol(B),
	    ["Shift value ",BStr," must be constant "];
	_ ->
	    io_lib:format("~p\n", [Err])
    end.


do_run(Do, Formula, GOpts) ->
    R = do_run_(Do, Formula, GOpts),
    garbage_collect(self(),[{type,major}]),
    R.

do_run_(Do, Formula, GOpts) ->
    T0 = erlang:monotonic_time(),
    Bs0 = varp_formula:new(GOpts),
    S0 = stat(Bs0),
    varp_formula:info(Bs0, "pass ~p\n", [build]),
    {Main,Bs} = case varp_formula:build(Formula,Bs0) of
		    {{bool,Var0},Bs0_1} -> {Var0,Bs0_1};
		    {{uint,1,[Var0]},Bs0_1} -> {Var0,Bs0_1};
		    {{_Type,_N,Vs},Bs0_1} -> 
			VsB = [{bool,Vi} || Vi <- Vs],
			{{bool,M0},Bs0_2} = varp_formula:any(VsB,Bs0_1),
			{M0,Bs0_2}
		end,
    S1 = stat(Bs),
    T1 = erlang:monotonic_time(),
    Time = erlang:convert_time_unit(T1-T0,native,microsecond),
    Ts = Time/1000000,
    show_info(S1, S0, Ts, Bs),

    Timeout = maps:get(timeout, GOpts, infinity),
    Bs1 = varp:set_global_timeout(Bs, Timeout),
    Bs2 = Bs1#bs { main = Main },
    {R,Acc,Bs3} = do(Do,[],Bs2),
    Method = method(Do),
    case Bs2#bs.proof_fd of
	undefined -> ok;
	user -> ok;
	Fd -> file:close(Fd)
    end,
    case varp_formula:getopt(Bs2, print) of
	false -> 
	    {R,Acc,Bs3};
	_ ->
	    N = if is_list(Acc) -> length(Acc);
		   is_integer(Acc) -> Acc
		end,
	    if N =:= 0 ->
		    output_partial_model(Bs2,R);
	       true ->
		    ok
	    end,
	    M = case R of
		    ?DONE -> N;
		    ?CONTINUE when N>0 -> N;
		    _ -> R
		end,
	    display_result(M, Method, Bs3),
	    {R,Acc,Bs3}
    end.

do([{Plugin,Param}|Do],Acc0,Bs) ->
    S0 = stat(Bs),
    varp_formula:info(Bs, "pass ~p\n", [Plugin]),
    T0 = erlang:monotonic_time(),
    try Plugin:run(Bs, Param) of
	{Result,Acc1,Bs1} ->
	    T1 = erlang:monotonic_time(),
	    S1 = stat(Bs1),
	    Time = erlang:convert_time_unit(T1-T0,native,microsecond),
	    Ts = Time/1000000,
	    %% io:format("DO ~s = R=~p, Acc=~p\n", [Plugin,Result,Acc1]),
	    show_info(S1, S0, Ts, Bs1),
	    Acc = combine_result(Acc0,Acc1),
	    case Result of
		?INCONSISTENT ->
		    no_models(Bs1);
		?CANCEL ->
		    {?CANCEL,Acc,Bs1};
		?ERROR ->
		    {?ERROR,Acc,Bs1};
		?DONE ->
		    {?DONE,Acc,Bs1};
		?TIMEOUT ->
		    case is_local_timeout(Bs1) andalso 
			not is_global_timeout(Bs1) of
			true ->
			    do(Do, Acc, Bs1); %% continue
			false ->
			    {?TIMEOUT,Acc,Bs1}
		    end;
		_ when Acc =:= []; Acc =:= 0 ->
		    case one_model(Bs1) of
			false ->
			    do(Do, Acc, Bs1);
			Acc2 ->
			    Acc3 = combine_result(Acc2,Acc),
			    {?DONE,Acc3,Bs1}
		    end;
		_ ->
		    do(Do, Acc, Bs1)
	    end
    catch
	?EXCEPTION(error, Reason, Stacktrace) ->
	    io:format("~s crashed ~p: ~p\n",
		      [Plugin, Reason, ?GET_STACK(Stacktrace)]),
	    error
    end;
do([], Acc, Bs) ->
    {?CONTINUE, Acc, Bs}.

combine_result(N, M) when is_integer(N), is_integer(M) ->
    N+M;
combine_result(Ns,Ms) when is_list(Ns), is_list(Ms) ->
    Ns++Ms;
combine_result(N, Ms) when is_integer(N), is_list(Ms) ->
    N+length(Ms);
combine_result(Ns,M) when is_list(Ns), is_integer(M) ->
    length(Ns)+M.

show_info(S1, S0, Ts, Bs) ->
    varp_formula:info(Bs, "    | bcp: ~w\n    | clause:n:~w,2:~w,3:~w,d:~w\n    | #clauses:~w, #dead:~w, #conflict:~w\n | time=~.2fs\n",
		      [S1#stat.bcp_count-S0#stat.bcp_count,
		       S1#stat.clause_n_counter - S0#stat.clause_n_counter,
		       S1#stat.clause_2_counter - S0#stat.clause_2_counter,
		       S1#stat.clause_3_counter - S0#stat.clause_3_counter,
		       S1#stat.clause_d_counter - S0#stat.clause_d_counter,
		       S1#stat.clauses,
		       S1#stat.dead_clauses,
		       S1#stat.conflict_count-S0#stat.conflict_count,
		       Ts]),
    varp_formula:info(Bs,"    | bound: ~w [~w/~w]\n",
		      [S1#stat.bound-S0#stat.bound,
		       S1#stat.bound,
		       varp_formula:number_of_variables(Bs)
		      ]).

stat(Bs) ->
    #stat { clause_n_counter = varp_formula:clause_bcp_counter(Bs,n),
	    clause_2_counter = varp_formula:clause_bcp_counter(Bs,2),
	    clause_3_counter = varp_formula:clause_bcp_counter(Bs,3),
	    clause_d_counter = varp_formula:clause_bcp_counter(Bs,dead),
	    bcp_count     = varp_formula:bcp_counter(Bs),
	    conflict_count = varp_formula:conflict_counter(Bs),
	    bound          = varp_formula:number_of_bound(Bs),
	    clauses        = varp_formula:number_of_clauses(Bs),
	    dead_clauses   = varp_formula:number_of_dead_clauses(Bs)
	  }.

%% extract "method" form Do list
method(Do) ->
    case lists:keymember(varp_satisfy,1,Do) of
	true -> satisfy;
	false ->
	    case lists:keymember(varp_falsify,1,Do) of
		true -> falsify;
		false ->
		    case lists:keymember(varp_prove,1,Do) of
			true -> prove;
			false -> none
		    end
	    end
    end.

display_result(N, satisfy, _Bs) when is_integer(N), N>0 ->
    io:format("% ~w\n", [N]);
display_result(N, falsify, _Bs) when is_integer(N), N>0 ->
    io:format("% ~w\n", [N]);
display_result(N, prove,_Bs) when is_integer(N), N>0 ->
    io:format("% FALSE\n", []);
display_result(N, none,_Bs) when is_integer(N), N>0 ->
    io:format("% ~w\n", [N]);
display_result(?INCONSISTENT, satisfy, Bs) ->
    case varp_formula:getopt(Bs, starexec) of
	true ->
	    put(exit_code, 20),
	    io:format("s UNSATISFIABLE\n");
	false ->
	    io:format("% 0\n", [])
    end;
display_result(?INCONSISTENT, falsify, _Bs) ->
    io:format("% 0\n", []);
display_result(?INCONSISTENT,prove,_Bs) ->
    io:format("% TRUE\n", []);
display_result(?INCONSISTENT,none,_Bs) ->
    ok; %% io:format("\n", []);
display_result(?TIMEOUT,_,_Bs) ->
    io:format("% TIMEOUT\n", []);
display_result(?CANCEL,_,_Bs) ->
    io:format("% USER ABORT\n", []);
display_result(?ERROR,_,_Bs) ->
    io:format("% ERROR\n", []);
display_result(?CONTINUE,prove,_Bs) ->
    io:format("% UNKNOWN\n", []);
display_result(?CONTINUE,_,_Bs) ->
    ok. %% io:format("\n", [])


%% check if there is already a "unique" model
one_model(Bs) when Bs#bs.main =:= ?F ->
    false;
one_model(Bs) ->
    NV = varp_formula:number_of_variables(Bs),
    NB = varp_formula:number_of_bound(Bs),
    if NV =:= NB ->
	    Model = output_model(Bs,false,1),
	    case varp_formula:getopt(Bs,method) of
		collect -> [Model];
		count -> 1
	    end;
       true ->
	    false
    end.

no_models(Bs) ->
    case varp_formula:getopt(Bs,method) of
	collect ->
	    {?INCONSISTENT,[],Bs};
	count -> 
	    {?INCONSISTENT,0,Bs}
    end.

order_decl([]) -> [];
order_decl(Vs) -> order_decl(Vs,[]).

order_decl([Key1,Key2|Vs],Opts) when is_integer(Key1), is_integer(Key2) ->
    order_decl(Vs,[{order,[Key1,Key2]}|Opts]);
order_decl([Key1|Vs],Opts) when is_integer(Key1) ->
    order_decl(Vs,[{order,[Key1]}|Opts]);
order_decl([{order_list,Ls1}|Vs],[{order_list,Ls}|Opts]) ->
    order_decl(Vs, [{order_list,Ls++Ls1}|Opts]);
order_decl([{order_list,Ls1}|Vs],Opts) ->
    order_decl(Vs, [{order_list,Ls1}|Opts]);
order_decl([V|Vs],[{order_list,Ls}|Opts]) when is_tuple(V) ->
    order_decl(Vs, [{order_list,Ls++[V]}|Opts]);
order_decl([V|Vs],Opts) when is_tuple(V) ->
    order_decl(Vs, [{order_list,[V]}|Opts]);
order_decl([],Opts) ->
    case lists:reverse(Opts) of
	[{order_list,L1},{order,K},{order_list,L2}] ->
	    [{sort,K},{first,L1},{last,L2}];
	[{order_list,L1},{order,K}] ->
	    [{sort,K},{first,L1}];
	[{order,K},{order_list,L2}] ->
	    [{sort,K},{last,L2}];
	[{order_list,L1}] ->
	    [{first,L1}];
	[{order,K}] ->
	    [{sort,K}];
	[] ->
	    []
    end.

%% load files and form a conjunction over all files
load_files([F|Fs],Formula0,Sections,JoinOp,GOpts) ->
    Ext = filename:extension(F),
    if Ext =:= ".cnf"; Ext =:= ".snf"; Ext =:= ".dimacs" ->
	    {ok, Data} = read_file(F),
	    case varp_dimacs:parse(Data) of
		Error={error,Ln,Reason} ->
		    io:format("~s:~w error: ~p\n", [F,Ln,Reason]),
		    Error;
		Cnf = {cnf,{_NVars,_NClauses,Sections0,_CLs}} ->
		    %% io:format("% loaded: ~p\n", [Cnf]),
		    Formula1 = join_f(JoinOp,Cnf,Formula0),
		    Sections1 = append_sections(Sections, Sections0),
		    load_files(Fs,Formula1,Sections1,JoinOp,GOpts);
		Snf = {snf,{_NVars,_NClauses,Sections0,_CLs}} ->
		    %% io:format("% loaded: ~p\n", [Snf]),
		    Formula1 = join_f(JoinOp,Snf,Formula0),
		    Sections1 = append_sections(Sections, Sections0),
		    load_files(Fs,Formula1,Sections1,JoinOp,GOpts)
	    end;
       Ext =:= ".dat"; Ext =:= ".txt" -> %% fixme
	    %% try input modules
	    Input = maps:get(input, Sections, []),
	    Meta  = maps:get(meta,GOpts,[]),
	    case varp_input(Input, F, Meta) of
		{ok,Formula} ->
		    Formula1 = join_f(JoinOp,Formula,Formula0),
		    load_files(Fs,Formula1,Sections,JoinOp,GOpts);
		{ok,MetaF,Formula} ->
		    %% io:format("Meta = ~p\n", [MetaF]),
		    Meta1 = maps:merge(Meta, maps:from_list(MetaF)),
		    %% io:format("Meta1 = ~p\n", [Meta1]),
		    GOpts1 = maps:put(meta,Meta1,GOpts),
		    Formula1 = join_f(JoinOp,Formula,Formula0),
		    load_files(Fs,Formula1,Sections,JoinOp,GOpts1);
		Error ->
		    Error
	    end;
       true ->
	    %% io:format("Read file ~s\n", [F]),
	    {ok, Data} = read_file(F),
	    case parse(F, Data, GOpts) of
		{ok,{Sections1,Formula}} ->
		    %% io:format("% loaded: ~s\n", [F]),
		    Formula1 = join_f(JoinOp,Formula,Formula0),
		    load_files(Fs,Formula1,
			       append_sections(Sections,Sections1),
			       JoinOp,GOpts);
		Error ->
		    Error
	    end
    end;
load_files([],Formula,Sections,_JoinOp,GOpts) ->
    {ok,{Sections,Formula,GOpts}}.


%% special input format
varp_input([Input | InputList], FileName, Meta) ->
    {M,F,A} = mfa_arg(Input, file),
    case code:ensure_loaded(M) of
	{module,Mod} ->
	    case erlang:function_exported(M, F, length(A)+2) of
		true ->
		    apply(Mod, F, [FileName, Meta]++A);
		false ->
		    case erlang:function_exported(M, F, length(A)+1) of
			true ->
			    apply(Mod, F, [FileName]++A);
			false ->
			    varp_input(InputList, FileName, Meta)
		    end
	    end;
	{error,_} ->
	    varp_input(InputList, FileName, Meta)
    end;
varp_input([], _FileName, _Meta) ->
    {error, no_input}.

%% special output format
varp_output([Out | OutputList], Fd, Partial, Model) ->
    {M,F,A} = mfa_arg(Out, output),
    case code:ensure_loaded(M) of
	{module,Mod} ->
	    case erlang:function_exported(Mod, F, length(A)+3) of
		true ->
		    apply(Mod, F, [Fd, Partial, Model]++A);
		false ->
		    varp_output(OutputList, Fd, Partial, Model)
	    end;
	{error,Err} ->
	    io:format("varp_output module error ~p\n", [Err]),
	    varp_output(OutputList, Fd, Partial, Model)
    end;
varp_output([], _Fd, _Partial, _Model) ->
    {error, no_output}.

mfa_arg({id,Name},Func) ->
    {list_to_atom(Name),Func,[]};
mfa_arg(M,Func) when is_atom(M) ->
    {list_to_atom(M),Func,[]};
mfa_arg({M,F,A},_Func) when is_atom(M), is_atom(F), is_list(A) -> 
    {M,F,A}.

%% possibly emit a model
output_partial_model(Bs, _R) ->
    case varp_formula:getopt(Bs,partial) of
	true ->
	    output_model(Bs,true,0);
	false ->
	    ok
    end.

output_model(Bs,Partial,I) ->
    output_model_header(Bs,Partial,I),
    Model = varp_formula:model(Bs),
    case varp_formula:getopt(Bs,print) of
	false ->
	    Model;
	Flavour ->
	    case varp_output(Bs#bs.output, user, Partial, Model) of
		{error, no_output} ->
		    varp_formula:print_model(Flavour,I,Partial,Model),
		    Model;
		_ ->
		    Model
	    end
    end.

output_model_header(Bs,Partial,_I) ->
    case get(output_model_header) of
	false ->
	    ok;  %% already outputed or ignored
	_ ->
	    put(output_model_header, false),
	    if Partial -> io:format("PARTIAL\n");
	       true ->
		    case varp_formula:getopt(Bs,starexec) of
			true ->
			    put(exit_code, 10),
			    io:format("s SATISFIABLE\n");
			false ->
			    ok
		    end
	    end
    end.

%% fixme analyze the path to see if there are 
%% archive tar/tar.gz/tgz/zip components in the path
%% in such case open the archive and extract the file
%% as binary

-spec archive_path(FileName::string()) ->
			  {file,DirName::string(),FileName::string()} |
			  {archive,Type::gz|zip,Archive::string(),
			   File::string()} |
			  {error,term()}.

archive_path(FileName) ->
    case archive_path_(filename:split(FileName)) of
	{file,Ps1,F} ->
	    {file,fjoin(Ps1),F};
	{archive,Type,Ps1,Fs} ->
	    {archive,Type,fjoin(Ps1),fjoin(Fs)};
	{error,_}=Error -> Error
    end.
     
archive_path_([F]) ->
    {file,[],F};
archive_path_([D|Ds]) ->
    case filelib:is_dir(D) of
	true ->
	    archive_path_(Ds, D);
	false ->
	    case archive_type(D) of
		undefined ->
		    archive_path_(Ds, D);
		Type ->
		    {archive,Type,[D],Ds}
	    end
    end.

archive_path_(Ds, D) ->
    case archive_path_(Ds) of
	{archive,Type,Ds1,Fs} ->
	    {archive,Type,[D|Ds1],Fs};
	{file,Ds1,F} -> 
	    {file,[D|Ds1],F};
	Error={error,_} -> Error
    end.

archive_type(FileName) ->
    archive_type(FileName, [{".tar.gz", tgz},
			    {".tgz",    tgz},
			    {".tar",    tar},
			    {".zip",    zip}]).

archive_type(FileName, [{Sfx,Type}|L]) ->
    case lists:suffix(Sfx, FileName) of
	true -> Type;
	false -> archive_type(FileName, L)
    end;
archive_type(_FileName, []) ->
    undefined.

fjoin([]) -> "";
fjoin(Fs) -> filename:join(Fs).


%% load/parse formulas given on command line like -f "A && B"
load_formulas([], A, _JoinOp, _GOpts) ->
    {ok,{empty_sections(),A}};
load_formulas(Fs, A, JoinOp, GOpts) ->
    parse_formulas(Fs,A,empty_sections(),JoinOp,GOpts).

parse_formulas([F|Fs], Formula, Sections0,JoinOp,GOpts) ->
    case parse("*command-line*", F, GOpts) of
	{ok,{Sections1,Formula1}} ->
	    parse_formulas(Fs, join_f(JoinOp, Formula, Formula1),
			   append_sections(Sections0, Sections1),
			   JoinOp,GOpts);
	Error ->
	    Error
    end;
parse_formulas([], Formula, Sections, _JoinOp,_GOpts) ->
    {ok,{Sections,Formula}}.

empty_sections() ->
    #{ decls=>#{}, literals=> #{}, syms => #{}, defs=>#{},
       order=>[],  assert=>[], input=>[], output=>[] }.

append_sections(#{ decls:=D0,order:=O0,literals:=Ls0,defs:=Ds0,
		   assert:=A0,input:=I0, output:=T0,syms:=S0 },
		#{ decls:=D1,order:=O1,literals:=Ls1,defs:=Ds1,
		   assert:=A1,input:=I1, output:=T1,syms:=S1 }) ->
    #{ decls =>maps:merge(D0,D1),  %% must be fixed!
       order => O0++O1, 
       literals =>maps:merge(Ls0,Ls1),
       defs => merge_defs(Ds0, Ds1),
       assert => A0++A1,
       input => I0++I1,
       output => T0++T1,
       syms => maps:merge(S0,S1)  %% fix?
     }.

section_opts(#{ decls := Decls,
		order := Order,
		literals := Literals,
		defs := Defs,
		assert := Assert,
		input := Input,
		output := Output,
		syms := Syms },
	     GOpts) ->
    GOpts#{
	   order => order_decl(Order),
	   decls => Decls,
	   defs => Defs,
	   literals => Literals,
	   assert => Assert,
	   input => Input,
	   output => Output,
	   syms => Syms
	  }.

merge_defs(Ds0, Ds1) ->
    maps:fold(
      fun(Key,DefList1,Ds00) ->
	      DefList0 = maps:get(Key,Ds00,[]),
	      maps:put(Key,DefList0++DefList1,Ds00)
      end, Ds0, Ds1).
    
join_f(_JoinOp,undefined,B) -> B;
join_f(_JoinOp,A,undefined) -> A;
join_f(JoinOp,A,B) -> {JoinOp,A,B}.

process_args(As=[[$-|_]|_], Plugins, Do, Files, GOptSpec, GOpts, Bound) ->
    {As1,GOpts1,Bound1} = 
	varp_option:process_args(As, GOptSpec, GOpts, Bound),
    process_args(As1,Plugins,Do,Files,GOptSpec,GOpts1,Bound1);    
process_args([Arg|As], Plugins, Do, Files, GOptSpec, GOpts, Bound) ->
    case maps:get(Arg, Plugins, undefined) of
	undefined ->
	    process_args(As,Plugins,Do,[Arg|Files],GOptSpec,GOpts,Bound);
	Mod ->
	    OptionInfoList = Mod:options(),
	    OptionSpec = varp_option:options_spec(OptionInfoList),
	    OptMap = varp_option:default_opts(OptionInfoList),
	    {As1,OptMap1,Bound1} = 
		varp_option:process_args(As, OptionSpec, OptMap, Bound),
	    process_args(As1, Plugins, [{Mod, OptMap1}|Do], Files,
			 GOptSpec,GOpts,Bound1)
    end;
process_args([], _Plugins, Do, Files,_GOptSpec,GOpts,Bound) ->
    {lists:reverse(Do), lists:reverse(Files), GOpts, Bound}.


read_in() ->
    collect_in([]).

collect_in(Acc) ->
    case io:get_line('') of
	eof -> 
	    {ok,list_to_binary(lists:reverse(Acc))};
	Line ->
	    collect_in([Line|Acc])
    end.

file(File) ->
    case read_file(File) of
	{ok,Binary} ->
	    parse(File,Binary);
	Error={error,Reason} ->
	    io:format("Unable to read file ~s (~w)\n",
		      [File, Reason]),
	    Error
    end.

scan_file(File) ->
    case read_file(File) of
	{ok,Binary} ->    
	    tokens(binary_to_list(Binary));
	Error={error,Reason} ->
	    io:format("Unable to read file ~s (~w)\n",
		      [File, Reason]),
	    Error
    end.

%% Archive aware file:read
read_file(FileName) ->
    case archive_path(FileName) of
	{file,"",File} -> file:read_file(File);
	{file,Dir,File} -> file:read_file(filename:join(Dir,File));
	{archive,tgz,ArchiveFile,File} ->
	    case file:open(ArchiveFile,[read,compressed,raw,binary]) of
		{ok,Fd} ->
		    case erl_tar:extract({file,Fd},[{files,[File]},memory]) of
			{ok,[{File,Bin}]} ->
			    file:close(Fd),
			    {ok,Bin};
			Error ->
			    Error
		    end;
		Error -> Error
	    end;
	{archive,tar,ArchiveFile,File} ->
	    case file:open(ArchiveFile,[read,binary,raw]) of
		{ok,Fd} ->
		    case erl_tar:extract({file,Fd},[{files,[File]},memory]) of
			{ok,[{File,Bin}]} ->
			    file:close(Fd),
			    {ok,Bin};
			Error ->
			    Error
		    end;
		Error -> Error
	    end;
	{archive,zip,ArchiveFile,File} ->
	    case zip:extract(ArchiveFile,[{file_list,[File]},memory]) of
		{ok,[{File,Bin}]} ->
		    {ok,Bin};
		Error ->
		    Error
	    end
    end.

%% extract member names from archive file
archive_file_list(ArchiveType,ArchiveFile) ->
    case ArchiveType of
	tgz ->
	    case file:open(ArchiveFile,[read,binary,compressed,raw]) of
		{ok,Fd} ->
		    Res = erl_tar:table({file,Fd}),
		    file:close(Fd),
		    Res;
		Error -> Error
	    end;
	tar ->
	    case file:open(ArchiveFile,[read,binary,raw]) of
		{ok,Fd} ->
		    Res = erl_tar:table({file,Fd}),
		    file:close(Fd),
		    Res;
		Error -> Error
	    end;
	zip ->
	    case zip:table(ArchiveFile) of
		{ok,List} ->
		    {ok,zip_names(List)};
		Error ->
		    Error
	    end
    end.

zip_names([#zip_comment{}|L]) -> zip_names(L);
zip_names([#zip_file{name=Name}|L]) ->
    [Name|zip_names(L)];
zip_names([]) ->
    [].

parse(String) ->
    parse("*internal*", String).

parse(File, String) ->
    parse(File, String, #{}).

parse(File, Binary, GOpts) when is_binary(Binary) ->
    parse(File, binary_to_list(Binary), GOpts);    
parse(File, String, GOpts) ->
    case tokens(String) of
	{ok,Ts} ->
	    case varp_parse:parse(Ts) of
		{ok,{Sections,Formula}} ->
		    case split_sections(Sections,GOpts) of
			{ok, SectionMap} ->
			    {ok,{SectionMap,Formula}};
			Error ->
			    io:format("~s: Error: ~p\n", [File,Error]),
			    Error
		    end;
		Error={error,{Ln,Mod,Why}} when 
		      is_integer(Ln), is_atom(Mod) ->
		    Reason = Mod:format_error(Why),
		    io:format("~s:~w: ~s\n", [File,Ln,Reason]),
		    Error;
		Error ->
		    io:format("~s: Error: ~p\n", [File,Error]),
		    Error
	    end;
	Error ->
	    io:format("~s: Error: ~p\n", [File, Error]),
	    Error
    end.

split_sections(Sections) ->
    split_sections(Sections,#{}).

split_sections(Sections,GOpts) ->
    split_sections(Sections,empty_sections(),GOpts).

split_sections([{declare,DeclList}|Sections], Map=#{ decls:=Decl0 },GOpts) ->
    Bs = #bs { meta = maps:get(meta,GOpts,#{}) },  %% dummy bs
    case add_decls(DeclList, Decl0, Bs) of
	{ok,Decls1} ->
	    split_sections(Sections, Map#{ decls => Decls1 },GOpts);
	Error ->
	    Error
    end;
split_sections([{order,Order}|Sections],Map=#{ order:=Order0 },GOpts) ->
    split_sections(Sections, Map#{ order => Order0++Order },GOpts);
split_sections([{literals,Ls}|Sections],Map=#{ literals:=Ls0 },GOpts) ->
    Ls1 = maps:from_list([{L,true} || L <- Ls]),
    Ls2 = maps:merge(Ls1,Ls0),
    split_sections(Sections, Map#{ literals => Ls2 },GOpts);
split_sections([{define,{p,P,Ps},Expr}|Sections], Map=#{ defs:=Defs0 },GOpts) ->
    PSym = {P,length(Ps)},
    DefList = maps:get(PSym, Defs0, []),
    Defs1 = maps:put(PSym,DefList++[{Ps,Expr}],Defs0),
    split_sections(Sections, Map#{ defs => Defs1 },GOpts);
split_sections([{assert,Expr}|Sections], Map=#{ assert:=Assert0 },GOpts) ->
    split_sections(Sections, Map#{ assert => Assert0++[Expr] },GOpts);
split_sections([{input,Name}|Sections], Map=#{ input:=Input0 },GOpts) ->
    split_sections(Sections, Map#{ input => Input0++[Name] },GOpts);
split_sections([{output,Name}|Sections], Map=#{ output:=Output0 },GOpts) ->
    split_sections(Sections, Map#{ output => Output0++[Name] },GOpts);
split_sections([], Map, _GOpts) ->
    {ok, Map}.

-ifdef(PSYM_ARITY).
make_psym(Sym,Args) -> {Sym,length(Args)}.
-else.
make_psym(Sym,_Args) -> Sym.
-endif.

add_decls([{{p,Sym,Args},PType,SExpr}|Ds], Decls, Bs) ->
    Size = varp_formula:eval_meta(SExpr, Bs),
    PSym = make_psym(Sym,Args),
    case maps:find(PSym, Decls) of
	error ->
	    Decls1 = maps:put(PSym, {PType,length(Args),Size}, Decls),
	    add_decls(Ds, Decls1, Bs);
	{ok,_} ->
	    {error, {symbol, Sym, already_declared}}
    end;
add_decls([], Decls, _Bs) ->
    {ok,Decls}.
    
string(Binary) when is_binary(Binary) ->
    string(binary_to_list(Binary));
string(String) when is_list(String) ->
    {ok,Ts} = tokens(String),
    varp_parse:parse(Ts).

tokens(String) ->
    case varp_scan:string(remove_comments(String)) of
	{ok,Ts,_Ln} -> {ok,Ts};
	Error -> Error
    end.

%% remove C-style comments from data
remove_comments([$/,$/|Cs]) -> remove_comments(remove_line(Cs));
remove_comments([$/,$*|Cs]) -> remove_comments(remove_block(Cs));
remove_comments([C|Cs]) -> [C|remove_comments(Cs)];
remove_comments([]) -> [].

%% remove until */ but keep all \n
remove_block([$*,$/|Cs]) -> Cs;
remove_block([$\n|Cs]) -> [$\n|remove_block(Cs)];
remove_block([_|Cs]) -> remove_block(Cs);
remove_block([]) -> [].

%% remove until end-of-line (but keep it)
remove_line(Cs=[$\n|_]) -> Cs;
remove_line([_|Cs]) -> remove_line(Cs);
remove_line([]) -> [].

set_local_timeout(Bs, Timeout) when is_number(Timeout), Timeout > 0 ->
    TRef = erlang:start_timer(trunc(1000*Timeout), undefined, ok),
    Bs#bs { t_local = TRef };
set_local_timeout(Bs, infinity) ->
    Bs#bs { t_local = undefined }.

set_global_timeout(Bs, Timeout) when is_number(Timeout), Timeout > 0 ->
    TRef = erlang:start_timer(trunc(1000*Timeout), undefined, ok),
    Bs#bs { t_global = TRef };
set_global_timeout(Bs, infinity) ->
    Bs#bs { t_global = undefined }.

%% FIXME: read_timer + receive may be fast than
%%  calling monotonic_time + couters:get !?

check_timeout_or_cancel(Bs, Counter, CheckInterval) ->
    Time1 = erlang:monotonic_time(millisecond),
    Time0 = counters:get(Bs#bs.counters, Counter),
    if Time0 =:= 0 ->
	    counters:put(Bs#bs.counters,Counter,Time1),
	    false;
       Time1 - Time0 >= CheckInterval ->
	    counters:put(Bs#bs.counters,Counter,Time1),
	    is_timeout_or_was_canceled(Bs);
       true ->
	    false
    end.

is_timeout_or_was_canceled(Bs) ->
    Canceled = was_canceled(),
    case is_timeout(Bs) of
	true ->
	    {true,?TIMEOUT};
	false ->
	    if Canceled ->
		    {true,?CANCEL};
	       true ->
		    false
	    end
    end.

was_canceled() ->
    receive
	{cancel,_From} ->
	    true
    after 0 ->
	    false
    end.
	    

is_timeout(Bs) ->
    is_local_timeout(Bs) orelse is_global_timeout(Bs).

is_local_timeout(Bs) ->
    case read_timer(Bs#bs.t_local) of
	0 -> true;
	_T -> 
	    %% io:format("local_time=~w\n", [_T]),
	    false
    end.

is_global_timeout(Bs) ->
    case read_timer(Bs#bs.t_global) of
	0 -> true;
	_T ->
	    %% io:format("global_time=~w\n", [_T]),
	    false
    end.

read_timer(undefined) -> 
    infinity;
read_timer(TRef) when is_reference(TRef) ->
    case erlang:read_timer(TRef) of
	false -> 0;
	Remain -> Remain
    end.

%% This is the negation of the decision variables blocking the
%% current model.
block_clause(Bs) ->
    Level = varc:info(Bs#bs.vp, level),
    block_clause_(Bs, Level, []).

block_clause_(_Bs, 0, Clause) ->
    Clause;
block_clause_(Bs, Level, Clause) ->
    Xi = varc:get_decision(Bs#bs.vp, Level),
    block_clause_(Bs, Level-1, [-Xi|Clause]).

%% Decision clause, use for proof output
decision_clause(Bs) ->
    Level = varc:info(Bs#bs.vp, level),
    decision_clause(Bs, Level).

decision_clause(_Bs, 0) ->
    [];
decision_clause(Bs, Level) ->
    case varc:get_undo_state(Bs#bs.vp, Level) of
	done -> decision_clause(Bs,Level-1);
	undefined -> error(bad_level);
	_ -> %% set or toggle
	    Xi = varc:get_decision(Bs#bs.vp, Level),
	    [-Xi|decision_clause__(Bs,Level-1)]
    end.

decision_clause__(_Bs, 0) ->
    [];
decision_clause__(Bs, Level) ->
    Xi = varc:get_decision(Bs#bs.vp, Level),
    [-Xi|decision_clause__(Bs, Level-1)].
