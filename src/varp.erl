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
-export([read_file/1]).
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
-export([clear_local_timeout/1]).
-export([set_global_timeout/2]).
-export([clear_global_timeout/1]).
-export([is_local_timeout/1]).
-export([is_global_timeout/1]).
-export([is_timeout/1]).
-export([is_timeout_or_was_canceled/1]).
-export([check_timeout_or_cancel/3]).
-export([decision_clause/1, decision_clause/2]).
-export([block_clause/1]).
-export([make_psym/2]).
-export([format_error/1]).

%% varp_nif api
-export([new/1]).
-export([clone/1]).
-export([clone/2]).
-export([info/2]).
-export([config/3]).
-export([add_variable/1]).
-export([add_variable/2]).
-export([add_variable/3]).
-export([add_variables/2]).
-export([add_variables/3]).
-export([add_variables/4]).
-export([del_variable/2]).
-export([add_symbol/3]).
-export([del_symbol/2]).
-export([get_symbol/2]).
-export([find_symbol/2]).
-export([first_symbol/1]).
-export([next_symbol/2]).
-export([variable_info/3]).
-export([literal_info/3]).
-export([value/2]).
-export([level/1]).
-export([bound/2]).
-export([bind/2, bind/3]).
-export([decide/2, decide/3]).
-export([subst/3]).
-export([implication_clause/2]).
-export([implication_level/2]).
-export([conflicting_clause/1]).
-export([conflicting_clause/2]).
-export([conflict/3, conflict/4]).
-export([minimize/2, minimize/3]).
-export([is_variable/2]).
-export([is_bound/2]).
-export([is_equal/3]).
-export([isused/2, isused/3]).
-export([isatom/2, isatom/3]).
-export([set_phase/2, get_phase/2]).
-export([push/1]).
-export([pop/1, pop/2]).
-export([undo/1]).
-export([bcp/1, bcp/2, bcp/3]).
-export([nbcp/1]).
-export([vbcp/2, vbcp/3]).
-export([add_clause/2]).
-export([add_clause/3]).
-export([find_clause/2]).
-export([get_clause/2]).
-export([get_clause/3]).
-export([get_clause/4]).
-export([del_clause/2]).
-export([move_clause/3]).
-export([compress_clause/2]).
-export([clean_clause/2]).
-export([get_clauses/2]).
-export([get_clauses/3]).
-export([use_clause/2]).
-export([clause_info/2,clause_info/3]).
-export([get_undo_state/2]).
-export([get_nbindings/2, get_nbindings/3, get_nbindings/4]). 
-export([get_bindings/1, get_bindings/2, get_bindings/3, get_bindings/4]).
-export([get_number_of_bindings/2]).
-export([get_queue/1]).
-export([queue_first/1]).
-export([queue_next/2]).
-export([queue_clear/1]).
-export([get_decision/2]).
-export([order_sort/2, order_sort/3, order_sort/4]).
-export([order_first/2, order_last/2]).
-export([order_first/3, order_last/3]).
-export([next_unbound/1, next_unbound/2]).
-export([bump/3]).
-export([subscribe/2]).
-export([clauseset_size/2]).
-export([clauseset_offset/2, clauseset_offset/3]).
-export([clauseset_sort/2]).
-export([clauseset_first/1, clauseset_first/2]).
-export([clauseset_next/2]).
-export([unmark/1]).
-export([mark/2, mark/3]).
-export([intersect_marks/2]).
-export([intersect_var/4]).
-export([get_marked/2]).

%% variants
-export([new/0]).
-export([memory/0, memory/1]).
-export([version/0]).
-export([i/0]).
-export([i/1]).
-export([info/1]).
-export([info_keys/0]).
-export([variable_info/2, variable_info_keys/0]).
-export([literal_info/2,  literal_info_keys/0]).
-export([get_latest_binding/1]).
-export([get_bindings_list/2, get_bindings_list/3]).
-export([get_bindings_trail/2]).
-export([get_all_bindings/1]).

-export([get_max_clause_length/1]).
-export([get_number_of_variables/1]).
-export([get_number_of_clauses/1]).
-export([get_number_of_dead_clauses/1]).
-export([get_number_of_conflicting_clauses/1]).
-export([get_number_of_bound_variables/1]).
-export([get_number_of_unbound_variables/1]).
-export([get_clause_bcp_counter/1]).
-export([get_clause_bcp_counter/2]).
-export([get_bcp_counter/1]).
-export([get_conflict_counter/1]).

%% utils
-export([vec_create/2, vec_create/3]).
-export([vec_step/2]).
-export([vec_extend/3]).
-export([vec_extend_rand/3]).
-export([vec_extend_friend/4]).
-export([vec_is_bound/2]).
-export([vec_value/2]).
-export([vec_bind/2]).
-export([vtl/3]).
-export([intersect/1, intersect/2]).
-export([install_bindings/2, install_bindings/3]).
-export([vec_sat/2, vec_sat/5, vec_sat/6, vec_sat/7]).
-export([vec_sat_lap/5]).

-export([get_marked/1]).
-export([intersect_var/3]).
-export([intersect_var0/4]).
-export([make_friend_map/1]).
-export([order_all/1, phase_all/1]).

-define(BINDING_AS_TUPLE, true).

-include_lib("stdlib/include/zip.hrl").

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
	spec => {enum,[{"undefined",undefined},{"u",undefined},
		       {"true", true},{"1",true},
		       {"false",false},{"0",false}]},
	default => true,
	description => "Inital phase selection."
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
	 default => 0,
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
     #{ long => "statistics",
	key => statistics,
	spec =>  {enum,[?BOOL]},
	default => false,
	description => "Show counter statistics"
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
    application:ensure_all_started(varp),
    Plugins = load_plugins(),
    GlobalOptionSpec = global_option_spec(),
    GOpts0 = default_options(),
    GOpts1 = load_options(GlobalOptionSpec, GOpts0),
    Do0 = load_do(Plugins),
    {Do1,Files,GOpts2,Bound0} =
	process_args(Args, Plugins, [], [], GlobalOptionSpec, GOpts1, []),
    Bound = maps:from_list(Bound0),
    Do = if Do1 =/= [] -> Do1;
	    true -> Do0
	 end,
    {ReadIn,{Sections0,Formula0}} =
	try load_formulas(maps:get(formula,GOpts2,[]), undefined, 'and',
			  GOpts2) of
	    {ok,{S0,undefined}}-> {true,{S0,undefined}};
	    {ok,R0} -> {false,R0}
	catch
	    ?EXCEPTION(error,Error0,Trace0) ->
		io:format("~s\n", [format_error(Error0)]),
		io:format("~p\n", [?GET_STACK(Trace0)]),
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
			?EXCEPTION(error,Error1,Trace1) ->
			    io:format("~s\n", [format_error(Error1)]),
			    io:format("~p\n", [?GET_STACK(Trace1)]),
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
			?EXCEPTION(error,Error2,Trace2) ->
			    io:format("~s\n", [format_error(Error2)]),
			    io:format("~p\n", [?GET_STACK(Trace2)]),
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
		?EXCEPTION(error,Error3,Trace3) ->
		    io:format("~s\n", [format_error(Error3)]),
		    io:format("~p\n", [?GET_STACK(Trace3)]),
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
			  try varp_option:setopt(Key,Value,Mi,OptionSpec) of
			      Mj -> Mj
			  catch
			      error:badkey ->
				  io:format("unknown key ~w\n", [Key]),
				  Mi;
			      error:badarg ->
				  io:format("unsupported value ~w for key ~w\n",
					    [Value, Key]),
				  Mi
			  end
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
    varp_monitor:stop(), %% if started
    case R of
	{'EXIT',{Error, _Where}} ->
	    io:format("~s\n", [format_error(Error)]),
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
    ?info(Bs0#bs.option, "pass ~p\n", [build]),
    {Main,Bs} = case varp_formula:build(Formula,Bs0) of
		    {{bool,Var0},Bs0_1} -> {Var0,Bs0_1};
		    {{uint,1,[Var0]},Bs0_1} -> {Var0,Bs0_1};
		    {undefined,Bs0_1} -> {undefined,Bs0_1}; %% validate etc
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
    ?info(Bs#bs.option, "pass ~p\n", [Plugin]),
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
	?EXCEPTION(error, Reason, Trace) ->
	    io:format("~s crashed ~p\n", [Plugin, Reason]),
	    io:format("~p\n", [?GET_STACK(Trace)]),
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
    ?info(Bs#bs.option, "    | bcp: ~w\n    | clause:n:~w,2:~w,3:~w,d:~w\n    | #clauses:~w, #dead:~w, #conflict:~w\n | time=~.2fs\n",
		      [S1#stat.bcp_count-S0#stat.bcp_count,
		       S1#stat.clause_n_counter - S0#stat.clause_n_counter,
		       S1#stat.clause_2_counter - S0#stat.clause_2_counter,
		       S1#stat.clause_3_counter - S0#stat.clause_3_counter,
		       S1#stat.clause_d_counter - S0#stat.clause_d_counter,
		       S1#stat.clauses,
		       S1#stat.dead_clauses,
		       S1#stat.conflict_count-S0#stat.conflict_count,
		       Ts]),
    ?info(Bs#bs.option,"    | bound: ~w [~w/~w]\n",
	  [S1#stat.bound-S0#stat.bound,
	   S1#stat.bound,
	   get_number_of_variables(Bs#bs.vp)
	  ]).

stat(#bs{vp=Vp}) ->
    #stat { clause_n_counter = get_clause_bcp_counter(Vp,n),
	    clause_2_counter = get_clause_bcp_counter(Vp,2),
	    clause_3_counter = get_clause_bcp_counter(Vp,3),
	    clause_d_counter = get_clause_bcp_counter(Vp,dead),
	    bcp_count        = get_bcp_counter(Vp),
	    conflict_count   = get_conflict_counter(Vp),
	    bound            = get_number_of_bound_variables(Vp),
	    clauses          = get_number_of_clauses(Vp),
	    dead_clauses     = get_number_of_dead_clauses(Vp)
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
    NV = get_number_of_variables(Bs#bs.vp),
    NB = get_number_of_bound_variables(Bs#bs.vp),
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

order_decl([Key1,Key2|Vs],Opts) when is_atom(Key1), is_atom(Key2) ->
    order_decl(Vs,[{order,[Key1,Key2]}|Opts]);
order_decl([Key1|Vs],Opts) when is_atom(Key1) ->
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

clear_local_timeout(Bs) ->
    Bs#bs { t_local = undefined }.

set_local_timeout(Bs, Timeout) when is_number(Timeout), Timeout > 0 ->
    TRef = erlang:start_timer(trunc(1000*Timeout), undefined, ok),
    Bs#bs { t_local = TRef };
set_local_timeout(Bs, infinity) ->
    Bs#bs { t_local = undefined }.

clear_global_timeout(Bs) ->
    Bs#bs { t_global = undefined }.

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
    Level = varp_nif:level(Bs#bs.vp),
    block_clause_(Bs, Level, []).

block_clause_(_Bs, 0, Clause) ->
    Clause;
block_clause_(Bs, Level, Clause) ->
    Xi = varp_nif:get_decision(Bs#bs.vp, Level),
    block_clause_(Bs, Level-1, [-Xi|Clause]).

%% Decision clause, use for proof output
decision_clause(Bs) ->
    Level = varp_nif:level(Bs#bs.vp),
    decision_clause(Bs, Level).

decision_clause(_Bs, 0) ->
    [];
decision_clause(Bs, Level) ->
    case varp_nif:get_undo_state(Bs#bs.vp, Level) of
	done -> decision_clause(Bs,Level-1);
	undefined -> error(bad_level);
	_ -> %% set or toggle
	    Xi = varp_nif:get_decision(Bs#bs.vp, Level),
	    [-Xi|decision_clause__(Bs,Level-1)]
    end.

decision_clause__(_Bs, 0) ->
    [];
decision_clause__(Bs, Level) ->
    Xi = varp_nif:get_decision(Bs#bs.vp, Level),
    [-Xi|decision_clause__(Bs, Level-1)].

%% nif calls and lowlevel utils
variable_info(Vp, Index) ->
    [{What,varp_nif:variable_info(Vp, Index, What)} || 
	What <-variable_info_keys()].

variable_info_keys() ->
    [implication, implication_clause,
     level, phase, degree, is_atom, is_used, symbol].

literal_info(Vp,Index) ->
    [{What,varp_nif:literal_info(Vp,Index,What)} ||
	What <- literal_info_keys()].

literal_info_keys() ->
    [mark, inqueue, degree, user, xref, symbol].

%% VARP_NIF wrapper

new(Options) -> varp_nif:new(Options).
clone(Vp,Opts) -> varp_nif:clone(Vp,Opts).
info(Vp, Key) -> varp_nif:info(Vp, Key).
config(Vp,Item,Value) -> varp_nif:config(Vp,Item,Value).
add_variable(Vp) -> varp_nif:add_variable(Vp).
add_variable(Vp,IsAtom) -> varp_nif:add_variable(Vp,IsAtom).
add_variable(Vp,IsAtom,IsUsed) -> varp_nif:add_variable(Vp,IsAtom,IsUsed).
add_variables(Vp,Num) -> varp_nif:add_variables(Vp,Num).
add_variables(Vp,Num,IsAtom) -> varp_nif:add_variables(Vp,Num,IsAtom).
add_variables(Vp,Num,IsAtom,IsUsed) -> varp_nif:add_variables(Vp,Num,IsAtom,IsUsed).
del_variable(Vp, Index) -> varp_nif:del_variable(Vp, Index).
add_symbol(Vp,Lit, Name) -> varp_nif:add_symbol(Vp,Lit, Name).
del_symbol(Vp,Name) -> varp_nif:del_symbol(Vp,Name).
get_symbol(Vp,Lit) -> varp_nif:get_symbol(Vp,Lit).
find_symbol(Vp,Name) -> varp_nif:find_symbol(Vp,Name).
first_symbol(Vp) -> varp_nif:first_symbol(Vp).
next_symbol(Vp,Symbol) -> varp_nif:next_symbol(Vp,Symbol).
variable_info(Vp,Index,What) -> varp_nif:variable_info(Vp,Index,What).
literal_info(Vp,Index,What) -> varp_nif:literal_info(Vp,Index,What).
level(Vp) -> varp_nif:level(Vp).
value(Vp,Lit) -> varp_nif:value(Vp,Lit).
bound(Vp,Lit) -> varp_nif:bound(Vp,Lit).
bind(Vp, X) -> varp_nif:bind(Vp, X).
bind(Vp,X,Level) -> varp_nif:bind(Vp,X,Level).
decide(Vp,X) -> varp_nif:decide(Vp,X).
decide(Vp,X,Level) -> varp_nif:decide(Vp,X,Level).
subst(Vp,X,Y) -> varp_nif:subst(Vp,X,Y).
implication_clause(Vp,Lit) -> varp_nif:implication_clause(Vp,Lit).
implication_level(Vp,Lit) -> varp_nif:implication_level(Vp,Lit).
conflicting_clause(Vp) -> varp_nif:conflicting_clause(Vp).
conflicting_clause(Vp,Index) -> varp_nif:conflicting_clause(Vp,Index).
conflict(Vp,Bump,IndexOrClause) -> varp_nif:conflict(Vp,Bump,IndexOrClause).
conflict(Vp,Bump,IndexOrClause,UnitLiteral) ->
    varp_nif:conflict(Vp,Bump,IndexOrClause,UnitLiteral).
minimize(Vp,CluseIndex) -> varp_nif:minimize(Vp,CluseIndex).
minimize(Vp,CluseIndex,Style) -> varp_nif:minimize(Vp,CluseIndex,Style).
is_variable(Vp,Lit) -> varp_nif:is_variable(Vp,Lit).
is_bound(Vp,Lit) -> varp_nif:is_bound(Vp,Lit).
is_equal(Vp,LitA,LitB) -> varp_nif:is_equal(Vp,LitA,LitB).
isused(Vp,Var) -> varp_nif:isused(Vp,Var).
isused(Vp,Var,Status) -> varp_nif:isused(Vp,Var,Status).
isatom(Vp,Var) -> varp_nif:isatom(Vp,Var).
isatom(Vp,Var,Status) -> varp_nif:isatom(Vp,Var,Status).
set_phase(Vp, Lit) -> varp_nif:set_phase(Vp, Lit).
get_phase(Vp, Var) -> varp_nif:get_phase(Vp, Var).
pop(Vp) -> varp_nif:pop(Vp).
pop(Vp,Level) -> varp_nif:pop(Vp,Level).
push(Vp) -> varp_nif:push(Vp).
undo(Vp) -> varp_nif:undo(Vp).
bcp(Vp) -> varp_nif:bcp(Vp).
bcp(Vp,TurboLiteralList) -> varp_nif:bcp(Vp,TurboLiteralList).
bcp(Vp,TurboLiteralList,TurboAll) -> varp_nif:bcp(Vp,TurboLiteralList,TurboAll).
nbcp(Vp) -> varp_nif:nbcp(Vp).
vbcp(Vp,Xs) -> varp_nif:vbcp(Vp,Xs).
vbcp(Vp,Xs,SingleLevel) -> varp_nif:vbcp(Vp,Xs,SingleLevel).
clauseset_size(Vp, Si) -> varp_nif:clauseset_size(Vp, Si).
add_clause(Vp,Ls) -> varp_nif:add_clause(Vp,Ls).
add_clause(Vp,Ls,Si) -> varp_nif:add_clause(Vp,Ls,Si).
find_clause(Vp,Ls) -> varp_nif:find_clause(Vp,Ls).
get_clause(Vp,Index) -> varp_nif:get_clause(Vp,Index).
get_clause(Vp,Index,Skip) -> varp_nif:get_clause(Vp,Index,Skip).
get_clause(Vp,Index,SkipLiteral,Raw) ->
    varp_nif:get_clause(Vp,Index,SkipLiteral,Raw).
compress_clause(Vp,Index) -> varp_nif:compress_clause(Vp,Index).
use_clause(Vp,Index) -> varp_nif:use_clause(Vp,Index).
bump(Vp,Lit,Bump) -> varp_nif:bump(Vp,Lit,Bump).
subscribe(Vp,Event) -> varp_nif:subscribe(Vp,Event).
clause_info(Vp,Index,What) -> varp_nif:clause_info(Vp,Index,What).
clause_info(Vp,Index) -> varp_nif:clause_info(Vp,Index).
del_clause(Vp,Index) -> varp_nif:del_clause(Vp,Index).
move_clause(Vp,Index,Si) -> varp_nif:move_clause(Vp,Index,Si).
clean_clause(Vp,Index) -> varp_nif:clean_clause(Vp,Index).
get_clauses(Vp,Var,How) -> varp_nif:get_clauses(Vp,Var,How).
queue_first(Vp) -> varp_nif:queue_first(Vp).
queue_next(Vp, Lit) -> varp_nif:queue_next(Vp, Lit).
queue_clear(Vp) -> varp_nif:queue_clear(Vp).
get_decision(Vp, Level) -> varp_nif:get_decision(Vp, Level).
get_undo_state(Vp, Level) -> varp_nif:get_undo_state(Vp, Level).
get_nbindings(Vp,Count) -> varp_nif:get_nbindings(Vp,Count).
get_nbindings(Vp,Count,AsTrail) -> varp_nif:get_nbindings(Vp,Count,AsTrail).
get_nbindings(Vp,Count,AsTrail,AsTuple) -> varp_nif:get_nbindings(Vp,Count,AsTrail,AsTuple).
get_bindings(Vp) -> varp_nif:get_bindings(Vp).
get_bindings(Vp, Level) -> varp_nif:get_bindings(Vp,Level).
get_bindings(Vp, Level, Trail) -> varp_nif:get_bindings(Vp,Level,Trail).
get_bindings(Vp, Level, Trail, AsTuple) -> varp_nif:get_bindings(Vp, Level, Trail, AsTuple).
get_number_of_bindings(Vp, Level) -> varp_nif:get_number_of_bindings(Vp, Level).
order_first(Vp, List) -> varp_nif:order_first(Vp, List).
order_last(Vp, List) -> varp_nif:order_last(Vp, List).
order_first(Vp, List, SetPhase) -> varp_nif:order_first(Vp, List, SetPhase).
order_last(Vp, List, SetPhase) -> varp_nif:order_last(Vp, List, SetPhase).
order_sort(Vp, Key1) -> varp_nif:order_sort(Vp, Key1).
order_sort(Vp, Key1, KeyArg) -> varp_nif:order_sort(Vp, Key1, KeyArg).
order_sort(Vp, Key1, Key2, Arg) -> varp_nif:order_sort(Vp, Key1, Key2, Arg).
clauseset_offset(Vp, Si) -> varp_nif:clauseset_offset(Vp, Si).
clauseset_offset(Vp, Si, Offset) -> varp_nif:clauseset_offset(Vp, Si, Offset).
clauseset_sort(Vp, Si) -> varp_nif:clauseset_sort(Vp, Si).
clauseset_first(Vp, Si) -> varp_nif:clauseset_first(Vp, Si).
clauseset_next(Vp, Ix) -> varp_nif:clauseset_next(Vp, Ix).
next_unbound(Vp) -> varp_nif:next_unbound(Vp).
next_unbound(Vp, Previous) -> varp_nif:next_unbound(Vp, Previous).
unmark(Vp) -> varp_nif:unmark(Vp).
mark(Vp, Bs) -> varp_nif:mark(Vp, Bs).
mark(Vp, Bs, Clear) -> varp_nif:mark(Vp, Bs, Clear).
intersect_marks(Vp, Bs) -> varp_nif:intersect_marks(Vp, Bs).
intersect_var(Vp, _Var, Bs0, AsTuple) -> varp_nif:intersect_var(Vp, _Var, Bs0, AsTuple).
get_marked(Vp, Tuple) -> varp_nif:get_marked(Vp, Tuple).

%% return index to first clause | false
clauseset_first(Vp) ->
    clauseset_first(Vp, ?DELTA).

%% Get all clauses in queue
get_queue(Vp) ->
    case queue_first(Vp) of
	false -> [];
	I ->
	    get_queue_(Vp,I,[I])
    end.

get_queue_(Vp,I,Acc) ->
    case queue_next(Vp,I) of
	false -> lists:reverse(Acc);
	J -> get_queue_(Vp,J,[J|Acc])
    end.

get_clauses(Vp,Var) ->
    get_clauses(Vp,Var,literal).

clone(Vp) ->
    clone(Vp, #{}).

-spec new() -> varp_nif:varp().
	  
new() ->
    varp_nif:new(#{}).

version() ->
    varp_nif:info(new(), version).

i() ->
    Vt = new(),
    _ = [ io:format("~w: ~p\n", [Key,varp_nif:info(Vt, Key)]) || 
	    Key <- 
		[version,
		 literal_size,
		 literal_integer,
		 value_packing,
		 xref,
		 hash,
		 init_phase,
		 use_phase,
		 seed,
		 memory_literal_size,
		 memory_variable_size,
		 memory_clause_size,
		 memory_symbol_size,
		 memory_size
		]],
    ok.

i(Vp) ->
    _ = [ io:format("~w: ~p\n", [Key,varp_nif:info(Vp, Key)]) ||
	    Key <- info_keys()],
    ok.

info(Vp) ->
    [ {Key,varp_nif:info(Vp, Key)} || Key <- info_keys()].

info_keys() ->
    [
     number_of_clauses,
     number_of_dead_clauses,
     number_of_conflicting_clauses,
     number_of_variables,
     number_of_bound_variables,
     number_of_unbound_variables,
     bcp_counter,
     conflict_counter,
     clause_n_counter,
     clause_2_counter,
     clause_3_counter,
     clause_d_counter,
     size,
     level,
     version,
     literal_size,     %% 8,16,32,64 (sizeof literal)
     literal_integer,  %% true,false (integer or pointer)
     value_packing,    %% 1,4,undefined (variable value packing)
     xref,             %% xref is used (need for saturate with substitution)
     hash,             %% hash is used
     init_phase,       %% initial phase value
     use_phase,        %% used saved phase value
     seed,
     memory_literal_size,
     memory_variable_size,
     memory_clause_size,
     memory_symbol_size,
     memory_size
    ].

memory() ->
    memory(new()).

memory(Vp) ->
    Keys = [number_of_variables,
	    number_of_clauses,
	    memory_literal_size,
	    memory_variable_size,
	    memory_clause_size,
	    memory_symbol_size,
	    memory_size],
    [ {Key,varp_nif:info(Vp, Key)} || Key <- Keys].
    

get_number_of_variables(Vp) ->
    varp_nif:info(Vp, number_of_variables).

get_number_of_bound_variables(Vp) ->
    varp_nif:info(Vp, number_of_bound_variables).

get_number_of_unbound_variables(Vp) ->
    varp_nif:info(Vp, number_of_unbound_variables).

get_number_of_clauses(Vp) ->
    varp_nif:info(Vp, number_of_clauses).

get_number_of_dead_clauses(Vp) ->
    varp_nif:info(Vp, number_of_dead_clauses).

get_number_of_conflicting_clauses(Vp) ->
    varp_nif:info(Vp, number_of_conflicting_clauses).

get_max_clause_length(Vp) ->
    varp_nif:info(Vp, max_clause_length).

get_clause_bcp_counter(Vp) ->
    varp_nif:info(Vp, clause_bcp_counter).

get_clause_bcp_counter(Vp,n) ->
    varp_nif:info(Vp, clause_n_counter);
get_clause_bcp_counter(Vp,2) ->
    varp_nif:info(Vp, clause_2_counter);
get_clause_bcp_counter(Vp,3) ->
    varp_nif:info(Vp, clause_3_counter);
get_clause_bcp_counter(Vp,dead) ->
    varp_nif:info(Vp, clause_d_counter).

get_bcp_counter(Vp) ->
    varp_nif:info(Vp, bcp_counter).

get_conflict_counter(Vp) ->
    varp_nif:info(Vp, conflict_counter).

%% get the very latest binding
-spec get_latest_binding(Vp::varp_nif:varp()) ->
	  {Var::integer(),Value::integer()}|false.

get_latest_binding(Vp) ->
    case get_nbindings(Vp,1,false) of
	[B={Var,_Val}|_] when is_integer(Var) -> B;
	_ -> false
    end.

get_all_bindings(V) ->
    Level = varp_nif:level(V),
    [{L,varp_nif:get_decision(V,L),varp_nif:get_bindings(V, L)} ||
	L <- lists:seq(Level,0,-1)].

get_bindings_list(Vp, Level) ->
    varp_nif:get_bindings(Vp, Level, false, false).
get_bindings_list(Vp, Level, Trail) ->
    varp_nif:get_bindings(Vp, Level, Trail, false).

get_bindings_trail(Vp, Level) ->
    varp_nif:get_bindings(Vp, Level, true, false).

%% bcp over vector [X1,X2,...]
%% example X1,X2,X3
%% -X1 -X2 -X3  = E0
%% -X1 -X2  X3  = E1
%% -X1  X2 -X3  = E2
%% -X1  X2  X3  = E3
%%  X1 -X2 -X3  = E4
%%  X1 -X2  X3  = E5
%%  X1  X2 -X3  = E6
%%  X1  X2  X3  = E7
%% 
%%  Y10 = intersect(E0,E1,E2,E3)
%%  Y11 = intersect(E4,E5,E6,E7)
%%
%%  Y20 = intersect(E2,E3,E6,E7)
%%  Y21 = intersect(E0,E1,E4,E5)
%% 
%%  Y30 = intersect(E1,E3,E5,E7)
%%  Y31 = intersect(E0,E2,E4,E6)
%%
%%  intersect_var(X1, Y10, Y11)
%%  intersect_var(X2, Y20, Y21)
%%  intersect_var(X3, Y30, Y31)
%%
vec_sat_lap(V,K,Q,F,R) ->
    case vec_create(V, K) of
	[] -> true;
	Vec0 -> vec_sat_lap_(V,Vec0,Q,F,R)
    end.

%% FIXME? if a vector
%% contain a constant, we should probably update the
%% vector to speed up things (a bit)?
vec_sat_lap_(V,Vec0,Q,F,R) ->
    vec_sat_lap_(V,Vec0,Q,F,R,undefined).

vec_sat_lap_(V,Vec0,Q,F,R,FriendMap) ->
    case vec_sat(V,Vec0,Q,F,R,true,FriendMap) of
	false -> false;
	true ->
	    case vec_step(V, Vec0) of
		false -> true;
		Vec1 -> 
		    vec_sat_lap_(V,Vec1,Q,F,R,FriendMap)
	    end
    end.

vec_sat(V,V0,Q,F,R) ->
    vec_sat(V,V0,Q,F,R,true,undefined).

vec_sat(V,V0,Q,F,R,FriendMap) ->
    vec_sat(V,V0,Q,F,R,true,FriendMap).

vec_sat(V,V0,Q,F,R,Subst,FriendMap) ->
    V1 = vec_extend(V, V0, Q),
    V2 = vec_extend_friend(V, V1, F, FriendMap),
    V3 = vec_extend_rand(V, V2, R),
    ?dbg0("V0=~w, V1=~w, V2=~w, V3=~w\n", [V0,V1,V2,V3]),
    vec_sat(V, V3, Subst).

vec_sat(Vp, Vi) ->
    vec_sat(Vp, Vi, true).

vec_sat(V, Vec, Subst) when is_list(Vec) ->
    0 = varp_nif:push(V),
    Res = satv_(V,list_to_tuple(Vec)),
    varp_nif:pop(V, 0),
    ?dbg0("Vec ~w, Res=~w\n", [Vec, Res]),
    case Res of
	false ->
	    false;
	[] ->
	    true;
	Bs ->
	    case install_bindings0(V, Subst, Bs) of
		true ->
		    varp_nif:bcp(V);
		false ->
		    false
	    end
    end.

satv_(V, Vt) when is_tuple(Vt) ->
    N = tuple_size(Vt),
    Bt = bcpv_(V,(1 bsl N)-1, Vt, []),
    satvar_(V, 0, N, Vt, Bt, []).

%% eval for variable I 
satvar_(V, I, N, Vt, Bt, Bs) when I < N ->
    Vi = element(I+1, Vt),
    ?dbg0("~w: Vi = ~w (Vt=~w)\n", [I,Vi,Vt]),
    Js = lists:seq(0, (1 bsl N)-1),
    B1s = [element(J+1,Bt) || J <- Js, (J band (1 bsl I)) =/= 0],
    B1 = interv(V,B1s),
    ?dbg0("~w/1: ~w => ~w\n", [Vi,B1s,B1]),
    B0s = [element(J+1,Bt) || J <- Js, (J band (1 bsl I)) =:= 0],
    B0 = interv(V,B0s),
    ?dbg0("~w/0: ~w =>  ~w\n", [Vi,B0s,B0]),
    if B0 =:= false, B1 =:= false ->
	    ?dbg0("  B2 = ~w\n", [false]),
	    false;
       B0 =:= false, B1 =:= {} -> 
	    ?dbg0("  B2 = ~w\n", [{}]),
	    satvar_(V, I+1, N, Vt, Bt, Bs);
       B1 =:= false, B0 =:= {} -> 
	    ?dbg0("  B2 = ~w\n", [{}]),
	    satvar_(V, I+1, N, Vt, Bt, Bs);
       B0 =:= false ->
	    ?dbg0("  B2 = ~w\n", [B1]),
	    satvar_(V, I+1, N, Vt, Bt, [B1|Bs]);
       B1 =:= false ->
	    ?dbg0("  B2 = ~w\n", [B0]),
	    satvar_(V, I+1, N, Vt, Bt, [B0|Bs]);
       true ->
	    case intersect_bindings(V, Vi, B0, B1) of
		{} ->
		    ?dbg0("  B2 = ~w\n", [{}]),
		    satvar_(V, I+1, N, Vt, Bt, Bs);
		B2 ->
		    ?dbg0("  B2 = ~w\n", [B2]),
		    satvar_(V, I+1, N, Vt, Bt, [B2|Bs])
	    end
    end;
satvar_(_V, N, N, _Vt, _Bt, Bs) ->
    Bs.

%% interv0(_V, As) ->
%%    intersect(As).

interv(_V, []) -> false;
interv(V, [false|As]) -> interv(V, As);
interv(V, [A|As]) -> varp_nif:mark(V, A), interv_(V, As).

interv_(V, [false|As]) -> interv_(V, As);
interv_(V, [A|As]) -> varp_nif:intersect_marks(V, A), interv_(V, As);
interv_(V, []) -> varp_nif:get_marked(V, true).


bcpv_(_V,-1, _Vt, Acc) ->
    list_to_tuple(Acc);
bcpv_(V,I, Vt, Acc) ->
    Vec = vtl(V, I, Vt),
    ?dbg0("bcpv: ~w\n", [Vec]),
    L = varp_nif:push(V),
    case varp_nif:vbcp(V, Vec) of
	true ->
	    Ei = bcpv_bindings(V, L+1),
	    varp_nif:pop(V, L),
	    bcpv_(V,I-1, Vt, [Ei|Acc]);
	{_J,Lj} -> %% Vec[J]=Lj is inconsistent
	    %% io:format("~w: level=~w\n", [L, varp_nif:level(V)]),
	    varp_nif:pop(V, L),
	    bcpv_(V, I-1, Vt, [false|Acc]);
	    %% case varp_nif:implication_clause(V, -Lj) of
	    %% -1 ->  %% Probably a unit
	    %% varp_nif:pop(V, L),
	    %% bcpv_(V, I-1, Vt, [false|Acc]);
	    %% CCix ->
	    %% 		    bcpv_vconflict(V,L,CCix,Lj,I-1,Vt,[false|Acc])
	    %% end;
	false ->  %% Last eval is contradictory
	    %% varp_nif:pop(V, L),
	    %% bcpv_(V, I-1, Vt, [false|Acc])
	    %% FIX: optional learn option!
	    bcpv_conflict(V,L,I-1, Vt, [false|Acc])
    end.

bcpv_conflict(Vp, L, I, Vt, Acc) ->
    case varp_conflict:analyze(Vp, 0, local) of
	[{1,_Count,Aix}|_] ->
	    ?dbg0("UNIT=~w\n", [varp_nif:get_clause(Vp, Aix)]),
	    varp_nif:pop(Vp, L),
	    true = varp_nif:move_clause(Vp, Aix, gamma),
	    case varp_nif:bcp(Vp) of
		true ->
		    bcpv_(Vp,I, Vt, Acc);
		false ->
		    L1 = varp_nif:push(Vp),
		    bcpv_conflict(Vp, L1, I, Vt, Acc)
	    end;
	[{_Len,_Count,Aix}|_] ->
	    ?dbg1("LEARN=~w\n", [varp_nif:get_clause(Vp, Aix)]),
	    varp_nif:pop(Vp, L),
	    {true,_Gix} = varp_nif:move_clause(Vp, Aix, gamma),
	    bcpv_(Vp, I, Vt, Acc);
	[] ->
	    varp_nif:pop(Vp, L),
	    bcpv_(Vp,I,Vt,Acc)
    end.


bcpv_vconflict(V,L,CCix,Lj,I,Vt,Acc) ->
    ?dbg1("CCix=~w, Lj=~w\n", [CCix, Lj]),
    ?dbg1("~w=>~s\n", [-Lj,format_clause(V,CCix)]),
    %% Bump?
    case varp_nif:conflict(V, 0, CCix, -Lj) of
	undefined ->  %% duplicate
	    varp_nif:pop(V, L),
	    bcpv_(V, I, Vt, Acc);
	Aix when is_integer(Aix) ->
	    Len0 = varp_nif:clause_info(V, Aix, length),
	    io:format("CLAUSE[~w]=~w\n", [Len0,varp_nif:get_clause(V, Aix)]),
	    case varp_nif:minimize(V, Aix, local) of
		undefined -> %% duplicate
		    ?dbg0("DUPLICATE\n", []),
		    bcpv_(V, I, Vt, Acc);
		1 ->
		    ?dbg0("UNIT ~w\n", [varp_nif:get_clause(V, Aix)]),
		    varp_nif:pop(V, L),
		    true = varp_nif:move_clause(V, Aix, gamma),
		    true = varp_nif:bcp(V),
		    bcpv_(V,I, Vt, Acc);
		Len ->
		    ?dbg1("Removed: ~w\n,", [Len0-Len]),
		    %% io:format("LEARN=~w\n", [varp_nif:get_clause(V, Aix)]),
		    varp_nif:pop(V, L),
		    {true,_Gix} = varp_nif:move_clause(V,Aix,gamma),
		    bcpv_(V, I, Vt, Acc)
	    end
    end.

%% Get bindings on all levels, assume a decision
%% is present on (almost) all levels.
bcpv_bindings(V, L) ->
    bcpv_bindings_(V, L, varp_nif:level(V), []).

bcpv_bindings_(V, L, Lmax, Acc) when L =< Lmax ->
    %% ????
    case varp_nif:get_bindings(V, L, false, _AsTuple=false) of
	[] ->
	    bcpv_bindings_(V, L+1, Lmax, Acc);
	[_Decide|Bs] ->
	    %% io:format("Bs = ~w\n", [Bs]),
	    bcpv_bindings_(V, L+1, Lmax, [Bs|Acc])
    end;
bcpv_bindings_(_V, _L, _Lmax, Acc) ->
    lists:append(lists:reverse(Acc)).

%% format clause as [~w/0, ~w/1 ~w]
format_clause(V, Cix) when is_integer(Cix) ->
    format_clause(V, get_clause(V, Cix, undefined,true));
format_clause(V, [A|As]) ->
    ["[", format_lit(V,A), format_clause1(V, As), "]"].

format_clause1(V, As) ->
    [[",", format_lit(V, Ai)] || Ai <- As].

format_lit(V, A) ->
    case varp_nif:value(V, A) of
	false -> io_lib:format("~w/0", [A]);
	true -> io_lib:format("~w/1", [A]);
	undefined -> io_lib:format("~w", [A])
    end.

%% eval all 2^N combinations of Vt
%% bcpv_(_V,-1, _Vt, Acc) ->
%%     list_to_tuple(Acc);
%% bcpv_(V,I, Vt, Acc) ->
%%     varp_nif:push(V),
%%     case bindv(V, I, Vt) of
%% 	false ->
%% 	    varp_nif:queue_clear(V),
%% 	    varp_nif:pop(V),
%% 	    bcpv_(V,I-1, Vt, [false|Acc]);
%% 	true ->
%% 	    L = varp_nif:push(V),
%% 	    Ei = case varp_nif:bcp(V) of
%% 		     false -> false;
%% 		     true -> varp_nif:get_bindings(V, L+1)
%% 		 end,
%% 	    varp_nif:pop(V),
%% 	    varp_nif:pop(V),
%% 	    bcpv_(V,I-1, Vt, [Ei|Acc])
%%     end.

%% extract the I:th permutaion from Vt
%%  vtl(0, {A,B,C}) -> [A,B,C]
%%  vtl(2#111, {A,B,C}) -> [A,B,C]
%%  vtl(2#011, {A,B,C}) -> [-A,B,C]

%% to be used with new vbcp(Vp, Xs, true)
vtl(V, I, Vt) ->
    vtl_(V, tuple_size(Vt), I, Vt, []).
vtl_(_V, 0, _I, _Vt, Acc) ->
    Acc;
vtl_(V, J, I, Vt, Acc) ->
    E = element(J,Vt),
    if I band (1 bsl (J-1)) =/= 0 ->
	    vtl_(V, J-1, I, Vt, [E|Acc]);
       true -> 
	    vtl_(V, J-1, I, Vt, [-E|Acc])
    end.

%% given number I set vars in Vt according to bit
bindv(V, I, Vt) ->
    bindv(V, tuple_size(Vt), I, Vt).
    
bindv(_V, 0, _I, _Vt) ->
    true;
bindv(V, J, I, Vt) ->
    Xj = if I band (1 bsl (J-1)) =/= 0 -> 
		 element(J,Vt); 
	    true ->
		 -element(J,Vt)
	 end,
    varp_nif:bind(V,Xj) andalso bindv(V,J-1,I,Vt).


intersect_var(Vp, Var, Bs0) ->
    varp_nif:intersect_var(Vp, Var, Bs0, ?BINDING_AS_TUPLE).

intersect_bindings(Vp, Var, Bs0, Bs1) ->
    varp_nif:mark(Vp, Bs1),
    varp_nif:intersect_var(Vp, Var, Bs0, true).

get_marked(Vp) ->
    varp_nif:get_marked(Vp, ?BINDING_AS_TUPLE).

intersect_var0(_Vp, Var, Bs0, Bs1) ->
    intersect_var0_(Var, Bs0, bindings_to_map(Bs1)).

intersect_var0_(Var, [X|Bs0], Map) ->
    case maps:find(X, Map) of
	{ok,true} ->
	    %% !Var => X,  Var => X  
	    [X | intersect_var0_(Var, Bs0, Map)];
	error ->
	    case maps:find(-X, Map) of
		{ok,true} ->
		    %% !Var => X  Var => !X
		    [{Var,-X} | intersect_var0_(Var, Bs0, Map)];
		error ->
		    intersect_var0_(Var, Bs0, Map)
	    end
    end;
intersect_var0_(_Var, [], _Map) ->
    [].

%% intersect a list of list of bindings - return bindings
intersect([]) -> false;
intersect([A]) -> A;
intersect([A,B]) -> intersect_(A,B);
intersect([false|Bs]) -> intersect(Bs);
intersect([A|Bs]) -> intersect__(Bs, bindings_to_map(A)).

intersect__([false|Bs], Map) -> intersect__(Bs, Map);
intersect__([B|Bs], Map) -> intersect__(Bs, inter_map(B, Map));
intersect__([], Map) -> map_to_bindings(Map).

%% intersect two binding lists
intersect(As, Bs) -> intersect_(As, Bs).

intersect_(false, Bs) -> Bs;
intersect_(As, false) -> As;
intersect_(As, Bs) -> inter_values(Bs, bindings_to_map(As)).

inter_map(Bs, Map) ->
    inter_map_(Bs, Map, #{}).

inter_map_([B|Bs], Map, Dst) ->
    case maps:find(B, Map) of
	{ok,true} -> inter_map_(Bs, Map, Dst#{ B => true });
	_ -> inter_map_(Bs, Map, Dst)
    end;
inter_map_([], _Map, Dst) ->
    Dst.

inter_values([B|Bs], Map) ->
    case maps:find(B, Map) of
	{ok,true} -> [B | inter_values(Bs, Map)];
	_ -> inter_values(Bs, Map)
    end;
inter_values([], _Map) ->
    [].

%% make map of bindings into list of bindings
map_to_bindings(Map) ->
    [ X || {X,true} <- maps:to_list(Map)].

%% make a set of bindings
bindings_to_map(As) ->
    bindings_to_map(As, #{}).
bindings_to_map([A|As], Map) ->
    bindings_to_map(As, Map#{ A => true });
bindings_to_map([],Map) ->
    Map.

install_bindings0(V,Bs) ->
    install_bindings0(V,_Subst=true,Bs).

install_bindings0(V,Subst,[Bt|Bs]) when is_tuple(Bt) ->
    case install_tuple_bindings_(V, 0, Subst, 1, Bt) of
	true -> install_bindings0(V,Subst,Bs);
	false -> false
    end;
install_bindings0(V,Subst,[B|Bs]) when is_list(B) ->
    case install_list_bindings_(V, 0, Subst, B) of
	true -> install_bindings0(V,Subst,Bs);
	false -> false
    end;
install_bindings0(_V,_Subst,[]) ->
    true.


install_bindings(V,Bs) when is_list(Bs) ->
    install_list_bindings_(V, varp_nif:level(V), true, Bs);
install_bindings(V,Bt) when is_tuple(Bt) ->
    install_tuple_bindings_(V, varp_nif:level(V), true, 1, Bt).

install_bindings(V,Level,Bs) when is_list(Bs) ->
    install_list_bindings_(V, Level, true, Bs);
install_bindings(V,Level,Bt) when is_tuple(Bt) ->
    install_tuple_bindings_(V, Level, true, 1, Bt).

install_tuple_bindings_(_Vp, _Level, _Subst, I, Bt) when I > tuple_size(Bt) ->
    true;
install_tuple_bindings_(Vp, Level, Subst, I, Bt) when I =< tuple_size(Bt) ->
    install_binding(Vp, element(I,Bt), Level, Subst),
    install_tuple_bindings_(Vp,Level,Subst,I+1,Bt).

install_list_bindings_(_Vp,_Level,_Subst,[]) ->
    true;
install_list_bindings_(Vp,Level,Subst,[B|Bs]) ->
    install_binding(Vp, B, Level, Subst),
    install_list_bindings_(Vp,Level,Subst,Bs).


install_binding(Vp, X, _Level, _Subst) when is_integer(X) ->
    ?dbg0("install ~w = 1\n", [X]),
    true = varp_nif:bind(Vp, X);
install_binding(_Vp, {X,X}, _Level, _Subst) ->
    true;
install_binding(Vp, {X,t},  _Level, _Subst) ->
    ?dbg0("install ~w = t\n", [X]),
    true = varp_nif:bind(Vp, X);
install_binding(Vp, {X,f},  _Level, _Subst) ->
    ?dbg0("install ~w = f\n", [X]),
    true = varp_nif:bind(Vp, -X);
install_binding(Vp, {X,Y}, _Level = 0, _Subst = true) ->
    ?dbg0("install ~w = ~w\n", [X, Y]),
    Xa = varp_nif:variable_info(Vp, X, is_atom),
    Ya = varp_nif:variable_info(Vp, Y, is_atom),
    if Ya, not Xa ->
	    varp_nif:subst(Vp, Y, X);
       true ->
	    varp_nif:subst(Vp, X, Y)
    end;
install_binding(_Vp, _Bnd, _Level, _Subst) ->
    false.

%%
vec_value(V, Vec) ->
    [case varp_nif:value(V, Xi) of
	 undefined -> u;
	 Vi -> Vi
     end || Xi <- Vec].

vec_bind(_V, []) ->
    true;
vec_bind(V, [Xi|Vec]) ->
    varp_nif:bind(V, Xi) andalso vec_bind(V, Vec).

%% read "vector" of unbound variables
vec_create(V, K) ->
    vec_create(V, varp_nif:next_unbound(V), K).

vec_create(_V, false, _K) ->
    [];
vec_create(V, Vi, K) ->
    vec_create_(V, Vi, K-1, [Vi]).

vec_create_(_V, _Vi, 0, Vec) -> 
    Vec;
vec_create_(V, Vi, I, Vec) ->
    case varp_nif:next_unbound(V, Vi) of
	false ->
	    case varp_nif:next_unbound(V) of
		false -> Vec;
		Vj -> vec_create_(V, Vj, I-1, [Vj|Vec])
	    end;
	Vj ->
	    vec_create_(V, Vj, I-1, [Vj|Vec])
    end.

%% add (at most) Q "next" elements to Vec (not already in Vec)
vec_extend(V, Vec, Q) ->
    vec_extend_(V, Vec, Q).

vec_extend_(_V, Vec, 0) -> Vec;
vec_extend_(V, Vec, I) -> 
    case next_unbound_skip(V, hd(Vec), Vec) of
	false -> Vec;
	V1 -> vec_extend_(V, [V1|Vec], I-1)
    end.

vec_extend_friend(V, Vec, P, undefined) ->
    vec_extend(V, Vec, P);
vec_extend_friend(_V, Vec=[Xi|_], P, FriendMap) ->
    %% pick friends from -Xi
    W = maps:get(-Xi, FriendMap, []) -- Vec,
    Vec ++ lists:sublist(W, P).

%%
%% do a saturation run and build a reverse map
%% X -> Y1 Y2 Y3 ...  then 
%% friend(Y1, X)
%% friend(Y2, X)
%% friend(Y3, X)
%%
make_friend_map(V) ->
    make_friend_map_(V, varp_nif:next_unbound(V), #{}).

make_friend_map_(_V, false, Map) -> 
    Map;
make_friend_map_(V, Xi, Map0) ->
    Map1 = add_lit_friends(V, Xi, Map0),
    Map2 = add_lit_friends(V, -Xi, Map1),
    make_friend_map_(V, varp_nif:next_unbound(V, Xi), Map2).

add_lit_friends(V, Xi, Map) ->
    L = varp_nif:push(V),
    case varp_nif:bind(V, Xi) of
	false ->
	    varp_nif:queue_clear(V),
	    varp_nif:pop(V, L),
	    Map;
	true ->
	    varp_nif:push(V),
	    case varp_nif:bcp(V) of
		false ->
		    varp_nif:pop(V, L),
		    Map;
		true ->
		    Map1 = add_friends(get_bindings_list(V, 2), Xi, Map),
		    varp_nif:pop(V, L),
		    Map1
	    end
    end.

add_friends([Yi|Ys], X, Map) ->
    Fs = maps:get(Yi, Map, []),
    case lists:member(X, Fs) of
	true ->
	    add_friends(Ys, X, Map);
	false ->
	    add_friends(Ys, X, maps:put(Yi, [X|Fs], Map))
    end;
add_friends([], _X, Map) ->
    Map.

%% FIXME: add depth info for all friends?
%% depth(V, Yi, DepthMap) ->
%%    Cix = varp_nif:implication_clause(V, Yi),
%%    Clause = varp_nif:get_clause(V, Cix, Yi),
%%    Depth = lists:max([maps:get(-Li, DepthMap) || Li <- Clause])+1,
%%    {Depth, DepthMap#{ Yi => Depth }}.
    
%% add (at most) R random elements to Vec (not already in Vec)
vec_extend_rand(V, Vec, R) ->
    N = get_number_of_variables(V),
    M = get_number_of_unbound_variables(V) - length(Vec),
    vec_extend_rand_(V, Vec, N, M, R).

vec_extend_rand_(_V, Vec, _N, _M, 0) -> Vec;
vec_extend_rand_(_V, Vec, _N, M, _I) when M =< 0 -> Vec;
vec_extend_rand_(V, Vec, N, M, I) ->
    V1 = next_rand_unbound_skip(V, N, Vec),
    vec_extend_rand_(V, [V1|Vec], N, M-1, I-1).

vec_is_bound(_V, []) ->
    false;
vec_is_bound(V, [Xi|Vec]) ->
    case varp_nif:is_bound(V, Xi) of
	true -> true;
	false -> vec_is_bound(V, Vec)
    end.

%% step vector (list) over variables
vec_step(V, Vec) ->
    vec_step(V, Vec, []).

vec_step(_V, [], _Skip) ->
    false;
vec_step(V, [Vi|Vec], Skip) ->
    case next_unbound_skip(V, Vi, Skip) of
	false ->
	    case vec_step(V, Vec, [Vi|Skip]) of
		false -> false;
		Vec1 = [Vj|_] ->
		    case next_unbound_skip(V, Vj, Skip) of
			false -> false;
			Vk -> [Vk|Vec1]
		    end
	    end;
	Vj -> [Vj|Vec]
    end.

next_unbound_skip(V, Vi, Skip) ->
    case varp_nif:next_unbound(V, Vi) of
	false -> false;
	Vj ->
	    case lists:member(Vj, Skip) of
		true -> next_unbound_skip(V, Vj, Skip);
		false -> Vj
	    end
    end.

%% Select a random variables, that is not member of Skip, among
%% variables in range 1..N
%% FIXME: this may loop too long if few unbound variables are available!
next_rand_unbound_skip(V, N, Skip) when N > 0 ->
    J = rand:uniform(N),
    case varp_nif:next_unbound(V, J) of
	false ->
	    next_rand_unbound_skip(V, N, Skip);
	V1 ->
	    case lists:member(V1, Skip) of
		true -> next_rand_unbound_skip(V, N, Skip);
		false -> V1
	    end
    end.

%% utility to get a list of unbound literals
order_all(Vp) ->
    order_all_(Vp,varp_nif:next_unbound(Vp),[]).

order_all_(_Vp,false,Acc) ->
    lists:reverse(Acc);
order_all_(Vp,Xi,Acc) ->
    order_all_(Vp,varp_nif:next_unbound(Vp, Xi), [Xi|Acc]).

phase_all(Vp) ->
    [varp_nif:variable_info(Vp,Vi,phase) || Vi <- order_all(Vp)].
