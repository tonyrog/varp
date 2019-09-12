%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2010, Tony Rogvall
%%% @doc
%%%    Prover interface
%%% @end
%%% Created :  5 Aug 2010 by Tony Rogvall <tony@rogvall.se>

-module(varp).

-export([start/0, start0/0]).
-export([main/1]).
-export([do_run/3]).

-export([parse/1, parse/2]).
-export([scan_file/1]).
-export([file/1, string/1]).
-export([archive_path/1]).
-export([output_model/2]).
-export([empty_sections/0]).

-export([load_plugins/0]).
-export([load_do/0, load_do/1]).
-export([parse_do/1, parse_do/2]).

-export([load_options/0, load_options/1, load_options/2]).
-export([load_option_list/1, load_option_list/3]).

-export([default_options/0]).

-include_lib("stdlib/include/zip.hrl").
-include("varp.hrl").
-include("log.hrl").

-record(stat,
	{
	 clause_count,
	 clause_count_2,
	 clause_count_3,
	 clause_count_dead,
	 eval_count,
	 bound,
	 clauses,
	 dead_clauses
	}).

global_options() ->
    [
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
	 description => "random seed"
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
	 default => lifo,
	 description => "lifo, fifo or depth first queue type."
       },
      #{ long => "version",
	 short => "V", 
	 key => version,
	 spec => string,
	 default => vsn(),
	 description => "Report current version."
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
	default => [],  %% ordset
	description => "Internal list of meta variables and values"},
     #{ key => defs,
	spec => {set,{pred,term}},
	default => [],  %% ordset
	description => "Internal list of all definitions"},
     #{ key => decls,
	spec => {set,{predpat,atom,term}},
	default => [],  %% ordset
	description => "Internal list of all declarations"},     
     #{ key => literals,
	spec => {set,atom},
	default => [],  %% ordset
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
	description => "Internal list of output modules"}
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
    io:format("varp dummy start\n"),
    %% dummy start for servator when generating application
    application:start(varp),
    ok.

main(Args) ->
    %% io:format("main: arguments = ~p\n", [Args]),
    application:start(varp),

    Plugins = load_plugins(),
    %% io:format("main: plugins = ~p\n", [Plugins]),

    GlobalOptionSpec = global_option_spec(),
    GOpts0 = default_options(),

    %% io:format("options0 = ~p\n", [GOpts0]),
    GOpts1 = load_options(GlobalOptionSpec, GOpts0),
    %% io:format("main: options1 = ~p\n", [GOpts1]),
    Do0 = load_do(Plugins),

    {Do1,Files,GOpts2,Bound} =
	process_args(Args, Plugins, [], [], GlobalOptionSpec, GOpts1, []),

    Do = if Do1 =/= [] -> Do1;
	    true -> Do0
	 end,
    %% io:format("main: do = ~p\n", [Do]),
    %% io:format("files = ~p\n", [Files]),
    %% io:format("options2 = ~p\n", [GOpts2]),
    %% io:format("bound = ~p\n", [Bound]),

    {ReadIn,{Sections0,Formula0}} =
	case load_formulas(maps:get(formula,GOpts2,[]), undefined, 'and') of
	    {ok,{S0,undefined}}-> {true,{S0,undefined}};
	    {ok,R0} -> {false,R0};
	    __Error -> halt(1)
	end,

    GOpts3 = section_opts(Sections0, GOpts2#{ meta => Bound }),

    case Files of
	[] when not ReadIn ->
	    do_run(Do, Formula0, GOpts3);
	[] when ReadIn ->
	    case read_in() of
		{ok,<<>>} ->
		    do_run(Do, Formula0, GOpts3);
		{ok,Data} ->
		    case parse("*stdin*", Data) of
			{ok,{Sections1,Formula}} ->
			    Formula1 = join_f('and',Formula0,Formula),
			    Sections = append_sections(Sections0,Sections1),
			    GOpts4 = section_opts(Sections,GOpts3),
			    do_run(Do,Formula1,GOpts4);
			_Error ->
			    halt(1)
		    end;
		_Error ->
		    halt(1)
	    end;
	[F] -> %% check if batch mode, run tar/zip over all formulas
	    case archive_type(F) of
		undefined ->
		    case load_files([F],Formula0,Sections0,'and',GOpts3) of
			{ok,{Sections1,Formula}} ->
			    GOpts4 = section_opts(Sections1, GOpts3),
			    do_run(Do,Formula,GOpts4);
			_Error ->
			    halt(1)
		    end;
		Type -> %% with formula?
		    run_batch(Do,Type,F,GOpts3)
	    end;
	Fs ->
	    case load_files(Fs,Formula0,Sections0,'and',GOpts3) of
		{ok,{Sections1,Formula}} ->
		    GOpts4 = section_opts(Sections1, GOpts3),
		    do_run(Do,Formula,GOpts4);
		_Error ->
		    halt(1)
	    end
    end,
    halt(0).

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
	    %% io:format("mod = ~p\n", [Mod]),
	    %% io:format("list = ~p\n", [OptionInfoList]),
	    %% io:format("spec = ~p\n", [OptionSpec]),
	    %% io:format("map = ~p\n", [OptMap]),
	    OptMap1 =
		lists:foldl(
		  fun({Key,Value}, Mi) ->
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
		  {ok,{Sections,Formula}} ->
		      do_run(Do,Formula, section_opts(Sections, GOpts));
		  Error ->
		      io:format("~s: error ~p\n", [F,Error]),
		      ok
	      end
      end, Fs).

do_run(Do, Formula, GOpts) ->
    R = do_run_(Do, Formula, GOpts),
    garbage_collect(self(),[{type,major}]),
    R.

do_run_(Do, Formula, GOpts) ->
    {{bool,Main}, Bs} = varp_formula:build(Formula,GOpts),
    Bs1 = Bs#bs { main = Main },
    R = do(Do, Bs1),
    Method = method(Do),
    case Bs#bs.proof_fd of
	undefined -> ok;
	user -> ok;
	Fd -> file:close(Fd)
    end,
    case varp_formula:getopt(Bs1, print) of
	false -> R;
	_ -> display_result(R, Method, Bs1), R
    end.

do([{Plugin,Param}|Do], Bs) ->
    S0 = stat(Bs),
    varp_formula:info(Bs, "pass ~p\n", [Plugin]),
    T0 = erlang:monotonic_time(),
    try Plugin:run(Bs, Param) of
	R ->
	    T1 = erlang:monotonic_time(),
	    S1 = stat(Bs),
	    Time = erlang:convert_time_unit(T1-T0,native,microsecond),
	    Ts = Time/1000000,
	    show_info(S1, S0, Ts, Bs),
	    case R of
		false ->
		    no_models(Bs);
		Bs1 when is_record(Bs1,bs) ->
		    case one_model(Bs1) of
			false -> do(Do, Bs1);
			Result -> Result
		    end;
		Result ->
		    Result
	    end
    catch
	?EXCEPTION(error, Reason, Stacktrace) ->
	    io:format("~s crashed ~p: ~p\n",
		      [Plugin, Reason, ?GET_STACK(Stacktrace)]),
	    error
    end;
do([], _Bs) ->
    undefined.

show_info(S1, S0, Ts, Bs) ->
    varp_formula:info(Bs, "    | eval: ~w\n    | clause:~w,~w(2),~w(3),~w(dead)\n    | #clauses = ~w, #dead = ~w\n    | time=~.2fs\n",
		      [S1#stat.eval_count-S0#stat.eval_count,
		       S1#stat.clause_count - S0#stat.clause_count,
		       S1#stat.clause_count_2 - S0#stat.clause_count_2,
		       S1#stat.clause_count_3 - S0#stat.clause_count_3,
		       S1#stat.clause_count_dead - S0#stat.clause_count_dead,
		       S1#stat.clauses,
		       S1#stat.dead_clauses,
		       Ts]),
    varp_formula:info(Bs,"    | bound: ~w [~w/~w]\n",
		      [S1#stat.bound-S0#stat.bound,
		       S1#stat.bound,
		       varp_formula:number_of_variables(Bs)
		      ]).

stat(Bs) ->
    #stat { clause_count   = varp_formula:clause_eval_counter(Bs,0),
	    clause_count_2 = varp_formula:clause_eval_counter(Bs,2),
	    clause_count_3 = varp_formula:clause_eval_counter(Bs,3),
	    clause_count_dead = varp_formula:clause_eval_counter(Bs,dead),
	    eval_count     = varp_formula:eval_counter(Bs),
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
    
display_result({N,_Models}, Method, Bs) ->
    display_result(N, Method, Bs);
display_result(0, satisfy, Bs) ->
    case varp_formula:getopt(Bs, starexec) of
	true ->
	    io:format("s UNSATISFIABLE\n");
	false ->
	    io:format("% 0\n", [])
    end;
display_result(N, satisfy, _Bs) when is_integer(N) ->
    io:format("% ~w\n", [N]);
display_result(0, falsify, _Bs) ->
    io:format("% 0\n", []);
display_result(N, falsify, _Bs) when is_integer(N) ->
    io:format("% ~w\n", [N]);
display_result(0,prove,_Bs) ->
    io:format("% TRUE\n", []);
display_result(0,none,_Bs) ->
    ok; %% io:format("\n", []);
display_result(_N,prove,_Bs) ->
    io:format("% FALSE\n", []);
display_result(undefined,prove,_Bs) ->
    io:format("% UNKNOWN\n", []);
display_result(undefined,_,_Bs) ->
    ok; %% io:format("\n", []);
display_result(error,_,_Bs) ->
    io:format("% ERROR\n", []).

%% check if there is already a "unique" model
one_model(Bs) ->
    NV = varp_formula:number_of_variables(Bs),
    NB = varp_formula:number_of_bound(Bs),
    if NV =:= NB ->
	    Model = output_model(Bs,1),
	    case varp_formula:getopt(Bs,method) of
		collect -> {1,[Model]};
		count -> 1
	    end;
       true ->
	    false
    end.

no_models(Bs) ->
    case varp_formula:getopt(Bs,partial) of
	true ->
	    %% print partial model, the variables bound
	    Mdl = varp_formula:model(Bs),
	    Mdl1 = varp_formula:filter_bindings(Mdl),
	    io:format("partial: ~s\n",
		      [lists:join(",",[varp_formula:format_binding(Bound) || Bound <- Mdl1 ])]);
	false ->
	    ok
    end,
    case varp_formula:getopt(Bs,method) of
	collect -> {0,[]};
	count -> 0
    end.

anon_decls([{{p,P,Ps},Type,Size}|Decls]) ->
    [{{p,P,['_' || _ <- Ps]},Type,Size}|anon_decls(Decls)];
anon_decls([]) ->
    [].

order_decl([]) -> [];
order_decl(Vs) -> order_decl(Vs,[]).

order_decl([Key1,Key2|Vs],Opts) when is_atom(Key1), is_atom(Key2) ->
    order_decl(Vs,[{order,[Key1,Key2]}|Opts]);
order_decl([Key1|Vs],Opts) when is_atom(Key1) ->
    order_decl(Vs,[{order,[Key1]}|Opts]);
order_decl([V|Vs],[{order_list,Ls}|Opts]) when is_tuple(V) ->
    order_decl(Vs, [{order_list,Ls++[V]}|Opts]);
order_decl([V|Vs],Opts) when is_tuple(V) ->
    order_decl(Vs, [{order_list,[V]}|Opts]);
order_decl([],Opts) ->
    case lists:reverse(Opts) of
	[{order_list,L1},{order,K},{order_list,L2}] ->
	    [{order,K},{order_first,L1},{order_last,L2}];
	[{order_list,L1},{order,K}] ->
	    [{order,K},{order_first,L1}];
	[{order,K},{order_list,L2}] ->
	    [{order,K},{order_last,L2}];
	[{order_list,L1}] ->
	    [{order_first,L1}];
	[{order,K}] ->
	    [{order,K}];
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
		Cnf = {cnf,{_NVars,_NClauses,Sections0,_Ls,_CLs}} ->
		    %% io:format("% loaded: ~p\n", [Cnf]),
		    Formula1 = join_f(JoinOp,Cnf,Formula0),
		    Sections1 = append_sections(Sections, Sections0),
		    load_files(Fs,Formula1,Sections1,JoinOp,GOpts);
		Snf = {snf,{_NVars,_NClauses,Sections0,_Ls,_CLs}} ->
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
		Error ->
		    Error
	    end;
       true ->
	    io:format("Read file ~s\n", [F]),
	    {ok, Data} = read_file(F),
	    case parse(F, Data) of
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
load_files([],Formula,Sections,_JoinOp,_GOpts) ->
    {ok,{Sections,Formula}}.


%% special input format
varp_input([#cid{name=ModuleName} | InputList], FileName, Meta) ->
    Module = list_to_atom(ModuleName),
    case code:ensure_loaded(Module) of
	{module,M} ->
	    case erlang:function_exported(M, file, 2) of
		true ->
		    apply(M, file, [FileName, Meta]);
		false ->
		    case erlang:function_exported(M, file, 1) of
			true ->
			    apply(M, file, [FileName]);
			false ->
			    varp_input(InputList, FileName, Meta)
		    end
	    end;
	{error,_} ->
	    varp_input(InputList, FileName, Meta)
    end;
varp_input([], _FileName, _Meta) ->
    {error, no_input}.

%% special input format
varp_output([#cid{name=ModuleName} | OutputList], Fd, Model) ->
    Module = list_to_atom(ModuleName),
    case code:ensure_loaded(Module) of
	{module,M} ->
	    case erlang:function_exported(M, output, 2) of
		true ->
		    apply(M, output, [Fd, Model]);
		false ->
		    varp_output(OutputList, Fd, Model)
	    end;
	{error,_} ->
	    varp_output(OutputList, Fd, Model)
    end;
varp_output([], _Fd, _Model) ->
    {error, no_output}.

%% possibly emit a model

output_model(Bs,I) ->
    output_model_header(Bs, I),
    Model = varp_formula:model(Bs),
    case varp_formula:getopt(Bs,print) of
	false ->
	    Model;
	Flavour ->
	    case varp_output(Bs#bs.output, user, Model) of
		{error, no_output} ->
		    varp_formula:print_model(Flavour,I,Model),
		    Model;
		_ ->
		    Model
	    end
    end.

output_model_header(Bs,_I) ->
    case varp_formula:getopt(Bs,starexec) of
	true ->
	    case get(answer) of
		true -> 
		    ok;
		_ ->
		    io:format("s SATISFIABLE\n"),
		    put(answer, true)
	    end;
	false ->
	    ok
    end.

%% fixme analyze the path to see if there are 
%% archive tar/tar.gz/tgz/zip compoinents in the path
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
load_formulas([], A, _JoinOp) ->
    {ok,{empty_sections(),A}};
load_formulas(Fs, A, JoinOp) ->
    parse_formulas(Fs,A,empty_sections(),JoinOp).

parse_formulas([F|Fs], Formula, Sections0,JoinOp) ->
    case parse("*command-line*", F) of
	{ok,{Sections1,Formula1}} ->
	    parse_formulas(Fs, join_f(JoinOp, Formula, Formula1),
			   append_sections(Sections0, Sections1), JoinOp);
	Error ->
	    Error
    end;
parse_formulas([], Formula, Sections, _JoinOp) ->
    {ok,{Sections,Formula}}.


empty_sections() ->
    #{ decls=>[], order=>[], literals=>[], defs=>[], 
       assert=>[], input=>[], output=>[] }.

append_sections(#{ decls:=D0,order:=O0,literals:=Ls0,defs:=Ds0,
		   assert:=A0,input:=I0, output:=T0 },
		#{ decls:=D1,order:=O1,literals:=Ls1,defs:=Ds1,
		   assert:=A1,input:=I1, output:=T1 }) ->
    #{ decls=>D0++D1, 
       order=>O0++O1, 
       literals=>Ls0++Ls1,
       defs=>Ds0++Ds1,
       assert => A0++A1,
       input => I0++I1,
       output => T0++T1
     }.


section_opts(#{ decls := Decls,
		order := Order,
		literals := Literals,
		defs := Defs,
		assert := Assert,
		input := Input,
		output := Output },
	     GOpts) ->
    GOpts#{
	   order => order_decl(Order),
	   decls => anon_decls(Decls),
	   defs => Defs,
	   literals => Literals,
	   assert => Assert,
	   input => Input,
	   output => Output}.
    
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

parse(File, Binary) when is_binary(Binary) ->
    parse(File, binary_to_list(Binary));
parse(File, String) ->
    case tokens(String) of
	{ok,Ts} ->
	    case varp_parse:parse(Ts) of
		{ok,{Sections,Formula}} ->
		    SectionMap = split_sections(Sections),
		    {ok,{SectionMap,Formula}};
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
    split_sections(Sections,empty_sections()).

split_sections([{declare,Decl}|Sections], Map=#{ decls:=Decl0 }) ->
    split_sections(Sections, Map#{ decls => Decl0++Decl });
split_sections([{order,Order}|Sections],Map=#{ order:=Order0 }) ->
    split_sections(Sections, Map#{ order => Order0++Order });
split_sections([{literals,Ls}|Sections],Map=#{ literals:=Ls0 }) ->
    split_sections(Sections, Map#{ literals => Ls0++Ls });
split_sections([{define,P,Expr}|Sections], Map=#{ defs:=Defs0 }) ->
    split_sections(Sections, Map#{ defs => Defs0++[{P,Expr}] });
split_sections([{assert,Expr}|Sections], Map=#{ assert:=Assert0 }) ->
    split_sections(Sections, Map#{ assert => Assert0++[Expr] });
split_sections([{input,Name}|Sections], Map=#{ input:=Input0 }) ->
    split_sections(Sections, Map#{ input => Input0++[Name] });
split_sections([{output,Name}|Sections], Map=#{ output:=Output0 }) ->
    split_sections(Sections, Map#{ output => Output0++[Name] });
split_sections([], Map) ->
    Map.
    
string(Binary) when is_binary(Binary) ->
    string(binary_to_list(Binary));
string(String) when is_list(String) ->
    {ok,Ts} = tokens(String),
    varp_parse:parse(Ts).

tokens(String) ->
    case varp_scan:string(remove_comments(String)) of
	{ok,Ts,_Ln} -> 
	    %% io:format("tokens=~p\n", [Ts]),
	    {ok,Ts};
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
