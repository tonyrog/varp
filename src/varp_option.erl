%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2013, Tony Rogvall
%%% @doc
%%%    Option processing
%%% @end
%%% Created : 13 Dec 2013 by Tony Rogvall <tony@rogvall.se>

-module(varp_option).

-export([set_opts/1, set_opts/2]).
-export([default_opts/0]).
-export([setopt/3, getopt/2]).
-export([usage/0]).

-export([options/0]).
-export([process_args/2]).
-export([process_args/4]).

-include("log.hrl").

%% -define(dbg(F,A), io:format((F),(A))).
-define(dbg(F,A), ok).

%% debug/test
-export([match_value/3]).
%%
%% Option format:
%%  --long 123
%%  --long=123
%%  -long 123
%%  -l 123
%%  -l123
%%

-define(BOOL,
	{"true",true},
	{"false",false},
	{"1",true},
	{"0",false}).

-define(ORDER,
	{"undefined", undefined},
	{"identity",  identity},
	{"random",    random},
	{"depth",     '+depth'},
	{"+depth",    '+depth'},
	{"-depth",    '-depth'},
	{"occur",     '+occur'},
	{"+occur",    '+occur'},
	{"-occur",    '-occur'}).

options() ->
    V1 = #{ long => "value",
	    short => "v",
	    key => value,
	    spec => {enum,[?BOOL,{"none", none}]},
	    default => none,
	    description => "Main formula variable value."},
    V2 = #{ long => "print",
	    short => "p",
	    key => print,
	    spec => {enum,
		     [?BOOL,
		      {"literal",literal},
		      {"erlang",erlang},
		      {"model",model}]},
	    default => model,
	    description => "Print models when found."
	  },
    V3 = #{ long => "partial",
	    key => partial,
	    spec => {enum,[?BOOL]},
	    default => false,
	    description => "Print partial models when possible."
	  },
    V4 = #{ long => "method",
	    key => method,
	    spec => {enum,
		     [{"collect", collect},
		      {"count", count}]},
	    default => collect,
	    description => "Count or collect models."
	  },
    V5 = #{ long => "max",
	    short => "n",
	    key => max,
	    spec => unsigned,
	    default => 0,
	    description => "Max number of models to count or collect, 0=all."
	  },
    V6 = #{ long => "order",
	    key => order,
	    spec => {list,{enum,[?ORDER]}},
	    default => [identity],
	    description => "Specifiy variable order."
	  },
    V61 = #{ long => "order-first",
	     key => order_first,
	     spec => {list,literal},
	     default => [],
	     description => "Literals sorted first."
	   },
    V62 = #{ long => "order-last",
	     key => order_last,
	     spec => {list,literal},
	     default => [],
	     description => "Literals sorted last."
	   },
    V63 = #{ long => "display-order",
	     short => "d",
	     key => display_order,
	     spec => {enum,[?BOOL]},
	     default => false,
	     description => "Display declared variable order."
	   },
    V7 = #{ long => "bcp",
	    key => bcp,
	    spec => {enum,[?BOOL]},
	    default => false,
	    description => "Do not use equivalence classes."
	  },
    V71 = #{ long => "clause",
	     short => "c",
	     key => clause,
	     spec => {enum,[?BOOL]},
	     default => false,
	     description => "Use clause form."
	   },
    V8 = #{ long => "saturate",
	    short => "s",
	    key => saturate,
	    spec => unsigned, 
	    default => undefined,
	    description => "Saturation level."
	  },
    V9 = #{ long => "backtrack",
	    short => "b",
	    key => backtrack,
	    spec => {enum,[?BOOL]},
	    default => true,
	    description => "Use backtracking."
	  },
    V91 = #{ long => "backjump",
	     short => "j",
	     key => backjump,
	     spec => {enum,[?BOOL]},
	     default => false,
	     description => "Use backjumping during backtrack."
	  },
    V92 = #{ long => "minimize",
	     short => "z",
	     key => minimize,
	     spec => {enum,[?BOOL]},
	     default => true,
	     description => "Use conflict clause minimization."
	   },
    V93 = #{ long => "compress",
	     short => "g",
	     key => compress,
	     spec => {enum,[?BOOL]},
	     default => false,
	     description => "Compress clauses."
	   },
    V10 = #{ long => "pair",
	     key => pair,
	     spec => {enum,[?BOOL]},
	     default => false,
	     description => "Add extra variable in saturation."
	   },
    V11 = #{ long => "assoc",
	     key => assoc,
	     spec => {enum,
		      [{"left",left},
		       {"right",right},
		       {"middle",middle}]}, 
	     default => left,
	     description => "Specify the order how all and any are built."
	   },
    V12 = #{ long => "threshold",
	     key => threshold,
	     spec => unsigned,
	     default => 0,
	     description => "Threshold for bound variables in saturation round"
	   },
    V12t = #{ long  => "time",
	      short => "t",
	      key   => time,
	      spec  => {union,[float,{enum,[{"infinity",infinity}]}]},
	      default => infinity,
	      description => "Max time to run saturation in milliseconds"
	    },
    V12l = #{ long  => "laps",
	      short => "l",
	      key   => laps,
	      spec  => {union,[unsigned,{enum,[{"infinity",infinity}]}]},
	      default => infinity,
	      description => "Max saturation lap count"
	    },
    V13 = #{ long => "carry",
	     key => carry,
	     spec => {enum,[?BOOL,{"ignore",ignore}]},
	     default => ignore,
	     description => "How to handle carry in addition."
	   },
    V14 = #{ long => "borrow",
	     key => borrow,
	     spec => {enum,[?BOOL,{"ignore",ignore}]},
	     default => ignore,
	     description => "How to handle borrow in subtraction."
	   },
    V15 = #{ long => "divz",
	     key => divz,
	     spec => {enum,[?BOOL,{"ignore",ignore}]},
	     default => false,
	     description => "How to handle divide by zero."
	   },
    V16 = #{ long => "log",
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
    V17 = #{ long => "out",
	     short => "o",
	     key => out,
	     spec => string, 
	     default => "",
	     description => "Output file name."
	   },
    V18 = #{ long => "formula",
	     short => "f",
	     key => formula,
	     spec => {multiple,string},
	     default => [],
	     description => "Command line formula."
	   },
    V19 = #{ long => "version",
	     short => "V", 
	     key => version,
	     spec => string,
	     default => vsn(),
	     description => "Report current version."
	   },
    V20 = #{ long => "help",
	     short => "h", 
	     key => help,
	     spec => void,
	     default => undefined,
	     description => "This help."
	   },
    V21 = #{ key => meta,
	     spec => {set,{string,term}},
	     default => [],  %% ordset
	     description => "Internal list of meta variables and values"},
    V22 = #{ key => defs,
	     spec => {set,{pred,term}},
	     default => [],  %% ordset
	     description => "Internal list of all definitions"},
    V23 = #{ key => decls,
	     spec => {set,{predpat,atom,term}},
	     default => [],  %% ordset
	     description => "Internal list of all declarations"},
    V25 = #{ key => saturations,
	     spec => {list,term},
	     default => [],
	     description => "Internal sequence of saturations"},
    V26 = #{ key => literals,
	     spec => {set,atom},
	     default => [],  %% ordset
	     description => "Internal list of all literals"},
    V26_1 = #{ key => assert,
	       spec => {list,term},
	       default => [],  %% list
	       description => "Internal list of all assertions"},
    V26_2 = #{ key => input,
	       spec => {list,term},
	       default => [],  %% list
	       description => "Internal list of input modules"},
    V26_3 = #{ key => output,
	       spec => {list,term},
	       default => [],  %% list
	       description => "Internal list of output modules"},

    V27 = #{ long => "iorder",
	     key => iorder,
	     spec => unsigned,
	     default => 0,
	     description => "max conflict clause length"},

    V28 = #{ long => "stumble",
	     key => stumble,
	     spec => unsigned,
	     default => 0,
	     description => "extra backjump level"},

    V29 = #{ long => "olle",
	     key => olle,
	     spec => float,
	     default => 0,
	     description => "extra backjump factor"},

    V30 = #{ long => "stumble-olle",
	     key => stumble_olle,
	     spec =>  {enum,[?BOOL]},
	     default => false,
	     description => "both backjump and factor"},

    V31 = #{ long => "seed",
	     key => seed,
	     spec => integer,
	     default => -1,
	     description => "random seed"},

    V33 = #{ long => "max-conflicts",
	     key => max_conflicts,
	     spec =>  unsigned,
	     default => 0,
	     description => "max number of conflicts to generate per conflict"},

    V34 = #{ long => "num-conflicts",
	     key => num_conflicts,
	     spec =>  unsigned,
	     default => 1,
	     description => "number of conflicts to analyse"},

    V35 = #{ long => "max-learned",
	     key => max_learned,
	     spec =>  unsigned,
	     default => 0,
	     description => "Max number of clauses to generate in learning"},

    V36 = #{ long => "max-learned-factor",
	     key => max_learned_factor,
	     spec =>  float,
	     default => 0,
	     description => "Factor to calculate number of learned clauses"},

    V37 = #{ long => "keep-factor",
	     key => keep_factor,
	     spec =>  float01,
	     default => 0.5,
	     description => "Number of clauses to keep"},

    V38 = #{ long => "min-keep-clauses",
	     key => min_keep_clauses,
	     spec =>  unsigned,
	     default => 0,
	     description => "Min number of clauses to keep"},

    V39 = #{ long => "restart-counter",
	     key => restart_counter,
	     spec =>  unsigned,
	     default => 0,
	     description => "Number of counts/eval until restart"},

    V40 = #{ long => "restart-interval",
	     key => restart_interval,
	     spec =>  unsigned,
	     default => 0,
	     description => "Restart interval in milliseconds"},

    V41 = #{ long => "starexec",
	     key => starexec,
	     spec =>  {enum,[?BOOL]},
	     default => false,
	     description => "Report result in starexec format"},

    V42 = #{ long => "reduction",
	     short => "r",
	     key => reduction,
	     spec => {union,[unsigned,{enum,[{"all",all}]}]},
	     default => 0,
	     description => "Add literal reduction clauses."
	  },
    V43 = #{ long => "reduction-type",
	     short => "R",
	     key => reduction_type,
	     spec => {enum,[{"both",both},{"min",min},{"pos",pos},{"neg",neg}]},
	     default => min,
	     description => "Type of reductions clauses."
	  },
    V44 = #{ long => "dump",
	     key => dump,
	     spec => integer,
	     default => -1,
	     description => "dump clauses at phase i"
	   },

    %% now build a map from long/short => Vi (will be a literal)
    #{ value => V1, "value" => V1, "v" => V1,
       print => V2, "print" => V2, "p" => V2,
       partial => V3, "partial" => V3,
       method  => V4, "method"  => V4,
       max => V5, "max" => V5, "n" => V5,
       order => V6, "order" => V6,
       order_first => V61, "order_first" => V61, "order-first" => V61,
       order_last => V62, "order_last" => V62, "order-last" => V62,
       display_order => V63, 
       "display_order" => V63,
       "display-order" => V63,
       "d" => V63,
       bcp => V7, "bcp" => V7,
       clause => V71, "clause" => V71, "c" => V71,
       saturate => V8, "saturate" => V8, "s" => V8,
       backtrack => V9, "backtrack" => V9, "b" => V9,
       backjump => V91, "backjump" => V91, "j" => V91,
       minimize => V92, "minimize" => V92, "z" => V92,
       compress => V93, "compress" => V93, "g" => V93,
       pair => V10, "pair" => V10,
       assoc => V11, "assoc" => V11,
       threshold => V12, "threshold" => V12,
       time => V12t, "time" => V12t, "t" => V12t,
       laps => V12l, "laps" => V12l, "l" => V12l,
       carry => V13, "carry" => V13,
       borrow => V14, "borrow" => V14,
       divz => V15, "divz" => V15,
       log => V16, "log" => V16,
       out => V17, "out" => V17, "o" => V17,
       formula => V18, "formula" => V18, "f" => V18,
       version => V19, "version" => V19, "V" => V19,
       help => V20, "help" => V20, "h" => V20,
       meta => V21,
       defs => V22,
       decls => V23,
       literals => V26,
       assert => V26_1,
       input => V26_2,
       output => V26_3,
       saturations => V25,
       %% Backjump options
       iorder => V27, "iorder" => V27, "i" => V27,
       stumble => V28, "stumble" => V28, 
       olle => V29, "olle" => V29,
       stumble_olle => V30, "stumble_olle" => V30, "stumble-olle" => V30,
       seed => V31, "seed" => V31,
       max_conflicts => V33, "max_conflicts" => V33, "max-conflicts" => V33,
       num_conflicts => V34, "num_conflicts" => V34, "num-conflicts" => V34,
       max_learned => V35, "max_learned" => V35, "max-learned" => V35,
       max_learned_factor => V36, 
       "max_learned_factor" => V36,
       "max-learned-factor" => V36,
       keep_factor => V37, 
       "keep_factor" => V37,
       "keep-factor" => V37,
       min_keep_clauses => V38,
       "min_keep_clauses" => V38,
       "min-keep-clauses" => V38,
       restart_counter=>V39, 
       "restart_counter"=>V39,
       "restart-counter"=>V39,
       restart_interval=>V40,
       "restart_interval"=>V40,
       "restart-interval"=>V40,
       starexec=>V41, "starexec"=>V41,
       reduction=>V42, "reduction"=>V42, "r"=>V42,
       reduction_type=>V43, "reduction-type"=>V43, "R"=>V43,
       dump=>V44, "dump"=>V44
     }.

%% list of options with unique key
key_options() ->
    L = maps:fold(
	  fun(_K,V=#{key:=Key},Acc) ->
		  [{Key,V}|Acc]
	  end, [], options()),
    lists:ukeysort(1, L).

%% generate a list of options from option map, with unique 'key'
options_list() ->
    [V || {_,V} <- key_options()].

process_args(Args, Mode) ->
    %% io:format("process_args:~w: ~p\n", [Mode,Args]),
    process_args(Args, Mode, [], []).

%% process long options and values
process_args(["--"++OptName|As],Mode,Opts,Bound) ->
    case get_long_opt(OptName) of
	false -> usage(OptName);
	{#{ key:=help },_Val} -> usage();
	{#{ key:=version },_Val} -> version();
	{#{ key:=Key,spec:=ValSpec },Val} ->
	    case match_value(ValSpec,Val,As) of
		false -> usage();
		{ok,Value,As1} ->
		    process_args(As1,Mode,[{Key,Value}|Opts],Bound)
	    end
    end;
process_args(["-"++OptName|As],Mode,Opts,Bound) ->
    case get_long_opt(OptName) of
	false ->
	    case get_short_opt(OptName) of
		false -> usage(OptName);
		{#{ key:=help },_Val} -> usage();
		{#{ key:=version },_Val} -> version();
		{#{ key:=Key,spec:=ValSpec },Val} ->
		    case match_value(ValSpec,Val,As) of
			false -> usage();
			{ok,Value,As1} ->
			    process_args(As1,Mode,[{Key,Value}|Opts],Bound)
		    end
	    end;
	{#{ key:=help },_Val} -> usage();
	{#{ key:=version },_Val} -> version();
	{#{ key:=Key,spec:=ValSpec },Val} ->
	    case match_value(ValSpec,Val,As) of
		false -> usage(Key,Val);
		{ok,Value,As1} ->
		    process_args(As1,Mode,[{Key,Value}|Opts],Bound)
	    end
    end;
process_args([Var,"=",Value|As],Mode,Opts,Bound) ->
    try list_to_integer(Value) of
	N ->
	    process_args(As,Mode,Opts,[{Var,N}|Bound])
    catch
	error:badarg ->
	    process_args(As,Mode,Opts,[{Var,Value}|Bound])
    end;
process_args([A|As],Mode,Opts,Bound) ->
    case string:chr(A,$=) of
	0 -> 
	    {Mode,Bound,lists:reverse(Opts),[A|As]};
	I ->
	    {Var,"="++Value0} = lists:split(I-1,A),
	    {Value,As1} = 
		if Value0 =:= "" -> 
			case As of
			    [A2|As2] -> {A2,As2};
			    [] -> {"",[]}
			end;
		   true -> {Value0,As}
		end,
	    %% V = list_to_atom(Var),
	    case string:to_integer(Value) of
		{N,""} -> process_args(As1,Mode,Opts,[{Var,N}|Bound]);
		_ -> process_args(As1,Mode,Opts,[{Var,Value}|Bound])
	    end
    end;
process_args([], Mode, Opts, Bound) ->
    {Mode, Bound, lists:reverse(Opts), []};
process_args(_, _Mode, _Opts, _Bound) ->
    usage().

-ifdef(not_used).
tr([From|Cs], From, To) -> [To|tr(Cs,From,To)];
tr([C|Cs], From, To ) -> [C|tr(Cs,From,To)];
tr([], _From, _To) -> [].
-endif.

get_long_opt(Cs) ->
    {Name,AltName,Cs1} = get_option_name(Cs),
    case maps:find(Name, options()) of
	{ok,OptInfo=#{ long := Name }} -> {OptInfo,Cs1};
	{ok,OptInfo=#{ long := AltName }} -> {OptInfo,Cs1};
	_ -> false
    end.

get_short_opt(Cs) ->
    {Name,_,Cs1} = get_option_name(Cs),
    case maps:find(Name, options()) of
	{ok,OptInfo=#{ short := Name }} -> {OptInfo,Cs1};
	_ -> false
    end.
%%
%% option names are in ascii include letters _ - 
%% - may only be located in between groups of letter
%% _ may be any where
%%
get_option_name(Cs) ->
    get_option_name(Cs,false,[],[]).


get_option_name([$-|Cs],true,Alt,Acc) ->
    get_option_name(Cs,false,[$_|Alt],[$-|Acc]);
get_option_name([$_|Cs],_InName,Alt,Acc) ->
    get_option_name(Cs,false,[$_|Alt],[$-|Acc]);
get_option_name([C|Cs],_InName,Alt,Acc) when
      C >= $a, C =< $z; C >= $A, C =< $Z ->
    get_option_name(Cs,true,[C|Alt],[C|Acc]);
get_option_name(Cs,_InName,Alt,Acc) ->
    {lists:reverse(Acc), lists:reverse(Alt), Cs}.


match_value(Spec, [], [Val|As]) ->
    case match_val(Spec, Val) of
	{ok,Value} -> {ok,Value,As};
	false  -> false
    end;
match_value(Spec, [$=|Val], As) ->
    match_value(Spec, Val, As);
match_value(Spec, Val, As) ->
    case match_val(Spec, Val) of
	{ok,Value} -> {ok,Value,As};
	false  -> false
    end.

%% Match a value list
-ifdef(unused).
match_values(Spec,Vs,As) ->
    match_values(Spec,Vs,[],As).
-endif.

match_values(Spec,[V|Vs],Acc,As) ->
    case match_value(Spec,V,As) of
	{ok,Value,As1} ->
	    match_values(Spec,Vs,[Value|Acc],As1);
	false ->
	    false
    end;
match_values(_Spec,[],Acc,As) ->
    {ok,lists:reverse(Acc),As}.

match_val({multiple,Spec}, Val) ->
    match_val_(Spec, Val);
match_val(Spec, Val) ->
    %% io:format("match_val: ~p val=~p\n", [Spec, Val]),
    match_val_(Spec, Val).

match_val_(integer, Val) ->
    try list_to_integer(Val) of
	N -> {ok,N}
    catch
	error:badarg -> false
    end;
match_val_(unsigned, Val) ->
    try list_to_integer(Val) of
	N when N>=0 -> {ok,N};
	_ -> false
    catch
	error:badarg -> false
    end;
match_val_(float, Val) ->
    try list_to_float(Val) of
	F -> {ok,F}
    catch
	error:badarg ->
	    try list_to_integer(Val) of
		I -> {ok,float(I)}
	    catch
		error:badarg -> false
	    end
    end;
match_val_(float01, Val) ->
    try list_to_float(Val) of
	F -> {ok,F}
    catch
	error:badarg ->
	    try list_to_integer(Val) of
		I -> {ok,float(I)}
	    catch
		error:badarg -> false
	    end
    end;
match_val_(string, Val) ->
    {ok,Val};
match_val_({enum,List}, Val) when is_list(List) ->
    case proplists:get_value(Val,List) of
	undefined -> false;
	Enum -> {ok,Enum}
    end;
match_val_({list,variable},Val) ->
    %% trick
    {ok,Ts,_} = varp_scan:string("{"++Val++"}"),
    {ok,{_Decls,{vec,VarList}}} = varp_parse:parse(Ts),
    {ok, VarList};
match_val_({list,literal},Val) ->
    %% trick
    {ok,Ts,_} = varp_scan:string("{"++Val++"}"),
    {ok,{_Decls,{vec,LiteralList}}} = varp_parse:parse(Ts),
    {ok, LiteralList};
match_val_({list,Spec}, Val) ->
    Vals = string:tokens(Val, ", "),
    {ok,Vs,_} = match_values(Spec, Vals, [], []),
    {ok,Vs};
match_val_({union,Ts}, Val) ->
    match_union_(Ts, Val);
match_val_(void, "") ->
    {ok,true}.

match_union_([T|Ts], Val) ->
    case match_val_(T, Val) of
	false -> match_union_(Ts, Val);
	Result -> Result
    end;
match_union_([], _Val) ->
    false.


version() ->
    io:format("version ~s\n", [vsn()]),
    halt(0).

vsn() ->
    case application:get_key(varp,vsn) of
	{ok,V} -> V;
	undefined -> "undefined"
    end.

usage() ->
    io:format("varp: usage: varp [<Mode>] [Options] [Bindings] [files]\n"),
    io:format("  <Mode> = satisfy|falsify|prove|cnf|snf|version|help\n"),
    io:format("Options\n"),
    lists:foreach(
      fun(I=#{ long:=LongOpt, spec:=Spec,
	       default:=Def, description:=Desc }) ->
	      ShortOpt = maps:get(short,I,undefined),
	      Names = [["--",LongOpt],"|",["-",LongOpt],
		       if ShortOpt =:= undefined -> "";
			  true -> ["|","-",ShortOpt]
		       end],
	      if Spec =:= undefined ->
		      io:format("  ~s\n    ~s\n\n", 
				[Names,Desc]);
		 true ->
		      io:format("  ~s = ~s (~s)\n    ~s\n\n", 
				[Names,format_spec(Spec),
				 format_value(Def),
				 Desc])
	      end;
	 (#{ key := _Key }) -> %% ignore internal options
	      ok
      end, options_list()),
    halt(1).

usage(Opt) when is_list(Opt) ->
    io:format("varp: unknown option ~s\n", [Opt]),
    halt(1);
usage(Key) when is_atom(Key) ->
    case lists:keyfind(Key, 1, key_options()) of
	false -> 
	    io:format("varp: unknown option '~s'\n", [Key]),
	    halt(1);
	#{long:=Long, spec:=Spec} ->
	    io:format("varp: bad argument to option '~s', allowed values are ~s\n", 
		      [Long,format_spec(Spec)]),
	    halt(1)
    end.

usage(Key,Value) when is_atom(Key) ->
    case lists:keyfind(Key, 1, key_options()) of
	false ->
	    io:format("varp: unknown option '~s'\n", [Key]),
	    halt(1);
	#{long:=Long,spec:=Spec} ->
	    io:format("varp: bad argument ~s to option '~s', allowed values are ~s\n", 
		      [Value,Long,format_spec(Spec)]),
	    halt(1)
    end.

format_spec({multiple,T}) -> "{"++format_spec(T)++"}*";
format_spec({list,T}) -> "["++format_spec(T)++"]";
format_spec(unsigned) -> "unsigned integer";
format_spec(integer)  -> "integer";
format_spec(float)    -> "float";
format_spec(float01)  -> "float01";
format_spec(string)   -> "string";
format_spec(variable) -> "variable";
format_spec(literal)  -> "literal";
format_spec(atom)     -> "atom";
format_spec(void)     -> "void";
format_spec({enum,Vs}) when is_list(Vs) ->
    string:join([Name || {Name,_Enum} <- Vs], "|");
format_spec({union,Ts}) ->
    string:join([format_spec(T) || T <- Ts], "|").

format_value(N) when is_integer(N) -> integer_to_list(N);
format_value(F) when is_float(F) -> io_lib_format:fwrite_g(F);
format_value(A) when is_atom(A) -> atom_to_list(A);
format_value(L) when is_list(L) ->
    try list_to_binary(L) of
	Bin -> binary_to_list(Bin)
    catch
	error:_ -> 
	    string:join([format_value(V)||V<-L], ",")
    end.

%% saturation options
%% #{ 
%%     saturate => 1      :: unsigned()             %% saturation level
%%     pair => false      :: boolean()              %% add extra variable
%%     order => undefined :: order(),               %% variable order
%%     time  => infinity  :: infinity | integer(),  %% max time to run
%%     threshold => 0,    :: integer()              %% fixpoint threshold
%%     laps => infinity   :: infinity | integer(),  %% number of laps to run
%% }
%%

%%
%% Set options
%%

set_opts(Opts) when is_list(Opts) ->
    set_opts(Opts, default_opts()).

set_opts([{Opt,Value} | Opts], OptMap) ->
    ?dbg("set_opts: ~w ~p\n", [Opt,Value]),
    set_opts(Opts, setopt(Opt,Value,OptMap));
set_opts([], OptMap) ->
    OptMap.

default_opts() ->
    default_opts_(options_list(), #{ }).

default_opts_([#{ key := Key, default := Value}|Opts], OptMap) ->
    default_opts_(Opts, OptMap#{ Key => Value});
default_opts_([], OptMap) ->
    OptMap.

setopt(saturate, Level, OptMap) when is_integer(Level), Level > 0 ->
    List = getopt(saturations, OptMap),
    Sat  = get_saturate_opt(OptMap#{ saturate=>Level}),
    ?dbg("s = ~p\n", [Sat]),
    List1 = List ++ [Sat],
    OptMap#{ saturate => Level, saturations => List1 };
setopt(Key, Value, OptMap) when is_atom(Key) ->
    %% io:format("key=~w, value=~w\n", [Key,Value]),
    case maps:find(Key, options()) of
	{ok,OptInfo=#{ key := Key, spec := Spec }} ->
	    OldValue = case maps:find(Key, OptMap) of
			   error -> maps:get(default,OptInfo);
			   {ok,Value0} -> Value0
		       end,
	    case validate_value(Key, Spec, Value, OldValue) of
		{true,Value1} ->
		    %%io:format("~p => ~p\n", [Key,Value1]),
		    OptMap# { Key => Value1 };
		true ->
		    %%io:format("~p => ~p\n", [Key,Value]),
		    OptMap# { Key => Value };
		false ->
		    erlang:error(badarg)
	    end;
	_ ->
	    erlang:error(badkey)
    end.

get_saturate_opt(OptMap) ->
    #{
      saturate  => getopt(saturate, OptMap),
      pair      => getopt(pair, OptMap),
      order     => getopt(order, OptMap),
      time      => getopt(time, OptMap),
      threshold => getopt(threshold, OptMap),
      laps      => getopt(laps, OptMap)
     }.

%%
%% Check value against spec
%%
validate_value(log,{enum,_Enums},Level,_Old) when is_atom(Level) ->
    %% special? fixme!
    Map = #{  debug => ?LOG_LEVEL_DEBUG,
	      info  => ?LOG_LEVEL_INFO,
	      notice => ?LOG_LEVEL_NOTICE,
	      warning => ?LOG_LEVEL_WARNING,
	      error => ?LOG_LEVEL_ERROR,
	      critical => ?LOG_LEVEL_CRITICAL,
	      alert => ?LOG_LEVEL_ALERT,
	      emergency => ?LOG_LEVEL_EMERGENCY,
	      none => ?LOG_LEVEL_NONE },
    case maps:find(Level, Map) of
	error -> false;
	{ok,Value} -> {true,Value}
    end;
validate_value(log,{enum,_Enums},Level,_Old) when is_integer(Level) ->
    %% special? fixme!
    if Level >= ?LOG_LEVEL_NONE, Level =< ?LOG_LEVEL_DEBUG -> {true,Level};
       true -> false
    end;
validate_value(_Key,{enum,Enums},Value,_Old) ->
    case lists:keyfind(Value, 2, Enums) of
	false -> false;
	_ -> true
    end;
validate_value(_Key,unsigned,Value,_Old) ->
    is_integer(Value) andalso Value >= 0;
validate_value(_Key,integer,Value,_Old) ->
    is_integer(Value);
validate_value(_Key,float,Value,_Old) ->
    is_number(Value);
validate_value(_Key,float01,Value,_Old) ->
    is_float(Value) andalso (Value > 0.0) andalso (Value < 1.0);
validate_value(_Key,string,Value,_Old) ->
    is_string(Value);
validate_value(_Key,atom,Value,_Old) ->
    is_atom(Value);
validate_value(_Key,void, Value,_Old) ->
    (Value =:= "") orelse (value =:= undefined);
validate_value(_Key,term, _Value,_Old) ->  %% any value
    true;
validate_value(_Key,pred, Value,_Old) ->  %% predicate
    case Value of
	{p,_Name,_Args} when is_list(_Args) -> true;
	_ -> false
    end;
validate_value(_Key, predpat, Value,_Old) ->  %% predicate pattern
    case Value of
	{p,Name,Args} -> {true,{p,Name,['_' || _ <- Args]}};
	_ -> false
    end;
validate_value(_Key,literal, Value,_Old) ->  %% variable / pred / vector
    case Value of
	{'!', {p,_Name,_Args}} when is_list(_Args) -> true;
	{p,_Name,_Args} when is_list(_Args) -> true;
	{bit_index,_,_} -> true;
	{bit_range,_,_,_} -> true;
	{int,_,_} -> true;
	{uint,_,_} -> true;
	_ -> false
    end;
validate_value(_Key,variable, Value,_Old) ->  %% variable / pred / vector
    case Value of
	{p,_Name,_Args} when is_list(_Args) -> true;
	{bit_index,_,_} -> true;
	{bit_range,_,_,_} -> true;
	{int,_,_} -> true;
	{uint,_,_} -> true;
	_ -> false
    end;
validate_value(Key,{union,Types},Value,Old) -> %% alternative types
    validate_union(Key,Types,Value,Old);
validate_value(Key,{multiple,Type},Value,Old) -> %% list of Type
    case validate_value(Key,Type,Value,Old) of
	true ->
	    {true,Old++[Value]};
	false ->
	    false
    end;
validate_value(_Key,{append,list},ValueList,Old) ->
    if is_list(ValueList) ->
	    {true,Old ++ ValueList};
       true ->
	    false
    end;
validate_value(Key,{set,Type},Set,OldSet) ->
    Set1 = 
	lists:foldl(fun (_E,false) -> false;
			(E,Acc) ->
			    case validate_value(Key,Type,E,undefined) of
				true -> [E|Acc];
				{true,E1} -> [E1|Acc];
				false -> false
			    end
		    end, [], Set),
    case Set1 of
	false -> false;
	_ ->  {true,ordsets:union(Set1,OldSet)}
    end;
validate_value(Key,{list,Type},List,_OldList) ->
    List1 =
	lists:foldl(fun (_E,false) -> false;
			(E,Acc) ->
			    case validate_value(Key,Type,E,undefined) of
				true -> [E|Acc];
				{true,E1} -> [E1|Acc];
				false -> false
			    end
		    end, [], List),
    case List1 of
	false -> false;
	_ ->  {true,lists:reverse(List1)}
    end;
validate_value(_Key,{},Value,_Old) ->
    Value =:= {};
validate_value(Key,{T1},Value,_Old) ->
    case is_tuple(Value) andalso (tuple_size(Value) =:= 1) of
	true ->
	    try {valid_element(Key,T1,element(1,Value))} of
		Tuple -> {true,Tuple}
	    catch
		error:badarg -> false
	    end;
	false -> false
    end;
validate_value(Key,{T1,T2},Value,_Old) ->
    case is_tuple(Value) andalso (tuple_size(Value) =:= 2) of
	true ->
	    try {valid_element(Key,T1,element(1,Value)),
		 valid_element(Key,T2,element(2,Value))} of
		Tuple -> {true,Tuple}
	    catch
		error:badarg -> false
	    end;
	false -> false
    end;
validate_value(Key,{T1,T2,T3},Value,_Old) ->
    case is_tuple(Value) andalso (tuple_size(Value) =:= 3) of
	true ->
	    try {valid_element(Key,T1,element(1,Value)),
		 valid_element(Key,T2,element(2,Value)),
		 valid_element(Key,T3,element(3,Value))} of
		Tuple -> {true,Tuple}
	    catch
		error:badarg -> false
	    end;
	false -> false
    end.

validate_union(Key,[Type|Types],Value,Old) ->
    case validate_value(Key,Type,Value,Old) of
	true -> true;
	false -> validate_union(Key,Types,Value,Old)
    end;
validate_union(_Key,[],_Value,_Old) ->
    false.

valid_element(Key,Type,Value) ->
    case validate_value(Key,Type,Value,undefined) of
	true -> Value;
	{true,Value1} -> Value1
    end.

is_string([C|Cs]) when is_integer(C), C >= 0, C =< 16#ffffffff ->
    is_string(Cs);
is_string([]) -> true;
is_string(_) -> false.

%%
%% Get options
%%
getopt(Key, OptMap) ->
    case OptMap of
	#{ Key := Value }  -> Value
    end.
