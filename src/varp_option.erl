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
-export([process_args/4]).

%% -include("varp_option.hrl").
-include("log.hrl").

%%
%% Option format:
%%  --long 123
%%  --long=123
%%  -long 123
%%  -l 123
%%  -l123
%%

-define(BOOL,{"true",true},{"1",true},{"false",false},{"0",false}).

options() ->    
    V1 = #{ long => "value",
	    short => "v",
	    key => value,
	    spec => {enums,[?BOOL,{"none", none}]},
	    default => none,
	    description => "Main formula variable value."
	  },
    V2 = #{ long => "print",
	    short => "p",
	    key => print,
	    spec => {enums,
		     [?BOOL,
		      {"literal",literal},
		      {"erlang",erlang},
		      {"model",model}]},
	    default => false,
	    description => "Print models when found."
	  },
    V3 = #{ long => "partial",
	    key => partial,
	    spec => {enums,[?BOOL]},
	    default => false,
	    description => "Print partial models when possible."
	  },
    V4 = #{ long => "method",
	    key => method,
	    spec => {enums,
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
	    spec => {enums,
		     [{"identity",identity},
		      {"reverse", reverse},
		      {"depth",depth},
		      {"occure",occure},
		      {"depth_occure",depth_occure},
		      {"occure_depth",occure_depth}]},
	    default => identity,
	    description => "Specifiy variable order."
	  },
    V7 = #{ long => "bcp",
	    key => bcp,
	    spec => {enums,[?BOOL]},
	    default => false,
	    description => "Do not use equivalence classes."
	  },
    V8 = #{ long => "saturate",
	    short => "s",
	    key => saturate,
	    spec => unsigned, 
	    default => 0,
	    description => "Saturation vector width."
	  },
    V9 = #{ long => "backtrack",
	    short => "b",
	    key => backtrack,
	    spec => {enums,[?BOOL]},
	    default => true,
	    description => "Use backtracking."
	  },
    V10 = #{ long => "pair",
	     key => pair,
	     spec => {enums,[?BOOL]},
	     default => true,
	     description => "Add extra variable in saturation."
	   },
    V11 = #{ long => "assoc",
	     key => assoc,
	     spec => {enums,
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
    V13 = #{ long => "carry",
	     key => carry,
	     spec => {enums,[?BOOL,{"ignore",ignore}]},
	     default => ignore,
	     description => "How to handle carry in addition."
	   },
    V14 = #{ long => "borrow",
	     key => borrow,
	     spec => {enums,[?BOOL,{"ignore",ignore}]},
	     default => ignore,
	     description => "How to handle borrow in subtraction."
	   },
    V15 = #{ long => "divz",
	     key => divz,
	     spec => {enums,[?BOOL,{"ignore",ignore}]},
	     default => false,
	     description => "How to handle divide by zero."
	   },
    V16 = #{ long => "log",
	     key => log,
	     spec => {enums,
		      [{"debug",?DEBUG},
		       {"info",?INFO},
		       {"notice",?NOTICE},
		       {"warning",?WARNING},
		       {"error",?ERROR},
		       {"critical",?CRITICAL},
		       {"alert",?ALERT},
		       {"emergency",?EMERGENCY},
		       {"none",?LOG_NONE}]},
	     default => ?LOG_NONE,
	     description => "Output log level."
	   },
    V17 = #{ long => "output",
	     short => "o",
	     key => output,
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
    %% now build a map from long/short => Vi (will be a literal)
    #{ "value" => V1, "v" => V1,
       "print" => V2, "p" => V2,
       "partial" => V3,
       "method"  => V4,
       "max" => V5, "n" => V5,
       "order" => V6,
       "bcp" => V7,
       "saturate" => V8, "s" => V8,
       "backtrack" => V9, "b" => V9,
       "pair" => V10,
       "assoc" => V11,
       "threshold" => V12,
       "carry" => V13,
       "borrow" => V14,
       "divz" => V15,
       "log" => V16,
       "output" => V17, "o" => V17,
       "formula" => V18, "f" => V18,
       "version" => V19, "V" => V19,
       "help" => V20, "h" => V20
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
    %% V = list_to_atom(Var),
    case string:to_integer(Value) of
	{N,""} -> process_args(As,Mode,Opts,[{Var,N}|Bound]);
	_ -> process_args(As,Mode,Opts,[{Var,Value}|Bound])
    end;
process_args([A|As],Mode,Opts,Bound) ->
    case string:chr(A,$=) of
	0 -> 
	    {Mode, Bound, Opts,[A|As]};
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
    {Mode, Bound, Opts, []};
process_args(_, _Mode, _Opts, _Bound) ->
    usage().

get_long_opt(Cs) ->
    {Name,Cs1} = get_option_name(Cs),
    case maps:find(Name, options()) of
	{ok,OptInfo=#{ long := Name }} -> {OptInfo,Cs1};
	_ -> false
    end.

get_short_opt(Cs) ->
    {Name,Cs1} = get_option_name(Cs),
    case maps:find(Name, options()) of
	{ok,OptInfo=#{ short := Name }} -> {OptInfo,Cs1};
	_ -> false
    end.
    
get_option_name(Cs) ->
    get_option_name(Cs,[]).

get_option_name([C|Cs],Acc) when 
      C >= $a, C =< $z; C >= $A, C =< $Z ->
    get_option_name(Cs,[C|Acc]);
get_option_name(Cs,Acc) ->
    {lists:reverse(Acc), Cs}.



match_value({multiple,Type}, Val, As) ->
    match_value(Type, Val, As);
match_value(void, "", As) ->
    {ok,true,As};
match_value(Spec, [$=|Val], As) ->
    case match_value(Spec, Val) of
	{ok,Value} -> {ok,Value,As};
	false  -> false
    end;
match_value(Spec, [], [Val|As]) ->
    case match_value(Spec, Val) of
	{ok,Value} -> {ok,Value,As};
	false  -> false
    end;
match_value(Spec, Val, As) ->
    case match_value(Spec, Val) of
	{ok,Value} -> {ok,Value,As};
	false  -> false
    end.

match_value(integer, Val) ->
    try list_to_integer(Val) of
	N -> {ok,N}
    catch
	error:badarg -> false
    end;
match_value(unsigned, Val) ->
    try list_to_integer(Val) of
	N when N>=0 -> {ok,N};
	_ -> false
    catch
	error:badarg -> false
    end;
match_value(string, Val) ->
    {ok,Val};
match_value({enums,List}, Val) when is_list(List) ->
    case proplists:get_value(Val,List) of
	undefined -> false;
	Enum -> {ok,Enum}
    end.

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
      fun(I=#{long:=LongOpt,spec:=Spec,
	      default:=Def,description:=Desc }) ->
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
	      end
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
format_spec(unsigned) -> "unsigned integer";
format_spec(integer)  -> "integer";
format_spec(string)   -> "string";
format_spec(void)     -> "void";
format_spec({enums,Vs}) when is_list(Vs) ->
    string:join([Name || {Name,_Enum} <- Vs], "|").

format_value(N) when is_integer(N) -> integer_to_list(N);
format_value(A) when is_atom(A) -> atom_to_list(A);
format_value(L) when is_list(L) -> L.


%%
%% Set options
%%

set_opts(Opts) when is_list(Opts) ->
    set_opts(Opts, default_opts()).

set_opts([{Opt,Value}|Opts], OptMap) ->
    set_opts(Opts, setopt(Opt,Value, OptMap));
set_opts([debug|Opts], OptMap) ->
    set_opts(Opts, setopt(log, debug, OptMap));
set_opts([Opt|Opts], OptMap) when is_atom(Opt) ->
    set_opts(Opts, setopt(Opt,true,OptMap));
set_opts([], OptMap) ->
    OptMap.

default_opts() ->
    default_opts_(options_list(), 
		  #{ decls => [],
		     defs  => [],
		     code  => [],
		     meta  => []}).

default_opts_([#{ key := Key, default := Value}|Opts], OptMap) ->
    default_opts_(Opts, setopt_(Key, Value, OptMap));
default_opts_([], OptMap) ->
    OptMap.

setopt(value,true,OptMap)  -> setopt_(value,true,OptMap);
setopt(value,false,OptMap) -> setopt_(value,false,OptMap);
setopt(value,none,OptMap)  -> setopt_(value,none,OptMap);
setopt(env,Env,OptMap) when is_list(Env) ->
    Meta = lists:foldl(
	     fun({X,V},E0) ->
		     E1 = proplists:delete(X,E0),
		     [{X,V} | E1]
	     end, maps:get(meta, OptMap), Env),
    OptMap#{ meta => Meta };
setopt(defs,Ds,OptMap) when is_list(Ds) ->
    Defs = lists:foldl(
	      fun({Px,Def},E0) ->
		      E1 = proplists:delete(Px,E0),
		      [{Px,Def} | E1]
	      end, maps:get(defs, OptMap), Ds),
    OptMap#{ defs => Defs };
setopt(decls,Ds,OptMap) when is_list(Ds) ->
    Decls = lists:foldl(
	      fun({Sign,Size,{p,Name,Args}},E0) ->
		      Args1 = ['_' || _ <- Args], %% anonymous list
		      Px = {p,Name,Args1},
		      E1 = proplists:delete(Px,E0),
		      [{Px,Sign,Size} | E1]
	      end, maps:get(decls, OptMap), Ds),
    OptMap#{ decls => Decls };
setopt(code,Code,OptMap) ->
    OptMap#{ code => maps:get(code, OptMap) ++ Code };
setopt(print,true,OptMap)   -> setopt_(print,true,OptMap);
setopt(print,false,OptMap)  -> setopt_(print,false,OptMap);
setopt(print,model,OptMap)  -> setopt_(print,model,OptMap);
setopt(print,literal,OptMap)  -> setopt_(print,literal,OptMap);
setopt(print,erlang,OptMap)  -> setopt_(print,erlang,OptMap);
setopt(partial,true,OptMap)   -> setopt_(partial,true,OptMap);
setopt(partial,false,OptMap)  -> setopt_(partial,false,OptMap);
setopt(method,collect,OptMap) -> setopt_(method,collect,OptMap);
setopt(method,count,OptMap) -> setopt_(method,count,OptMap);
setopt(max,N,OptMap) when is_integer(N), N>=0 ->
    setopt_(max,N,OptMap);
%% fixme check all order options! (normalize?)
setopt(order,Order,OptMap) -> setopt_(order,Order,OptMap);
setopt(bcp,Bool,OptMap) when is_boolean(Bool) ->
    setopt_(bcp, Bool, OptMap);
setopt(saturate,K,OptMap) when is_integer(K),K>=0 ->
    setopt_(saturate,K,OptMap);
setopt(threshold,K,OptMap) when is_integer(K),K>=0 ->
    setopt_(threshold,K,OptMap);
setopt(pair,true,OptMap) -> setopt_(pair,true,OptMap);
setopt(pair,false,OptMap) -> setopt_(pair,false,OptMap);
setopt(assoc,left,OptMap) -> setopt_(assoc,left,OptMap);
setopt(assoc,right,OptMap) -> setopt_(assoc,right,OptMap);
setopt(assoc,middle,OptMap) -> setopt_(assoc,middle,OptMap);
setopt(carry,true,OptMap)    ->    setopt_(carry,true,OptMap);
setopt(carry,false,OptMap)   ->   setopt_(carry,false,OptMap);
setopt(carry,ignore,OptMap)  ->  setopt_(carry,ignore,OptMap);
setopt(borrow,true,OptMap)   ->   setopt_(borrow,true,OptMap);
setopt(borrow,false,OptMap)  ->  setopt_(borrow,false,OptMap);
setopt(borrow,ignore,OptMap) -> setopt_(borrow,ignore,OptMap);
setopt(divz,true,OptMap) ->   setopt_(divz,true,OptMap);
setopt(divz,false,OptMap) ->  setopt_(divz,false,OptMap);
setopt(divz,ignore,OptMap) -> setopt_(divz,ignore,OptMap);
setopt(log,debug,OptMap) -> setopt_(log,?DEBUG,OptMap);
setopt(log,info,OptMap)  -> setopt_(log,?INFO, OptMap);
setopt(log,notice,OptMap) -> setopt_(log,?NOTICE,OptMap);
setopt(log,warning,OptMap) -> setopt_(log,?WARNING,OptMap);
setopt(log,error,OptMap) -> setopt_(log,?ERROR,OptMap);
setopt(log,critical,OptMap) -> setopt_(log,?CRITICAL,OptMap);
setopt(log,alert,OptMap) -> setopt_(log,?ALERT,OptMap);
setopt(log,emergency,OptMap) -> setopt_(log,?EMERGENCY,OptMap);
setopt(log,none,OptMap) -> setopt_(log,?LOG_NONE,OptMap);
setopt(log,Level,OptMap) when Level >= ?LOG_NONE, Level =< ?DEBUG -> 
    setopt_(log,Level,OptMap);
setopt(backtrack,true,OptMap) -> setopt_(backtrack,true,OptMap);
setopt(backtrack,false,OptMap) -> setopt_(backtrack,false,OptMap);
setopt(formula,_,OptMap) -> OptMap.  %% not used internally

setopt_(Key, Value, OptMap) ->
    OptMap#{ Key => Value }.

%%
%% Get options
%%
getopt(Key, OptMap) ->
    case OptMap of
	#{ Key := Value }  -> Value
    end.
