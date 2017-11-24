%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2013, Tony Rogvall
%%% @doc
%%%    Option processing
%%% @end
%%% Created : 13 Dec 2013 by Tony Rogvall <tony@rogvall.se>

-module(varp_option).

-export([options/0]).
-export([process_args/4]).

-export([match_long_opt/3]).
-export([match_short_opt/3]).

-export([setopts/2, setopt/3, getopt/2]).

-include("option.hrl").
-include("log.hrl").

%%
%% Option format:
%% 
%%  Long may be given as
%%  --long 123
%%  --long=123
%%  -long 123
%%  Short Name
%%  -l 123
%%
-type option_type() :: unsigned | string | undefined | [{string(),atom()}].
-type option_spec() :: option_type() | {multiple,option_type()}.

-record(optinfo,
	{
	  long  :: string(),
	  short :: string(),
	  key   :: atom(),
	  spec :: option_spec(),
	  default :: term(),
	  description :: string()
	}).

options() ->
    Log = [{"debug",debug}, {"info",info},{"notice",notice},
	   {"warning",warning},{"error",error},{"critical",critical},
	   {"alert",alert},{"emergency",emergency},{"none",none}],
    Bool = [{"true", true}, {"false", false}],
    [ #optinfo{ long ="value",
	       short="v",
	       key=value,
	       spec=[{"true",true},
		     {"false",false},
		     {"none", none}],
	       default=none,
	       description="Main formula variable value."
	     },
      #optinfo { long="print",
		short="p",
		key=print,
		spec=[{"true",true},{"literal",literal},{"erlang",erlang},
		      {"model",model},{"false",false}],
		default=false,
		description="Print models when found."
	      },
      #optinfo { long="partial",
		key=partial,
		spec=Bool,
		default=false,
		description="Print partial models when possible."
	      },
      #optinfo { long="method",
		key=method,
		spec=[{"collect", collect}, {"count", count}],
		default=collect,
		description="Count or collect models."
	      },
      #optinfo { long="max",
		short="n",
		key=max,
		spec=unsigned,
		default=0,
		description="Max number of models to count or collect, 0=all."
	      },
      #optinfo { long="order",
		key=order,
		spec=[{"identity",identity},
		      {"reverse", reverse},
		      {"depth",depth},
		      {"occure",occure},
		      {"depth_occure",depth_occure},
		      {"occure_depth",occure_depth}],
		default=identity,
		description="Specifiy variable order."
	      },
      #optinfo { long="bcp",
		key=bcp,
		spec=Bool,
		default=false,
		description="Do not use equivalence classes."
	      },
      #optinfo { long="saturate",
		short="s",
		key=saturate,
		spec=unsigned, 
		default=0,
		description="Saturation vector width."
	      },
      #optinfo { long="backtrack",
		short="b",
		key=backtrack,
		spec=Bool,
		default=true,
		description="Use backtracking."
	      },
      #optinfo { long="pair",
		key=pair,
		spec=Bool,
		default=true,
		description="Add extra variable in saturation."
	      },
      #optinfo { long="assoc",
		key=assoc,
		spec=[{"left",left},
		      {"right",right},
		      {"middle",middle}], 
		default=left,
		description="Specify the order how all and any are built."
	      },
      #optinfo { long="threshold",
		key=threshold,
		spec=unsigned,
		default=0,
		description="Take more rounds in saturation"
	      },
      #optinfo { long="carry",
		key=carry,
		spec=[{"true",true},{"false",false},{"ignore",ignore}],
		default=ignore,
		description="How to handle carry in addition."
	      },
      #optinfo { long="borrow",
		key=borrow,
		spec=[{"true",true},{"false",false},{"ignore",ignore}],
		default=ignore,
		description="How to handle borrow in subtraction."
	      },
      #optinfo { long="divz",
		key=divz,
		spec=[{"true",true},{"false",false},{"ignore",ignore}],
		default=false,
		description="How to handle divide by zero."
	      },
      #optinfo { long="log",
		key=log, 
		spec=Log,
		default=none,
		description="Output log level."
	      },
      #optinfo { long="output",
		short="o",
		key=output,
		spec=string, 
		default="",
		description="Output file name."
	      },
      #optinfo { long="formula",
		short="f",
		key=formula,
		spec={multiple,string},
		default=[],
		description="Command line formula."
	      },
      #optinfo { long="version",
		short="v", 
		key=version,
		spec=string,
		default=vsn(),
		description="Report current version."
	      },
      #optinfo { long="help",
		short="h", 
		key=help,
		spec=void,
		default=undefined,
		description="This help."
	      }
    ].


%% process long options and values
process_args(["--"++LongOpt|As],Mode,Opts,Bound) ->
    case match_long_opt(LongOpt,As,options()) of
	false ->
	    usage(LongOpt);
	{#optinfo { key=help},_Val,_As1} ->
	    usage();
	{#optinfo { key=version},_Val,_As1} ->
	    version();
	{#optinfo { key=Key,spec=ValSpec},Val,As1} ->
	    case match_value(ValSpec,Val) of
		false ->
		    usage(Key,Val);
		{ok,Value} ->
		    process_args(As1,Mode,[{Key,Value}|Opts],Bound)
	    end
    end;
process_args(["-"++LongOpt|As],Mode,Opts,Bound) ->
    case match_long_opt(LongOpt,As,options()) of
	false ->
	    case match_short_opt(LongOpt,As,options()) of
		false ->
		    usage();
		{#optinfo { key=help },_Val,_As1} ->
		    usage();
		{#optinfo { key=version },_Val,_As1} ->
		    version();
		{#optinfo { key=Key, spec=ValSpec},Val,As1} ->
		    case match_value(ValSpec,Val) of
			false ->
			    usage(Key,Val);
			{ok,Value} ->
			    process_args(As1,Mode,[{Key,Value}|Opts],Bound)
		    end
	    end;
	{#optinfo { key=help},_Val,_As1} ->
	    usage();
	{#optinfo { key=version},_Val,_As1} ->
	    version();
	{#optinfo { key=Key,spec=ValSpec},Val,As1} ->
	    case match_value(ValSpec,Val) of
		false ->
		    usage(Key,Val);
		{ok,Value} ->
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
		if Value0 == "" -> 
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


match_value({multiple,Type}, Val) ->
    match_value(Type, Val);
match_value(integer, Val) ->
    case string:to_integer(Val) of
	{N, ""} -> {ok,N};
	_ -> false
    end;
match_value(unsigned, Val) ->
    case string:to_integer(Val) of
	{N, ""} when N>=0 -> {ok,N};
	_ -> false
    end;
match_value(string, Val) ->
    {ok,Val};
match_value(void, "") ->
    {ok, true};
match_value([{Value,Enum}|_Vs], Value) ->
    {ok, Enum};
match_value([_|Vs], Value) ->
    match_value(Vs, Value);
match_value([], _) ->
    false.

match_long_opt(LongOpt,As,[Opt|Opts]) ->
    case match_string(Opt#optinfo.long, LongOpt) of
	false ->
	    match_long_opt(LongOpt,As,Opts);
	"" when Opt#optinfo.spec == void -> %% no value!
	    {Opt,"",As};
	"" ->
	    case As of
		["=",Value|As1]  -> {Opt,Value,As1};
		["="++Value|As1] -> {Opt,Value,As1};
		[Value|As1]      -> {Opt,Value,As1};
		[] -> {Opt,"",[]}
	    end;
	"=" ->
	    case As of
		[Value|As1] -> {Opt,Value,As1};
		[] -> {Opt,"",[]}
	    end;
	"="++Value1 ->
	    {Opt,Value1,As};
	_ ->
	    usage(LongOpt)
    end;
match_long_opt(_LongOpt,_As,[]) ->
    false.

match_short_opt(ShortOpt,As,[Opt|Opts]) ->
    case match_string(Opt#optinfo.short, ShortOpt) of
	false ->
	    match_short_opt(ShortOpt,As,Opts);
	"" when Opt#optinfo.spec == void -> %% no value!
	    {Opt,"",As};
	More when Opt#optinfo.spec == void -> %% multi option
	    {Opt,"",[[$-|More]|As]};
	"" ->
	    case As of
		[Value|As1] -> {Opt,Value,As1};
		[] -> {Opt,"",[]}
	    end;
	Value ->
	    {Opt,Value,As}
    end;
match_short_opt(_ShortOpt,_As,[]) ->
    false.

match_string([C|Cs], [C|Ds]) ->
    match_string(Cs, Ds);
match_string([], Ds) ->
    Ds;
match_string(_, _) ->
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
      fun(#optinfo{long=LongOpt,short=ShortOpt,spec=Spec,
		  default=Def,description=Desc }) ->
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
      end, options()),
    halt(1).

usage(Opt) when is_list(Opt) ->
    io:format("varp: unknown option ~s\n", [Opt]),
    halt(1);    
usage(Key) when is_atom(Key) ->
    case lists:keyfind(Key, #optinfo.key, options()) of
	false -> 
	    io:format("varp: unknown option '~s'\n", [Key]),
	    halt(1);
	Opt ->
	    io:format("varp: bad argument to option '~s', allowed values are ~s\n", 
		      [Opt#optinfo.long,format_spec(Opt#optinfo.spec)]),
	    halt(1)
    end.

usage(Key,Value) when is_atom(Key) ->
    case lists:keyfind(Key, #optinfo.key, options()) of
	false ->
	    io:format("varp: unknown option '~s'\n", [Key]),
	    halt(1);
	Opt ->
	    io:format("varp: bad argument ~s to option '~s', allowed values are ~s\n", 
		      [Value,Opt#optinfo.long,format_spec(Opt#optinfo.spec)]),
	    halt(1)
    end.

format_spec({multiple,T}) -> "{"++format_spec(T)++"}*";
format_spec(unsigned) -> "unsigned integer";
format_spec(integer)  -> "integer";
format_spec(string)   -> "string";
format_spec(void)     -> "void";
format_spec(Vs) when is_list(Vs) ->
    string:join([Name || {Name,_Enum} <- Vs], "|").

format_value(N) when is_integer(N) -> integer_to_list(N);
format_value(A) when is_atom(A) -> atom_to_list(A);
format_value(L) when is_list(L) -> L.


%%
%% Set options
%%
setopts([{Opt,Value}|Opts], OptRec) ->
    setopts(Opts, setopt(Opt,Value,OptRec));
setopts([debug|Opts], OptRec) ->
    setopts(Opts, setopt(log, debug, OptRec));
setopts([Opt|Opts], OptRec) when is_atom(Opt) ->
    setopts(Opts, setopt(Opt,true,OptRec));
setopts([], OptRec) ->
    OptRec.

setopt(value,true,OptRec)  -> setopt_(#option.value,true,OptRec);
setopt(value,false,OptRec) -> setopt_(#option.value,false,OptRec);
setopt(value,none,OptRec)  -> setopt_(#option.value,none,OptRec);

setopt(env,Env,OptRec) when is_list(Env) -> 
    Meta = lists:foldl(
	     fun({X,V},E0) ->
		     E1 = proplists:delete(X,E0),
		     [{X,V} | E1]
	     end, OptRec#option.meta, Env),
    OptRec#option { meta = Meta };

setopt(defs,Ds,OptRec) when is_list(Ds) ->
    Defs = lists:foldl(
	      fun({Px,Def},E0) ->
		      E1 = proplists:delete(Px,E0),
		      [{Px,Def} | E1]
	      end, OptRec#option.defs, Ds),
    OptRec#option { defs = Defs };

setopt(decls,Ds,OptRec) when is_list(Ds) ->
    Decls = lists:foldl(
	      fun({Sign,Size,{p,Name,Args}},E0) ->
		      Args1 = ['_' || _ <- Args], %% anonymous list
		      Px = {p,Name,Args1},
		      E1 = proplists:delete(Px,E0),
		      [{Px,Sign,Size} | E1]
	      end, OptRec#option.decls, Ds),
    OptRec#option { decls = Decls };

setopt(code,Code,OptRec) ->
    OptRec#option { code = OptRec#option.code ++ Code };

setopt(print,true,OptRec)   -> setopt_(#option.print,true,OptRec);
setopt(print,false,OptRec)  -> setopt_(#option.print,false,OptRec);
setopt(print,model,OptRec)  -> setopt_(#option.print,model,OptRec);
setopt(print,literal,OptRec)  -> setopt_(#option.print,literal,OptRec);
setopt(print,erlang,OptRec)  -> setopt_(#option.print,erlang,OptRec);
setopt(partial,true,OptRec)   -> setopt_(#option.partial,true,OptRec);
setopt(partial,false,OptRec)  -> setopt_(#option.partial,false,OptRec);

setopt(method,collect,OptRec) -> setopt_(#option.method,collect,OptRec);
setopt(method,count,OptRec) -> setopt_(#option.method,count,OptRec);

setopt(max,N,OptRec) when is_integer(N), N>=0 ->
    setopt_(#option.max,N,OptRec);
%% fixme check all order options! (normalize?)
setopt(order,Order,OptRec) -> setopt_(#option.order,Order,OptRec);

setopt(bcp,Bool,OptRec) when is_boolean(Bool) -> 
    setopt_(#option.bcp, Bool, OptRec);

setopt(saturate,K,OptRec) when is_integer(K),K>=0 ->
    setopt_(#option.saturate,K,OptRec);
setopt(threshold,K,OptRec) when is_integer(K),K>=0 ->
    setopt_(#option.threshold,K,OptRec);

setopt(pair,true,OptRec) ->    setopt_(#option.pair,true,OptRec);
setopt(pair,false,OptRec) ->   setopt_(#option.pair,false,OptRec);

setopt(assoc,left,OptRec) ->    setopt_(#option.assoc,left,OptRec);
setopt(assoc,right,OptRec) ->   setopt_(#option.assoc,right,OptRec);
setopt(assoc,middle,OptRec) ->   setopt_(#option.assoc,middle,OptRec);

setopt(carry,true,OptRec)    ->    setopt_(#option.carry,true,OptRec);
setopt(carry,false,OptRec)   ->   setopt_(#option.carry,false,OptRec);
setopt(carry,ignore,OptRec)  ->  setopt_(#option.carry,ignore,OptRec);

setopt(borrow,true,OptRec)   ->   setopt_(#option.borrow,true,OptRec);
setopt(borrow,false,OptRec)  ->  setopt_(#option.borrow,false,OptRec);
setopt(borrow,ignore,OptRec) -> setopt_(#option.borrow,ignore,OptRec);

setopt(divz,true,OptRec) ->   setopt_(#option.divz,true,OptRec);
setopt(divz,false,OptRec) ->  setopt_(#option.divz,false,OptRec);
setopt(divz,ignore,OptRec) -> setopt_(#option.divz,ignore,OptRec);

setopt(log,debug,OptRec) -> setopt_(#option.log,?DEBUG,OptRec);
setopt(log,info,OptRec)  -> setopt_(#option.log,?INFO, OptRec);
setopt(log,notice,OptRec) -> setopt_(#option.log,?NOTICE,OptRec);
setopt(log,warning,OptRec) -> setopt_(#option.log,?WARNING,OptRec);
setopt(log,error,OptRec) -> setopt_(#option.log,?ERROR,OptRec);
setopt(log,critical,OptRec) -> setopt_(#option.log,?CRITICAL,OptRec);
setopt(log,alert,OptRec) -> setopt_(#option.log,?ALERT,OptRec);
setopt(log,emergency,OptRec) -> setopt_(#option.log,?EMERGENCY,OptRec);
setopt(log,none,OptRec) -> setopt_(#option.log,?LOG_NONE,OptRec);
setopt(log,Level,OptRec) when Level >= ?LOG_NONE, Level =< ?DEBUG -> 
    setopt_(#option.log,Level,OptRec);
setopt(backtrack,true,OptRec) -> setopt_(#option.backtrack,true,OptRec);
setopt(backtrack,false,OptRec) -> setopt_(#option.backtrack,false,OptRec);
setopt(formula,_,OptRec) -> OptRec.  %% not used internally

setopt_(KeyPos, Value, OptRec) ->
    setelement(KeyPos, OptRec, Value).

%%
%% Get options
%%
getopt(value,  OptRec)    -> OptRec#option.value;
getopt(print,  OptRec)    -> OptRec#option.print;
getopt(partial, OptRec)    -> OptRec#option.partial;
getopt(log,    OptRec)    -> OptRec#option.log;
getopt(debug,  OptRec)    -> OptRec#option.log =:= ?DEBUG;
getopt(method, OptRec)    -> OptRec#option.method;
getopt(max, OptRec)       -> OptRec#option.max;
getopt(order, OptRec)     -> OptRec#option.order;
getopt(carry,  OptRec)    -> OptRec#option.carry;
getopt(borrow, OptRec)    -> OptRec#option.borrow;
getopt(divz, OptRec)      -> OptRec#option.divz;
getopt(eval_bcp, OptRec)  -> OptRec#option.bcp;
getopt(saturate, OptRec)  -> OptRec#option.saturate;
getopt(threshold, OptRec) -> OptRec#option.threshold;
getopt(pair, OptRec)      -> OptRec#option.pair;
getopt(assoc, OptRec)     -> OptRec#option.assoc;
getopt(backtrack,OptRec)  -> OptRec#option.backtrack;
getopt(meta,OptRec) -> OptRec#option.meta;
getopt(defs,OptRec) -> OptRec#option.defs;
getopt(decls,OptRec) -> OptRec#option.decls;
getopt(code,OptRec) -> OptRec#option.code.

