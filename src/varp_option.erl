%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2013, Tony Rogvall
%%% @doc
%%%    Option processing
%%% @end
%%% Created : 13 Dec 2013 by Tony Rogvall <tony@rogvall.se>

-module(varp_option).

-compile(export_all).

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

-record(option,
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
    [ #option{ long ="value",
	       short="v",
	       key=value,
	       spec=[{"true",true},
		     {"false",false},
		     {"none", none}],
	       default=none,
	       description="Main formula variable value."
	     },
      #option { long="print",
		short="p",
		key=print,
		spec=[{"true",true},{"literal",literal},{"erlang",erlang},
		      {"model",model},{"false",false}],
		default=false,
		description="Print models when found."
	      },
      #option { long="partial",
		key=partial,
		spec=Bool,
		default=false,
		description="Print partial models when possible."
	      },
      #option { long="method",
		key=method,
		spec=[{"collect", collect}, {"count", count}],
		default=collect,
		description="Count or collect models."
	      },
      #option { long="max",
		short="n",
		key=max,
		spec=unsigned,
		default=0,
		description="Max number of models to count or collect, 0=all."
	      },
      #option { long="order",
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
      #option { long="bcp",
		key=bcp,
		spec=Bool,
		default=false,
		description="Do not use equivalence classes."
	      },
      #option { long="saturate",
		short="s",
		key=saturate,
		spec=unsigned, 
		default=0,
		description="Saturation vector width."
	      },
      #option { long="backtrack",
		short="b",
		key=backtrack,
		spec=Bool,
		default=true,
		description="Use backtracking."
	      },
      #option { long="pair",
		key=pair,
		spec=Bool,
		default=true,
		description="Add extra variable in saturation."
	      },
      #option { long="assoc",
		key=assoc,
		spec=[{"left",left},
		      {"right",right},
		      {"middle",middle}], 
		default=left,
		description="Specify the order how all and any are built."
	      },
      #option { long="threshold",
		key=threshold,
		spec=unsigned,
		default=0,
		description="Take more rounds in saturation"
	      },
      #option { long="carry",
		key=carry,
		spec=[{"true",true},{"false",false},{"ignore",ignore}],
		default=ignore,
		description="How to handle carry in addition."
	      },
      #option { long="borrow",
		key=borrow,
		spec=[{"true",true},{"false",false},{"ignore",ignore}],
		default=ignore,
		description="How to handle borrow in subtraction."
	      },
      #option { long="divz",
		key=divz,
		spec=[{"true",true},{"false",false},{"ignore",ignore}],
		default=false,
		description="How to handle divide by zero."
	      },
      #option { long="log",
		key=log, 
		spec=Log,
		default=none,
		description="Output log level."
	      },
      #option { long="output",
		short="o",
		key=output,
		spec=string, 
		default="",
		description="Output file name."
	      },
      #option { long="formula",
		short="f",
		key=formula,
		spec={multiple,string},
		default=[],
		description="Command line formula."
	      },
      #option { long="version",
		short="v", 
		key=version,
		spec=string,
		default=vsn(),
		description="Report current version."
	      },
      #option { long="help",
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
	{#option { key=help},_Val,_As1} ->
	    usage();
	{#option { key=version},_Val,_As1} ->
	    version();
	{#option { key=Key,spec=ValSpec},Val,As1} ->
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
		{#option { key=help },_Val,_As1} ->
		    usage();
		{#option { key=version },_Val,_As1} ->
		    version();
		{#option { key=Key, spec=ValSpec},Val,As1} ->
		    case match_value(ValSpec,Val) of
			false ->
			    usage(Key,Val);
			{ok,Value} ->
			    process_args(As1,Mode,[{Key,Value}|Opts],Bound)
		    end
	    end;
	{#option { key=help},_Val,_As1} ->
	    usage();
	{#option { key=version},_Val,_As1} ->
	    version();
	{#option { key=Key,spec=ValSpec},Val,As1} ->
	    case match_value(ValSpec,Val) of
		false ->
		    usage(Key,Val);
		{ok,Value} ->
		    process_args(As1,Mode,[{Key,Value}|Opts],Bound)
	    end
    end;
process_args([Var,"=",Value|As],Mode,Opts,Bound) ->
    V = list_to_atom(Var),
    case string:to_integer(Value) of
	{N,""} -> process_args(As,Mode,Opts,[{V,N}|Bound]);
	_ -> process_args(As,Mode,Opts,[{V,Value}|Bound])
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
	    V = list_to_atom(Var),
	    case string:to_integer(Value) of
		{N,""} -> process_args(As1,Mode,Opts,[{V,N}|Bound]);
		_ -> process_args(As1,Mode,Opts,[{V,Value}|Bound])
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
    case match_string(Opt#option.long, LongOpt) of
	false ->
	    match_long_opt(LongOpt,As,Opts);
	"" when Opt#option.spec == void -> %% no value!
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
    case match_string(Opt#option.short, ShortOpt) of
	false ->
	    match_short_opt(ShortOpt,As,Opts);
	"" when Opt#option.spec == void -> %% no value!
	    {Opt,"",As};
	More when Opt#option.spec == void -> %% multi option
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
      fun(#option{long=LongOpt,short=ShortOpt,spec=Spec,
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
    case lists:keyfind(Key, #option.key, options()) of
	false -> 
	    io:format("varp: unknown option '~s'\n", [Key]),
	    halt(1);
	Opt ->
	    io:format("varp: bad argument to option '~s', allowed values are ~s\n", 
		      [Opt#option.long,format_spec(Opt#option.spec)]),
	    halt(1)
    end.

usage(Key,Value) when is_atom(Key) ->
    case lists:keyfind(Key, #option.key, options()) of
	false ->
	    io:format("varp: unknown option '~s'\n", [Key]),
	    halt(1);
	Opt ->
	    io:format("varp: bad argument ~s to option '~s', allowed values are ~s\n", 
		      [Value,Opt#option.long,format_spec(Opt#option.spec)]),
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

