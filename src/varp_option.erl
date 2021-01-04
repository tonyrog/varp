%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2013, Tony Rogvall
%%% @doc
%%%    Option processing
%%% @end
%%% Created : 13 Dec 2013 by Tony Rogvall <tony@rogvall.se>

-module(varp_option).

-export([getopt/2]).
-export([setopt/4]).
-export([usage/1, usage/2, usage/3]).

-export([process_args/4]).

-export([default_opts/1]).
-export([options_spec/1]).
-export([options_spec_list/1]).

%% -define(DEBUG, true).
-include("varp.hrl").

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
%% fixme: boolean options -lax == -l true -a true -x true
%% 


%% Given a option list construct a map
%% from keywords to options
%% Long :: string()  => OptMap
%% Long_ :: string() => OptMap
%% Short ::string()  => OptMap
%% Key :: atom()     => OptMap
options_spec(OptionInfoList) ->
    lists:foldl(
      fun(Info = #{ key := Key}, M0) ->
	      M1 = M0#{ Key => Info },
	      M2 = add_mapping(short, Info, M1),
	      M3 = add_mapping(long, Info, M2),
	      M4 = add_mapping(long, fun tr_/1, Info, M3),
	      M4
      end, #{}, OptionInfoList).

%% translate $- into $_
tr_([$-|Cs]) -> [$_|tr_(Cs)];
tr_([C|Cs]) ->  [C|tr_(Cs)];
tr_([]) -> [].

add_mapping(Key, Info, Map) ->
    add_mapping(Key, false, Info, Map).

add_mapping(Key, Rewrite, Info, Map) ->
    case maps:find(Key, Info) of
	error -> Map;
	{ok,Value} -> maps:put(rewrite(Rewrite,Value), Info, Map)
    end.

rewrite(false, Value) -> Value;
rewrite(Fun,Value) -> Fun(Value).
    

key_options(Spec) ->
    L = maps:fold(
	  fun(_K,V=#{key:=Key},Acc) ->
		  [{Key,V}|Acc]
	  end, [], Spec),
    lists:ukeysort(1, L).

%% generate a list of options from option map, with unique 'key'
options_spec_list(Spec) ->
    [V || {_,V} <- key_options(Spec)].


%% process long options and values
process_args(["--"++OptName|As],Spec,Map,Bound) ->
    case get_long_opt(OptName,Spec) of
	false -> usage(OptName, Spec);
	{#{ key:=help },_Val} -> usage(Spec);
	{#{ key:=version },_Val} -> version();
	{#{ key:=Key,spec:=Type },Val} ->
	    case match_value(Type,Val,As) of
		false -> usage(Spec);
		{ok,Value,As1} ->
		    process_args(As1,Spec,
				 insert_value(Key,Value,Type,Map),Bound)
	    end
    end;
process_args(["-"++OptName|As],Spec,Map,Bound) ->
    case get_long_opt(OptName,Spec) of
	false ->
	    case get_short_opt(OptName,Spec) of
		false -> usage(OptName, Spec);
		{#{ key:=help },_Val} -> usage(Spec);
		{#{ key:=version },_Val} -> version();
		{#{ key:=Key,spec:=Type },Val} ->
		    case match_value(Type,Val,As) of
			false -> usage(Spec);
			{ok,Value,As1} ->
			    process_args(As1,Spec,
					 insert_value(Key,Value,Type,Map),
					 Bound)
		    end
	    end;
	{#{ key:=help },_Val} -> usage(Spec);
	{#{ key:=version },_Val} -> version();
	{#{ key:=Key,spec:=Type },Val} ->
	    case match_value(Type,Val,As) of
		false -> usage(Key,Val,Spec);
		{ok,Value,As1} ->
		    process_args(As1,Spec,
				 insert_value(Key,Value,Type,Map),
				 Bound)
	    end
    end;
process_args([Var,"=",Value|As],Spec,Map,Bound) ->
    try list_to_integer(Value) of
	N ->
	    process_args(As,Spec,Map,[{Var,N}|Bound])
    catch
	error:badarg ->
	    process_args(As,Spec,Map,[{Var,Value}|Bound])
    end;
process_args([A|As],Spec,Map,Bound) ->
    case string:chr(A,$=) of
	0 -> 
	    {[A|As],Map,Bound};
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
		{N,""} -> process_args(As1,Spec,Map,[{Var,N}|Bound]);
		_ -> process_args(As1,Spec,Map,[{Var,Value}|Bound])
	    end
    end;
process_args([], _Spec, Map, Bound) ->
    {[], Map, Bound}.

insert_value(Key, Value, {multiple,_Type}, Map) ->
    List = maps:get(Key, Map, []),
    Map#{ Key=>List++[Value]};
insert_value(Key, Value, _Type, Map) ->
    Map#{ Key=>Value }.

-ifdef(not_used).
tr([From|Cs], From, To) -> [To|tr(Cs,From,To)];
tr([C|Cs], From, To ) -> [C|tr(Cs,From,To)];
tr([], _From, _To) -> [].
-endif.

get_long_opt(Cs,OptSpec) ->
    {Name,AltName,Cs1} = get_option_name(Cs),
    case maps:find(Name, OptSpec) of
	{ok,OptInfo=#{ long := Name }} -> {OptInfo,Cs1};
	{ok,OptInfo=#{ long := AltName }} -> {OptInfo,Cs1};
	_ -> false
    end.

get_short_opt(Cs,OptSpec) ->
    {Name,_,Cs1} = get_option_name(Cs),
    case maps:find(Name, OptSpec) of
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
    case lists:keyfind(Val, 1, List) of
	false -> false;
	{_, Enum} -> {ok,Enum}
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
    {ok,true};
match_val_(map, _Val) -> %% no map format yet!
    {ok,#{}}.


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

print_help({_Key,I=#{ long:=LongOpt, spec:=TypeSpec,
		      default:=Def, description:=Desc }}) ->
    ShortOpt = maps:get(short,I,undefined),
    Names = [["--",LongOpt],"|",["-",LongOpt],
	     if ShortOpt =:= undefined -> "";
		true -> ["|","-",ShortOpt]
	     end],
    if TypeSpec =:= undefined ->
	    io:format("  ~s\n    ~s\n\n", [Names,Desc]);
       true ->
	    io:format("  ~s = ~s (~s)\n    ~s\n\n", 
		      [Names,format_spec(TypeSpec),
		       format_value(Def),
		       Desc])
    end;
print_help({_Key,#{ key := _Key }}) -> %% ignore internal options
    ok.

usage(Spec) ->
    io:format("varp: usage: varp [<plugin> [Options]]* <bindings>* <files>*\n"),
    io:format("OPTIONS\n"),

    lists:foreach(fun(Opt) -> 
			  print_help(Opt) end,
		  key_options(Spec)),
    case application:get_env(varp, plugins) of
	undefined -> 
	    ok;
	{ok,Ps} -> 
	    lists:foreach(
	      fun({_,PluginName,Plugin}) ->
		      io:format("PLUGIN ~s OPTIONS\n", [PluginName]),
		      OptionList =Plugin:options(),
		      Spec1 = varp_option:options_spec(OptionList),
		      lists:foreach(
			fun(Opt) -> 
				print_help(Opt) 
			end, key_options(Spec1))
	      end, Ps)
    end,
    halt(1).

usage(Opt,_Spec) when is_list(Opt) ->
    io:format("varp: unknown option ~s\n", [Opt]),
    halt(1);
usage(Key,Spec) when is_atom(Key) ->
    case lists:keyfind(Key, 1, key_options(Spec)) of
	false -> 
	    io:format("varp: unknown option '~s'\n", [Key]),
	    halt(1);
	#{long:=Long, spec:=TypeSpec} ->
	    io:format("varp: bad argument to option '~s', allowed values are ~s\n", 
		      [Long,format_spec(TypeSpec)]),
	    halt(1)
    end.

usage(Key,Value,Spec) when is_atom(Key) ->
    case lists:keyfind(Key, 1, key_options(Spec)) of
	false ->
	    io:format("varp: unknown option '~s'\n", [Key]),
	    halt(1);
	#{long:=Long,spec:=TypeSpec} ->
	    io:format("varp: bad argument ~s to option '~s', allowed values are ~s\n", 
		      [Value,Long,format_spec(TypeSpec)]),
	    halt(1)
    end.

format_spec({multiple,T}) -> "{"++format_spec(T)++"}*";
format_spec({list,T}) -> "["++format_spec(T)++"]";
format_spec(map)      -> "map";
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

default_opts(OptionInfoList) ->
    default_opts_(OptionInfoList, #{ }).

default_opts_([#{ key := Key, default := Value}|OptionInfoList], OptMap) ->
    default_opts_(OptionInfoList, OptMap#{ Key => Value});
default_opts_([], OptMap) ->
    OptMap.

setopt(Key, Value, OptMap, OptSpec) when is_atom(Key) ->
    ?dbg0("key=~w, value=~w\n", [Key,Value]),
    ?dbg0("OptSpec = ~p\n", [OptSpec]),

    case maps:find(Key, OptSpec) of
	{ok,OptInfo=#{ key := Key, spec := Spec }} ->
	    OldValue = case maps:find(Key, OptMap) of
			   error -> maps:get(default,OptInfo);
			   {ok,Value0} -> Value0
		       end,
	    case validate_value(Key, Spec, Value, OldValue) of
		{true,Value1} ->
		    ?dbg0("~p => ~p\n", [Key,Value1]),
		    OptMap# { Key => Value1 };
		true ->
		    ?dbg0("~p => ~p\n", [Key,Value]),
		    OptMap# { Key => Value };
		false ->
		    erlang:error(badarg)
	    end;
	_ ->
	    io:format("key ~p not in ~p\n", [Key,OptSpec]),
	    erlang:error(badkey)
    end.

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
    is_number(Value) andalso (Value >= 0.0) andalso (Value =< 1.0);
validate_value(_Key,string,Value,_Old) ->
    is_string(Value);
validate_value(_Key,atom,Value,_Old) ->
    is_atom(Value);
validate_value(_Key,void, Value,_Old) ->
    (Value =:= "") orelse (value =:= undefined);
validate_value(_Key,map, Value,_Old) ->
    is_map(Value);
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
    ?GETOPT(Key, OptMap).
