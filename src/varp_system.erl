%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2026, Tony Rogvall
%%% @doc
%%%    Transition systems for bounded model checking.
%%%
%%%    A `system' definition is expanded, right after parsing, into the
%%%    declarations and macros that a hand written unrolling uses (see
%%%    formulas/varp/die_hard.varp and doc/MODEL_CHECKING.md):
%%%
%%%      system jugs {
%%%          state B:4, L:4;
%%%          input fill_big, ...;
%%%          init  B == 0 and L == 0;
%%%          next  fill_big implies next(B) == 5 and next(L) == L ...;
%%%          assume not (fill_big and fill_small);  // holds in every step
%%%          reach B == 4;
%%%      }
%%%
%%%    becomes
%%%
%%%      declare B($t):4, L($t):4;
%%%      declare fill_big($t), ...;
%%%      define jugs_init($t)  B($t) == 0 and L($t) == 0;
%%%      define jugs_next($t)  fill_big($t) implies B($t) == 5 and ... L($t-1);
%%%      define jugs_reach($k) jugs_init(0) and [A $s=1..$k] jugs_next($s)
%%%                            and B($k) == 4;
%%%      define jugs($k)       jugs_reach($k);
%%%
%%%    and, when the file has no formula of its own, the formula
%%%    `jugs(k)' with the bound `k' taken from the bindings.
%%% @end

-module(varp_system).

-export([expand_file/1, expand/1, format_error/1]).
-export([init_formula/1, next_formula/2, step_property/4, property_kind/2]).
-export([induction_formulas/3]).

-define(T, <<"$t">>).   %% step parameter of init/next/property macros
-define(K, <<"$k">>).   %% bound parameter of the unrolled properties
-define(S, <<"$s">>).   %% step variable of the unrolling quantifiers
-define(L, <<"$l">>).   %% loop step of a lasso
-define(BOUND, <<"k">>). %% the binding the default formula uses
-define(ALL, <<"$all">>).            %% the composition of all systems
-define(ALL_INIT, <<"$all_init">>).
-define(ALL_NEXT, <<"$all_next">>).

%% called from the grammar on every parsed file
%%
%% Several systems in one file compose synchronously: every step all of
%% them take a transition, a name declared in more than one system is
%% one shared variable, and every property is checked in that composed
%% world.  Each system keeps its own <name>_init/<name>_next macros; the
%% composed path is $all_init/$all_next, and the property macros use it.
expand_file({Defs0, Assigns, Formula}) ->
    %% templates become instances, channels become systems
    Defs = channels(instances(Defs0)),
    Names = [N || {system,N,_,_,_} <- Defs],
    Path = case Names of
	       [_,_|_] -> {?ALL_INIT, ?ALL_NEXT};
	       _ -> undefined
	   end,
    %% every system knows the state and input names of the others, so
    %% a shared variable need not be declared in the reading system
    Shared = shared_names(Defs),
    {Defs1, Systems} = expand_defs(Defs, {Path,Shared}, [], []),
    Defs2 = case Path of
		undefined -> Defs1;
		_ -> Defs1 ++ composite(Names, Systems)
	    end,
    Formula1 =
	case Formula of
	    undefined ->
		case [N || {N,true,_} <- Systems] of
		    [Name|_] -> {p, Name, [?BOUND]};
		    [] -> Formula
		end;
	    _ -> Formula
	end,
    {Defs2, Assigns, Formula1}.

expand_defs([S={system,Name,_Params,Items,Line}|Defs], PS={Path,Shared},
	    Acc, Systems) ->
    HasProperty = lists:any(fun(I) -> is_property(element(1,I)) end, Items),
    Expanded = try expand(S, Path, Shared)
	       catch error:{system,Reason} ->
		       erlang:error({system,Line,Reason})
	       end,
    [Info] = [I || {system_info,_,I} <- Expanded],
    expand_defs(Defs, PS, lists:reverse(Expanded) ++ Acc,
		[{Name,HasProperty,Info}|Systems]);
expand_defs([D|Defs], PS, Acc, Systems) ->
    expand_defs(Defs, PS, [D|Acc], Systems);
expand_defs([], _PS, Acc, Systems) ->
    {lists:reverse(Acc), lists:reverse(Systems)}.

%% {states, inputs} declared anywhere in the file
shared_names(Defs) ->
    Items = lists:append([Is || {system,_,_,Is,_} <- Defs]),
    #{ states => lists:usort([decl_name(D) || {state,Ds} <- Items, D <- Ds]),
       inputs => lists:usort([decl_name(D) || {input,Ds} <- Items, D <- Ds]) }.

%% ------------------------------------------------------------------
%% Instances: "instance p1 = producer(out = ch1);" copies the template
%% with its parameters bound to the given names and every other
%% declared name prefixed "p1_".  A template with instances is not a
%% system of its own; one without parameters used directly is.
%% ------------------------------------------------------------------

instances(Defs) ->
    Insts = [I || I = {instance,_,_,_,_} <- Defs],
    Templates = [S || S = {system,_,_,_,_} <- Defs],
    Instantiated = lists:usort([Sys || {instance,_,Sys,_,_} <- Insts]),
    lists:flatmap(
      fun({instance,Inst,Sys,Args,Line}) ->
	      case lists:keyfind(Sys, 2, Templates) of
		  false ->
		      erlang:error({system,Line,{no_such_system,Sys}});
		  {system,_,Params,Items,_} ->
		      Map = instance_map(Inst, param_names(Params), Args,
					 Items, Line),
		      [{system,Inst,[],rename(Items, Map),Line}]
	      end;
	 (S={system,Name,_,_,_}) ->
	      case lists:member(Name, Instantiated) of
		  true -> [];
		  false -> [S]
	      end;
	 (D) -> [D]
      end, Defs).

%% parameters come from the circuit_params grammar: [{in,[decl]},...]
param_names(Params) ->
    [decl_name(D) || {_Group,Ds} <- Params, D <- Ds].

instance_map(Inst, Params, Args, Items, Line) ->
    Bound = bind_args(Params, Args, Line),
    Declared = [decl_name(D) || {Tag,Ds} <- Items,
				Tag =:= state orelse Tag =:= input, D <- Ds],
    Locals = [{N, <<Inst/binary,"_",N/binary>>} || N <- Declared,
						 not lists:keymember(N, 1, Bound)],
    maps:from_list(Bound ++ Locals).

%% positional or "name = value" arguments; a value is a name
bind_args(Params, Args, Line) ->
    bind_args(Params, Args, Line, []).
bind_args(_Params, [], _Line, Acc) ->
    lists:reverse(Acc);
bind_args(Params, [{'=',P,V}|Args], Line, Acc) ->
    case lists:member(P, Params) of
	true -> bind_args(Params, Args, Line, [{P,arg_name(V, Line)}|Acc]);
	false -> erlang:error({system,Line,{no_such_parameter,P}})
    end;
bind_args([P|Params], [V|Args], Line, Acc) ->
    bind_args(Params, Args, Line, [{P,arg_name(V, Line)}|Acc]);
bind_args([], [_|_], Line, _Acc) ->
    erlang:error({system,Line,too_many_arguments}).

arg_name(N, _Line) when is_binary(N) -> N;
arg_name({p,N,[]}, _Line) -> N;
arg_name(V, Line) -> erlang:error({system,Line,{argument_not_a_name,V}}).

%% rename declared names and "name_field" (a channel end) in the body
rename(Name, Map) when is_binary(Name) ->
    case maps:find(Name, Map) of
	{ok,New} -> New;
	error -> rename_field(Name, Map)
    end;
rename({p,Name,Args}, Map) ->
    {p, rename(Name, Map), rename(Args, Map)};
rename({send,Ch,V,C}, Map) ->
    {send, rename(Ch, Map), rename(V, Map), rename(C, Map)};
rename({recv,Ch,X,C}, Map) ->
    {recv, rename(Ch, Map), rename(X, Map), rename(C, Map)};
rename(T, Map) when is_tuple(T) ->
    list_to_tuple([rename(X, Map) || X <- tuple_to_list(T)]);
rename(L, Map) when is_list(L) ->
    [rename(X, Map) || X <- L];
rename(X, _Map) ->
    X.

%% "src_n", "src_q0" with src a parameter bound to a channel
rename_field(Name, Map) ->
    case binary:split(Name, <<"_">>) of
	[Prefix, Field] ->
	    case maps:find(Prefix, Map) of
		{ok,New} -> <<New/binary,"_",Field/binary>>;
		error -> Name
	    end;
	_ -> Name
    end.

%% ------------------------------------------------------------------
%% Channels: "channel ch:8[2];" is a queue of two 8 bit values, a
%% system of its own with the slots and the count as state and the
%% ends as inputs:
%%   ch_send, ch_data   driven by the "send ch <value> when <cond>;"
%%   ch_recv            driven by the "recv ch <state> when <cond>;"
%%   ch_q0.., ch_n      the slots (ch_q0 is the head) and the count
%% A send into a full queue or a recv from an empty one is not a
%% transition.  An end no system drives is off.
%% ------------------------------------------------------------------

channels(Defs) ->
    Systems = [S || S = {system,_,_,_,_} <- Defs],
    Senders = lists:usort([Ch || {system,_,_,Is,_} <- Systems, {send,Ch,_,_} <- Is]),
    Receivers = lists:usort([Ch || {system,_,_,Is,_} <- Systems, {recv,Ch,_,_} <- Is]),
    lists:map(
      fun({channel,Name,Width,Depth,Line}) when is_integer(Depth), Depth >= 1 ->
	      channel_system(Name, Width, Depth, Line,
			     lists:member(Name, Senders),
			     lists:member(Name, Receivers));
	 ({channel,_Name,_Width,Depth,Line}) ->
	      erlang:error({system,Line,{channel_depth,Depth}});
	 (D) -> D
      end, Defs).

channel_system(Ch, Width, Depth, Line, HasSender, HasReceiver) ->
    F = fun(Field) -> <<Ch/binary,"_",Field/binary>> end,
    Q = fun(I) -> F(<<"q",(integer_to_binary(I))/binary>>) end,
    Send = F(<<"send">>), Data = F(<<"data">>), Recv = F(<<"recv">>),
    N = F(<<"n">>),
    NBits = max(1, bits(Depth)),
    Slots = lists:seq(0, Depth-1),
    Items =
	[{state, [{{p,Q(I),[]},uint,Width} || I <- Slots] ++ [{{p,N,[]},uint,NBits}]},
	 {input, [{p,Send,[]}, {{p,Data,[]},uint,Width}, {p,Recv,[]}]},
	 {init, {lop,eq,N,uconst(0)}},
	 %% blocking ends
	 {next, {lop,imp,Send,{lop,lt,N,uconst(Depth)}}},
	 {next, {lop,imp,Recv,{lop,gt,N,uconst(0)}}},
	 %% the count
	 {next, {lop,imp,{lop,'and',Send,{lop,'not',Recv}},
		 {lop,eq,{p,<<"next">>,[N]},{lop,add,N,uconst(1)}}}},
	 {next, {lop,imp,{lop,'and',Recv,{lop,'not',Send}},
		 {lop,eq,{p,<<"next">>,[N]},{lop,sub,N,uconst(1)}}}},
	 {next, {lop,imp,{lop,equ,Send,Recv},
		 {lop,eq,{p,<<"next">>,[N]},N}}}]
	++
	%% the slots: shift down on recv, the sent value lands at the
	%% first free slot after the shift
	lists:append(
	  [begin
	       Written = {lop,'and',Send,
			  {lop,'or',
			   {lop,'and',Recv,{lop,eq,N,uconst(I+1)}},
			   {lop,'and',{lop,'not',Recv},{lop,eq,N,uconst(I)}}}},
	       Above = if I+1 < Depth -> Q(I+1); true -> Q(I) end,
	       [{next, {lop,imp,Written,{lop,eq,{p,<<"next">>,[Q(I)]},Data}}},
		{next, {lop,imp,{lop,'and',{lop,'not',Written},Recv},
			{lop,eq,{p,<<"next">>,[Q(I)]},Above}}},
		{next, {lop,imp,{lop,'and',{lop,'not',Written},{lop,'not',Recv}},
			{lop,eq,{p,<<"next">>,[Q(I)]},Q(I)}}}]
	   end || I <- Slots])
	++ [{assume,{lop,'not',Send}} || not HasSender]
	++ [{assume,{lop,'not',Recv}} || not HasReceiver],
    {system, Ch, [], Items, Line}.

bits(V) when V < 2 -> 1;
bits(V) -> 1 + bits(V bsr 1).

uconst(V) -> {uint, bits(V), V}.

%% $all_init($t) and $all_next($t): the conjunction over the systems
composite(Names, Systems) ->
    [{define, {p,?ALL_INIT,[?T]},
      conj([{p,macro(N,"init"),[?T]} || N <- Names])},
     {define, {p,?ALL_NEXT,[?T]},
      conj([{p,macro(N,"next"),[?T]} || N <- Names])},
     %% the union of the states, for the lasso of "eventually"
     {system_info, ?ALL,
      #{ name => ?ALL, init => ?ALL_INIT, next => ?ALL_NEXT,
	 states => lists:usort(lists:append([maps:get(states,I) || {_,_,I} <- Systems])),
	 inputs => lists:usort(lists:append([maps:get(inputs,I) || {_,_,I} <- Systems])),
	 props => lists:append([maps:get(props,I) || {_,_,I} <- Systems]) }}].

format_error(next_outside_next) ->
    "next(...) is only allowed in the next item of a system";
format_error({next_of_non_state, _Arg}) ->
    "next(...) needs a state variable";
format_error({no_such_system, S}) ->
    lists:flatten(io_lib:format("instance of an unknown system ~s", [S]));
format_error({no_such_parameter, P}) ->
    lists:flatten(io_lib:format("the system has no parameter ~s", [P]));
format_error(too_many_arguments) ->
    "more arguments than the system has parameters";
format_error({argument_not_a_name, _V}) ->
    "an instance argument must be a name";
format_error({channel_depth, _D}) ->
    "channel depth must be a positive integer";
format_error(Reason) ->
    lists:flatten(io_lib:format("system: ~p", [Reason])).

is_property(invariant) -> true;
is_property(reach) -> true;
is_property(eventually) -> true;
is_property(_) -> false.

%% {system,Name,Params,Items,Line} -> [definition()]
expand(S) -> expand(S, undefined, #{ states => [], inputs => [] }).

%% Path: {InitMacro,NextMacro} of the composed path when the file has
%% several systems, undefined when the system is on its own.  Shared:
%% the state and input names of the other systems.
expand({system, Name, Params, Items, _Line}, Path, Shared) ->
    expand({system, Name, Params, Items}, Path, Shared);
expand({system, Name, _Params, Items}, Path, Shared) ->
    States = [decl_name(D) || {state,Ds} <- Items, D <- Ds],
    Inputs = [decl_name(D) || {input,Ds} <- Items, D <- Ds],
    %% own declarations first: they decide the kind of a name
    Vars = #{ states => States ++ (maps:get(states, Shared) -- Inputs),
	      inputs => Inputs ++ (maps:get(inputs, Shared) -- States) },
    Decls = [{declare, [index_decl(D) || D <- Ds]}
	     || {Tag,Ds} <- Items, Tag =:= state orelse Tag =:= input],
    Init = conj([E || {init,E} <- Items]),
    Next = conj([E || {next,E} <- Items] ++
		[channel_op(I) || I <- Items,
				  element(1,I) =:= send orelse element(1,I) =:= recv]),
    %% assumptions hold in every step: on the state and input of the
    %% step, so they go with init (step 0) and after every transition
    Assume = conj([E || {assume,E} <- Items]),
    InitName = macro(Name, "init"),
    NextName = macro(Name, "next"),
    Macros =
	[{define, {p,InitName,[?T]},
	  conj2(rewrite(Init, init, ?T, Vars), rewrite(Assume, prop, ?T, Vars))},
	 {define, {p,NextName,[?T]},
	  conj2(rewrite(Next, next, ?T, Vars), rewrite(Assume, prop, ?T, Vars))}],
    Props = [{K, E} || {K,E} <- Items, is_property(K)],
    {PathInit, PathNext} = case Path of
			       undefined -> {InitName, NextName};
			       _ -> Path
			   end,
    PropDefs =
	[{define, {p,macro(Name,K),[?K]},
	  property(K, E, PathInit, PathNext, Vars)} || {K,E} <- Props],
    Default =
	case Props of
	    [{K0,_}|_] ->
		[{define, {p,Name,[?K]}, {p,macro(Name,K0),[?K]}}];
	    [] -> []
	end,
    Info = #{ name => Name, init => PathInit, next => PathNext,
	      states => States, inputs => Inputs,
	      props => [{K, rewrite(E, prop, ?T, Vars)} || {K,E} <- Props] },
    Decls ++ Macros ++ PropDefs ++ Default ++ [{system_info, Name, Info}].

%%% ------------------------------------------------------------------
%%% Pieces for an incremental driver (varp_bmc): the system_info of a
%%% system ends up in the `systems' section, and these build the
%%% formula of one step at a time.
%%% ------------------------------------------------------------------

init_formula(#{ init := InitName }) ->
    {p, InitName, [{const,0}]}.

next_formula(#{ next := NextName }, K) ->
    {p, NextName, [{const,K}]}.

%% which property the file formula {p,Name,[Bound]} asks for:
%% the system name itself means the first property
property_kind(#{ name := Name, props := Props }, Name) ->
    case Props of
	[{Kind,_}|_] -> Kind;
	[] -> false
    end;
property_kind(#{ name := Name, props := Props }, PropName) ->
    case [Kind || {Kind,_} <- Props, macro(Name, Kind) =:= PropName] of
	[Kind|_] -> Kind;
	[] -> false
    end.

%% a violation of the property at bound K, given that bounds below K
%% and down to First were examined before
step_property(Info=#{ props := Props }, Kind, K, First) ->
    {Kind, P} = lists:keyfind(Kind, 1, Props),
    case Kind of
	reach ->
	    at(P, {const,K});
	invariant when K =:= First, K > 0 ->
	    {{'ANY',[{op,'=',?S,{range,{const,0},{const,K}}}]},
	     {lop,'not',at(P, ?S)}};
	invariant ->
	    {lop,'not',at(P, {const,K})};
	eventually when K =:= 0 ->
	    false;   %% a lasso needs at least one step
	eventually ->
	    #{ states := States } = Info,
	    Loop = conj([{lop,eq,{p,X,[{const,K}]},{p,X,[?L]}} || X <- States]),
	    {lop,'and',
	     {{'ALL',[{op,'=',?S,{range,{const,0},{const,K}}}]},
	      {lop,'not',at(P, ?S)}},
	     {{'ANY',[{op,'=',?L,{range,{const,0},{const,K-1}}}]}, Loop}}
    end.

%% k-induction for "invariant P" (or "reach P", read as the invariant
%% "not P").  {Base, Step} for the bound K:
%%   Base: init(0) and next(1..K) and (not P(0) or ... or not P(K))
%%   Step: next(1..K+1) and P(0..K) and not P(K+1) and all states distinct
%% Base SAT is a counterexample, Step UNSAT proves the invariant.
induction_formulas(Info=#{ init := InitName, next := NextName,
			   states := States, props := Props }, Kind, K) ->
    {Kind, P0} = lists:keyfind(Kind, 1, Props),
    P = case Kind of
	    invariant -> P0;
	    reach -> {lop,'not',P0}
	end,
    Next = fun(S) -> {p,NextName,[{const,S}]} end,
    Holds = fun(S) -> at(P, {const,S}) end,
    Fails = fun(S) -> {lop,'not',at(P, {const,S})} end,
    Base = conj([{p,InitName,[{const,0}]}] ++
		[Next(S) || S <- lists:seq(1,K)] ++
		[disj([Fails(S) || S <- lists:seq(0,K)])]),
    Distinct = [{lop,'not',conj([{lop,eq,{p,X,[{const,I}]},{p,X,[{const,J}]}}
				 || X <- States])}
		|| I <- lists:seq(0,K), J <- lists:seq(I+1,K+1)],
    Step = conj([Next(S) || S <- lists:seq(1,K+1)] ++
		[Holds(S) || S <- lists:seq(0,K)] ++
		[Fails(K+1)] ++ Distinct),
    _ = Info,
    {Base, Step}.

disj([]) -> false;
disj([E]) -> E;
disj([E|Es]) -> {lop,'or',E,disj(Es)}.

%% P with its step parameter $t replaced
at(P, Step) -> subst(P, ?T, Step).

subst(From, From, To) -> To;
subst(T, From, To) when is_tuple(T) ->
    list_to_tuple([subst(X, From, To) || X <- tuple_to_list(T)]);
subst(L, From, To) when is_list(L) ->
    [subst(X, From, To) || X <- L];
subst(X, _From, _To) -> X.

macro(Name, Suffix) when is_atom(Suffix) ->
    macro(Name, atom_to_list(Suffix));
macro(Name, Suffix) ->
    <<Name/binary, "_", (list_to_binary(Suffix))/binary>>.

conj([]) -> true;
conj([E]) -> E;
conj([E|Es]) -> {lop,'and',E,conj(Es)}.

conj2(E, true) -> E;
conj2(true, E) -> E;
conj2(A, B) -> {lop,'and',A,B}.

%% send ch V when C:  ch_send equ C and (C implies ch_data == V)
%% recv ch X when C:  ch_recv equ C and (C implies next(X) == ch_q0)
channel_op({send,Ch,V,C}) ->
    {lop,'and',
     {lop,equ,<<Ch/binary,"_send">>,C},
     {lop,imp,C,{lop,eq,<<Ch/binary,"_data">>,V}}};
channel_op({recv,Ch,X,C}) ->
    {lop,'and',
     {lop,equ,<<Ch/binary,"_recv">>,C},
     {lop,imp,C,{lop,eq,{p,<<"next">>,[X]},<<Ch/binary,"_q0">>}}}.

%% declarations: {p,Name,Params} | {{p,Name,Params},Type,Width}
decl_name({{p,Name,_},_Type,_Width}) -> Name;
decl_name({p,Name,_}) -> Name.

index_decl({{p,Name,Params},Type,Width}) ->
    {{p,Name,Params++[?T]},Type,Width};
index_decl({p,Name,Params}) ->
    {p,Name,Params++[?T]}.

%% ------------------------------------------------------------------
%% properties, unrolled to the bound $k
%% ------------------------------------------------------------------

%% init(0) and [A $s=1..$k] next($s)
path(InitName, NextName) ->
    {lop,'and',
     {p,InitName,[{const,0}]},
     {{'ALL',[{op,'=',?S,{range,{const,1},?K}}]}, {p,NextName,[?S]}}}.

property(reach, P, InitName, NextName, Vars) ->
    {lop,'and', path(InitName, NextName), rewrite(P, prop, ?K, Vars)};
property(invariant, P, InitName, NextName, Vars) ->
    {lop,'and', path(InitName, NextName),
     {{'ANY',[{op,'=',?S,{range,{const,0},?K}}]},
      {lop,'not',rewrite(P, prop, ?S, Vars)}}};
property(eventually, P, InitName, NextName, Vars) ->
    %% a lasso that avoids P: state($k) equals some earlier state($l)
    #{ states := States } = Vars,
    Loop = conj([{lop,eq,{p,X,[?K]},{p,X,[?L]}} || X <- States]),
    {lop,'and',
     {lop,'and', path(InitName, NextName),
      {{'ALL',[{op,'=',?S,{range,{const,0},?K}}]},
       {lop,'not',rewrite(P, prop, ?S, Vars)}}},
     {{'ANY',[{op,'=',?L,{range,{const,0},{op,sub,?K,{const,1}}}}]}, Loop}}.

%% ------------------------------------------------------------------
%% rewrite a body: state and input names get a step argument
%%   init/prop: X -> X(Idx)
%%   next:      X -> X(Idx-1), next(X) -> X(Idx), input u -> u(Idx)
%% ------------------------------------------------------------------

rewrite(E, Mode, Idx, Vars) ->
    rw(E, #{ mode => Mode, idx => Idx, vars => Vars, bound => [] }).

rw(Name, Ctx) when is_binary(Name) ->
    case var_kind(Name, Ctx) of
	none -> Name;
	Kind -> {p, Name, [step(Kind, Ctx)]}
    end;
rw({p, <<"next">>, [Arg]}, Ctx=#{ mode := next }) ->
    case next_arg(Arg, Ctx) of
	{Name, Params} ->
	    {p, Name, [rw(P, Ctx) || P <- Params] ++ [maps:get(idx, Ctx)]};
	false ->
	    erlang:error({system, {next_of_non_state, Arg}})
    end;
rw({p, <<"next">>, _}, _Ctx) ->
    erlang:error({system, next_outside_next});
rw({p, Name, Params}, Ctx) ->
    Params1 = [rw(P, Ctx) || P <- Params],
    case var_kind(Name, Ctx) of
	none -> {p, Name, Params1};
	Kind -> {p, Name, Params1 ++ [step(Kind, Ctx)]}
    end;
rw({{Q, Binds}, Body}, Ctx) when is_list(Binds) ->
    %% quantifier: its variables shadow state names in the body
    Bound = [V || {op,'=',V,_} <- Binds, is_binary(V)],
    Binds1 = [rw_bind(B, Ctx) || B <- Binds],
    Ctx1 = Ctx#{ bound => Bound ++ maps:get(bound, Ctx) },
    {{Q, Binds1}, rw(Body, Ctx1)};
rw(T, Ctx) when is_tuple(T) ->
    list_to_tuple([rw(X, Ctx) || X <- tuple_to_list(T)]);
rw(L, Ctx) when is_list(L) ->
    [rw(X, Ctx) || X <- L];
rw(X, _Ctx) ->
    X.

rw_bind({op,'=',V,Range}, Ctx) -> {op,'=',V,rw(Range, Ctx)};
rw_bind(B, Ctx) -> rw(B, Ctx).

next_arg(Name, _Ctx) when is_binary(Name) -> {Name, []};
next_arg({p, Name, Params}, _Ctx) -> {Name, Params};
next_arg(_, _) -> false.

var_kind(Name, #{ vars := #{ states := States, inputs := Inputs },
		  bound := Bound }) ->
    case lists:member(Name, Bound) of
	true -> none;
	false ->
	    case lists:member(Name, States) of
		true -> state;
		false ->
		    case lists:member(Name, Inputs) of
			true -> input;
			false -> none
		    end
	    end
    end.

step(state, #{ mode := next, idx := Idx }) -> {op,sub,Idx,{const,1}};
step(_Kind, #{ idx := Idx }) -> Idx.
