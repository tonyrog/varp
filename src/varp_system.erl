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

-define(T, <<"$t">>).   %% step parameter of init/next/property macros
-define(K, <<"$k">>).   %% bound parameter of the unrolled properties
-define(S, <<"$s">>).   %% step variable of the unrolling quantifiers
-define(L, <<"$l">>).   %% loop step of a lasso
-define(BOUND, <<"k">>). %% the binding the default formula uses

%% called from the grammar on every parsed file
expand_file({Defs, Assigns, Formula}) ->
    {Defs1, Systems} = expand_defs(Defs, [], []),
    Formula1 =
	case Formula of
	    undefined ->
		case [N || {N,true} <- Systems] of
		    [Name|_] -> {p, Name, [?BOUND]};
		    [] -> Formula
		end;
	    _ -> Formula
	end,
    {Defs1, Assigns, Formula1}.

expand_defs([S={system,Name,_Params,Items,Line}|Defs], Acc, Systems) ->
    HasProperty = lists:any(fun({K,_}) -> is_property(K) end, Items),
    Expanded = try expand(S)
	       catch error:{system,Reason} ->
		       erlang:error({system,Line,Reason})
	       end,
    expand_defs(Defs, lists:reverse(Expanded) ++ Acc,
		[{Name,HasProperty}|Systems]);
expand_defs([D|Defs], Acc, Systems) ->
    expand_defs(Defs, [D|Acc], Systems);
expand_defs([], Acc, Systems) ->
    {lists:reverse(Acc), lists:reverse(Systems)}.

format_error(next_outside_next) ->
    "next(...) is only allowed in the next item of a system";
format_error({next_of_non_state, _Arg}) ->
    "next(...) needs a state variable";
format_error(Reason) ->
    lists:flatten(io_lib:format("system: ~p", [Reason])).

is_property(invariant) -> true;
is_property(reach) -> true;
is_property(eventually) -> true;
is_property(_) -> false.

%% {system,Name,Params,Items,Line} -> [definition()]
expand({system, Name, Params, Items, _Line}) ->
    expand({system, Name, Params, Items});
expand({system, Name, _Params, Items}) ->
    States = [decl_name(D) || {state,Ds} <- Items, D <- Ds],
    Inputs = [decl_name(D) || {input,Ds} <- Items, D <- Ds],
    Vars = #{ states => States, inputs => Inputs },
    Decls = [{declare, [index_decl(D) || D <- Ds]}
	     || {Tag,Ds} <- Items, Tag =:= state orelse Tag =:= input],
    Init = conj([E || {init,E} <- Items]),
    Next = conj([E || {next,E} <- Items]),
    InitName = macro(Name, "init"),
    NextName = macro(Name, "next"),
    Macros =
	[{define, {p,InitName,[?T]}, rewrite(Init, init, ?T, Vars)},
	 {define, {p,NextName,[?T]}, rewrite(Next, next, ?T, Vars)}],
    Props = [{K, E} || {K,E} <- Items, is_property(K)],
    PropDefs =
	[{define, {p,macro(Name,K),[?K]},
	  property(K, E, InitName, NextName, Vars)} || {K,E} <- Props],
    Default =
	case Props of
	    [{K0,_}|_] ->
		[{define, {p,Name,[?K]}, {p,macro(Name,K0),[?K]}}];
	    [] -> []
	end,
    Info = #{ name => Name, init => InitName, next => NextName,
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
