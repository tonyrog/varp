%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2015, Tony Rogvall
%%% @doc
%%%    NIF interface to varc 
%%% @end
%%% Created : 20 Aug 2015 by Tony Rogvall <tony@rogvall.se>

-module(varc).

-on_load(init/0).

-export([new/0]).
-export([new/1]).
-export([info/2]).
-export([config/3]).
-export([add_variable/1]).
-export([add_variable/2]).
-export([del_variable/2]).
-export([add_symbol/3]).
-export([get_symbol/2]).
-export([is_atom/2]).
-export([find_symbol/2]).
-export([variable_info/2, variable_info/3]).
-export([literal_info/3]).
-export([value/2]).
-export([bind/2, bind/3]).
-export([subst/3]).
-export([key/3]).
-export([implication_clause/2]).
-export([conflicting_clause/1]).
-export([conflicting_clause/2]).
-export([is_variable/2]).
-export([is_bound/2]).
-export([is_equal/3]).
-export([set_level/2]).
-export([undo_level/2]).
-export([keep_level/2]).
-export([move_level/3]).
-export([eval/1]).
-export([add_clause/2]).
-export([find_clause/2]).
-export([get_clause/2]).
-export([get_clause/3]).
-export([get_clause/4]).
-export([del_clause/2]).
-export([compress_clause/2]).
-export([clean_clause/2]).
-export([clean_literal/2]).
-export([sort_none_permanent_clauses/1]).
-export([get_clauses/2]).
-export([get_clauses/3]).
-export([use_clause/2]).
-export([clause_info/2,clause_info/3]).
-export([get_queue/1]).
-export([get_queue_first/1]).
-export([get_queue_next/2]).
-export([get_latest_binding/1]).
-export([get_nbindings/2]).
-export([get_nbindings/3]).
-export([get_bindings/1]).
-export([get_bindings/2]).
-export([get_bindings/3]).
-export([order_init/1]).
-export([order_first/1, order_next/2, order_next/3]).
-export([order_sort/2, order_sort/3, order_sort/4]).
-export([order_sort_first/2, order_sort_last/2]).
-export([order_all/1]).
-export([decay/2]).
-export([subscribe/2]).
-export([clause_first/1]).
-export([clause_first_none_keep/1]).
-export([clause_next/2]).

-export([info/1]).
-export([info_keys/0]).
-export([get_max_clause_length/1]).
-export([get_number_of_variables/1]).
-export([get_number_of_clauses/1]).
-export([get_number_of_dead_clauses/1]).
-export([get_number_of_conflicting_clauses/1]).
-export([get_number_of_bound_variables/1]).
-export([get_number_of_unbound_variables/1]).
-export([get_clause_eval_counter/1]).
-export([get_clause_eval_counter/2]).
-export([get_eval_counter/1]).

%% -define(debug, true).

-ifdef(debug).
-define(debug(F,A), io:format((F),(A))).
-else.
-define(debug(F,A), ok).
-endif.

-type varc() :: reference().
-type literal() :: integer().
-type sort_key()  :: identity|random|occur|depth|
		     occur_depth|depth_occur|
		     occur_ascending|occur_descending|
		     depth_ascending|depth_descending|
		     occur_depth_ascending|occur_depth_descending|
		     depth_occur_ascending|depth_occur_descending.
-type sort_value() :: integer().

-define(nif_stub(),
	erlang:nif_error({nif_not_loaded,module,?MODULE,line,?LINE})).

init() ->
    Nif = filename:join([code:priv_dir(varp), "varc_nif"]),
    ?debug("Loading: ~s\n", [Nif]),
    erlang:load_nif(Nif, 0).

new() ->
    new([]).

%%
%% options
%%    {size, Size::unsigned()}   -- inital variable tavle size
%%    {grow, Grow::unsigned()}   -- variable table growth step
%%    {qtype,lifo|fifo}          -- use lifo/fifo strategy in eval
%%    {activity,boolean()}       -- use activity in conflicts (false)
%%

new(Options) when is_list(Options) ->
    ?nif_stub().

info(_Vp, Item) when is_atom(Item) ->
    ?nif_stub().

%% set config
%%    permanent       -- number of clauses that are permanent
%%    keep            -- size of lru cache for garbage collect conflict clauses
%%    max_conflicting -- max number of conflicting <= MAX_CONFLICTING
%% 
config(_Vp, Item, _Value) when is_atom(Item) ->
    ?nif_stub().

add_variable(Vp) ->
    add_variable(Vp, true).

add_variable(_Vp, IsAtom) when is_boolean(IsAtom) ->
    ?nif_stub().

del_variable(_Vp, _Index) when is_integer(_Index) ->
    ?nif_stub().

-spec add_symbol(Vp::varc(), Lit::literal(), Name::term()) -> ok.
add_symbol(_Vp, Lit, _Name)  when is_integer(Lit) ->
    ?nif_stub().

-spec get_symbol(Vp::varc(), Lit::literal()) -> [term()]. %% aliases
get_symbol(Vp, Lit) when is_integer(Lit) ->
    variable_info(Vp, Lit, symbol).

-spec is_atom(Vp::varc(), Lit::literal()) -> [term()]. %% aliases
is_atom(Vp, Lit) when is_integer(Lit) ->
    variable_info(Vp, Lit, is_atom).

%% find variable index from variable name (term or binary)
-spec find_symbol(Vp::varc(), Name::term()) -> false | literal().
find_symbol(_Vp, _Name) ->
    ?nif_stub().

%%
%% What::implication|implication_clause|implication_pos|
%%       activity|level|degree|is_atom|symbol
%%
variable_info(Vp, Index) ->
    [{What,variable_info(Vp, Index, What)} ||
	What <- [implication, implication_clause, implication_pos,
		 activity, level, degree, is_atom, symbol]].

variable_info(_Vp,Index,_What)
  when is_integer(Index), Index >= 0 ->
    ?nif_stub().

literal_info(_Vp,Index,_What)
  when is_integer(Index), Index >= 0 ->
    ?nif_stub().

%%
%% Get literal value 
%%
-spec value(Vp::varc(), Lit::literal()) -> integer().

value(_Vp, Lit) when is_integer(Lit) ->
    ?nif_stub().

%% bind literal
-spec bind(Vp::varc(), X::literal()) -> boolean().

bind(_Vp, X) when is_integer(X) ->
    ?nif_stub().


%% bind literal at level
-spec bind(Vp::varc(), X::literal(), Level::integer()) -> boolean().

bind(_Vp, X, Level) when is_integer(X),
			is_integer(Level) ->
    ?nif_stub().

%% X/Y substitute Y for X, replace all instances of Y with X
-spec subst(Vp::varc(), X::literal(), Y::literal()) -> boolean().

subst(_Vp, X, Y) when is_integer(X),
		      is_integer(Y) ->
    ?nif_stub().

-spec key(Vp::varc(), Lit::literal(), K::integer()) -> integer().
key(_Vp, Lit, _K) when is_integer(Lit) ->
    ?nif_stub().

-spec implication_clause(Vp::varc(), Lit::literal()) ->
				{Cix::integer(),Pos::integer(),Mark::integer()}.
implication_clause(_Vp, Lit) when is_integer(Lit) ->
    ?nif_stub().

-spec conflicting_clause(Vp::varc()) -> Cix::integer().
conflicting_clause(Vp) ->
    conflicting_clause(Vp, 0).

-spec conflicting_clause(Vp::varc(), Index::integer()) -> Cix::integer().
conflicting_clause(_Vp, _Index) ->
    ?nif_stub().

-spec is_variable(Vp::varc(), Lit::literal()) -> boolean().
is_variable(_Vp, Lit) when is_integer(Lit) ->
    ?nif_stub().

-spec is_bound(Vp::varc(), Lit::literal()) -> boolean().
is_bound(_Vp, Lit) when is_integer(Lit) ->
    ?nif_stub().

-spec is_equal(Vp::varc(), LitA::literal(), LitB::literal()) -> boolean().
is_equal(_Vp, LitA, LitB) when is_integer(LitA),
			       is_integer(LitB) ->
    ?nif_stub().

set_level(_Vp,Level) when is_integer(Level), Level >= 0 ->
    ?nif_stub().

-spec keep_level(Vp::varc(), Level::integer()) -> ok.

keep_level(_Vp,_Level) ->
    ?nif_stub().

-spec move_level(Vp::varc(), From::integer(), To::integer()) -> ok.

move_level(_Vp,_From,_To) ->
    ?nif_stub().

-spec undo_level(Vp::varc(), Level::integer()) -> ok.

undo_level(_Vp,_Level) ->
    ?nif_stub().

eval(_Vp) ->
    ?nif_stub().

-spec add_clause(Vp::varc(),Ls::[literal()]) ->
			false | error | integer().
add_clause(_Vp,Ls) when is_list(Ls) ->
    ?nif_stub().

-spec find_clause(Vp::varc(),Ls::[literal()]) ->
			 false | integer().
find_clause(_Vp,Ls) when is_list(Ls) ->
    ?nif_stub().

get_clause(Vp,Index) ->
    get_clause(Vp,Index,undefined,false).

get_clause(Vp,Index,Skip) ->
    get_clause(Vp,Index,Skip,false).

-spec get_clause(Vp::varc(), ClauseIndex::integer(),
		 SkipLiteral::literal(),Raw::boolean()) ->
			[literal()] | true.

get_clause(_Vp,Index,_SkipLiteral,Raw)
  when is_boolean(Raw), is_integer(Index), Index >= 0 ->
    ?nif_stub().


-spec compress_clause(Vp::varc(), ClauseIndex::integer()) -> binary().

compress_clause(_Vp,Index)
  when is_integer(Index), Index >= 0 ->
    ?nif_stub().

use_clause(_Vp,_Index) ->
    ?nif_stub().

decay(_Vp,Decay) when is_number(Decay), Decay >= 1.0 ->
    ?nif_stub().

subscribe(_Vp,Event) when is_atom(Event) ->
    ?nif_stub().

clause_info(_Vp,Index,_What)
  when is_integer(Index), Index >= 0 ->
    ?nif_stub().

clause_info(Vp,Index) ->
    [{What,clause_info(Vp,Index,What)}||What<-[status,watch]].

-spec del_clause(Vp::varc(), integer()|[literal()]) -> ok.
del_clause(_Vp,Index)
  when is_integer(Index), Index >= 0 ->
    ?nif_stub().

clean_clause(_Vp,Index)
  when is_integer(Index), Index >= 0 ->
    ?nif_stub().

clean_literal(_Vp,Lit)
  when is_integer(Lit), Lit >= 1 ->
    ?nif_stub().

sort_none_permanent_clauses(_Vp) ->
    ?nif_stub().

get_clauses(Vp,Var) ->
    get_clauses(Vp,Var,literal).

get_clauses(_Vp,Var,How)
  when (How =:= variable orelse How =:= literal orelse How =:= watch),
       is_integer(Var), Var >= 0 ->
    ?nif_stub().

get_queue_first(_Vp) ->
    ?nif_stub().

get_queue_next(_Vp, _Cix) ->
    ?nif_stub().

%% get the very latest binding
-spec get_latest_binding(Vp::varc()) -> {Var::integer(),Value::integer()}|false.
get_latest_binding(Vp) ->
    case get_nbindings(Vp,1,false) of
	[B={Var,_Val}|_] when is_integer(Var) -> B;
	_ -> false
    end.

get_nbindings(Vp,N) when is_integer(N), N>= 0 ->
    get_nbindings(Vp,N,false).

get_nbindings(_Vp,N,_ClauseInfo) when is_integer(N), N>= 0 ->
    ?nif_stub().

%% get all bindings
get_bindings(Vp) ->
    get_bindings(Vp, 0, false).

%% get bindings until mark
get_bindings(Vp, Mark) ->
    get_bindings(Vp, Mark, false).

%% get bindings and possible clause info until mark
get_bindings(_Vp, Mark, _ClauseInfo)
  when is_integer(Mark), Mark > 0 ->
    ?nif_stub().

%% initial index to use if using order_next, instead of order_first
order_init(_Vp) -> 
    0.

%% return {Ix,Var} | false
order_first(_Vp) ->
    ?nif_stub().

order_next(Vp, Ix) ->
    order_next(Vp, Ix, 0).

%% return next unbound variable, after skipping Skip number of unbound
-spec order_next(Vp::varc(), Ix::integer(), Skip::integer()) ->
			integer() | false.
order_next(_Vp, _Ix, _Skip) ->
    ?nif_stub().

-spec order_sort(Vp::varc(), Key1::sort_key()) -> integer().
			
order_sort(Vp, Key1) ->
    order_sort(Vp, Key1, undefined).

-spec order_sort(Vp::varc(), Key1::sort_key(), Key2::sort_key()) -> integer().

order_sort(Vp, Key1, Key2) ->
    order_sort(Vp, Key1, Key2, 0).

-spec order_sort(Vp::varc(), Key1::sort_key(), Key2::sort_key(),
		 Arg::sort_value()) -> 
			integer().
order_sort(_Vp, _Key1, _Key2, _Arg) ->
    ?nif_stub().

-spec order_sort_first(Vp::varc(), [literal()]) -> ok.
order_sort_first(_Vp, _VarList) ->
    ?nif_stub().

-spec order_sort_last(Vp::varc(), [literal()]) -> ok.
order_sort_last(_Vp, _VarList) ->
    ?nif_stub().

%% return index to first clause | false
clause_first(_Vp) ->
    ?nif_stub().

%% return index to first clause in the none! keep area | false
clause_first_none_keep(_Vp) ->
    ?nif_stub().

%% return index to next clause | false
clause_next(_Vp, _Ix) ->
    ?nif_stub().

%% Get all clauses in queue
get_queue(Vp) ->
    case get_queue_first(Vp) of
	false -> [];
	I ->
	    get_queue_(Vp,I,[I])
    end.

get_queue_(Vp,I,Acc) ->
    case get_queue_next(Vp,I) of
	false -> lists:reverse(Acc);
	J -> get_queue_(Vp,J,[J|Acc])
    end.

%% utility to get a list of unbound variables
order_all(V) ->
    case order_first(V) of
	false -> [];
	{I,Var} -> order_all_(V, I, [Var])
    end.

order_all_(V, I, Acc) ->
    case order_next(V,I) of
	false -> lists:reverse(Acc);
	{I1,Var} -> order_all_(V, I1, [Var|Acc])
    end.

info(Vp) ->
    [ {Key,info(Vp, Key)} || Key <- info_keys()].

info_keys() ->
    [
     max_clause_length,
     number_of_clauses,
     number_of_dead_clauses,
     number_of_conflicting_clauses,
     number_of_variables,
     number_of_bound_variables,
     number_of_unbound_variables,
     clause_eval_counter,
     eval_counter,
     undo_stack_size,
     value_stack_size,
     grow,
     size,
     permanent,        %% index of first permanent clause
     keep,
     level,
     literal_size,     %% 8,16,32,64 (sizeof literal)
     literal_integer,  %% true,false (integer or pointer)
     literal_signed,   %% true,false (when literal_integer)
     value_packing,    %% 1,4,undefined (variable value packing)
     edge_list         %% true,false (edge_list is enabled or not)
    ].

get_number_of_variables(Vp) ->
    info(Vp, number_of_variables).

get_number_of_bound_variables(Vp) ->
    info(Vp, number_of_bound_variables).

get_number_of_unbound_variables(Vp) ->
    info(Vp, number_of_unbound_variables).

get_number_of_clauses(Vp) ->
    info(Vp, number_of_clauses).

get_number_of_dead_clauses(Vp) ->
    info(Vp, number_of_dead_clauses).

get_number_of_conflicting_clauses(Vp) ->
    info(Vp, number_of_conflicting_clauses).

get_max_clause_length(Vp) ->
    info(Vp, max_clause_length).

get_clause_eval_counter(Vp) ->
    info(Vp, clause_eval_counter).

get_clause_eval_counter(Vp,0) ->
    info(Vp, clause_eval_counter);
get_clause_eval_counter(Vp,2) ->
    info(Vp, clause2_eval_counter);
get_clause_eval_counter(Vp,3) ->
    info(Vp, clause3_eval_counter);
get_clause_eval_counter(Vp,dead) ->
    info(Vp, dead_eval_counter).

get_eval_counter(Vp) ->
    info(Vp, eval_counter).
