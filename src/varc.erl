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
-export([clone/1]).
-export([clone/2]).
-export([info/2]).
-export([config/3]).
-export([add_variable/1]).
-export([add_variable/2]).
-export([del_variable/2]).
-export([add_symbol/3]).
-export([get_symbol/2]).
-export([is_atom/2]).
-export([find_symbol/2]).
-export([variable_info/2, variable_info/3, variable_info_keys/0]).
-export([literal_info/2, literal_info/3, literal_info_keys/0]).
-export([value/2]).
-export([bind/2, bind/3]).
-export([subst/3]).
-export([key/3]).
-export([implication_clause/2]).
-export([implication_level/2]).
-export([implication_pos/2]).
-export([conflicting_clause/1]).
-export([conflicting_clause/2]).
-export([conflict/4]).
-export([minimize/2]).
-export([is_variable/2]).
-export([is_bound/2]).
-export([is_equal/3]).
-export([set_level/2]).
-export([undo_level/2]).
-export([keep_level/2]).
-export([move_level/3]).
-export([undo/1]).
-export([bcp/1]).
-export([nbcp/1]).
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
-export([clean_edges/2]).
-export([get_clauses/2]).
-export([get_clauses/3]).
-export([use_clause/2]).
-export([clause_info/2,clause_info/3]).
-export([get_latest_binding/1]).
-export([get_decision/2]).
-export([get_undo_state/2]).
-export([get_nbindings/2]).
-export([get_nbindings/3]).
-export([get_bindings/2]).
-export([get_bindings/3]).
-export([get_all_bindings/1]).
-export([get_number_of_bindings/2]).
-export([get_queue/1]).
-export([queue_first/1]).
-export([queue_next/2]).
-export([queue_clear/1]).
-export([order_sort/2, order_sort/3, order_sort/4]).
-export([order_sort_first/2, order_sort_last/2]).
-export([next_unbound/1]).
-export([first_unbound_index/1, next_unbound_index/2]).
-export([order_map/2]).
-export([order_all/1]).
-export([decay/2]).
-export([bump/3]).
-export([subscribe/2]).
-export([clauseset_size/2]).
-export([clauseset_offset/2, clauseset_offset/3]).
-export([clauseset_sort/2]).
-export([clauseset_first/1, clauseset_first/2]).
-export([clauseset_next/2]).
-export([set_user_count/3]).

-export([info/1, info_keys/0]).
-export([get_max_clause_length/1]).
-export([get_number_of_variables/1]).
-export([get_number_of_clauses/1]).
-export([get_number_of_dead_clauses/1]).
-export([get_number_of_edges/1]).
-export([get_number_of_dead_edges/1]).
-export([get_number_of_conflicting_clauses/1]).
-export([get_number_of_bound_variables/1]).
-export([get_number_of_unbound_variables/1]).
-export([get_clause_eval_counter/1]).
-export([get_clause_eval_counter/2]).
-export([get_bcp_counter/1]).
-export([get_conflict_counter/1]).

%% -define(debug, true).

-ifdef(debug).
-define(debug(F,A), io:format((F),(A))).
-else.
-define(debug(F,A), ok).
-endif.

-define(DELTA, 0).
-define(GAMMA, 1).
-define(BETA,  2).
-define(ALPHA, 3).

-type varc() :: reference().
-type literal() :: integer().
-type sort_key() :: integer().
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
%% new options
%%    {size, Size::unsigned()}    -- inital variable tavle size
%%    {grow, Grow::unsigned()}    -- variable table growth step
%%    {qtype,lifo|fifo|recursive} -- use lifo/fifo strategy in bcp
%%    {xref, boolean()}           -- use cross references
%%    {hash, boolean()}           -- install hash over clauses
%%    {edge, boolean()}           -- use edge instead of 2-clauses
%%    {activity,mvsids|off}       -- use activity in conflicts (off)
%%

new(Options) when is_list(Options) ->
    ?nif_stub().

%%
%% clone options 
%%    new options +
%%    {level, Level}     -- clone bindings up until level 'Level'
%%    {set, delta}       -- clone clauseset DELTA
%%    {set, gamma}       -- clone clauseset GAMMA
%%    {set, beta}        -- clone clauseset BETA
%%    {set, alpha}       -- clone clauseset ALPHA
%%    {queue, boolean()} -- clone eval queue
%%

clone(Vp) ->
    clone(Vp, []).

clone(_Vp, Options) when is_list(Options) ->
    ?nif_stub().

info(_Vp, Key) when is_atom(Key) ->
    ?nif_stub().

%% set config
%%    xref            -- turn on/off xref
%%    permanent       -- number of clauses that are permanent
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

variable_info(_Vp,Index,_What)
  when is_integer(Index), Index >= 0 ->
    ?nif_stub().

variable_info(Vp, Index) ->
    [{What,variable_info(Vp, Index, What)} || What <-variable_info_keys()].

variable_info_keys() ->
    [implication, implication_clause, implication_pos,
     activity, level, degree, is_atom, symbol].

literal_info(_Vp,Index,_What)
  when is_integer(Index), Index >= 0 ->
    ?nif_stub().

literal_info(Vp,Index) ->
    [{What,literal_info(Vp,Index,What)} || What <- literal_info_keys()].

literal_info_keys() ->
    [degree, user, edge, symbol].

%%
%% Get literal value 
%%
-spec value(Vp::varc(), Lit::literal()) -> t | f | undefined.

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

-spec key(Vp::varc(), Lit::literal(), K::integer()) -> float().
key(_Vp, Lit, _K) when is_integer(Lit) ->
    ?nif_stub().

-spec implication_clause(Vp::varc(), Lit::literal()) ->
				Cix::integer().
implication_clause(_Vp, Lit) when is_integer(Lit) ->
    ?nif_stub().

-spec implication_level(Vp::varc(), Lit::literal()) ->
			       Level::integer().
implication_level(_Vp, Lit) when is_integer(Lit) ->
    ?nif_stub().

-spec implication_pos(Vp::varc(), Lit::literal()) ->
			     Pos::integer().
implication_pos(_Vp, Lit) when is_integer(Lit) ->
    ?nif_stub().

-spec conflicting_clause(Vp::varc()) -> Cix::integer().
conflicting_clause(Vp) ->
    conflicting_clause(Vp, 0).

-spec conflicting_clause(Vp::varc(), Index::integer()) -> Cix::integer().
conflicting_clause(_Vp, _Index) ->
    ?nif_stub().

-spec conflict(Vp::varc(), Level::integer(), Bump::float(),
	       ConflictNum::integer()) -> ClauseIndex::integer().
conflict(_Vp, _Level, _Bump, _Index) ->
    ?nif_stub().    

-spec minimize(Vp::varc(), ClauseIndex::integer()) -> integer().
%% minimize the clause and return number of literals removed
minimize(_Vp, _CluseIndex) ->
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

undo(_Vp) ->
    ?nif_stub().

bcp(_Vp) ->
    ?nif_stub().

nbcp(_Vp) ->
    ?nif_stub().

-spec clauseset_size(Vp::varc(),Si::integer()) ->
			     integer().
clauseset_size(_Vp, _Si) ->
    ?nif_stub().    

-spec add_clause(Vp::varc(),Ls::[literal()]) ->
			false | error | integer().
add_clause(_Vp,Ls) when is_list(Ls) ->
    ?nif_stub().

-spec add_clause(Vp::varc(),Ls::[literal()],Si::0..3) ->
			false | error | integer().
add_clause(_Vp,Ls,Si) when is_list(Ls), is_integer(Si), Si>=0, Si=<3 ->
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

decay(_Vp,Decay) when is_number(Decay) ->
    ?nif_stub().

%% bump variable
bump(_Vp,_Lit,Bump) when is_number(Bump) ->
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

-spec move_clause(Vp::varc(),ClauseIndex::integer(),SI::integer()) ->
			 integer().
move_clause(_Vp,_Index,_Si) when
      is_integer(_Index), _Index >= 0, is_integer(_Si), _Si >= 0, _Si =< 3 ->
    ?nif_stub().

clean_clause(_Vp,Index)
  when is_integer(Index), Index >= 0 ->
    ?nif_stub().

clean_edges(_Vp,Lit)
  when is_integer(Lit), Lit >= 1 ->
    ?nif_stub().

get_clauses(Vp,Var) ->
    get_clauses(Vp,Var,literal).

get_clauses(_Vp,Var,How)
  when (How =:= variable orelse How =:= literal orelse How =:= watch),
       is_integer(Var), Var >= 0 ->
    ?nif_stub().

-spec queue_first(Vp::varc()) -> literal() | false.
queue_first(_Vp) ->
    ?nif_stub().

-spec queue_next(Vp::varc(), Literal::integer()) -> literal() | false.
queue_next(_Vp, _Lit) ->
    ?nif_stub().

-spec queue_clear(Vp::varc()) -> true.

queue_clear(_Vp) ->
    ?nif_stub().

%% get decision variable (bind) on Level
-spec get_decision(Vp::varc(), Level::integer()) ->
			  literal().
get_decision(_Vp, _Level) ->
    ?nif_stub().

-spec get_undo_state(Vp::varc(), Level::integer()) ->
			    'undefined'|'set'|'toggle'|'done'.
get_undo_state(_Vp, _Level) ->
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

get_all_bindings(V) ->
    Level = info(V, level),
    [{L,get_decision(V,L),get_bindings(V, L)} ||
	L <- lists:seq(Level,0,-1)].

%% get bindings on Level
get_bindings(Vp, Level) ->
    get_bindings(Vp, Level, false).

%% get bindings and possible clause info on Level
get_bindings(_Vp, Level, _ClauseInfo)
  when is_integer(Level), Level > 0 ->
    ?nif_stub().

get_number_of_bindings(_Vp, _Level) ->
    ?nif_stub().

-spec order_sort(Vp::varc(), Key1::sort_key()) -> integer().
			
order_sort(Vp, Key1) ->
    order_sort(Vp, Key1, 0).

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

-spec order_sort_last(Vp::varc(), ReversedVarList::[literal()]) -> ok.
%% The list of variables must be reversed!
order_sort_last(_Vp, _VarList) ->
    ?nif_stub().

clauseset_offset(_Vp, _Si) ->
    ?nif_stub().

clauseset_offset(_Vp, _Si, _Offset) ->
    ?nif_stub().

clauseset_sort(_Vp, _Si) ->
    ?nif_stub().    

%% return index to first clause | false
clauseset_first(Vp) ->
    clauseset_first(Vp, ?DELTA).

clauseset_first(_Vp, _Si) ->
    ?nif_stub().

%% return index to next clause | false
clauseset_next(_Vp, _Ix) ->
    ?nif_stub().

%% set user count (unsigned 32-bit) for sorting
set_user_count(_Vp, _Lit, _Value) ->
    ?nif_stub().

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

%% return next unbound literal or false
-spec next_unbound(Vp::varc()) ->
			  integer() | false.
next_unbound(_Vp) ->
    ?nif_stub().

-spec next_unbound_index(Vp::varc(), Index::integer()) ->
				integer() | false.
next_unbound_index(_Vp, _Index) ->
    ?nif_stub().

-spec first_unbound_index(Vp::varc()) ->
				 integer() | false.
first_unbound_index(_Vp) ->
    ?nif_stub().

%% return literal from index
-spec order_map(Vp::varc(), Index::integer()) -> literal().
order_map(_Vp, _Index) ->
    ?nif_stub().

%% utility to get a list of unbound literals
order_all(Vp) ->
    order_all_(Vp,[],first_unbound_index(Vp)).

order_all_(_Vp,Acc,false) ->
    lists:reverse(Acc);
order_all_(Vp,Acc,Index) ->
    L = order_map(Vp, Index),
    order_all_(Vp, [L|Acc], next_unbound_index(Vp, Index)).

info(Vp) ->
    [ {Key,info(Vp, Key)} || Key <- info_keys()].

info_keys() ->
    [
     max_clause_length,
     number_of_clauses,
     number_of_dead_clauses,
     number_of_edges,
     number_of_dead_edges,
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
     edge_2_counter,
     edge_d_counter,
     grow,
     size,
     level,
     literal_size,     %% 8,16,32,64 (sizeof literal)
     literal_integer,  %% true,false (integer or pointer)
     value_packing,    %% 1,4,undefined (variable value packing)
     edge,             %% true,false (edge_list is enabled or not)
     activity,         %% conflict activity is enabled (used in sort activity)
     xref              %% xref is used (need for saturate with substitution)
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

get_number_of_edges(Vp) ->
    info(Vp, number_of_edges).

get_number_of_dead_edges(Vp) ->
    info(Vp, number_of_dead_edges).

get_number_of_conflicting_clauses(Vp) ->
    info(Vp, number_of_conflicting_clauses).

get_max_clause_length(Vp) ->
    info(Vp, max_clause_length).

get_clause_eval_counter(Vp) ->
    info(Vp, clause_eval_counter).

get_clause_eval_counter(Vp,n) ->
    info(Vp, clause_n_counter);
get_clause_eval_counter(Vp,2) ->
    info(Vp, clause_2_counter);
get_clause_eval_counter(Vp,3) ->
    info(Vp, clause_3_counter);
get_clause_eval_counter(Vp,dead) ->
    info(Vp, clause_d_counter);
get_clause_eval_counter(Vp,edge_eval) ->
    info(Vp, edge_2_counter);
get_clause_eval_counter(Vp,edge_dead) ->
    info(Vp, edge_d_counter).

get_bcp_counter(Vp) ->
    info(Vp, bcp_counter).

get_conflict_counter(Vp) ->
    info(Vp, conflict_counter).
