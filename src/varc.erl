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
-export([decide/2, decide/3]).
-export([subst/3]).
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
-export([get_nbindings/2, get_nbindings/3, get_nbindings/4]).
-export([get_bindings/2, get_bindings/3, get_bindings/4, get_bindings/5]).
-export([get_all_bindings/1]).
-export([get_number_of_bindings/2]).
-export([get_queue/1]).
-export([queue_first/1]).
-export([queue_next/2]).
-export([queue_clear/1]).
-export([order_sort/2, order_sort/3, order_sort/4]).
-export([order_first/2, order_last/2]).
-export([next_unbound/1, next_unbound/2]).
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
-export([get_clause_bcp_counter/1]).
-export([get_clause_bcp_counter/2]).
-export([get_bcp_counter/1]).
-export([get_conflict_counter/1]).
%% utils
-export([vec_create/3]).
-export([vec_step/2]).
-export([vec_extend/3]).
-export([vec_extend_rand/3]).
-export([vec_is_bound/2]).
-export([vec_value/2]).
-export([vec_bind/2]).
-export([intersect/1, intersect/2]).
-export([intersect_var/3]).
-export([install_bindings/2, install_bindings/3]).
-export([vec_sat/4, vec_sat/2]).
-export([vec_sat_lap/4]).
%% bindings
-export([mark_literals/2]).
-export([mark_intersect/2]).
-export([mark_list/1]).
%% -export([mark_tuple/1]).
%% -export([mark_intersect_var/3])

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
%%    {qtype,lifo|fifo|recursive} -- use lifo/fifo strategy in bcp
%%    {xref, boolean()}           -- use cross references
%%    {hash, boolean()}           -- install hash over clauses
%%    {edge, boolean()}           -- use edge instead of 2-clauses
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
%%    {queue, boolean()} -- clone bcp queue
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
%%       level|degree|is_atom|symbol
%%

variable_info(_Vp,Index,_What)
  when is_integer(Index), Index >= 0 ->
    ?nif_stub().

variable_info(Vp, Index) ->
    [{What,variable_info(Vp, Index, What)} || What <-variable_info_keys()].

variable_info_keys() ->
    [implication, implication_clause, implication_pos,
     level, degree, is_atom, symbol].

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


%% decide literal, affected by phase!
-spec decide(Vp::varc(), X::literal()) -> boolean().

decide(_Vp, X) when is_integer(X) ->
    ?nif_stub().


%% decide literal at level, affected by phase!
-spec decide(Vp::varc(), X::literal(), Level::integer()) -> boolean().

decide(_Vp, X, Level) when is_integer(X),
			   is_integer(Level) ->
    ?nif_stub().



%% X/Y substitute Y for X, replace all instances of Y with X
-spec subst(Vp::varc(), X::literal(), Y::literal()) -> boolean().

subst(_Vp, X, Y) when is_integer(X),
		      is_integer(Y) ->
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
    [{What,clause_info(Vp,Index,What)}||What<-[status,watch,length]].

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

get_nbindings(Vp,N,ClauseInfo) when is_integer(N), N>= 0 ->
    get_nbindings(Vp,N,ClauseInfo,false).

get_nbindings(_Vp,N,_ClauseInfo,_Trail) when is_integer(N), N>= 0 ->
    ?nif_stub().

get_all_bindings(V) ->
    Level = info(V, level),
    [{L,get_decision(V,L),get_bindings(V, L)} ||
	L <- lists:seq(Level,0,-1)].

%% get bindings on Level
get_bindings(Vp, Level) ->
    get_bindings(Vp, Level, false, false, false).

%% get bindings and possible clause info on Level
get_bindings(Vp, Level, ClauseInfo) ->
    get_bindings(Vp, Level, ClauseInfo, false, false).

get_bindings(_Vp, Level, ClauseInfo, Trail) ->
    get_bindings(_Vp, Level, ClauseInfo, Trail, false).

get_bindings(_Vp, _Level, _ClauseInfo, _Trail, _Tuple) ->
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

-spec order_first(Vp::varc(), [literal()]) -> ok.
order_first(_Vp, _VarList) ->
    ?nif_stub().

-spec order_last(Vp::varc(), List::[literal()]) -> ok.
order_last(_Vp, _List) ->
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
			  literal() | false.
next_unbound(_Vp) ->
    ?nif_stub().

-spec next_unbound(Vp::varc(), Last::literal()) ->
			  literal() | false.
next_unbound(_Vp, _Last) ->
    ?nif_stub().

%% utility to get a list of unbound literals
order_all(Vp) ->
    order_all_(Vp,next_unbound(Vp),[]).

order_all_(_Vp,false,Acc) ->
    lists:reverse(Acc);
order_all_(Vp,Xi,Acc) ->
    order_all_(Vp, next_unbound(Vp, Xi), [Xi|Acc]).

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
     size,
     level,
     literal_size,     %% 8,16,32,64 (sizeof literal)
     literal_integer,  %% true,false (integer or pointer)
     value_packing,    %% 1,4,undefined (variable value packing)
     edge,             %% true,false (edge_list is enabled or not)
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

get_clause_bcp_counter(Vp) ->
    info(Vp, clause_bcp_counter).

get_clause_bcp_counter(Vp,n) ->
    info(Vp, clause_n_counter);
get_clause_bcp_counter(Vp,2) ->
    info(Vp, clause_2_counter);
get_clause_bcp_counter(Vp,3) ->
    info(Vp, clause_3_counter);
get_clause_bcp_counter(Vp,dead) ->
    info(Vp, clause_d_counter);
get_clause_bcp_counter(Vp,edge_bcp) ->
    info(Vp, edge_2_counter);
get_clause_bcp_counter(Vp,edge_dead) ->
    info(Vp, edge_d_counter).

get_bcp_counter(Vp) ->
    info(Vp, bcp_counter).

get_conflict_counter(Vp) ->
    info(Vp, conflict_counter).

%% Utils

%% bcp over vector [X1,X2,...]
%% example X1,X2,X3
%% -X1 -X2 -X3  = E0
%% -X1 -X2  X3  = E1
%% -X1  X2 -X3  = E2
%% -X1  X2  X3  = E3
%%  X1 -X2 -X3  = E4
%%  X1 -X2  X3  = E5
%%  X1  X2 -X3  = E6
%%  X1  X2  X3  = E7
%% 
%%  Y10 = intersect(E0,E1,E2,E3)
%%  Y11 = intersect(E4,E5,E6,E7)
%%
%%  Y20 = intersect(E2,E3,E6,E7)
%%  Y21 = intersect(E0,E1,E4,E5)
%% 
%%  Y30 = intersect(E1,E3,E5,E7)
%%  Y31 = intersect(E0,E2,E4,E6)
%%
%%  intersect_var(X1, Y10, Y11)
%%  intersect_var(X2, Y20, Y21)
%%  intersect_var(X3, Y30, Y31)
%%
vec_sat_lap(V, K, Q, R) ->
    case vec_create(V, next_unbound(V), K) of
	[] -> true;
	Vec0 -> vec_sat_lap_(V, Vec0, Q, R)
    end.

%% FIXME? if a vector
%% contain a constant, we should probably update the
%% vector to speed up things (a bit)?
vec_sat_lap_(V, Vec0, Q, R) ->
    case vec_sat(V, Vec0, Q, R) of
	false -> false;
	true ->
	    case vec_step(V, Vec0) of
		false -> true;
		Vec1 -> 
		    ?debug("step ~w => ~w, ~w\n", 
			  [Vec0, Vec1, vec_is_bound(V, Vec1)]),
		    vec_sat_lap_(V, Vec1, Q, R)
	    end
    end.

vec_sat(V, V0, Q, R) ->
    ?debug("vec_sat = ~w\n", [V0]),
    V1 = vec_extend(V, V0, Q),
    V2 = vec_extend_rand(V, V1, R),
    vec_sat(V, V2).

vec_sat(V, Vec) when is_list(Vec) ->
    set_level(V, 1),
    case satv_(V,list_to_tuple(Vec)) of
	false ->
	    false;
	[] ->
	    true;
	Bs ->
	    ?debug("sat vec ~w = ~w\n", [Vec,Bs]),
	    set_level(V, 0),
	    case install_bindings(V, 0, Bs) of
		true ->
		    bcp(V);
		false ->
		    false
	    end
    end.

satv_(V, Vt) when is_tuple(Vt) ->
    N = tuple_size(Vt),
    Bt = bcpv_(V,(1 bsl N)-1, N, Vt, []),
    satvar_(V, 0, N, Vt, Bt, []).

%% eval for variable I 
satvar_(V, I, N, Vt, Bt, Bs) when I < N ->
    Js = lists:seq(0, (1 bsl N)-1),
    B1 = interv(V,[element(J+1,Bt) || J <- Js, (J band (1 bsl I)) =/= 0]),
    B0 = interv(V,[element(J+1,Bt) || J <- Js, (J band (1 bsl I)) =:= 0]),
    if B0 =:= false, B1 =:= false -> false;
       B0 =:= false -> satvar_(V, I+1, N, Vt, Bt, B1++Bs);
       B1 =:= false -> satvar_(V, I+1, N, Vt, Bt, B0++Bs);
       true -> 
	    Bsi = intersect_var(element(I+1,Vt), B0, B1),
	    satvar_(V, I+1, N, Vt, Bt, Bsi++Bs)
    end;
satvar_(_V, N, N, _Vt, _Bt, Bs) ->
    Bs.

interv0(_V, As) ->
    intersect(As).

interv(_V, []) -> false;
interv(V, [false|As]) -> interv(V, As);
interv(V, [A|As]) -> mark_literals(V, A), interv_(V, As).

interv_(V, [false|As]) -> interv_(V, As);
interv_(V, [A|As]) -> mark_intersect(V, A), interv_(V, As);
interv_(V, []) -> mark_list(V).

%% eval all 2^N combinations of Vt
bcpv_(_V,-1, _N, _Vt, Acc) ->
    list_to_tuple(Acc);
bcpv_(V,I, N, Vt, Acc) ->
    set_level(V, 1),
    case bindv(V, N, I, Vt) of
	false ->
	    undo_level(V, 1),
	    bcpv_(V,I-1, N, Vt, [false|Acc]);
	true ->
	    set_level(V, 2),
	    Ei = case bcp(V) of
		     false -> false;
		     true -> get_bindings(V, 2)
		 end,
	    undo_level(V, 2),
	    undo_level(V, 1),
	    bcpv_(V,I-1, N, Vt, [Ei|Acc])
    end.

%% given number I set vars in Vt according to bit
bindv(_V, 0, _I, _Vt) ->
    true;
bindv(V, J, I, Vt) ->
    Xj = if I band (1 bsl (J-1)) =/= 0 -> element(J,Vt); 
	    true -> -element(J,Vt)
	 end,
    bind(V,Xj) andalso bindv(V,J-1,I,Vt).


mark_literals(_V, _Bs) ->
    ?nif_stub().
    
mark_intersect(_V, _Bs) ->
    ?nif_stub().

mark_list(_V) ->
    ?nif_stub().

intersect_var(Var, Bs0, Bs1) ->
    intersect_var_(Var, Bs0, bindings_to_map(Bs1)).

intersect_var_(Var, [X|Bs0], Map) ->
    case maps:find(X, Map) of
	{ok,true} ->
	    [X | intersect_var_(Var, Bs0, Map)];
	error ->
	    case maps:find(-X, Map) of
		{ok,true} ->
		    [{Var,-X} | intersect_var_(Var, Bs0, Map)];
		error ->
		    intersect_var_(Var, Bs0, Map)
	    end
    end;
intersect_var_(_Var, [], _Map) ->
    [].

%% intersect a list of list of bindings - return bindings
intersect([]) -> false;
intersect([A]) -> A;
intersect([A,B]) -> intersect_(A,B);
intersect([false|Bs]) -> intersect(Bs);
intersect([A|Bs]) -> intersect__(Bs, bindings_to_map(A)).

intersect__([false|Bs], Map) -> intersect__(Bs, Map);
intersect__([B|Bs], Map) -> intersect__(Bs, inter_map(B, Map));
intersect__([], Map) -> map_to_bindings(Map).

%% intersect two binding lists
intersect(As, Bs) -> intersect_(As, Bs).

intersect_(false, Bs) -> Bs;
intersect_(As, false) -> As;
intersect_(As, Bs) -> inter_values(Bs, bindings_to_map(As)).

inter_map(Bs, Map) ->
    inter_map_(Bs, Map, #{}).

inter_map_([B|Bs], Map, Dst) ->
    case maps:find(B, Map) of
	{ok,true} -> inter_map_(Bs, Map, Dst#{ B => true });
	_ -> inter_map_(Bs, Map, Dst)
    end;
inter_map_([], _Map, Dst) ->
    Dst.

inter_values([B|Bs], Map) ->
    case maps:find(B, Map) of
	{ok,true} -> [B | inter_values(Bs, Map)];
	_ -> inter_values(Bs, Map)
    end;
inter_values([], _Map) ->
    [].

%% make map of bindings into list of bindings
map_to_bindings(Map) ->
    [ X || {X,true} <- maps:to_list(Map)].

%% make a set of bindings
bindings_to_map(As) ->
    bindings_to_map(As, #{}).
bindings_to_map([A|As], Map) ->
    bindings_to_map(As, Map#{ A => true });
bindings_to_map([],Map) ->
    Map.

install_bindings(V,Bs) ->
    install_bindings(V, info(V, level), Bs).

install_bindings(_V,_Level,[]) ->
    true;
install_bindings(V,Level,Bs) ->
    install_(V,Level,Bs).

install_(V,Level,[X|Xs]) when is_integer(X) ->
    true = bind(V, X),
    install_(V,Level,Xs);
install_(V,Level,[{X,X}|Xs]) ->
    install_(V,Level,Xs);
install_(V,Level=0,[{X,t}|Xs]) ->
    true = bind(V, X),
    install_(V,Level,Xs);
install_(V,Level=0,[{X,f}|Xs]) ->
    true = bind(V, -X),
    install_(V,Level,Xs);
install_(V,0,[{X,Y}|Xs]) ->
    Xa = variable_info(V, X, is_atom),
    Ya = variable_info(V, Y, is_atom),
    if Ya, not Xa ->
	    subst(V, Y, X);
       true ->
	    subst(V, X, Y)
    end,
    install_(V,0,Xs);
install_(V,_Level,[{_X,_Y}|Xs]) ->
    %% can not install X=Y on level > 0
    install_(V,_Level,Xs);
install_(_V,_Level,[]) ->
    true.

%%
vec_value(V, Vec) ->
    [case value(V, Xi) of
	 undefined -> u;
	 Vi -> Vi
     end || Xi <- Vec].

vec_bind(_V, []) ->
    true;
vec_bind(V, [Xi|Vec]) ->
    bind(V, Xi) andalso vec_bind(V, Vec).

%% read "vector" of unbound variables starting from Var (must be unbound)
%% assume there are at least K unbound variables (FIXME)
vec_create(_V, false, _K) ->
    [];
vec_create(V, Vi, K) ->
    vec_create_(V, Vi, K-1, [Vi]).

vec_create_(_V, _Vi, 0, Vec) -> 
    Vec;
vec_create_(V, Vi, I, Vec) ->
    case next_unbound(V, Vi) of
	false ->
	    case next_unbound(V) of
		false -> Vec;
		Vj -> vec_create_(V, Vj, I-1, [Vj|Vec])
	    end;
	Vj ->
	    vec_create_(V, Vj, I-1, [Vj|Vec])
    end.

%% add (at most) Q "next" elements to Vec (not already in Vec)
vec_extend(V, Vec, Q) ->
    vec_extend_(V, Vec, Q).

vec_extend_(_V, Vec, 0) -> Vec;
vec_extend_(V, Vec, I) -> 
    case next_unbound_skip(V, hd(Vec), Vec) of
	false -> Vec;
	V1 -> vec_extend_(V, [V1|Vec], I-1)
    end.

%% add (at most) R random elements to Vec (not already in Vec)
vec_extend_rand(V, Vec, R) ->
    N = varc:get_number_of_variables(V),
    M = varc:get_number_of_unbound_variables(V) - length(Vec),
    vec_extend_rand_(V, Vec, N, M, R).

vec_extend_rand_(_V, Vec, _N, _M, 0) -> Vec;
vec_extend_rand_(_V, Vec, _N, M, _I) when M =< 0 -> Vec;
vec_extend_rand_(V, Vec, N, M, I) ->
    V1 = next_rand_unbound_skip(V, N, Vec),
    vec_extend_rand_(V, [V1|Vec], N, M-1, I-1).

vec_is_bound(_V, []) ->
    false;
vec_is_bound(V, [Xi|Vec]) ->
    case is_bound(V, Xi) of
	true -> true;
	false -> vec_is_bound(V, Vec)
    end.

%% step vector (list) over variables
vec_step(V, Vec) ->
    vec_step(V, Vec, []).

vec_step(_V, [], _Skip) ->
    false;
vec_step(V, [Vi|Vec], Skip) ->
    case next_unbound_skip(V, Vi, Skip) of
	false ->
	    case vec_step(V, Vec, [Vi|Skip]) of
		false -> false;
		Vec1 = [Vj|_] ->
		    case next_unbound_skip(V, Vj, Skip) of
			false -> false;
			Vk -> [Vk|Vec1]
		    end
	    end;
	Vj -> [Vj|Vec]
    end.

next_unbound_skip(V, Vi, Skip) ->
    case next_unbound(V, Vi) of
	false -> false;
	Vj ->
	    case lists:member(Vj, Skip) of
		true -> next_unbound_skip(V, Vj, Skip);
		false -> Vj
	    end
    end.

%% Select a random variables, that is not member of Skip, among
%% variables in range 1..N
%% FIXME: this may loop too long if few unbound variables are available!
next_rand_unbound_skip(V, N, Skip) when N > 0 ->
    J = rand:uniform(N),
    case next_unbound(V, J) of
	false ->
	    next_rand_unbound_skip(V, N, Skip);
	V1 ->
	    case lists:member(V1, Skip) of
		true -> next_rand_unbound_skip(V, N, Skip);
		false -> V1
	    end
    end.
