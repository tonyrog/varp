%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2015, Tony Rogvall
%%% @doc
%%%    NIF interface to varc 
%%% @end
%%% Created : 20 Aug 2015 by Tony Rogvall <tony@rogvall.se>

-module(varp_nif).

-on_load(init/0).

-export([new/0]).
-export([new/1]).
-export([clone/1]).
-export([clone/2]).
-export([info/2]).
-export([memory/1]).
-export([config/3]).
-export([add_variable/1]).
-export([add_variable/2]).
-export([add_variables/2]).
-export([add_variables/3]).
-export([del_variable/2]).
-export([add_symbol/3]).
-export([del_symbol/2]).
-export([get_symbol/2]).
-export([find_symbol/2]).
-export([first_symbol/1]).
-export([next_symbol/2]).
-export([variable_info/2, variable_info/3, variable_info_keys/0]).
-export([literal_info/2, literal_info/3, literal_info_keys/0]).
-export([value/2]).
-export([bound/2]).
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
-export([isused/2, isused/3]).
-export([isatom/2, isatom/3]).
-export([set_level/2]).
-export([undo_level/2]).
-export([keep_level/2]).
-export([move_level/3]).
-export([undo/1]).
-export([bcp/1, bcp/2, bcp/3]).
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
-export([get_clauses/2]).
-export([get_clauses/3]).
-export([use_clause/2]).
-export([clause_info/2,clause_info/3]).
-export([get_latest_binding/1]).
-export([get_decision/2]).
-export([get_undo_state/2]).
-export([get_nbindings/2, get_nbindings/3, get_nbindings/4]).
-export([get_bindings/2, get_bindings/3, get_bindings/4, get_bindings/5]).
-export([get_bindings_list/2, get_bindings_list/3, get_bindings_list/4]).
-export([get_bindings_trail/2]).
-export([get_all_bindings/1]).
-export([get_number_of_bindings/2]).
-export([get_queue/1]).
-export([queue_first/1]).
-export([queue_next/2]).
-export([queue_clear/1]).
-export([order_sort/2, order_sort/3, order_sort/4]).
-export([order_first/2, order_last/2]).
-export([next_unbound/1, next_unbound/2]).
-export([order_all/1, phase_all/1]).
-export([bump/3]).
-export([subscribe/2]).
-export([clauseset_size/2]).
-export([clauseset_offset/2, clauseset_offset/3]).
-export([clauseset_sort/2]).
-export([clauseset_first/1, clauseset_first/2]).
-export([clauseset_next/2]).
-export([set_user_count/3]).

-export([version/0]).
-export([i/0, i/1]).
-export([info/1, info_keys/0]).
-export([get_max_clause_length/1]).
-export([get_number_of_variables/1]).
-export([get_number_of_clauses/1]).
-export([get_number_of_dead_clauses/1]).
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
-export([vec_extend_friend/4]).
-export([vec_is_bound/2]).
-export([vec_value/2]).
-export([vec_bind/2]).
-export([intersect/1, intersect/2]).
-export([install_bindings/2, install_bindings/3]).
-export([vec_sat/6, vec_sat/5, vec_sat/2]).
-export([vec_sat_lap/5]).
%% bindings
-export([unmark/1]).
-export([mark/2, mark/3]).
-export([intersect_marks/2]).
-export([get_marked/1, get_marked/2]).
-export([intersect_var/3, intersect_var/4]).
-export([intersect_var0/4]).
%% util
-export([make_friend_map/1]).

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

-define(BINDING_AS_TUPLE, true).

-type varc() :: reference().
-type variable() :: pos_integer().
-type unsigned() :: non_neg_integer().
-type literal() :: integer().
-type sort_key() :: integer().
-type sort_value() :: integer().
-type binding() :: literal() | {literal(),literal()}.
-type bindings() :: [binding()] | {binding()}.  %% variable size tuple?
-type level() :: integer().
-type symbol() :: binary() | string() | term().

-define(nif_stub(),
	erlang:nif_error({nif_not_loaded,module,?MODULE,line,?LINE})).

init() ->
    Nif = filename:join([code:priv_dir(varp), "varp_nif"]),
    ?debug("Loading: ~s\n", [Nif]),
    erlang:load_nif(Nif, 0).

-spec new() -> varc().
	  
new() ->
    new(#{}).

-type new_options() :: 
	#{
	  %% inital variable table size
	  size  => unsigned(),
	  %% use lifo/fifo strategy in bcp
	  qtype => lifo|fifo|recursive,
	  %% use cross references
	  xref  => boolean(),
	  %% install hash over clauses
	  hash  => boolean(),
	  %% use phase saving
	  use_phase => boolean(),
	  %% initial phase
	  phase     => boolean()
	 }.

-spec new(new_options()) -> varc().

new(Options) when is_map(Options) ->
    ?nif_stub().

clone(Vp) ->
    clone(Vp, #{}).

-spec clone(Vp::varc(), Opts::clone_opts()) -> varc().
-type clone_opts() :: #{
			%% clone bindings up until level 'Level'
			level => unsigned(),
			%% clone clauseset(s)
			set   => clauseset()|[clauseset()],
			%% clone bcp queuea
			queue => boolean() }.
-type clauseset() :: delta|gamma|beta|alpha.


clone(_Vp, Options) when is_map(Options) ->
    ?nif_stub().


info(_Vp, Key) when is_atom(Key); is_list(Key) ->
    ?nif_stub().

%% set config
%%    xref            -- turn on/off xref
%%    permanent       -- number of clauses that are permanent
%%    max_conflicting -- max number of conflicting <= MAX_CONFLICTING
%% 
config(_Vp, Item, _Value) when is_atom(Item) ->
    ?nif_stub().

-spec add_variable(Vp::varc()) -> integer().
add_variable(_Vp) ->
    ?nif_stub().

-spec add_variable(Vp::varc(), IsAtom::boolean()) -> integer().
add_variable(_Vp, IsAtom) when is_boolean(IsAtom) ->
    ?nif_stub().

-spec add_variables(Vp::varc(), Num::integer()) -> 
	  {First::integer(), Last::integer()}.
add_variables(_Vp, Num) when is_integer(Num), Num>0 ->
    ?nif_stub().

-spec add_variables(Vp::varc(), Num::integer(), IsAtom::boolean()) -> 
	  {First::integer(), Last::integer()}.
add_variables(_Vp, Num, IsAtom) when
      is_integer(Num), Num>0, is_boolean(IsAtom) ->
    ?nif_stub().

del_variable(_Vp, _Index) when is_integer(_Index) ->
    ?nif_stub().

-spec add_symbol(Vp::varc(),Lit::literal()|[Lit::literal()], Name::term())-> ok.
add_symbol(_Vp, Lit, _Name)  when is_integer(Lit); is_list(Lit) ->
    ?nif_stub().

-spec del_symbol(Vp::varc(), Name::term()) -> ok.
del_symbol(_Vp, _Name)  ->
    ?nif_stub().

%% aliases
-spec get_symbol(Vp::varc(), Lit::literal()) -> [{term(),Pos::integer()}].
get_symbol(Vp, Lit) when is_integer(Lit) ->
    variable_info(Vp, Lit, symbol).

%% find variable index from variable name (term or binary)
-spec find_symbol(Vp::varc(), Name::term()) -> false | literal() | [literal()].
find_symbol(_Vp, _Name) ->
    ?nif_stub().

%% get first symbol
-spec first_symbol(Vp::varc()) -> false | symbol().
first_symbol(_Vp) ->
    ?nif_stub().

-spec next_symbol(Vp::varc(), Symbol::symbol()) -> false | symbol().
next_symbol(_Vp, _Symbol) ->
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
     level, phase, degree, is_atom, is_used, symbol].

literal_info(_Vp,Index,_What)
  when is_integer(Index), Index >= 0 ->
    ?nif_stub().

literal_info(Vp,Index) ->
    [{What,literal_info(Vp,Index,What)} || What <- literal_info_keys()].

literal_info_keys() ->
    [degree, user, xref, symbol].

%%
%% Get literal value 
%%
-spec value(Vp::varc(), Lit::literal()) -> true | false | undefined.

value(_Vp, Lit) when is_integer(Lit) ->
    ?nif_stub().

%% Get literal binding
-spec bound(Vp::varc(), Lit::literal()) -> 
	  true | false | literal() | undefined.

bound(_Vp, Lit) when is_integer(Lit) ->
    ?nif_stub().

%% bind literal
-spec bind(Vp::varc(), X::literal()) -> boolean().

bind(_Vp, X) when is_integer(X) ->
    ?nif_stub().


%% bind literal at level
-spec bind(Vp::varc(), X::literal(), Level::level()) -> boolean().

bind(_Vp, X, Level) when is_integer(X),
			 is_integer(Level) ->
    ?nif_stub().


%% decide literal, affected by phase!
-spec decide(Vp::varc(), X::literal()) -> boolean().

decide(_Vp, X) when is_integer(X) ->
    ?nif_stub().


%% decide literal at level, affected by phase!
-spec decide(Vp::varc(), X::literal(), Level::level()) -> boolean().

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
	  Level::level().
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

-spec conflict(Vp::varc(), Level::level(), Bump::number(),
	       ConflictNum::integer()) -> ClauseIndex::integer() | undefined.
conflict(_Vp, _Level, _Bump, _Index) ->
    ?nif_stub().    

-spec minimize(Vp::varc(), ClauseIndex::integer()) -> integer() | undefined.
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

-spec isused(Vp::varc(), Var::literal()) -> boolean().
isused(_Vp, Var) when is_integer(Var) ->
    ?nif_stub().

-spec isused(Vp::varc(), Var::literal(), Status::boolean()) -> boolean().
isused(_Vp, Var, Status) when is_integer(Var), is_boolean(Status) ->
    ?nif_stub().

-spec isatom(Vp::varc(), Var::literal()) -> boolean().
isatom(_Vp, Var) when is_integer(Var) ->
    ?nif_stub().

-spec isatom(Vp::varc(), Var::literal(), Status::boolean()) -> boolean().
isatom(_Vp, Var, Status) when is_integer(Var), is_boolean(Status) ->
    ?nif_stub().

-spec set_level(Vp::varc(), Level::level()) -> ok.

set_level(_Vp, Level) when is_integer(Level), Level >= 0 ->
    ?nif_stub().

-spec keep_level(Vp::varc(), Level::level()) -> ok.

keep_level(_Vp,_Level) ->
    ?nif_stub().

-spec move_level(Vp::varc(), From::level(), To::level()) -> ok.

move_level(_Vp,_From,_To) ->
    ?nif_stub().

-spec undo_level(Vp::varc(), Level::level()) -> ok.

undo_level(_Vp,_Level) ->
    ?nif_stub().

undo(_Vp) ->
    ?nif_stub().

-spec bcp(Vp::varc()) ->
		 false | true.
bcp(_Vp) ->
    ?nif_stub().

-spec bcp(Vp::varc(), TurboLiteralList::[literal()]) ->
		 false | true | turbo.
bcp(_Vp, _TurboLiteralList) ->
    ?nif_stub().

-spec bcp(Vp::varc(), TurboLiteralList::[literal()], TurboAll::boolean()) ->
		 false | true | turbo | {turbo,[literal()]}.
bcp(_Vp, _TurboLiteralList, _TurboAll) ->
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

-spec get_clause(Vp::varc(), ClauseIndex::integer()) -> [literal()] | true.

get_clause(_Vp,_Index) when is_integer(_Index), _Index >= 0 ->
    ?nif_stub().

-spec get_clause(Vp::varc(), ClauseIndex::integer(),
		 SkipLiteral::literal()) -> [literal()] | true.

get_clause(_Vp,_Index,_Skip) when
      is_integer(_Index), _Index >= 0 ->
    ?nif_stub().

-spec get_clause(Vp::varc(), ClauseIndex::integer(),
		 SkipLiteral::literal(),Raw::boolean()) ->
			[literal()] | true.

get_clause(_Vp,Index,_SkipLiteral,_Raw)
  when is_integer(Index), Index >= 0, is_boolean(_Raw) ->
    ?nif_stub().

-spec compress_clause(Vp::varc(), ClauseIndex::integer()) -> binary().

compress_clause(_Vp,Index)
  when is_integer(Index), Index >= 0 ->
    ?nif_stub().

use_clause(_Vp,_Index) ->
    ?nif_stub().

-spec bump(Vp::varc(), Lit::literal(), Bump::number()) -> ok.
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
-spec get_decision(Vp::varc(), Level::level()) ->
			  literal().
get_decision(_Vp, _Level) ->
    ?nif_stub().

-spec get_undo_state(Vp::varc(), Level::level()) ->
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

get_bindings_list(_Vp, Level, ClauseInfo, Trail) ->
    get_bindings(_Vp, Level, ClauseInfo, Trail, false).

get_bindings_list(_Vp, Level, ClauseInfo) ->
    get_bindings(_Vp, Level, ClauseInfo, false, false).

get_bindings_list(_Vp, Level) ->
    get_bindings(_Vp, Level, false, false, false).

get_bindings_trail(_Vp, Level) ->
    get_bindings(_Vp, Level, false, true, false).

-spec get_bindings(Vp::varc(), Level::level()) -> 
	  bindings().

%% get bindings, as list, on level 'Level' without clause info
get_bindings(_Vp, Level) when 
      is_integer(Level) ->
    ?nif_stub().

-spec get_bindings(Vp::varc(), Level::level(), ClauseInfo::boolean()) ->
	  bindings().

%% get bindings, as tuple, on level 'Level' with optional clause info
get_bindings(_Vp, Level, ClauseInfo) when 
      is_integer(Level),
      is_boolean(ClauseInfo) ->
    ?nif_stub().

-spec get_bindings(Vp::varc(), Level::level(), 
		   ClauseInfo::boolean(), Trail::boolean()) ->
	  bindings().

%% get bindings, as tuple, on level 'Level' with optional clause info
%% if Trail is true then return bindings in reversed order
get_bindings(_Vp, Level, ClauseInfo, Trail) when
      is_integer(Level),
      is_boolean(ClauseInfo),
      is_boolean(Trail) ->
    ?nif_stub().

-spec get_bindings(Vp::varc(), Level::level(), 
		   ClauseInfo::boolean(), Trail::boolean(),
		   AsTuple::boolean()) -> bindings().

get_bindings(_Vp, Level, ClauseInfo, Trail, AsTuple)  
  when is_integer(Level),
       is_boolean(ClauseInfo),
       is_boolean(Trail),
       is_boolean(AsTuple) ->
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
-spec next_unbound(Vp::varc()) -> variable() | false.
next_unbound(_Vp) ->
    ?nif_stub().

-spec next_unbound(Vp::varc(), Previous::variable()) ->
			  variable() | false.
next_unbound(_Vp, _Previous) ->
    ?nif_stub().

%% utility to get a list of unbound literals
order_all(Vp) ->
    order_all_(Vp,next_unbound(Vp),[]).

order_all_(_Vp,false,Acc) ->
    lists:reverse(Acc);
order_all_(Vp,Xi,Acc) ->
    order_all_(Vp, next_unbound(Vp, Xi), [Xi|Acc]).

phase_all(Vp) ->
    [variable_info(Vp,Vi,phase) || Vi <- order_all(Vp)].

version() ->
    info(new(), version).

i() ->
    Vt = new(),
    _ = [ io:format("~w: ~p\n", [Key,info(Vt, Key)]) || 
	    Key <- 
		[version,
		 literal_size,
		 literal_integer,
		 value_packing,
		 xref,
		 hash,
		 init_phase,
		 use_phase]],
    ok.

i(Vp) ->
    _ = [ io:format("~w: ~w\n", [Key,info(Vp, Key)]) || Key <- info_keys()],
    ok.

info(Vp) ->
    [ {Key,info(Vp, Key)} || Key <- info_keys()].

info_keys() ->
    [
     number_of_clauses,
     number_of_dead_clauses,
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
     size,
     level,
     version,
     literal_size,     %% 8,16,32,64 (sizeof literal)
     literal_integer,  %% true,false (integer or pointer)
     value_packing,    %% 1,4,undefined (variable value packing)
     xref,             %% xref is used (need for saturate with substitution)
     hash,             %% hash is used
     init_phase,       %% initial phase value
     use_phase,        %% used saved phase value
     memory_literal_size,
     memory_variable_size,
     memory_clause_size,
     memory_symbol_size,
     memory_size
    ].

memory(Vp) ->
    Keys = [number_of_variables,
	    number_of_clauses,
	    memory_literal_size,
	    memory_variable_size,
	    memory_clause_size,
	    memory_symbol_size,
	    memory_size],
    [ {Key,info(Vp, Key)} || Key <- Keys].
    

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

get_clause_bcp_counter(Vp) ->
    info(Vp, clause_bcp_counter).

get_clause_bcp_counter(Vp,n) ->
    info(Vp, clause_n_counter);
get_clause_bcp_counter(Vp,2) ->
    info(Vp, clause_2_counter);
get_clause_bcp_counter(Vp,3) ->
    info(Vp, clause_3_counter);
get_clause_bcp_counter(Vp,dead) ->
    info(Vp, clause_d_counter).

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
vec_sat_lap(V,K,Q,F,R) ->
    case vec_create(V, next_unbound(V), K) of
	[] -> true;
	Vec0 -> vec_sat_lap_(V,Vec0,Q,F,R)
    end.

%% FIXME? if a vector
%% contain a constant, we should probably update the
%% vector to speed up things (a bit)?
vec_sat_lap_(V,Vec0,Q,F,R) ->
    vec_sat_lap_(V,Vec0,Q,F,R,undefined).

vec_sat_lap_(V,Vec0,Q,F,R,FriendMap) ->
    case vec_sat(V,Vec0,Q,F,R,FriendMap) of
	false -> false;
	true ->
	    case vec_step(V, Vec0) of
		false -> true;
		Vec1 -> 
		    ?debug("step ~w => ~w, ~w\n", 
			  [Vec0, Vec1, vec_is_bound(V, Vec1)]),
		    vec_sat_lap_(V,Vec1,Q,F,R,FriendMap)
	    end
    end.

vec_sat(V,V0,Q,F,R) ->
    vec_sat(V,V0,Q,F,R,undefined).

vec_sat(V,V0,Q,F,R,FriendMap) ->
    %% ?debug("vec_sat = ~w\n", [V0]),
    V1 = vec_extend(V, V0, Q),
    V2 = vec_extend_friend(V, V1, F, FriendMap),
    V3 = vec_extend_rand(V, V2, R),
    %% ?debug("vec_sat = ~w => ~w\n", [V0, V3]),
    vec_sat(V, V3).

vec_sat(V, Vec) when is_list(Vec) ->
    set_level(V, 1),
    case satv_(V,list_to_tuple(Vec)) of
	false ->
	    false;
	[] ->
	    true;
	Bs ->
	    ?debug("satv_ ~w = ~w\n", [Vec,Bs]),
	    set_level(V, 0),
	    case install_bindings0(V, Bs) of
		true ->
		    bcp(V);
		false ->
		    false
	    end
    end.

satv_(V, Vt) when is_tuple(Vt) ->
    %% io:format("satv ~w\n", [Vt]),
    N = tuple_size(Vt),
    Bt = bcpv_(V,(1 bsl N)-1, Vt, []),
    satvar_(V, 0, N, Vt, Bt, []).

%% eval for variable I 
satvar_(V, I, N, Vt, Bt, Bs) when I < N ->
    Js = lists:seq(0, (1 bsl N)-1),
    B1 = interv(V,[element(J+1,Bt) || J <- Js, (J band (1 bsl I)) =/= 0]),
    B0 = interv(V,[element(J+1,Bt) || J <- Js, (J band (1 bsl I)) =:= 0]),
    %% io:format("satvar_ Vt = ~w, B0 = ~w, B1 = ~w\n", [Vt, B0, B1]),
    if B0 =:= false, B1 =:= false -> false;
       B0 =:= false, B1 =:= {} -> satvar_(V, I+1, N, Vt, Bt, Bs);
       B1 =:= false, B0 =:= {} -> satvar_(V, I+1, N, Vt, Bt, Bs);
       B0 =:= false -> satvar_(V, I+1, N, Vt, Bt, [B1|Bs]);
       B1 =:= false -> satvar_(V, I+1, N, Vt, Bt, [B0|Bs]);
       true ->
	    case intersect_bindings(V, element(I+1,Vt), B0, B1) of
		{} ->
		    satvar_(V, I+1, N, Vt, Bt, Bs);
		B2 ->
		    satvar_(V, I+1, N, Vt, Bt, [B2|Bs])
	    end
    end;
satvar_(_V, N, N, _Vt, _Bt, Bs) ->
    %% io:format("  Bs = ~w\n", [Bs]),
    Bs.

%% interv0(_V, As) ->
%%    intersect(As).

interv(_V, []) -> false;
interv(V, [false|As]) -> interv(V, As);
interv(V, [A|As]) -> mark(V, A), interv_(V, As).

interv_(V, [false|As]) -> interv_(V, As);
interv_(V, [A|As]) -> mark(V, A), interv_(V, As);
interv_(V, []) -> get_marked(V, true).

%% eval all 2^N combinations of Vt
bcpv_(_V,-1, _Vt, Acc) ->
    list_to_tuple(Acc);
bcpv_(V,I, Vt, Acc) ->
    %% io:format("bcpv I=~w\n", [I]),
    set_level(V, 1),
    case bindv(V, I, Vt) of
	false ->
	    queue_clear(V),
	    undo_level(V, 1),
	    bcpv_(V,I-1, Vt, [false|Acc]);
	true ->
	    set_level(V, 2),
	    Ei = case bcp(V) of
		     false -> false;
		     true -> get_bindings(V, 2)
		 end,
	    undo_level(V, 2),
	    undo_level(V, 1),
	    bcpv_(V,I-1, Vt, [Ei|Acc])
    end.

%% given number I set vars in Vt according to bit
bindv(V, I, Vt) ->
    bindv(V, tuple_size(Vt), I, Vt).
    
bindv(_V, 0, _I, _Vt) ->
    true;
bindv(V, J, I, Vt) ->
    Xj = if I band (1 bsl (J-1)) =/= 0 -> element(J,Vt); 
	    true -> -element(J,Vt)
	 end,
    %% io:format("bindv J=~w Xj=~w\n", [J, Xj]),
    bind(V,Xj) andalso bindv(V,J-1,I,Vt).

-spec unmark(Vp::varc()) -> ok.

unmark(_Vp) ->
    ?nif_stub().

-spec mark(Vp::varc(), Bs::bindings()|level()) -> ok.

mark(_Vp, _Bs) ->
    ?nif_stub().

-spec mark(Vp::varc(), Bs::bindings()|level(), Clear::boolean()) -> ok.

mark(_Vp, _Bs, _Clear) ->
    ?nif_stub().

-spec intersect_marks(Vp::varc(), Bs::bindings()|level()) -> ok.
intersect_marks(_Vp, _Bs) ->
    ?nif_stub().

intersect_var(Vp, Var, Bs0) ->
    intersect_var(Vp, Var, Bs0, ?BINDING_AS_TUPLE).

intersect_bindings(Vp, Var, Bs0, Bs1) ->
    mark(Vp, Bs1),
    intersect_var(Vp, Var, Bs0, true).

-spec intersect_var(Vp::varc(), Var::literal(),
		    Bs0::bindings()|level(), AsTuple::boolean()) -> 
	  bindings().
intersect_var(_Vp, _Var, _Bs0, _AsTuple) ->
    ?nif_stub().


get_marked(Vp) ->
    get_marked(Vp, ?BINDING_AS_TUPLE).

-spec get_marked(Vp::varc(), AsTuple::boolean()) -> bindings().

get_marked(_Vp, _Tuple) ->
    ?nif_stub().


intersect_var0(_Vp, Var, Bs0, Bs1) ->
    intersect_var0_(Var, Bs0, bindings_to_map(Bs1)).

intersect_var0_(Var, [X|Bs0], Map) ->
    case maps:find(X, Map) of
	{ok,true} ->
	    %% !Var => X,  Var => X  
	    [X | intersect_var0_(Var, Bs0, Map)];
	error ->
	    case maps:find(-X, Map) of
		{ok,true} ->
		    %% !Var => X  Var => !X
		    [{Var,-X} | intersect_var0_(Var, Bs0, Map)];
		error ->
		    intersect_var0_(Var, Bs0, Map)
	    end
    end;
intersect_var0_(_Var, [], _Map) ->
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

install_bindings0(V,[B|Bs]) when is_tuple(B) ->
    case install_tuple_bindings_(V, 0, 1, B) of
	true -> install_bindings0(V, Bs);
	false -> false
    end;
install_bindings0(V,[B|Bs]) when is_list(B) ->
    case install_list_bindings_(V, 0, B) of
	true -> install_bindings0(V, Bs);
	false -> false
    end;
install_bindings0(_V,[]) ->
    true.


install_bindings(V,Bs) when is_list(Bs) ->
    install_list_bindings_(V, info(V, level), Bs);
install_bindings(V,Bt) when is_tuple(Bt) ->
    install_tuple_bindings_(V, info(V, level), 1, Bt).

install_bindings(V,Level,Bs) when is_list(Bs) ->
    install_list_bindings_(V, Level, Bs);
install_bindings(V,Level,Bt) when is_tuple(Bt) ->
    install_tuple_bindings_(V, Level, 1, Bt).

install_tuple_bindings_(_V, _Level, I, Bt) when I > tuple_size(Bt) ->
    true;
install_tuple_bindings_(V, Level, I, Bt) when I =< tuple_size(Bt) ->
    case element(I,Bt) of
	X when is_integer(X) ->
	    true = bind(V, X),
	    install_tuple_bindings_(V,Level,I+1,Bt);	    
	{X,Y} when Level =:= 0 ->
	    Xa = variable_info(V, X, is_atom),
	    Ya = variable_info(V, Y, is_atom),
	    if Ya, not Xa ->
		    subst(V, Y, X);
	       true ->
		    subst(V, X, Y)
	    end,
	    install_tuple_bindings_(V,Level,I+1,Bt);
	{X,t} ->
	    true = bind(V, X),
	    install_tuple_bindings_(V,Level,I+1,Bt);
	{X,f} ->
	    true = bind(V, -X),
	    install_tuple_bindings_(V,Level,I+1,Bt)
    end.

install_list_bindings_(_V,_Level,[]) ->
    true;
install_list_bindings_(V,Level,[B|Bs]) ->
    case B of
	X when is_integer(X) ->
	    true = bind(V, X),
	    install_list_bindings_(V,Level,Bs);
	{X,X} ->
	    install_list_bindings_(V,Level,Bs);
	{X,t} ->
	    true = bind(V, X),
	    install_list_bindings_(V,Level,Bs);
	{X,f} ->
	    true = bind(V, -X),
	    install_list_bindings_(V,Level,Bs);
	{X,Y} when Level =:= 0 ->
	    Xa = variable_info(V, X, is_atom),
	    Ya = variable_info(V, Y, is_atom),
	    if Ya, not Xa ->
		    subst(V, Y, X);
	       true ->
		    subst(V, X, Y)
	    end,
	    install_list_bindings_(V,Level,Bs)
    end.


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

vec_extend_friend(V, Vec, P, undefined) ->
    vec_extend(V, Vec, P);
vec_extend_friend(_V, Vec=[Xi|_], P, FriendMap) ->
    %% pick friends from -Xi
    W = maps:get(-Xi, FriendMap, []) -- Vec,
    Vec ++ lists:sublist(W, P).

%%
%% do a saturation run and build a reverse map
%% X -> Y1 Y2 Y3 ...  then 
%% friend(Y1, X)
%% friend(Y2, X)
%% friend(Y3, X)
%%
make_friend_map(V) ->
    make_friend_map_(V, next_unbound(V), #{}).

make_friend_map_(_V, false, Map) -> 
    Map;
make_friend_map_(V, Xi, Map0) ->
    Map1 = add_lit_friends(V, Xi, Map0),
    Map2 = add_lit_friends(V, -Xi, Map1),
    make_friend_map_(V, next_unbound(V, Xi), Map2).

add_lit_friends(V, Xi, Map) ->
    set_level(V, 1),
    case bind(V, Xi) of
	false ->
	    queue_clear(V),
	    undo_level(V, 1),
	    Map;
	true ->
	    set_level(V, 2),
	    case bcp(V) of
		false ->
		    undo_level(V, 2),
		    undo_level(V, 1),
		    Map;
		true ->
		    Map1 = add_friends(get_bindings_list(V, 2), Xi, Map),
		    undo_level(V, 2),
		    undo_level(V, 1),
		    Map1
	    end
    end.

add_friends([Yi|Ys], X, Map) ->
    Fs = maps:get(Yi, Map, []),
    case lists:member(X, Fs) of
	true ->
	    add_friends(Ys, X, Map);
	false ->
	    add_friends(Ys, X, maps:put(Yi, [X|Fs], Map))
    end;
add_friends([], _X, Map) ->
    Map.

%% FIXME: add depth info for all friends?
%% depth(V, Yi, DepthMap) ->
%%    Cix = varp_nif:implication_clause(V, Yi),
%%    Clause = varp_nif:get_clause(V, Cix, Yi),
%%    Depth = lists:max([maps:get(-Li, DepthMap) || Li <- Clause])+1,
%%    {Depth, DepthMap#{ Yi => Depth }}.
    
%% add (at most) R random elements to Vec (not already in Vec)
vec_extend_rand(V, Vec, R) ->
    N = varp_nif:get_number_of_variables(V),
    M = varp_nif:get_number_of_unbound_variables(V) - length(Vec),
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
