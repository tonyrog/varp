%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2015, Tony Rogvall
%%% @doc
%%%    NIF interface to varc 
%%% @end
%%% Created : 20 Aug 2015 by Tony Rogvall <tony@rogvall.se>

-module(varp_nif).

-on_load(init/0).

-export([new/1]).
-export([clone/2]).
-export([getopt/2, getopt/3]).
-export([setopt/3, setopt/4]).
-export([getstat/2]).
-export([add_variable/1]).
-export([add_variable/2]).
-export([add_variable/3]).
-export([add_variables/2]).
-export([add_variables/3]).
-export([add_variables/4]).
-export([del_variable/2]).
-export([add_symbol/3]).
-export([del_symbol/2]).
-export([get_symbol/2]).
-export([find_symbol/2]).
-export([first_symbol/1]).
-export([next_symbol/2]).
-export([variable_info/3]).
-export([literal_info/3]).
-export([level/1]).
-export([value/2]).
-export([bound/2]).
-export([bind/2, bind/3]).
-export([decide/2, decide/3]).
-export([subst/3]).
-export([implication_clause/2]).
-export([implication_level/2]).
-export([conflicting_clause/1]).
-export([conflicting_clause/2]).
-export([conflict/3, conflict/4]).
-export([minimize/2, minimize/3]).
-export([is_variable/2]).
-export([is_bound/2]).
-export([is_equal/3]).
-export([isused/2, isused/3]).
-export([isatom/2, isatom/3]).
-export([phase/2, set_phase/2]).
-export([push/1]).
-export([pop/1, pop/2]).
-export([undo/1]).
-export([bcp/1, bcp/2, bcp/3]).
-export([nbcp/1]).
-export([vbcp/2, vbcp/3]).
-export([add_clause/2]).
-export([add_clause/3]).
-export([find_clause/2]).
-export([get_clause/2]).
-export([get_clause/3]).
-export([get_clause/4]).
-export([get_clause/5]).
-export([del_clause/2]).
-export([move_clause/3]).
-export([compress_clause/2]).
-export([clean_clause/2]).
-export([get_clauses/3]).
-export([use_clause/2]).
-export([clause_info/2,clause_info/3]).
-export([get_decision/2]).
-export([get_undo_state/2]).
-export([get_nbindings/2, get_nbindings/3,get_nbindings/4]). 
-export([get_bindings/1, get_bindings/2, get_bindings/3,get_bindings/4]).
-export([get_number_of_bindings/2]).
-export([queue_first/1]).
-export([queue_next/2]).
-export([queue_clear/1]).
-export([order_sort/2,order_sort/3,order_sort/4]).
-export([order_first/2, order_last/2]).
-export([order_first/3, order_last/3]).
-export([next_unbound/1, next_unbound/2]).
-export([bump/3]).
-export([subscribe/2]).
-export([clauseset_size/2]).
-export([clauseset_offset/2, clauseset_offset/3]).
-export([clauseset_sort/2]).
-export([clauseset_first/2]).
-export([clauseset_next/2]).
-export([unmark/1]).
-export([mark/2, mark/3]).
-export([intersect_marks/2]).
-export([intersect_var/4]).
-export([get_marked/2]).
-export([rand/1]).   %% debug!
-export([noop/1]).   %% bench
%% -define(DEBUG, true).

-ifdef(DEBUG).
-define(dbg(F,A), io:format((F),(A))).
-else.
-define(dbg(F,A), ok).
-endif.

-define(DELTA, 0).
-define(GAMMA, 1).
-define(BETA,  2).
-define(ALPHA, 3).

-type varp() :: reference().
-type variable() :: pos_integer().
-type unsigned() :: non_neg_integer().
-type literal() :: integer().
-type symbol() :: binary() | string() | term().
-type sort_key() :: atom() | string().
-type sort_value() :: integer().
-type binding() :: literal() | {literal(),literal()}.
-type bindings() :: [binding()] | {binding()}.  %% variable size tuple?
-type level() :: integer().
-type subflag() :: variable | atom | number_of_variables |
		   number_of_bound_variables | number_of_subst_variables |
		   number_of_clauses | number_of_dead_clauses |
		   max_level | max_bound | min_level | 
		   number_of_conflicts | number_of_propagations |
		   number_of_decisions | number_of_bcp.
-type option_key() ::
	qtype |       %% queue strategy in bcp
	xref |        %% use cross references
	hash |        %% install hash over clauses
	init_phase |  %% initial phase
	use_phase |   %% use phase saving
	seed          %% random seed
	.

-type stat_key() :: 
	level |     %% current level
	size  |     %% number of variables
	bcp_counter |  %% number of bcp 
	number_of_bcps |
	conflict_counter | %% number of conflicts
	number_of_conflicts |
	number_of_propagations |
	number_of_decisions |
	clause_n_counter |
	clause_m_counter |
	clause_2_counter |
	clause_3_counter |
	clause_d_counter |
	mark_counter |
	decision_counter |
	number_of_conflicting_clauses |
	number_of_variables |
	number_of_clauses |
	number_of_dead_clauses |
	number_of_learnt_clauses |
	number_of_bound_variables |
	number_of_subst_variables |
	number_of_unbound_variables |
	max_level | %% get deepest level (on reset)
	min_level | %% get shallowest level (on reset)
	max_bound | %% number of bound variables (since last, and reset)
	memory_literal_size |
	memory_variable_size |
	memory_clause_size |
	memory_symbol_size |
	memory_size |
	version |
	literal_size |
	literal_integer |
	value_packing.


-export_type([varp/0]).
-export_type([variable/0, literal/0, symbol/0]).
-export_type([sort_key/0,sort_value/0]).
-export_type([binding/0, bindings/0]).
-export_type([level/0]).
-export_type([subflag/0]).

-define(nif_stub(),
	erlang:nif_error({nif_not_loaded,module,?MODULE,line,?LINE})).

init() ->
    Nif = filename:join([code:priv_dir(varp), "varp_nif"]),
    ?dbg("Loading: ~s\n", [Nif]),
    erlang:load_nif(Nif, 0).

-type new_options() :: 
	#{
	  %% inital variable table size
	  size  => unsigned(),
	  %% use queue strategy in bcp
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

-spec new(new_options()) -> varp().

new(Options) when is_map(Options) ->
    ?nif_stub().

-spec clone(Vp::varp(), Opts::clone_opts()) -> varp().
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

-spec getopt(Vp::varp(), Key::option_key()) ->
	  (integer()|atom()|string()).
	  
getopt(_Vp, Key) when is_atom(Key); is_list(Key) ->
    ?nif_stub().
getopt(_Vp, Key, _System) when is_atom(Key); is_list(Key) ->
    ?nif_stub().

-spec getstat(Vp::varp(), Key::stat_key()) -> integer() | string().
getstat(_Vp, Key) when is_atom(Key); is_list(Key) ->
    ?nif_stub().

%% set config
%%    xref            -- turn on/off xref
%%    permanent       -- number of clauses that are permanent
%%    max_conflicting -- max number of conflicting <= MAX_CONFLICTING
%% 
-spec setopt(Vp::varp(), Key::option_key(), Value::(integer()|atom())) ->
	  ok.
setopt(_Vp, _Key, _Value) ->
    ?nif_stub().
-spec setopt(Vp::varp(), Key::option_key(), Value::(integer()|atom()),
	     System::(user|system)) ->
	  ok.
setopt(_Vp, _Key, _Value, _System) ->
    ?nif_stub().

-spec add_variable(Vp::varp()) -> integer().
add_variable(_Vp) ->
    ?nif_stub().

-spec add_variable(Vp::varp(), IsAtom::boolean()) ->
	  integer().
add_variable(_Vp, IsAtom) when is_boolean(IsAtom) ->
    ?nif_stub().

-spec add_variable(Vp::varp(), IsAtom::boolean(), IsUsed::boolean()) ->
	  integer().
add_variable(_Vp, IsAtom,IsUsed) 
  when is_boolean(IsAtom),is_boolean(IsUsed) ->
    ?nif_stub().

-spec add_variables(Vp::varp(), Num::integer()) -> 
	  {First::integer(), Last::integer()}.
add_variables(_Vp, Num) when is_integer(Num), Num>0 ->
    ?nif_stub().

-spec add_variables(Vp::varp(), Num::integer(), IsAtom::boolean()) -> 
	  {First::integer(), Last::integer()}.
add_variables(_Vp, Num, IsAtom) when
      is_integer(Num), Num>0, is_boolean(IsAtom) ->
    ?nif_stub().

-spec add_variables(Vp::varp(), Num::integer(),
		    IsAtom::boolean(),IsUsed::boolean()) ->
	  {First::integer(), Last::integer()}.
add_variables(_Vp, Num, IsAtom, IsUsed) when
      is_integer(Num), Num>0, is_boolean(IsAtom), is_boolean(IsUsed) ->
    ?nif_stub().

del_variable(_Vp, _Index) when is_integer(_Index) ->
    ?nif_stub().

-spec add_symbol(Vp::varp(),Lit::literal()|[Lit::literal()], Name::term())-> ok.
add_symbol(_Vp, Lit, _Name)  when is_integer(Lit); is_list(Lit) ->
    ?nif_stub().

-spec del_symbol(Vp::varp(), Name::term()) -> ok.
del_symbol(_Vp, _Name)  ->
    ?nif_stub().

%% aliases
-spec get_symbol(Vp::varp(), Lit::literal()) -> [{term(),Pos::integer()}].
get_symbol(Vp, Lit) when is_integer(Lit) ->
    variable_info(Vp, Lit, symbol).

%% find variable index from variable name (term or binary)
-spec find_symbol(Vp::varp(), Name::term()) -> false | literal() | [literal()].
find_symbol(_Vp, _Name) ->
    ?nif_stub().

%% get first symbol
-spec first_symbol(Vp::varp()) -> false | symbol().
first_symbol(_Vp) ->
    ?nif_stub().

-spec next_symbol(Vp::varp(), Symbol::symbol()) -> false | symbol().
next_symbol(_Vp, _Symbol) ->
    ?nif_stub().

%%
%% What::implication|implication_clause|level|degree|is_atom|symbol
%%

variable_info(_Vp,Index,_What)
  when is_integer(Index), Index >= 0 ->
    ?nif_stub().

literal_info(_Vp,Index,_What)
  when is_integer(Index), Index >= 0 ->
    ?nif_stub().

%% Get current level
-spec level(Vp::varp()) -> integer().

level(_Vp) ->
    ?nif_stub().    

%% Get literal value 
-spec value(Vp::varp(), Lit::literal()) -> true | false | undefined.

value(_Vp, Lit) when is_integer(Lit) ->
    ?nif_stub().

%% Get literal binding
-spec bound(Vp::varp(), Lit::literal()) -> 
	  true | false | literal() | undefined.

bound(_Vp, Lit) when is_integer(Lit) ->
    ?nif_stub().

%% bind literal
-spec bind(Vp::varp(), X::literal()) -> boolean().

bind(_Vp, X) when is_integer(X) ->
    ?nif_stub().

%% bind literal at level
-spec bind(Vp::varp(), X::literal(), Level::level()) -> boolean().

bind(_Vp, X, Level) when is_integer(X),
			 is_integer(Level) ->
    ?nif_stub().

%% decide literal, affected by phase!
-spec decide(Vp::varp(), X::literal()) -> boolean().

decide(_Vp, X) when is_integer(X) ->
    ?nif_stub().

%% decide literal at level, affected by phase!
-spec decide(Vp::varp(), X::literal(), Level::level()) -> boolean().

decide(_Vp, X, Level) when is_integer(X),
			   is_integer(Level) ->
    ?nif_stub().

%% X/Y substitute Y for X, replace all instances of Y with X
-spec subst(Vp::varp(), X::literal(), Y::literal()) -> boolean().

subst(_Vp, X, Y) when is_integer(X),
		      is_integer(Y) ->
    ?nif_stub().

-spec implication_clause(Vp::varp(), Lit::literal()) ->
				Cix::integer().
implication_clause(_Vp, Lit) when is_integer(Lit) ->
    ?nif_stub().

-spec implication_level(Vp::varp(), Lit::literal()) ->
	  Level::level().
implication_level(_Vp, Lit) when is_integer(Lit) ->
    ?nif_stub().

-spec conflicting_clause(Vp::varp()) -> Cix::integer().
conflicting_clause(Vp) ->
    conflicting_clause(Vp, 0).

-spec conflicting_clause(Vp::varp(), Index::integer()) -> Cix::integer().
conflicting_clause(_Vp, _Index) ->
    ?nif_stub().

-spec conflict(Vp::varp(), Bump::number(), 
	       ConflictNumOrClause::integer()|[literal()]) ->
	  ClauseIndex::integer() | undefined.
conflict(_Vp, _Bump, _IndexOrClause) ->
    ?nif_stub().

-spec conflict(Vp::varp(), Bump::number(), 
	       ConflictNumOrClause::integer()|[literal()],
	       UnitLiteral::literal()) ->
	  ClauseIndex::integer() | undefined.
conflict(_Vp, _Bump, _IndexOrClause, _UnitLiteral) ->
    ?nif_stub().

-spec minimize(Vp::varp(), ClauseIndex::integer()) -> integer() | undefined.
%% minimize the clause and return number of literals removed
minimize(_Vp, _CluseIndex) ->
    ?nif_stub().

-spec minimize(Vp::varp(), ClauseIndex::integer(), Style::none|local|global|recursive) ->
	  integer() | undefined.
%% minimize the clause and return number of literals removed
minimize(_Vp, _CluseIndex, _Style) ->
    ?nif_stub().

-spec is_variable(Vp::varp(), Lit::literal()) -> boolean().
is_variable(_Vp, Lit) when is_integer(Lit) ->
    ?nif_stub().

-spec is_bound(Vp::varp(), Lit::literal()) -> boolean().
is_bound(_Vp, Lit) when is_integer(Lit) ->
    ?nif_stub().

-spec is_equal(Vp::varp(), LitA::literal(), LitB::literal()) -> boolean().
is_equal(_Vp, LitA, LitB) when is_integer(LitA),
			       is_integer(LitB) ->
    ?nif_stub().

-spec isused(Vp::varp(), Var::literal()) -> boolean().
isused(_Vp, Var) when is_integer(Var) ->
    ?nif_stub().

-spec isused(Vp::varp(), Var::literal(), Status::boolean()) -> boolean().
isused(_Vp, Var, Status) when is_integer(Var), is_boolean(Status) ->
    ?nif_stub().

-spec isatom(Vp::varp(), Var::literal()) -> boolean().
isatom(_Vp, Var) when is_integer(Var) ->
    ?nif_stub().

-spec isatom(Vp::varp(), Var::literal(), Status::boolean()) -> boolean().
isatom(_Vp, Var, Status) when is_integer(Var), is_boolean(Status) ->
    ?nif_stub().

-spec phase(Vp::varp(), Var::literal()) -> -1 | 1 | undefined.
phase(_Vp, Var) when is_integer(Var) ->
    ?nif_stub().

-spec set_phase(Vp::varp(), Lit::literal()) -> -1 | 1 | undefined.
set_phase(_Vp, Lit) when is_integer(Lit) ->
    ?nif_stub().

%% push binding level and return the level before push
%% This allows code like:
%%    Level = push()
%%    try various_varp_code() of
%%        R -> R
%%    after
%%       pop(Level)
%%    end
%%
-spec push(Vp::varp()) -> Level::integer().
push(_Vp) ->
    ?nif_stub().

%% pop and undo bindings on current level and return current level
-spec pop(Vp::varp()) -> Level::integer().
pop(_Vp) ->
    ?nif_stub().

%% pop and undo until level but not including
%% for example pop(Vp, 0) will pop to top.
%% Pop will return the target Level 
-spec pop(Vp::varp(), Level::integer()) -> Level::integer().
pop(_Vp, _Level) ->
    ?nif_stub().

-spec undo(Vp::varp()) -> ok.
undo(_Vp) ->
    ?nif_stub().

-spec bcp(Vp::varp()) ->
		 false | true.
bcp(_Vp) ->
    ?nif_stub().

-spec bcp(Vp::varp(), TurboLiteralList::[literal()]) ->
		 false | true | turbo.
bcp(_Vp, _TurboLiteralList) ->
    ?nif_stub().

-spec bcp(Vp::varp(), TurboLiteralList::[literal()], TurboAll::boolean()) ->
		 false | true | turbo | {turbo,[literal()]}.
bcp(_Vp, _TurboLiteralList, _TurboAll) ->
    ?nif_stub().

-spec nbcp(Vp::varp()) -> false | true.
nbcp(_Vp) ->
    ?nif_stub().

-spec vbcp(Vp::varp(),[literal()]) -> {integer(),literal()} | false | true.
vbcp(_Vp, _Xs) ->
    ?nif_stub().

-spec vbcp(Vp::varp(),[literal()],SingleLevel::boolean()) ->
	  {integer(),literal()} | false | true.
vbcp(_Vp, _Xs, _SingleLevel) ->
    ?nif_stub().

-spec clauseset_size(Vp::varp(),Si::integer()) ->
			     integer().
clauseset_size(_Vp, _Si) ->
    ?nif_stub().    

-spec add_clause(Vp::varp(),Ls::[literal()]) ->
			false | error | integer().
add_clause(_Vp,Ls) when is_list(Ls) ->
    ?nif_stub().

-spec add_clause(Vp::varp(),Ls::[literal()],Si::0..3) ->
			false | error | integer().
add_clause(_Vp,Ls,Si) when is_list(Ls), is_integer(Si), Si>=0, Si=<3 ->
    ?nif_stub().

-spec find_clause(Vp::varp(),Ls::[literal()]) ->
			 false | integer().
find_clause(_Vp,Ls) when is_list(Ls) ->
    ?nif_stub().

-spec get_clause(Vp::varp(), ClauseIndex::integer()) -> 
	  [literal()] | true | false.

get_clause(_Vp,_Index) when is_integer(_Index), _Index >= 0 ->
    ?nif_stub().

-spec get_clause(Vp::varp(),ClauseIndex::integer(),SkipLiteral::literal()) -> 
	  [literal()] | true | false.

get_clause(_Vp,_Index,_Skip) when
      is_integer(_Index), _Index >= 0 ->
    ?nif_stub().

-spec get_clause(Vp::varp(), ClauseIndex::integer(),
		 SkipLiteral::literal(),Raw::boolean()) ->
	  [literal()] | true | false.

get_clause(_Vp,Index,_SkipLiteral,_Raw)
  when is_integer(Index), Index >= 0, is_boolean(_Raw) ->
    ?nif_stub().

-spec get_clause(Vp::varp(), 
		 ClauseIndex::integer(),
		 SkipLiteral::literal(),
		 Raw::boolean(),
		 AsTuple::boolean() ) ->
	  {literal()} | [literal()] | true | false.

get_clause(_Vp,Index,_SkipLiteral,_Raw,_AsTuple)
  when is_integer(Index), Index >= 0, is_boolean(_Raw),
       is_boolean(_AsTuple) ->
    ?nif_stub().

-spec compress_clause(Vp::varp(), ClauseIndex::integer()) -> binary().

compress_clause(_Vp,Index)
  when is_integer(Index), Index >= 0 ->
    ?nif_stub().

use_clause(_Vp,_Index) ->
    ?nif_stub().

-spec bump(Vp::varp(), Lit::literal(), Bump::number()) -> ok.
bump(_Vp,_Lit,Bump) when is_number(Bump) ->
    ?nif_stub().


-spec subscribe(Vp::varp(), Event::subflag()|[subflag()]) -> ok.
subscribe(_Vp,Event) when is_atom(Event) ->
    ?nif_stub().

clause_info(_Vp,Index,_What)
  when is_integer(Index), Index >= 0 ->
    ?nif_stub().

clause_info(Vp,Index) ->
    [{What,clause_info(Vp,Index,What)}||What<-[status,watch,length]].

-spec del_clause(Vp::varp(), integer()|[literal()]) -> ok.
del_clause(_Vp,Index)
  when is_integer(Index), Index >= 0 ->
    ?nif_stub().

-spec move_clause(Vp::varp(),ClauseIndex::integer(),SI::integer()) ->
			 integer().
move_clause(_Vp,_Index,_Si) when
      is_integer(_Index), _Index >= 0, is_integer(_Si), _Si >= 0, _Si =< 3 ->
    ?nif_stub().

clean_clause(_Vp,Index)
  when is_integer(Index), Index >= 0 ->
    ?nif_stub().

get_clauses(_Vp,Var,How)
  when (How =:= variable orelse How =:= literal orelse How =:= watch),
       is_integer(Var), Var >= 0 ->
    ?nif_stub().

-spec queue_first(Vp::varp()) -> literal() | false.
queue_first(_Vp) ->
    ?nif_stub().

-spec queue_next(Vp::varp(), Literal::integer()) -> literal() | false.
queue_next(_Vp, _Lit) ->
    ?nif_stub().

-spec queue_clear(Vp::varp()) -> true.
queue_clear(_Vp) ->
    ?nif_stub().

%% get decision variable (bind) on Level
-spec get_decision(Vp::varp(), Level::level()) ->
			  literal().
get_decision(_Vp, _Level) ->
    ?nif_stub().

-spec get_undo_state(Vp::varp(), Level::level()) ->
			    'undefined'|'set'|'toggle'|'done'.
get_undo_state(_Vp, _Level) ->
    ?nif_stub().

-spec get_nbindings(Vp::varp(), Count::non_neg_integer()) ->
	  bindings().

get_nbindings(_Vp,Count) when is_integer(Count), Count>= 0 ->
    ?nif_stub().

-spec get_nbindings(Vp::varp(),Count::non_neg_integer(),AsTrail::boolean()) ->
	  bindings().

get_nbindings(_Vp,Count,_AsTrail) when 
      is_integer(Count), Count >= 0 ->
    ?nif_stub().

-spec get_nbindings(Vp::varp(), Count::non_neg_integer(),
		    AsTrail::boolean(),AsTuple::boolean()) ->
	  bindings().

get_nbindings(_Vp,Count,_AsTrail,_AsTuple) 
  when is_integer(Count), Count>= 0 ->
    ?nif_stub().

-spec get_bindings(Vp::varp()) -> 
	  bindings().

%% get bindings, as list, on the current 'Level' 
get_bindings(_Vp) ->
    ?nif_stub().

-spec get_bindings(Vp::varp(), Level::level()) -> 
	  bindings().

%% get bindings, as list, on level 'Level' without clause info
get_bindings(_Vp, Level) when is_integer(Level) ->
    ?nif_stub().

-spec get_bindings(Vp::varp(), Level::level(), Trail::boolean()) ->
	  bindings().

%% get bindings, as tuple, on level 'Level' with optional clause info
%% if Trail is true then return bindings in reversed order
get_bindings(_Vp, Level, Trail) when
      is_integer(Level),
      is_boolean(Trail) ->
    ?nif_stub().

-spec get_bindings(Vp::varp(), Level::level(), 
		   Trail::boolean(),
		   AsTuple::boolean()) -> bindings().

get_bindings(_Vp, Level, Trail, AsTuple)  
  when is_integer(Level),
       is_boolean(Trail),
       is_boolean(AsTuple) ->
    ?nif_stub().

get_number_of_bindings(_Vp, _Level) ->
    ?nif_stub().

-spec order_sort(Vp::varp(), Key::sort_key()) -> ok.
order_sort(_Vp, _Key) ->
    ?nif_stub().

-spec order_sort(Vp::varp(), Key1::sort_key(), 
		 KeyOrArg::sort_key()|sort_value()) -> ok.
order_sort(_Vp, _Key1, _KeyOrArg) ->
    ?nif_stub().

-spec order_sort(Vp::varp(), Key1::sort_key(), Key2::sort_key(),
		 Arg::sort_value()) -> 
			integer().
order_sort(_Vp, _Key1, _Key2, _Arg) ->
    ?nif_stub().

-spec order_first(Vp::varp(), [literal()]) -> ok.
order_first(_Vp, _VarList) ->
    ?nif_stub().

-spec order_first(Vp::varp(), [literal()], SetPhase::boolean()) -> ok.
order_first(_Vp, _VarList, SetPhase) when is_boolean(SetPhase) ->
    ?nif_stub().

-spec order_last(Vp::varp(), List::[literal()]) -> ok.
order_last(_Vp, _List) ->
    ?nif_stub().

-spec order_last(Vp::varp(), [literal()], SetPhase::boolean()) -> ok.
order_last(_Vp, _VarList, SetPhase) when is_boolean(SetPhase) ->
    ?nif_stub().

clauseset_offset(_Vp, _Si) ->
    ?nif_stub().

clauseset_offset(_Vp, _Si, _Offset) ->
    ?nif_stub().

clauseset_sort(_Vp, _Si) ->
    ?nif_stub().    

clauseset_first(_Vp, _Si) ->
    ?nif_stub().

%% return index to next clause | false
clauseset_next(_Vp, _Ix) ->
    ?nif_stub().

%% return next unbound literal or false
-spec next_unbound(Vp::varp()) -> variable() | false.
next_unbound(_Vp) ->
    ?nif_stub().

-spec next_unbound(Vp::varp(), Previous::variable()) ->
			  variable() | false.
next_unbound(_Vp, _Previous) ->
    ?nif_stub().

-spec unmark(Vp::varp()) -> ok.

unmark(_Vp) ->
    ?nif_stub().

-spec mark(Vp::varp(), Bs::bindings()|level()) -> ok.

mark(_Vp, _Bs) ->
    ?nif_stub().

-spec mark(Vp::varp(), Bs::bindings()|level(), Clear::boolean()) -> ok.

mark(_Vp, _Bs, _Clear) ->
    ?nif_stub().

-spec intersect_marks(Vp::varp(), Bs::bindings()|level()) -> ok.
intersect_marks(_Vp, _Bs) ->
    ?nif_stub().

-spec intersect_var(Vp::varp(), Var::literal(),
		    Bs0::bindings()|level(), AsTuple::boolean()) -> 
	  bindings().
intersect_var(_Vp, _Var, _Bs0, _AsTuple) ->
    ?nif_stub().

-spec get_marked(Vp::varp(), AsTuple::boolean()) -> bindings().
get_marked(_Vp, _Tuple) ->
    ?nif_stub().

-spec rand(Vp::varp()) -> unsigned().
rand(_Vp) ->
    ?nif_stub().

-spec noop(Vp::varp()) -> ok.
noop(_Vp) ->
    ?nif_stub().
