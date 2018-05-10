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
-export([new/2]).
-export([info/2]).
-export([add_variable/1]).
-export([get/2]).
-export([put/3]).
-export([class/2]).
-export([occur/2]).
-export([depth/2]).
-export([implication_clause/2]).
-export([conflicting_clause/1]).
-export([is_variable/2]).
-export([is_bound/2]).
-export([class_next/2]).
-export([is_equal/3]).
-export([mark/1,mark/2]).
-export([undo/1,undo/2]).
-export([remove_mark/1, remove_mark/2]).
-export([eval/1]).
-export([add_clause/3]).
-export([add_clause/4]).
-export([add_clause/5]).
-export([add_clause/6]).
-export([add_clause/7]).
-export([add_clause/8]).
-export([get_clause/2]).
-export([get_clause_flags/2]).
-export([del_clause/2]).
-export([get_clauses/2]).
-export([get_queue/1]).
-export([get_queue_first/1]).
-export([get_queue_next/2]).
-export([clear_queue/1]).
-export([enqueue_all/1]).
-export([get_latest_binding/1]).
-export([get_nbindings/2]).
-export([get_nbindings/3]).
-export([get_bindings/2]).
-export([get_bindings/3]).
-export([order_init/1]).
-export([order_first/1, order_next/2, order_next/3]).
-export([order_sort/2, order_sort/3]).
-export([order_all/1]).

-export([get_info/1]).
-export([info_keys/0]).
-export([get_max_clause_length/1]).
-export([get_number_of_variables/1]).
-export([get_number_of_clauses/1]).
-export([get_number_of_bound_variables/1]).
-export([get_number_of_unbound_variables/1]).
-export([get_clause_eval_counter/1]).
-export([get_eval_counter/1]).

-ifdef(debug).
-define(debug(F,A), io:format((F),(A))).
-else.
-define(debug(F,A), ok).
-endif.

-type varc() :: reference().
-type clause_type() :: 'and'|'or'|'xor'|'reg'.
-type literal() :: integer().
-type sort_key()  :: identity|random|occur|depth|
		     occur_depth|depth_occur|
		     occur_ascending|occur_descending|
		     depth_ascending|depth_descending|
		     occur_depth_ascending|occur_depth_descending|
		     depth_occur_ascending|depth_occur_descending.
-type sort_value() :: integer().

-define(is_op(Op), (((Op) =:= 'and') 
		    orelse ((Op) =:= 'or') 
		    orelse ((Op) =:= 'xor')
		    orelse ((Op) =:= 'reg'))).

-define(nif_stub(),
	erlang:nif_error({nif_not_loaded,module,?MODULE,line,?LINE})).

init() ->
    Nif = filename:join([code:priv_dir(varp), "varc_nif"]),
    ?debug("Loading: ~s\n", [Nif]),
    erlang:load_nif(Nif, 0).


new() ->
    ?nif_stub().

new(Size) when is_integer(Size), Size >= 0 ->
    ?nif_stub().

new(Size,Expand) when is_integer(Size), Size >= 0,
		      is_integer(Expand), Expand >= 0 ->
    ?nif_stub().

info(_Vp, Item) when is_atom(Item) ->
    ?nif_stub().

add_variable(_Vp) ->
    ?nif_stub().

%%
%% Get literal value 
%%
-spec get(Vp::varc(), Lit::literal()) -> integer().

get(_Vp, Lit) when is_integer(Lit) ->
    ?nif_stub().

%% put literal value
-spec put(Vp::varc(), LitA::literal(), LibB::literal()) -> boolean().

put(_Vp, LitA, LitB) when is_integer(LitA),
			  is_integer(LitB) ->
    ?nif_stub().

-spec class(Vp::varc(), Lit::literal()) -> integer().
class(_Vp, Lit) when is_integer(Lit) ->
    ?nif_stub().

-spec occur(Vp::varc(), Lit::literal()) -> integer().
occur(_Vp, Lit) when is_integer(Lit) ->
    ?nif_stub().

-spec depth(Vp::varc(), Lit::literal()) -> integer().
depth(_Vp, Lit) when is_integer(Lit) ->
    ?nif_stub().

-spec implication_clause(Vp::varc(), Lit::literal()) ->
				{Cix::integer(),Pos::integer(),Mark::integer()}.
implication_clause(_Vp, Lit) when is_integer(Lit) ->
    ?nif_stub().

-spec conflicting_clause(Vp::varc()) -> Cix::integer().
conflicting_clause(_Vp) ->
    ?nif_stub().

-spec is_variable(Vp::varc(), Lit::literal()) -> boolean().
is_variable(_Vp, Lit) when is_integer(Lit) ->
    ?nif_stub().

-spec is_bound(Vp::varc(), Lit::literal()) -> boolean().
is_bound(_Vp, Lit) when is_integer(Lit) ->
    ?nif_stub().

class_next(_Vp, Lit) when is_integer(Lit) ->
    ?nif_stub().

-spec is_equal(Vp::varc(), LitA::literal(), LitB::literal()) -> boolean().
is_equal(_Vp, LitA, LitB) when is_integer(LitA),
			       is_integer(LitB) ->
    ?nif_stub().

mark(Vp) ->
    mark(Vp, 0).

mark(_Vp,Level) when is_integer(Level), Level >= 0 ->
    ?nif_stub().

%% remove latest mark
remove_mark(Vp) ->
    remove_mark(Vp,-1).

-spec remove_mark(Vp::varc(), Mark::integer()) -> ok.

remove_mark(_Vp,_Mark) ->
    ?nif_stub().

%% undo every thing
undo(_Vp) ->
    ?nif_stub().

-spec undo(Vp::varc(), Mark::integer()) -> ok.

undo(_Vp,_Mark) ->
    ?nif_stub().

eval(_Vp) ->
    ?nif_stub().

-spec add_clause(Vp::varc(),Op::clause_type(),Ls::[literal()]) -> ok.

add_clause(_Vp,Op,Ls) when ?is_op(Op), is_list(Ls) ->
    ?nif_stub().

-spec add_clause(Vp::varc(),Op::clause_type(),
		 X1::literal(),X2::literal()) -> ok.
add_clause(_Vp,_Op,_X1,_X2) ->
    ?nif_stub().

add_clause(_Vp,_Op,_X1,_X2,_X3) ->
    ?nif_stub().

add_clause(_Vp,_Op,_X1,_X2,_X3,_X4) ->
    ?nif_stub().

add_clause(_Vp,_Op,_X1,_X2,_X3,_X4,_X5) ->
    ?nif_stub().

add_clause(_Vp,_Op,_X1,_X2,_X3,_X4,_X5,_X6) ->
    ?nif_stub().

get_clause(_Vp,Index)
  when is_integer(Index), Index >= 0 ->
    ?nif_stub().

get_clause_flags(_Vp,Index)
  when is_integer(Index), Index >= 0 ->
    ?nif_stub().

del_clause(_Vp,Index)
  when is_integer(Index), Index >= 0 ->
    ?nif_stub().

get_clauses(_Vp,Var)
  when is_integer(Var), Var >= 0 ->
    ?nif_stub().

get_queue_first(_Vp) ->
    ?nif_stub().

get_queue_next(_Vp, _Cix) ->
    ?nif_stub().

clear_queue(_Vp) ->
    ?nif_stub().

enqueue_all(_Vp) ->
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

%% get bindings until mark
get_bindings(Vp, Mark) ->
    get_bindings(Vp, Mark, false).

%% get bindings and possible clause info until mark
get_bindings(_Vp, Mark, _ClauseInfo)
  when is_integer(Mark), Mark > 0 ->
    ?nif_stub().

%% initial index to use if using order_next, instead of order_first
order_init(_Vp) -> 
    1.

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

-spec order_sort(Vp::varc(), Sort::sort_key()) -> integer().
			
order_sort(_Vp, _Sort) ->
    ?nif_stub().

-spec order_sort(Vp::varc(), Sort::sort_key(),Arg::sort_value()) -> 
			integer().

order_sort(_Vp, _Sort, _Arg) ->
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

get_info(Vp) ->
    [ {Key,info(Vp, Key)} || Key <- info_keys()].

info_keys() ->
    [
     max_clause_length,
     number_of_clauses,
     number_of_variables,
     number_of_bound_variables,
     number_of_unbound_variables,
     clause_eval_counter,
     eval_counter,
     undo_stack_size,
     value_stack_size,
     class_stack_size,
     bcp,
     grow,
     size
    ].

get_number_of_variables(Vp) ->
    info(Vp, number_of_variables).

get_number_of_bound_variables(Vp) ->
    info(Vp, number_of_bound_variables).

get_number_of_unbound_variables(Vp) ->
    info(Vp, number_of_unbound_variables).

get_number_of_clauses(Vp) ->
    info(Vp, number_of_clauses).

get_max_clause_length(Vp) ->
    info(Vp, max_clause_length).

get_clause_eval_counter(Vp) ->
    info(Vp, clause_eval_counter).

get_eval_counter(Vp) ->
    info(Vp, eval_counter).
