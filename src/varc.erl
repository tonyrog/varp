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
-export([add_variable/1]).
-export([number_of_variables/1]).
-export([value/2]).
-export([class/2]).
-export([is_variable/2]).
-export([is_bound/2]).
-export([class_next/2]).
-export([equivalent/3]).
-export([is_equivalent/3]).
-export([mark/1]).
-export([undo/1]).
-export([add_clause/3]).
-export([add_clause/4]).
-export([add_clause/5]).
-export([add_clause/6]).
-export([add_clause/7]).
-export([add_clause/8]).
-export([get_clause/2]).
-export([number_of_clauses/1]).

-ifdef(debug).
-define(debug(F,A), io:format((F),(A))).
-else.
-define(debug(F,A), ok).
-endif.

-define(is_varc(Varc), is_binary(Varc)).
-define(is_op(Op), (((Op) =:= 'and') orelse ((Op) =:= 'or') orelse ((Op) =:= 'xor'))).

init() ->
    Nif = filename:join([code:priv_dir(varp), "varc_nif"]),
    ?debug("Loading: ~s\n", [Nif]),
    erlang:load_nif(Nif, 0).


new() ->
    erlang:error(nif_not_loaded).

new(Size) when is_integer(Size), Size >= 0 ->
    erlang:error(nif_not_loaded).

new(Size,Expand) when is_integer(Size), Size >= 0,
		      is_integer(Expand), Expand >= 0 ->
    erlang:error(nif_not_loaded).

add_variable(Varc) when ?is_varc(Varc) ->
    erlang:error(nif_not_loaded).

number_of_variables(Varc) when ?is_varc(Varc) ->
    erlang:error(nif_not_loaded).

value(Varc, Lit) when ?is_varc(Varc), is_integer(Lit) ->
    erlang:error(nif_not_loaded).

class(Varc, Lit) when ?is_varc(Varc), is_integer(Lit) ->
    erlang:error(nif_not_loaded).

is_variable(Varc, Lit) when ?is_varc(Varc), is_integer(Lit) ->
    erlang:error(nif_not_loaded).

is_bound(Varc, Lit) when ?is_varc(Varc), is_integer(Lit) ->
    erlang:error(nif_not_loaded).

class_next(Varc, Lit) when ?is_varc(Varc), is_integer(Lit) ->
    erlang:error(nif_not_loaded).

equivalent(Varc, LitA, LitB) when ?is_varc(Varc), 
				  is_integer(LitA),
				  is_integer(LitB) ->
    erlang:error(nif_not_loaded).

is_equivalent(Varc, LitA, LitB) when ?is_varc(Varc), 
				     is_integer(LitA),
				     is_integer(LitB) ->
    erlang:error(nif_not_loaded).

mark(Varc) when ?is_varc(Varc) ->
    erlang:error(nif_not_loaded).

undo(Varc) when ?is_varc(Varc) ->
    erlang:error(nif_not_loaded).

number_of_clauses(Varc) when ?is_varc(Varc) ->
    erlang:error(nif_not_loaded).

add_clause(Varc,Op,Ls) when ?is_varc(Varc), ?is_op(Op), is_list(Ls) ->
    erlang:error(nif_not_loaded).

add_clause(Varc,Op,X1,X2)
  when ?is_varc(Varc), ?is_op(Op),
       is_integer(X1),
       is_integer(X2) ->
    erlang:error(nif_not_loaded).

add_clause(Varc,Op,X1,X2,X3) 
  when ?is_varc(Varc), ?is_op(Op),
       is_integer(X1),
       is_integer(X2),
       is_integer(X3) ->
    erlang:error(nif_not_loaded).

add_clause(Varc,Op,X1,X2,X3,X4) when 
      ?is_varc(Varc), ?is_op(Op),
      is_integer(X1),
      is_integer(X2),
      is_integer(X3),
      is_integer(X4) ->
    erlang:error(nif_not_loaded).

add_clause(Varc,Op,X1,X2,X3,X4,X5) when 
      ?is_varc(Varc), ?is_op(Op),
      is_integer(X1),
      is_integer(X2),
      is_integer(X3),
      is_integer(X4),
      is_integer(X5) ->
    erlang:error(nif_not_loaded).

add_clause(Varc,Op,X1,X2,X3,X4,X5,X6) when 
      ?is_varc(Varc), ?is_op(Op),
      is_integer(X1),
      is_integer(X2),
      is_integer(X3),
      is_integer(X4),
      is_integer(X5),
      is_integer(X6) ->
    erlang:error(nif_not_loaded).

get_clause(Varc,Index)
    when ?is_varc(Varc), is_integer(Index), Index >= 0 ->
    erlang:error(nif_not_loaded).
