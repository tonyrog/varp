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
-export([get_number_of_variables/1]).
-export([get/2]).
-export([put/3]).
-export([class/2]).
-export([occure/2]).
-export([is_variable/2]).
-export([is_bound/2]).
-export([class_next/2]).
-export([equal/3]).
-export([mark/2]).
-export([undo/1]).
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
-export([get_number_of_clauses/1]).
-export([get_clauses/2]).
-export([get_queue/1]).
-export([clear_queue/1]).
-export([get_bindings/2]).
-export([order_first/1, order_next/2]).
-export([order_sort/2, order_sort/3]).
-export([order_all/1]).
-export([sat/1, sat/2]).

-ifdef(debug).
-define(debug(F,A), io:format((F),(A))).
-else.
-define(debug(F,A), ok).
-endif.

-define(is_varc(Varc), is_binary(Varc)).
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

add_variable(Varc) when ?is_varc(Varc) ->
    ?nif_stub().

get_number_of_variables(Varc) when ?is_varc(Varc) ->
    ?nif_stub().

get(Varc, Lit) when ?is_varc(Varc), is_integer(Lit) ->
    ?nif_stub().

put(Varc, LitA, LitB) when ?is_varc(Varc), 
			   is_integer(LitA),
			   is_integer(LitB) ->
    ?nif_stub().


class(Varc, Lit) when ?is_varc(Varc), is_integer(Lit) ->
    ?nif_stub().

occure(Varc, Lit) when ?is_varc(Varc), is_integer(Lit) ->
    ?nif_stub().

is_variable(Varc, Lit) when ?is_varc(Varc), is_integer(Lit) ->
    ?nif_stub().

is_bound(Varc, Lit) when ?is_varc(Varc), is_integer(Lit) ->
    ?nif_stub().

class_next(Varc, Lit) when ?is_varc(Varc), is_integer(Lit) ->
    ?nif_stub().

equal(Varc, LitA, LitB) when ?is_varc(Varc), 
			     is_integer(LitA),
			     is_integer(LitB) ->
    ?nif_stub().

mark(Varc,Level) when ?is_varc(Varc), is_integer(Level), Level >= 0 ->
    ?nif_stub().

undo(Varc) when ?is_varc(Varc) ->
    ?nif_stub().

eval(Varc) when ?is_varc(Varc) ->
    ?nif_stub().

get_number_of_clauses(Varc) when ?is_varc(Varc) ->
    ?nif_stub().

add_clause(Varc,Op,Ls) when ?is_varc(Varc), ?is_op(Op), is_list(Ls) ->
    ?nif_stub().

add_clause(Varc,Op,X1,X2)
  when ?is_varc(Varc), ?is_op(Op),
       is_integer(X1),
       is_integer(X2) ->
    ?nif_stub().

add_clause(Varc,Op,X1,X2,X3) 
  when ?is_varc(Varc), ?is_op(Op),
       is_integer(X1),
       is_integer(X2),
       is_integer(X3) ->
    ?nif_stub().

add_clause(Varc,Op,X1,X2,X3,X4) when 
      ?is_varc(Varc), ?is_op(Op),
      is_integer(X1),
      is_integer(X2),
      is_integer(X3),
      is_integer(X4) ->
    ?nif_stub().

add_clause(Varc,Op,X1,X2,X3,X4,X5) when 
      ?is_varc(Varc), ?is_op(Op),
      is_integer(X1),
      is_integer(X2),
      is_integer(X3),
      is_integer(X4),
      is_integer(X5) ->
    ?nif_stub().

add_clause(Varc,Op,X1,X2,X3,X4,X5,X6) when 
      ?is_varc(Varc), ?is_op(Op),
      is_integer(X1),
      is_integer(X2),
      is_integer(X3),
      is_integer(X4),
      is_integer(X5),
      is_integer(X6) ->
    ?nif_stub().

get_clause(Varc,Index)
  when ?is_varc(Varc), is_integer(Index), Index >= 0 ->
    ?nif_stub().

get_clause_flags(Varc,Index)
  when ?is_varc(Varc), is_integer(Index), Index >= 0 ->
    ?nif_stub().

del_clause(Varc,Index)
  when ?is_varc(Varc), is_integer(Index), Index >= 0 ->
    ?nif_stub().

get_clauses(Varc,Var)
  when ?is_varc(Varc), is_integer(Var), Var >= 0 ->
    ?nif_stub().

get_queue(Varc)
  when ?is_varc(Varc) ->
    ?nif_stub().

clear_queue(Varc)
  when ?is_varc(Varc) ->
    ?nif_stub().

get_bindings(Varc, Level)
  when ?is_varc(Varc), is_integer(Level), Level >= 0 ->
    ?nif_stub().

%% return {Ix,Var} | false
order_first(Varc) 
  when ?is_varc(Varc) ->
    ?nif_stub().

order_next(Varc, Ix)
  when ?is_varc(Varc), is_integer(Ix), Ix > 0 ->
    ?nif_stub().

order_sort(Varc, Sort) 
  when ?is_varc(Varc),
       ((Sort =:= id) orelse (Sort =:= random) orelse (Sort =:= occure)) ->
    ?nif_stub().

order_sort(Varc, Sort, Arg) 
  when ?is_varc(Varc),
       ((Sort =:= id) orelse (Sort =:= random) orelse (Sort =:= occure)),
       is_integer(Arg) ->
    ?nif_stub().

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

%% satify the rules, stop at first model or return false
sat(V) ->
    sat(V,0).

sat(V,M) ->
    put(conflicts, 0),
    case eval(V) of
	false -> 0;
	true ->
	    case order_first(V) of
		false -> model(V), 1;
		{I,Var} -> sat__(V,I,0,M,1,Var)
	    end
    end.

sat_(V,I,N,M,D) ->
    case eval(V) of
	false ->
	    put(conflicts, get(conflicts)+1),
	    N;
	true ->
	    case order_next(V,I) of
		false -> model(V), N+1;
		{I1,Var} -> sat__(V,I1,N,M,D+1,Var)
	    end
    end.

sat__(V,I,N,M,D,Var) ->
    mark(V, D),
    clear_queue(V),
    put(V, Var, false),
    N1 = sat_(V,I,N,M,D),
    undo(V),
    if M > 0, N1 >= M -> N1;
       true ->
	    mark(V, D),
	    clear_queue(V),
	    put(V, Var, true),
	    N2 = sat_(V,I,N1,M,D),
	    undo(V),
	    N2
    end.
    
model(V) ->
    io:format("~w\n", [varc:get_bindings(V, 0)]).
