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
-export([get_clauses/2]).
-export([get_queue/1]).
-export([clear_queue/1]).
-export([get_bindings/2]).
-export([order_first/1, order_next/2]).
-export([order_sort/2, order_sort/3]).
-export([order_all/1]).

-export([sat/1, sat/2]).
-export([saturate/2]).

-export([get_max_clause_length/1]).
-export([get_number_of_variables/1]).
-export([get_number_of_clauses/1]).


-ifdef(debug).
-define(debug(F,A), io:format((F),(A))).
-else.
-define(debug(F,A), ok).
-endif.

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

get(_Vp, Lit) when is_integer(Lit) ->
    ?nif_stub().

put(_Vp, LitA, LitB) when is_integer(LitA),
			  is_integer(LitB) ->
    ?nif_stub().


class(_Vp, Lit) when is_integer(Lit) ->
    ?nif_stub().

occure(_Vp, Lit) when is_integer(Lit) ->
    ?nif_stub().

is_variable(_Vp, Lit) when is_integer(Lit) ->
    ?nif_stub().

is_bound(_Vp, Lit) when is_integer(Lit) ->
    ?nif_stub().

class_next(_Vp, Lit) when is_integer(Lit) ->
    ?nif_stub().

equal(_Vp, LitA, LitB) when is_integer(LitA),
			    is_integer(LitB) ->
    ?nif_stub().

mark(_Vp,Level) when is_integer(Level), Level >= 0 ->
    ?nif_stub().

undo(_Vp) ->
    ?nif_stub().

eval(_Vp) ->
    ?nif_stub().

add_clause(_Vp,Op,Ls) when ?is_op(Op), is_list(Ls) ->
    ?nif_stub().

add_clause(_Vp,Op,X1,X2)
  when ?is_op(Op),
       is_integer(X1),
       is_integer(X2) ->
    ?nif_stub().

add_clause(_Vp,Op,X1,X2,X3) 
  when ?is_op(Op),
       is_integer(X1),
       is_integer(X2),
       is_integer(X3) ->
    ?nif_stub().

add_clause(_Vp,Op,X1,X2,X3,X4) when 
      ?is_op(Op),
      is_integer(X1),
      is_integer(X2),
      is_integer(X3),
      is_integer(X4) ->
    ?nif_stub().

add_clause(_Vp,Op,X1,X2,X3,X4,X5) when 
      ?is_op(Op),
      is_integer(X1),
      is_integer(X2),
      is_integer(X3),
      is_integer(X4),
      is_integer(X5) ->
    ?nif_stub().

add_clause(_Vp,Op,X1,X2,X3,X4,X5,X6) when 
      ?is_op(Op),
      is_integer(X1),
      is_integer(X2),
      is_integer(X3),
      is_integer(X4),
      is_integer(X5),
      is_integer(X6) ->
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

get_queue(_Vp) ->
    ?nif_stub().

clear_queue(_Vp) ->
    ?nif_stub().

get_bindings(_Vp, Level)
  when is_integer(Level), Level >= 0 ->
    ?nif_stub().

%% return {Ix,Var} | false
order_first(_Vp) ->
    ?nif_stub().

order_next(_Vp, Ix)
  when is_integer(Ix), Ix > 0 ->
    ?nif_stub().

order_sort(_Vp, Sort) 
  when ((Sort =:= id) orelse (Sort =:= random) orelse (Sort =:= occure)) ->
    ?nif_stub().

order_sort(_Vp, Sort, Arg) 
  when ((Sort =:= id) orelse (Sort =:= random) orelse (Sort =:= occure)),
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

get_number_of_variables(Vp) ->
    info(Vp, number_of_variables).

get_number_of_clauses(Vp) ->
    info(Vp, number_of_clauses).

get_max_clause_length(Vp) ->
    info(Vp, max_clause_length).


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


%% saturate clause set
saturate(Vp,0) ->
    eval(Vp);
saturate(Vp,1) -> %% K=1 only now
    case eval(Vp) of
	false -> false;
	true  ->
	    case order_first(Vp) of
		false -> false;
		{I,Var} -> 
		    saturate_(Vp,I,1,Var)
	    end
    end.

saturate_(Vp,I,D,Var) ->
    case saturate_1(Vp,D,Var) of
	false -> false;
	true ->
	    case order_next(Vp,I) of
		false -> true;
		{I1,Var1} ->
		    saturate_(Vp,I1,D,Var1)
	    end
    end.

%% do one variable
%% false is contradiction true is ok
saturate_1(Vp,D,Var) ->
    io:format("saturate1_: var=~w\n", [Var]),
    mark(Vp, D),
    clear_queue(Vp),
    case put(Vp,Var,false) and eval(Vp) of
	false ->
	    undo(Vp),
	    put(Vp, Var, true) and eval(Vp);
	true ->	    
	    Bs0 = get_bindings(Vp, D), %% Var=false is present!
	    undo(Vp),
	    mark(Vp, D),
	    clear_queue(Vp), %% needed?
	    case put(Vp,Var,true) and eval(Vp) of
		false ->
		    undo(Vp),
		    put(Vp,Var,false) and eval(Vp);
		true ->
		    %% intersect bindings Bs0 with current bindings
		    Bs = intersect(Vp, Var, Bs0),
		    io:format("intersect Bs=~w\n", [Bs]),
		    undo(Vp),
		    clear_queue(Vp), %% needed?
		    _ = [ put(Vp,B,V) || {B,V} <- Bs],
		    eval(Vp)
	    end
    end.

%% Vp is under the assumption that Var = TRUE
%% The bindings Bs0 are from the evaluation when Var = FALSE
%% evaluate the bindings and build the intersection
intersect(Vp, Var, [{Var,false}|Bs0]) -> %% we may have this bindings, ignore
    intersect(Vp,Var,Bs0);
intersect(Vp, Var, [{X,true}|Bs0]) ->
    %% !Var -> X
    case get(Vp, X) of
	true ->  %% Var -> X, !Var -> X   =>  X
	    [{X,true} | intersect(Vp,Var,Bs0)];
	false -> %% Var -> !X, !Var -> X  =>  Var=!X
	    [{Var,-X} | intersect(Vp,Var,Bs0)];
	_ ->
	    intersect(Vp,Var,Bs0)
    end;
intersect(Vp, Var, [{X,false}|Bs0]) ->
    %% !Var -> !X
    case get(Vp, X) of
	true ->  %% Var -> X, !Var -> !X   =>  Var=X
	    [{Var,X} | intersect(Vp,Var,Bs0)];
	false -> %% Var -> !X, !Var -> !X  =>  !X
	    [{X,false} | intersect(Vp,Var,Bs0)];
	_ ->
	    intersect(Vp,Var,Bs0)
    end;
intersect(Vp, Var, [{X,Y}|Bs0]) ->
    %% !Var => X=Y
    case {get(Vp, X),get(Vp,Y)} of
	{Z,Z} -> %% !Var -> X=Y, Var => X=Y => X=Y
	    [{X,Y} | intersect(Vp,Var,Bs0)];
	_ ->
	    intersect(Vp,Var,Bs0)
    end;
intersect(_Vp,_Var,[]) ->
    [].


	    
	    
	    

    

	    
    
    
