%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2010, Tony Rogvall
%%% @doc
%%%    Variable/Class handling
%%% @end
%%% Created : 30 Aug 2010 by Tony Rogvall <tony@rogvall.se>

-module(varc).

%% -on_load(init/0).

-export([new/0, new/1, new/2, number_of_variables/1, new_variable/1]).
-export([is_literal/2, is_variable/2, is_bound/2]).
-export([first_unbound/1, next_unbound/2, number_of_unbound/1]).

-export([value/2, class/2, class_next/2]).
-export([equivalent/3, is_equivalent/3]).
-export([bound/1, bound_all/1]).
-export([mark/1, undo/1, commit/1]).
-export([undo_stack/1]).

-export([r_class_list/2, r_class_list/3, 
	 class_var_list/2, class_ulist/2, class_var_ulist/2]).

-define(TRUE,    1).
-define(FALSE,  -1).
-define(UNBOUND, 0).

-ifdef(debug).
-define(assert(C),
	case (C) of
	    true -> ok;
	    false -> 
		io:format("assertion: ~s failed\n", [??C]),
		erlang:error(assert)
	end).
-else.
-define(assert(C), ok).
-endif.

%% -define(dbg(F,As), io:format((F), (As))).
-define(dbg(F,As), ok).
%%
%% vt  map from positive number (>1) -> integer (!= 0)
%% vc  map from positive number (>1) -> integer (!= 0)
%%
-type var()     :: pos_integer().
-type literal() :: integer().     %% NOT 0,1,-1
-type value()   :: integer().     %% NOT 0

-record(vct,
	{
	  %% next free variable number
	  vn :: non_neg_integer, 
	  %% number of bound variables (vt entires != 0)
	  bn :: non_neg_integer, 
	  %% all bindings : Var -> Var | Value
	  vt :: array(), 
	  %% all variable classes
	  vc :: array(),
	  %% bound / undo information
	  undo :: [mark|{vt,var(),value()}|{vc,var(),literal()}]
	}).

%%--------------------------------------------------------------------
%% @doc
%%    Create a new variable context
%% @end
%%--------------------------------------------------------------------

new() ->
    new(1).

new(Size) ->
    new(Size, 1).

new(_Size, _Expand) ->
    #vct { 
     vn = 2,
     bn = 0,
     vt = array:new([{default, 0}]),
     vc = array:new([{default, 0}]),
     undo = []
    }.

%% @hidden
init() ->
    Nif = filename:join([code:lib_dir(varp),"priv","varc_nif"]),
    %% io:format("Loading: ~s\n", [Nif]),
    erlang:load_nif(Nif, 0).

%%--------------------------------------------------------------------
%% @doc
%%    
%% @end
%%--------------------------------------------------------------------

number_of_variables(Vct) ->
    Vct#vct.vn - 2.

%%--------------------------------------------------------------------
%% @doc
%%    
%% @end
%%--------------------------------------------------------------------

new_variable(Vct) ->
    Var = Vct#vct.vn,
    { Var, Vct#vct { vn = Var+1 }}.

%%--------------------------------------------------------------------
%% @doc
%%    
%% @end
%%--------------------------------------------------------------------
    

undo(Vct) ->
    undo_(Vct#vct.undo, Vct#vct.vt, Vct#vct.vc, Vct#vct.bn, Vct).

%% @hidden
undo_([{vt,X,X0}|Us], Vt, Vc, Bn, Vct) ->
    ?dbg("undo: ~w = ~w\n", [X, X0]),
    Vt1 = array:set(X, X0, Vt),
    undo_(Us, Vt1, Vc, Bn-1, Vct);
undo_([{vc,Y,Y0}|Us], Vt, Vc, Bn, Vct) ->
    ?dbg("undo: class ~w = ~w\n", [Y, Y0]),
    Vc1 = array:set(Y, Y0, Vc),
    undo_(Us, Vt, Vc1, Bn, Vct);
undo_([mark|Us], Vt, Vc, Bn, Vct) ->
    Vct#vct { undo = Us, vt = Vt, vc = Vc, bn=Bn };
undo_([], Vt, Vc, Bn, Vct) ->
    Vct#vct { undo = [], vt = Vt, vc = Vc, bn=Bn }.

undo_stack(Vct) ->
    Vct#vct.undo.

%%--------------------------------------------------------------------
%% @doc
%%    Commit all binding upto last mark
%% @end
%%--------------------------------------------------------------------

commit(Vct) ->
    Vct#vct { undo = commit_(Vct#vct.undo) }.

commit_([mark|Us]) -> Us;
commit_([_|Us]) -> commit_(Us);
commit_([]) -> [].

%%--------------------------------------------------------------------
%% @doc
%%    Set a mark in the undo stack
%% @end
%%--------------------------------------------------------------------

mark(Vct) ->
    Vct#vct { undo = [mark|Vct#vct.undo]}.

%%--------------------------------------------------------------------
%% @doc
%%    Return value of a variable or a constant
%%    unbound variables will return the class variable
%% @end
%%--------------------------------------------------------------------

value(?FALSE, _Vct) -> ?FALSE;
value(?TRUE, _Vct)  -> ?TRUE;
value(X, Vct) when X < ?FALSE ->
    case array:get(-X, Vct#vct.vt) of
	0 -> X;
	X1 -> value(-X1, Vct)
    end;
value(X, Vct) when X > ?TRUE ->
    case array:get(X, Vct#vct.vt) of
	0 -> X;
	X1 -> value(X1, Vct)
    end.

%%--------------------------------------------------------------------
%% @doc
%%    Test if X is a literal, that is a variable or negated variable   
%% @end
%%--------------------------------------------------------------------

is_literal(X, Vct) when X > 1,  X < Vct#vct.vn  -> true;
is_literal(X, Vct) when X < -1, X > -Vct#vct.vn -> true;
is_literal(?TRUE, _Vct) -> false;
is_literal(?FALSE, _Vct) -> false.

%%--------------------------------------------------------------------
%% @doc
%%     Test if X is a variable, bound or unbund.
%% @end
%%--------------------------------------------------------------------

is_variable(X, _Vct) when X =< ?TRUE -> false;
is_variable(X, Vct) -> X < Vct#vct.vn.

%%--------------------------------------------------------------------
%% @doc
%%     Test if X is bound to a value or an other variable
%% @end
%%--------------------------------------------------------------------

is_bound(X, Vct) when X < 0 ->
    is_bound(-X, Vct);
is_bound(X, Vct) ->
    (array:get(X, Vct#vct.vt)) =/= 0.

%%--------------------------------------------------------------------
%% @doc
%%     List of recently bound variables (until mark)
%% @end
%%--------------------------------------------------------------------

bound(Vct) ->
    bound(Vct#vct.undo, []).

bound([mark|_], Xs) -> Xs;
bound([{vt,X,_}|Us], Xs)   -> bound(Us, [X|Xs]);
bound([{vc,_,_}|Us], Xs)   -> bound(Us, Xs);
bound([], Xs)       -> Xs.

%%--------------------------------------------------------------------
%% @doc
%%     List of all bound variables
%% @end
%%--------------------------------------------------------------------

bound_all(Vct) ->
    bound_all(Vct#vct.undo, []).

bound_all([mark|Us], Xs)      -> bound_all(Us,Xs);
bound_all([{vt,X,_}|Us], Xs)  -> bound_all(Us, [X|Xs]);
bound_all([{vc,_,_}|Us], Xs)  -> bound_all(Us, Xs);
bound_all([], Xs)        -> Xs.

%%--------------------------------------------------------------------
%% @doc
%%     Find next variable in a variable class, create with equivalent.
%% @end
%%--------------------------------------------------------------------

class_next(X, Vct) ->
    array:get(X, Vct#vct.vc).

class(?FALSE, _Vct) -> ?FALSE;
class(?TRUE, _Vct)  -> ?TRUE;
class(X, Vct) when X < ?FALSE ->
    case array:get(-X, Vct#vct.vc) of
	0 -> X;
	X1 -> class(-X1,Vct)
    end;
class(X, Vct) when X > ?TRUE ->
    case array:get(X, Vct#vct.vc) of
	0 -> X;
	X1 -> class(X1,Vct)
    end.

%%--------------------------------------------------------------------
%% @doc
%%     Get first unbound variable
%% @end
%%--------------------------------------------------------------------
first_unbound(Vct) ->
    next_unbound(1, Vct).

%%--------------------------------------------------------------------
%% @doc
%%     Get next unbound variable
%% @end
%%--------------------------------------------------------------------

next_unbound(I, Vct) ->
    next_unbound_(I+1, number_of_variables(Vct), Vct).

%% Major FIXME:
%% Note that I i goes from 2 .. N+1
%% N = number_of_variabeles = 1 => I = 2
%% N = number_of_variabeles = 2 => I = 2, I = 3
%%
next_unbound_(I, N, _Vct) when I > N+1 ->
    none;
next_unbound_(I, N, Vct) ->
    case is_bound(I, Vct) of
	true -> next_unbound_(I+1,N,Vct);
	false -> I
    end.

%% Number of variables not bound
number_of_unbound(Vct) ->
    number_of_variables(Vct) - Vct#vct.bn.

%%--------------------------------------------------------------------
%% @doc
%%     Get all variables in the class X (reversed)
%% @end
%%--------------------------------------------------------------------

r_class_list(X, Vct) ->
    r_class_list(X, Vct, []).

r_class_list(0,_Vct,Vs) -> 
    Vs;
r_class_list(Xc,Vct,Vs) ->
    if Xc =< ?FALSE ->
	    Xc1 = array:get(-Xc, Vct#vct.vc),
	    r_class_list(-Xc1,Vct,[Xc|Vs]);
       Xc >= ?TRUE ->
	    Xc1 = array:get(Xc, Vct#vct.vc),
	    r_class_list(Xc1,Vct,[Xc|Vs])
    end.

%%--------------------------------------------------------------------
%% @doc
%%     Get all literals found among classes in Xs (reversed)
%% @end
%%--------------------------------------------------------------------

class_var_list(Xs,Vct) ->
    class_var_list(Xs,Vct,[]).

class_var_list([X|Xs],Vct,Vs) ->
    Vs1 = r_class_list(X,Vct,Vs),
    class_var_list(Xs,Vct,Vs1);
class_var_list([],_Vct,Vs) ->
    Vs.

%%--------------------------------------------------------------------
%% @doc
%%     Get all variables in X
%% @end
%%--------------------------------------------------------------------

class_ulist(?FALSE, _Vct) -> [];
class_ulist(?TRUE, _Vct) -> [];
class_ulist(X, Vct) ->
    class_ulist(X, Vct, []).

class_ulist(0,_Vct,Vs) -> Vs;
class_ulist(Xc,Vct,Vs) ->
    if Xc < ?FALSE ->
	    Xc1 = array:get(-Xc, Vct#vct.vc),
	    class_ulist(-Xc1,Vct,[-Xc|Vs]);
       Xc > ?TRUE ->
	    Xc1 = array:get(Xc, Vct#vct.vc),
	    class_ulist(Xc1,Vct,[Xc|Vs])
    end.

%%--------------------------------------------------------------------
%% @doc
%%     Get all variables among Xs
%% @end
%%--------------------------------------------------------------------

class_var_ulist(Xs,Vct) ->
    class_var_ulist(Xs,Vct,[]).

class_var_ulist([X|Xs],Vct,Vs) ->
    Vs1 = class_ulist(X,Vct,Vs),
    class_var_ulist(Xs,Vct,Vs1);
class_var_ulist([],_Vct,Vs) ->
    Vs.


%%--------------------------------------------------------------------
%% @doc
%%     Test if X and Y belong to same variable class (with same sign)
%% @end
%%--------------------------------------------------------------------

is_equivalent(X, Y, Vct) ->
    class(X,Vct) =:= class(Y,Vct).


%%--------------------------------------------------------------------
%% @doc
%%     Make X and Y equivalent, belong to same equivalence class
%% @end
%%--------------------------------------------------------------------

equivalent(X, Y, Vct) ->
    ?assert(is_literal(X,Vct) andalso not is_bound(X,Vct)),
    X0 = array:get(X, Vct#vct.vt),
    ?dbg("equivalent: ~w = ~w\n", [X, Y]),
    Vt = array:set(X, Y, Vct#vct.vt),
    U0 = [{vt,X,X0}|Vct#vct.undo],
    Bn = Vct#vct.bn + 1,
    case class(Y,Vct) of
	?TRUE  -> 
	    Vct#vct { vt = Vt, undo=U0, bn=Bn };
	?FALSE -> 
	    Vct#vct { vt = Vt, undo=U0, bn=Bn };
	Yc when Yc < 0 ->
	    Y0 = array:get(-Yc, Vct#vct.vc),
	    ?dbg("equivalent: class ~w = ~w\n", [-Yc, -X]),
	    Vc = array:set(-Yc, -X, Vct#vct.vc),
	    U1 = [{vc,-Yc,Y0}|U0],
	    Vct#vct { vt = Vt, vc = Vc, undo=U1, bn=Bn };
 	Yc ->
	    Y0 = array:get(Yc, Vct#vct.vc),
	    ?dbg("equivalent: class ~w = ~w\n", [Yc, X]),
 	    Vc = array:set(Yc, X, Vct#vct.vc),
	    U1 = [{vc,Yc,Y0}|U0],
 	    Vct#vct { vt = Vt, vc = Vc, undo=U1, bn=Bn }
    end.

    

