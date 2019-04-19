%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2012, Tony Rogvall
%%% @doc
%%%    Building formulas
%%% @end
%%% Created :  2 Sep 2012 by Tony Rogvall <tony@rogvall.se>

-module(varp_formula).

-export([build/1, build/2]).
-export([new/0, new/1]).
-export([fresh_var/1]).
-export([add_variable/1]).
-export([variable/2, alias/3]).
-export([value/2, class/2]).
-export([get_info/1, get_info/2]).
-export([fmt_var/2, fmt_v/2, fmt_q/2]).
-export([fmt_var_list/2]).
-export([fmt_bind/4]).
-export([fmt_bind/3]).
-export([fmt_bind_list/2]).
-export([print/3]).
-export([find_var/2, get_var/2]).
-export([uint64/2, uint32/2, uint16/2, uint8/2]).
-export([format_p/1]).
-export([or_gate/3, and_gate/3, xor_gate/3]).
-export([or_clause/2, and_clause/2]).
-export([format_literal/2, format_literal/3]).
-export([format_literals/2, format_literals/3]).
-export([format_var/2]).
-export([format_clause/2, format_clause/3]).


%% building with operations
-export([operation/4, operation/3]).
-export([all/2, any/2]).
-export([eqk/4, gtk/4]).
-export([equal/3, equal/4]).
-export([is_equivalent/3]).
-export([is_equal/3]).
-export([is_bound/2]).
-export([is_unbound/2]).
-export([getopt/2, setopt/3]).
-export([number_of_variables/1]).
-export([number_of_bound/1]).
-export([number_of_unbound/1]).
-export([clause_eval_counter/1]).
-export([eval_counter/1]).
-export([order_sort/2, order_sort/4]).
-export([order_sort_first/2]).
-export([order_sort_last/2]).
-export([model/1, model/2]).
-export([first_init/1]).
-export([first_unbound/1]).
-export([next_unbound/2, next_unbound/3]).
-export([latest_bound/1]).
-export([info/3, debug/3]).
-export([get_bindings/2]).
-export([intersect/3]).
-export([model_variables/2]).
-export([clear_queue/1]).
-export([enqueue_all/1]).
-export([eval/1]).
-export([mark/1, mark/2]).
-export([remove_mark/1, remove_mark/2]).
-export([undo/1, undo/2]).
-export([vfold_op/4]).
-export([conflicting_clause/1]).
-export([implication_clause/2]).
-export([get_clause/2]).
-export([get_clause_flags/2]).
-export([add_clause/3]).
-export([use_clause/3]).
-export([set_var/3, add_var/4]).

-import(lists, [map/2, reverse/1, foldl/3]).

-include("log.hrl").
-include("varp.hrl").

-define(is_int_type(T),   (((T)=:=int) orelse ((T)=:=uint))).
-define(is_vec_type(T), (((T)=:=int) orelse ((T)=:=uint) orelse ((T)=:=bit))).

-type pred() :: {p,Name::atom(),[index()]}.
-type index() :: integer() | atom() | [integer()|atom()] | func().
-type func() :: {f,Name::atom(),[index()]}.

-type var() :: pred() |
	       {uint,pred(),Size::integer(),Bit::integer()} |
	       {int,pred(),Size::integer(),Bit::integer()} |
	       {bit,pred(),Size::integer(),Bit::integer()}.

-define(dbg0(F,As), ok).
%%-define(dbg(F,A), io:format((F),(A))).
%%-define(dcall(Fun), Fun()).
-define(dbg(F,A), ok).
-define(dcall(Fun), ok).

new() ->
    new(varp_option:default_option()).
%%
%% FIXME
%%  add options [{initial_size,Size},{grow,Expand},{bcp,boolean()}]
%%
new(OptMap) when is_map(OptMap) ->
    Vp  = varc:new([{bcp,maps:get(bcp,OptMap)}]),
    Counters = counters:new(?NUM_COUNTERS, []),
    #bs {
       option = OptMap,
       vs = #{ true => ?TRUE,
	       ?TRUE => true,
	       false => ?FALSE,
	       ?FALSE => false},
       meta = maps:get(meta,OptMap),
       defs = maps:get(defs,OptMap),
       decls = maps:get(decls,OptMap),
       literals = maps:get(literals,OptMap),
       counters = Counters,
       vp    = Vp
      }.

fresh_var(Bs) ->
    Var = varc:add_variable(Bs#bs.vp),
    {Var,Bs}.

add_variable(Bs) ->
    varc:add_variable(Bs#bs.vp).

%% build an OR gate with Y as output and Xs as input
%% Y = X1 or X2 .. or Xn
or_gate(Bs,Y,Xs) ->
    clause(Bs, 'or', [Y|Xs]).

%% build an AND gate with Y as output and Xs as input
%% Y = X1 and X2 .. and Xn =>  !Y = !X1 or !X2 ... !Xn
%%
and_gate(Bs,Y,Xs) ->
    clause(Bs, 'or', [-Y|[-L||L<-Xs]]).

%% build an OR gate with Y as output and Xs as input
%% Y = X1 xor X2 .. xor Xn
xor_gate(Bs,Y,Xs) ->
    clause(Bs, 'xor', [Y|Xs]).

%% build an OR clause with Xs as input
%% 1 = X1 or X2 .. or Xn
or_clause(Bs,Xs) ->
    clause(Bs, 'or', [?TRUE|Xs]).

%% build an AND clause with Xs as input
%% 0 = X1 and X2 .. and Xn => 1 = !X1 or !X2 .. or !Xn
and_clause(Bs,Xs) ->
    clause(Bs, 'or', [?TRUE|[-L||L<-Xs]]).

clause(Bs,'or',Ls=[X,Y,Z]) when abs(X) =/= 1 ->  %% or 2-gate
    case varp_option:getopt(clause,Bs#bs.option) of
	false -> %% install as gate
	    add_clause(Bs,'or',Ls),
	    Bs;
	true -> %% install as clauses
	    add_clause(Bs,'or',[1,-X,Y,Z]),
	    add_clause(Bs,'or',[1,X,-Y]),
	    add_clause(Bs,'or',[1,X,-Z]),
	    Bs
    end;
clause(Bs,'xor',Ls=[X,Y,Z]) ->
    Clause = varp_option:getopt(clause,Bs#bs.option),
    if not Clause -> %% install as gate
	    add_clause(Bs,'xor',Ls),
	    Bs;
	X =:= 1 ->
	    add_clause(Bs,'or',[1,-Y,-Z]),
	    add_clause(Bs,'or',[1,Y,Z]),
	    Bs;
	X =:= -1 ->
	    add_clause(Bs,'or',[1,-Y,Z]),
	    add_clause(Bs,'or',[1,Y,-Z]),
	    Bs;
	true -> %% install as clauses
	    add_clause(Bs,'or',[1,X,-Y,Z]),
	    add_clause(Bs,'or',[1,X,Y,-Z]),
	    add_clause(Bs,'or',[1,-X,-Y,-Z]),
	    add_clause(Bs,'or',[1,-X,Y,Z]),
	    Bs
    end;
clause(Bs,'or',Ls=[X,_,_|_]) when abs(X) =/= 1 -> %% or n-gate
    case varp_option:getopt(clause,Bs#bs.option) of
	false ->
	    L = length(Ls),
	    N = varc:get_max_clause_length(Bs#bs.vp),
	    if L =< N ->
		    _Cix = add_clause(Bs,'or',Ls),
		    Bs;
	       true ->
		    build_clause_tree(Bs,'or',hd(Ls),tl(Ls),L-1,N)
	    end;
	true -> %% install n-gate as clauses
	    build_gate_tree(Bs,'or',hd(Ls),tl(Ls))
    end;
clause(Bs,'xor',Ls=[X,_,_|_]) when abs(X) =/= 1 -> %% or n-gate
    case varp_option:getopt(clause,Bs#bs.option) of
	false ->
	    L = length(Ls),
	    N = varc:get_max_clause_length(Bs#bs.vp),
	    if L =< N ->
		    _Cix = add_clause(Bs,'xor',Ls),
		    Bs;
	       true ->
		    build_clause_tree(Bs,'xor',hd(Ls),tl(Ls),L-1,N)
	    end;
	true -> %% install n-gate as clauses
	    build_gate_tree(Bs,'xor',hd(Ls),tl(Ls))
    end;
clause(Bs,Op,Ls) ->
    ?dbg("clause: {~w,~w}\n", [Op,Ls]),
    L = length(Ls),
    N = varc:get_max_clause_length(Bs#bs.vp),
    if L =< N ->
	    _Cix = add_clause(Bs,Op,Ls),
	    Bs;
       true ->
	    build_clause_tree(Bs,Op,hd(Ls),tl(Ls),L-1,N)
    end.

add_clause(Bs,Op,Ls) ->
    case varc:add_clause(Bs#bs.vp,Op,Ls) of
	{false,_I} ->
	    error(conflict_clause_error);
	{true,I} -> %% non conflict
	    ?dcall(fun() ->
			   {_,[?TRUE|CL]} = varc:get_clause(Bs#bs.vp, I),
			   Flags = varc:get_clause_flags(Bs#bs.vp, I),
			   {W0,W1} = proplists:get_value(watch, Flags, {-1,-1}),
			   io:format("~w:(~w,~w) ~s\n", 
				     [I,W0,W1,format_clause(Bs,CL)])
		   end),
	    I;
	true ->
	    ?dcall(fun() ->
			   io:format("dead clause: ~s\n", 
				     [format_clause(Bs,Ls)])
		   end),
	    true
    end.
		

build_gate_tree(Bs,Op,X,Ls) ->
    case lists:split(length(Ls) div 2,Ls) of
	{[U],[V]} ->
	    clause(Bs,'or',[X,U,V]);
	{[U],[V1,V2]} ->
	    X1 = varc:add_variable(Bs#bs.vp),
	    Bs1=clause(Bs,'or',[X1,V1,V2]),
	    clause(Bs1,'or',[X,U,X1]);
	{Us,Vs} ->
	    X1 = varc:add_variable(Bs#bs.vp),
	    Bs2=build_gate_tree(Bs,Op,X1,Us),
	    X2 = varc:add_variable(Bs#bs.vp),
	    Bs3=build_gate_tree(Bs2,Op,X2,Vs),
	    clause(Bs3,'or',[X,X1,X2])
    end.

build_clause_tree(Bs,Op,X,Ls,L,N) ->
    Ls1 = build_branch_list(Bs,Op,Ls,L,N),
    L1 = length(Ls1),
    if L1 >= N ->
	    build_clause_tree(Bs,Op,X,Ls1,L1,N);
       true ->
	    _Cix = add_clause(Bs,Op,[X|Ls1]),
	    Bs
    end.

%% build clauses of size <= N retrun a list of clause variables
build_branch_list(_Bs,_Op,[V],1,_N) -> [V];
build_branch_list(_Bs,_Op,[],0,_N) -> [];
build_branch_list(Bs,Op,Ls,L,N) when L >= N ->
    V = varc:add_variable(Bs#bs.vp), %% child var
    {Ls1,Ls2} = lists:split(N-1,Ls),
    _Cix = add_clause(Bs,Op,[V|Ls1]),
    [V|build_branch_list(Bs,Op,Ls2,L-(N-1),N)];
build_branch_list(Bs,Op,Ls,_L,_N) ->
    V = varc:add_variable(Bs#bs.vp),
    _Cix = add_clause(Bs,Op,[V|Ls]),
    [V].

make_variable(V, Bs) ->
    {N,Bs1} = fresh_var(Bs),
    {N, alias(V,N,Bs1)}.

order_sort_last(Bs, VarList) ->
    {RevLast,Bs1} = variable_list_(Bs,VarList,[]),
    ?dbg("last=~w\n",[lists:reverse(RevLast)]),
    ok = varc:order_sort_last(Bs#bs.vp, RevLast),
    Bs1.

order_sort_first(Bs, VarList) ->
    {RevFirst,Bs1} = variable_list_(Bs,VarList,[]),
    First = lists:reverse(RevFirst),
    ?dbg("first=~w\n",[First]),
    ok = varc:order_sort_first(Bs#bs.vp, First),
    Bs1.

variable_list_(Bs, [V|Vs], Acc) ->
    case build_(V, Bs) of
	{{bool,X}, Bs1} ->
	    variable_list_(Bs1, Vs, [X|Acc]);
	{{bit,_N,Xs}, Bs1} ->
	    variable_list_(Bs1, Vs, cat(Xs,Acc));
	{{int,_N,Xs}, Bs1} ->
	    variable_list_(Bs1, Vs, cat(Xs,Acc));
	{{uint,_N,Xs}, Bs1} ->
	    variable_list_(Bs1, Vs, cat(Xs,Acc))
    end;
variable_list_(Bs, [], Acc) ->
    {Acc,Bs}.

cat([X|Xs], Ys) -> cat(Xs, [X|Ys]);
cat([], Ys) -> Ys.

order_sort(Bs,[Key1,Key2]) -> order_sort(Bs,Key1,Key2,-1);
order_sort(Bs,[Key1]) -> order_sort(Bs,Key1,undefined,-1).

order_sort(Bs,Key1,Key2,Arg) 
  when is_atom(Key1), is_atom(Key2), is_integer(Arg) ->
    Arg1 = if Key1 =:= random,Arg =:= -1;
	      Key2 =:= random,Arg =:= -1 ->
		   <<Seed:24>> = crypto:strong_rand_bytes(3),
		   Seed;
	      true ->
		   Arg
	   end,
    ?dbg("order ~w, ~w, ~w\n", [Key1,Key2,Arg1]),
    varc:order_sort(Bs#bs.vp,Key1,Key2,Arg1).

clear_queue(Bs) ->
    varc:clear_queue(Bs#bs.vp),
    Bs.

enqueue_all(Bs) ->
    varc:enqueue_all(Bs#bs.vp),
    Bs.

eval(Bs) ->
    varc:eval(Bs#bs.vp).

undo(Bs) ->
    varc:undo(Bs#bs.vp, -1).

undo(Bs,Mark) ->
    varc:undo(Bs#bs.vp,Mark).

remove_mark(Bs) ->
    varc:remove_mark(Bs#bs.vp, -1).

remove_mark(Bs,Mark) ->
    varc:remove_mark(Bs#bs.vp,Mark).

mark(Bs) ->
    varc:mark(Bs#bs.vp).

mark(Bs,Level) ->
    varc:mark(Bs#bs.vp, Level).

value(Bs,V) ->
    case varc:get(Bs#bs.vp, V) of
	?TRUE -> true;
	?FALSE -> false;
	W -> W
    end.

get_info(Bs) ->
    varc:get_info(Bs#bs.vp).

get_info(Bs, Key) ->
    varc:info(Bs#bs.vp, Key).

class(Bs,V) ->
    case varc:class(Bs#bs.vp, V) of
	?TRUE  -> ?TRUE;
	?FALSE -> ?FALSE;
	X -> abs(X)
    end.

is_bound(Bs,Lit) ->
    varc:is_bound(Bs#bs.vp,Lit).

is_unbound(Bs,Lit) ->
    not varc:is_bound(Bs#bs.vp,Lit).

is_equal(Bs,LitA, LitB) ->
    not varc:is_equal(Bs#bs.vp,LitA,LitB).

equal(Bs,X,Y) ->
    X0 = literal(X,Bs),
    Y0 = literal(Y,Bs),
    varc:put(Bs#bs.vp, X0, Y0).

equal(Bs,X,Y,Level) ->
    X0 = literal(X,Bs),
    Y0 = literal(Y,Bs),
    varc:put(Bs#bs.vp, X0, Y0, Level).

literal(true,_Bs)  -> ?TRUE;
literal(false,_Bs) -> ?FALSE;
literal(X, _Bs) when is_integer(X) -> X;
literal({'not',X}, Bs) -> -literal(X, Bs);
literal({bool,X}, Bs) -> literal(X, Bs);
literal(X, Bs) -> maps:get(X, Bs#bs.vs).

getopt(Bs,Key) ->
    varp_option:getopt(Key, Bs#bs.option).

setopt(Bs,Key,Value) ->
    Option = varp_option:setopt(Key,Value,Bs#bs.option),
    %% Mybe set option in backend as well? probably
    Bs#bs { option = Option }.

number_of_variables(Bs) ->
    varc:get_number_of_variables(Bs#bs.vp).
    
number_of_bound(Bs) ->
    varc:get_number_of_bound_variables(Bs#bs.vp).

number_of_unbound(Bs) ->
    varc:get_number_of_unbound_variables(Bs#bs.vp).

clause_eval_counter(Bs) ->
    varc:get_clause_eval_counter(Bs#bs.vp).

eval_counter(Bs) ->
    varc:get_eval_counter(Bs#bs.vp).

first_init(Bs) -> 
    varc:order_init(Bs#bs.vp).

first_unbound(Bs) -> 
    I0 = first_init(Bs),
    varc:order_next(Bs#bs.vp, I0).

next_unbound(Bs,I) ->
    varc:order_next(Bs#bs.vp, I).

next_unbound(Bs,I,Skip) ->
    varc:order_next(Bs#bs.vp,I,Skip).

latest_bound(Bs) ->
    varc:get_bindings(Bs#bs.vp, -1).

info(Bs,Fmt,As) -> ?info(Bs#bs.option, Fmt, As).

debug(Bs,Fmt,As) ->  ?debug(Bs#bs.option, Fmt, As).

get_bindings(Bs,Mark) when is_integer(Mark) -> 
    varc:get_bindings(Bs#bs.vp, Mark).

conflicting_clause(Bs) ->
    varc:conflicting_clause(Bs#bs.vp).

implication_clause(Bs, V) ->
    varc:implication_clause(Bs#bs.vp, V).

get_clause(Bs, I) ->
    varc:get_clause(Bs#bs.vp, I).

get_clause_flags(Bs, I) ->
    varc:get_clause_flags(Bs#bs.vp, I).

use_clause(Bs, I, How) ->
    varc:use_clause(Bs#bs.vp, I, How).

%% Bs is under the assumption that Var = TRUE
intersect(Bs, Var, B0) ->
    intersect_(Bs, varc:info(Bs#bs.vp, bcp), Var, B0).

%% evaluate the bindings and build the intersection
 %% we may have this bindings, crash!

intersect_(Bs,Bcp,Var,[{X,true}|B0]) ->
    %% !Var -> X
    case value(Bs, X) of
	true ->  %% Var -> X, !Var -> X   =>  X
	    [{X,true} | intersect_(Bs,Bcp,Var,B0)];
	false when not Bcp -> %% Var -> !X, !Var -> X  =>  Var=!X
	    [{Var,-X} | intersect_(Bs,Bcp,Var,B0)];
	_ ->
	    intersect_(Bs,Bcp,Var,B0)
    end;
intersect_(Bs,Bcp,Var,[{X,false}|B0]) ->
    %% !Var -> !X
    case value(Bs, X) of
	false -> %% Var -> !X, !Var -> !X  =>  !X
	    [{X,false} | intersect_(Bs,Bcp,Var,B0)];
	true when not Bcp ->  %% Var -> X, !Var -> !X   =>  Var=X
	    [{Var,X} | intersect_(Bs,Bcp,Var,B0)];
	_ ->
	    intersect_(Bs,Bcp,Var,B0)
    end;
intersect_(Bs,Bcp=false,Var,[{X,Y}|B0]) ->
    Y1 = varc:get(Bs#bs.vp, X),
    if Y =:= ?TRUE,  Y1 =:= ?FALSE -> %% !Var => X, Var => !X
	    [{Var,-X} | intersect_(Bs,Bcp,Var,B0)];
       Y =:= ?FALSE, Y1 =:= ?TRUE -> %% !Var => !X, Var => X
	    [{Var,X} | intersect_(Bs,Bcp,Var,B0)];
       true ->
	    intersect_(Bs,Bcp,Var,B0)
    end;
intersect_(Bs,Bcp=true,Var,[_|B0]) ->
    intersect_(Bs,Bcp,Var,B0);
intersect_(_Bs,_Bcp,_Var,[]) ->
    [].

%% compact version of fmt_var
fmt_v(_,?TRUE)  -> "1";
fmt_v(_,?FALSE) -> "0";
fmt_v(_,true)   -> "1";
fmt_v(_,false)  -> "0";
fmt_v(Bs,X) ->
    if X < 0 -> fmt_var_(Bs,-X, "~", "");
       true ->  fmt_var_(Bs,X, "", "")
    end.

fmt_q(Bs,X) ->
    fmt_var(Bs,X, "\"").

fmt_var(Bs,X) ->
    fmt_var(Bs,X, "").

fmt_var(_Bs,?TRUE,_Q)  -> "true";
fmt_var(_Bs,?FALSE,_Q) -> "false";
fmt_var(_Bs,true,_Q)   -> "true";
fmt_var(_Bs,false,_Q)  -> "false";
fmt_var(Bs,X,Q) ->
    if X < 0 ->
	    fmt_var_(Bs,-X, "!", Q);
       true ->
	    fmt_var_(Bs,X, "", Q)
    end.

fmt_var_(Bs,X,Pfx,Q) when is_integer(X) ->
    case maps:find(X,Bs#bs.vs) of
	error ->
	    [Q,Pfx,$$,integer_to_list(X),Q];
	{ok,[P={p,_,_}]} ->
	    [Q,Pfx,fmt_pred_(P),Q];
	{ok,[{T,P={p,_,_},_N,I}|_Ns]} when ?is_vec_type(T),is_integer(I) ->
	    [Q,Pfx,fmt_pred_(P),"[",integer_to_list(I),"]",Q];
	{ok,?TRUE} -> "true";
	{ok,?FALSE} -> "false"
    end.

fmt_pred_({p,P,[]}) -> 
    atom_to_list(P);
fmt_pred_({p,P,As}) ->
    [atom_to_list(P),"(",fmt_index_list(As),")"].

fmt_index_list([I]) ->
    [fmt_index(I)];
fmt_index_list([I|Is]) ->
    [fmt_index(I),","|fmt_index_list(Is)].

fmt_index(I) when is_integer(I) ->
    integer_to_list(I);
fmt_index(A) when is_atom(A) ->
    atom_to_list(A);
fmt_index(Set) when is_list(Set) ->
    ["{",fmt_ordset(Set),"}"];
fmt_index({f,F,Is}) ->
    fmt_func(F,Is).

fmt_func(F,Is) when is_atom(F) ->
    [atom_to_list(F)|fmt_fargs(Is)];
fmt_func(F,Is) when is_list(F); is_binary(F) ->
    [F|fmt_fargs(Is)].
    
fmt_fargs([]) -> [];
fmt_fargs(Is) ->
    ["(",fmt_index_list(Is),")"].

fmt_ordset([]) -> [];
fmt_ordset([I]) when is_integer(I) ->
    integer_to_list(I);
fmt_ordset([I|Is=[J|_]]) when is_integer(I), is_integer(J), I < J ->
    [integer_to_list(I),","|fmt_ordset(Is)].
    
fmt_var_list(Bs,Xs) ->
    concat([fmt_var(Bs,X)||X<-Xs],",").

variable(V, Bs) ->
    W = expand_meta(V, Bs),
    ?dbg("variable expand: ~p -> ~w\n", [V,W]),
    case find_var(W, Bs) of
	error ->
	    case W of
		{p,P,Rs} ->
		    %% check for a definition of P(x1,..xn)
		    case find_def(P, Bs#bs.defs) of
			false ->
			    make_variable(W, Bs);
			{_W1={p,_,Ps},Def} ->
			    ?dbg("~p = ~p\n", [_W1,Def]),
			    Names = [Name || #cid{name=Name}<-Ps],
			    Bnd2 = lists:zip(Names,Rs),
			    Meta = Bnd2 ++ Bs#bs.meta,
			    ?dbg("meta bind: ~p\n", [Meta]),
			    {R,Bs1} = build__(Def, Bs#bs { meta=Meta}),
			    Meta1 = lists:nthtail(length(Bnd2),Bs1#bs.meta),
			    case R of
				{bool,N} ->
				    {N,Bs1#bs { meta=Meta1}};
				Vector ->
				    {Vector,Bs1#bs { meta=Meta1}}
			    end
		    end;
		_ ->
		    make_variable(W, Bs)
	    end;
	{ok,N} ->
	    {N,Bs}
    end.

%%
%%  {r,f1,..fn} => {q,eval(f1),...,eval(fn)}
%%  if f1 is var xi (e.g atom xi) then bind [{xi,eval(fi)}]
%%
%%  {uint,xi,N,i} and {int,xi,N,i} are special for
%%  unsigned/integer variable bits
%%  {bit,xi,N,i} is used for bitvector
%%
expand_meta(W={uint,V,N,I},Bs) when is_integer(N), is_integer(I) ->
    case expand_meta(V,Bs) of
	V -> W;
	VV -> {uint,VV,N,I}
    end;
expand_meta(W={int,V,N,I},Bs) when is_integer(N), is_integer(I) ->
    case expand_meta(V,Bs) of
	V -> W;
	VV -> {int,VV,N,I}
    end;
expand_meta(W={bit,V,N,I},Bs) when is_integer(N), is_integer(I) ->
    case expand_meta(V,Bs) of
	V -> W;
	VV -> {bit,VV,N,I}
    end;
expand_meta(_Rx={p,P,Rs},Bs) ->
    %% eval "arguments"
    {Rs1,_Bnd} = bind_meta(Rs, Bs, [], []), 
    %% check for substitution R(x1,..,xn) / P(y1,..,ym)
    %% io:format("expand_meta: ~p in Bs=~p\n", [_Rx, Bs]),
    Found = find_subst(P, Bs#bs.subst),
    %% io:format("subst  = ~w\n", [Found]),
    case Found of
	false -> {p,P,Rs1};
	{{p,Q,[]},{p,_P,_Us}} -> {p,Q,[]};
	{{p,Q,Qs},{p,P,Ps}} when P =/= Q, length(Qs) > 0 ->
	    Bnd2 = lists:zip(Ps,Rs1),
	    %% io:format("subst: ~w [~w] => ~w\n", [{p,P,Ps},Bnd2,{p,Q,Qs}]),
	    Meta = Bnd2 ++ Bs#bs.meta,
	    expand_meta({p,Q,Qs}, Bs#bs { meta=Meta})
    end;
expand_meta(V,_Bs) ->
    %% io:format("expand_meta: ~p in Bs=~p\n", [V, _Bs]),
    V.

find_def(P, [Def={{p,P,_Vs},_}|_]) -> Def;
find_def(P, [_|Defs]) -> find_def(P, Defs);
find_def(_P, []) -> false.

find_subst(P, [E={_Qy,{p,P,_}}|_]) -> E;
find_subst(P, [_|Bnd]) -> find_subst(P, Bnd);
find_subst(_P ,[]) -> false.

bind_meta([V=#cid{name=N}|Vs], Bs, Acc, Bnd) ->
    W = eval_meta(V,Bs),
    bind_meta(Vs, Bs, [W|Acc], [{N,W}|Bnd]);
bind_meta([V|Vs], Bs, Acc, Bnd) ->
    W = eval_meta(V,Bs),
    bind_meta(Vs, Bs, [W|Acc], Bnd);
bind_meta([], _Bs, Acc, Bnd) ->
    {lists:reverse(Acc),lists:reverse(Bnd)}.


%% bind a "meta" variable
push_meta(V,I,Bs) ->
    Bs#bs { meta = [{V,I}|Bs#bs.meta]}.

pop_meta(Bs = #bs { meta = [_|Meta]}) ->
    Bs#bs { meta = Meta }.

-spec alias(V::var(),N::integer(),Bs::#bs{}) -> #bs{}.

alias(V,N,Bs) ->
    %% io:format("alias ~w\n", [V]),
    case find_var(N,Bs) of
	error ->
	    set_var(V,N,Bs);
	{ok,Alias} ->
	    add_var(V,N,Alias,Bs)
    end.

find_var(V, Bs) ->
    maps:find(V, Bs#bs.vs).

get_var(V, Bs) ->
    maps:get(V, Bs#bs.vs).

set_var(Var, Vi, Bs) ->
    Vs = Bs#bs.vs,
    Vs1 = Vs#{ Var => Vi,  Vi => [Var] },
    Bs#bs { vs = Vs1 }.

add_var(Var, Vi, Alias,Bs) ->
    Vs = Bs#bs.vs,
    Vs1 = Vs#{ Var => Vi, Vi => [Var|Alias] },
    Bs#bs { vs = Vs1 }.

fold_var(Fun, Acc, Bs) ->
    maps:fold(Fun, Acc, Bs#bs.vs).

%%
%% Generate the variable rules from a formula
%%
build(F) ->
    build(F,[]).

build(F,Opts) when is_list(Opts) ->
    %% io:format("Opts = ~p\n", [Opts]),
    build(F, varp_option:set_opts(Opts));
build(F,Opts) when is_map(Opts) ->
    ?dbg("Formula: ~p\n", [F]),
    Bs = new(Opts),
    Bs1 = build_code(getopt(Bs,defs),Bs),
    try build__(F, Bs1) of
      	Value -> Value
    catch
      	throw:contradiction -> 
     	    {{bool,?FALSE},Bs1}
    end.

build_code([], Bs) ->
    Bs;
build_code(Defs, Bs) ->
    case proplists:get_value(code, Defs) of
	undefined -> Bs;
	Code -> varp_code:generate(Code, Bs)
    end.

build__(F, Bs) ->
    %% io:format("build__ ~p\n", [F]),
    R={_F1,_} = build_(F, Bs),
    %% io:format("build__ => ~p", [_F1]),
    R.

build_(undefined, Bs) ->
    {undefined, Bs};
build_(true, Bs) ->
    {{bool,?TRUE}, Bs};
build_(false, Bs) ->
    {{bool,?FALSE}, Bs};
build_(V, Bs) when is_atom(V) -> %% meta variable
    W = eval_meta(V,Bs),
    if W >=0 ->
	    N = varp_math:integer_size(W),
	    const_vector(uint,W,N,Bs);
       W < 0 ->
	    N = varp_math:integer_size(W),
	    const_vector(int,W,N,Bs)
    end;

build_(V={p,P,Ps}, Bs) ->
    %% match delcs to see if this predicate is declared with
    %% sign and bit size look for {p,P,['_','_',...]}
    Px = {p,P,['_' || _ <- Ps]},
    case proplists:lookup(Px, Bs#bs.decls) of
	none ->
	    {X,Bs1} = variable(V, Bs),
	    {{bool,X},Bs1};
	{_,Sign,Size} ->
	    var_vector(Sign,V,Size,Bs)
    end;
build_({uint,N,V}, Bs) ->
    if is_atom(V) ->
	    Vn = atom_to_list(V),
	    case proplists:lookup(Vn,Bs#bs.meta) of
		none ->
		    io:format("variable '~s' is not bound\n", [Vn]),
		    error({unbound, Vn});
		{_,W} ->
		    const_vector(uint,W,N,Bs)
	    end;
       is_integer(V) -> const_vector(uint,V,N,Bs);
       true          -> var_vector(uint,V,N,Bs)
    end;
build_({int,N,V}, Bs) ->
    if is_atom(V) ->
	    Vn = atom_to_list(V),
	    case proplists:lookup(Vn,Bs#bs.meta) of
		none ->
		    io:format("variable '~s' is not bound\n", [Vn]),
		    error({unbound, Vn});
		{_,W} ->
		    const_vector(int,W,N,Bs)
	    end;
       is_integer(V) -> const_vector(int,V,N,Bs);
       true          -> var_vector(int,V,N,Bs)
    end;
build_({bit,N,V}, Bs) ->
    if  is_atom(V) -> 
	    Vn = atom_to_list(V),
	    case proplists:lookup(Vn,Bs#bs.meta) of
		none ->
		    io:format("variable '~s' is not bound\n", [Vn]),
		    error({unbound, Vn});
		{_,W} ->
		    const_vector(bit,W,N,Bs)
	    end;
	is_integer(V) -> const_vector(bit,V,N,Bs);
	true          -> var_vector(bit,V,N,Bs)
    end;
build_({expr,Expr}, Bs) ->
    W = eval_meta(Expr,Bs),
    if W >=0 ->
	    N = varp_math:integer_size(W),
	    const_vector(uint,W,N,Bs);
       W < 0 ->
	    N = varp_math:integer_size(W),
	    const_vector(int,W,N,Bs)
    end;
build_({vec,Fs}, Bs) ->
    {Xs,Bs1} = build_list(Fs, Bs),
    {{bit,length(Xs),[bit(X)||X <- Xs]},Bs1};
build_({'=', V, F}, Bs) when is_atom(V) ->
    {Y,Bs1} = build__(F, Bs),
    operation_('=', V, Y, Bs1);

build_({'-',F}, Bs) ->
    {Y,Bs1} = build__(F, Bs),
    operation_('-', Y, Bs1);
build_({'not',A}, Bs) ->
    {Y,Bs1} = build__(A, Bs),
    operation_('not', Y, Bs1);
build_({'~',A}, Bs) ->
    {Y,Bs1} = build__(A, Bs),
    operation_('~', Y, Bs1);
build_({'!',A}, Bs) ->
    {Y,Bs1} = build__(A, Bs),
    operation_('!', Y, Bs1);

build_({bit_index,A,I},Bs) ->
    I1 = eval_meta(I,Bs),
%%    io:format("A=~w, I1=~w\n", [A,I1]),
%%    A1 = case A of
%%	     {p,Var,[]} -> {p,Var,[I1]};
%%	     _ -> A
%%	 end,
    {B,Bs1} = build__(A, Bs),
%%    io:format("B = ~w\n", [B]),
    case B of
	{uint,N,Xs} -> {select_bool(I1,N,Xs), Bs1};
	{int,N,Xs}  -> {select_bool(I1,N,Xs), Bs1};
	{bit,N,Xs}  -> {select_bool(I1,N,Xs), Bs1};
	{bool,X}    -> {{bool,X},Bs1};
	X -> {select_bool(I1,1,[X]),Bs1}
    end;

build_({bit_range,A,I,J},Bs) ->
    I1 = eval_meta(I,Bs),
    J1 = eval_meta(J,Bs),
    case build__(A, Bs) of
	{{uint,N,Xs}, Bs1} -> {select_range(I1,J1,N,Xs), Bs1};
	{{int,N,Xs}, Bs1}  -> {select_range(I1,J1,N,Xs), Bs1};
	{{bit,N,Xs}, Bs1}  -> {select_range(I1,J1,N,Xs), Bs1};
	{X,Bs1} -> {select_range(I1,J1,1,[X]),Bs1}
    end;

%% Fixme: implement shift for variable argument
build_({'<<',A,K},Bs) when is_integer(K), K>=0 ->
    {Y,Bs1} = build__(A,Bs),
    operation_('<<',Y,K,Bs1);
build_({'<<<',A,K},Bs) when is_integer(K), K>=0 ->
    {Y,Bs1} = build__(A,Bs),
    operation_('<<<',Y,K,Bs1);
build_({'>>',A,K},Bs) when is_integer(K), K >= 0 ->
    {Y,Bs1} = build__(A,Bs),
    operation_('>>',Y,K,Bs1);
build_({'>>>',A,K},Bs) when is_integer(K), K >= 0 ->
    {Y,Bs1} = build__(A,Bs),
    operation_('>>>',Y,K,Bs1);

build_({cnf,{[],[],_Sections}},Bs) ->
    build__(false, Bs);
build_({cnf,{_Vars,_Clauses,_Sections,Units,Cs}},Bs) 
  when is_list(Cs), is_list(Units) ->
    %% fixme bind all literals in Ls = TRUE
    Bs1 = build_cnf(Cs, Bs),
    {{bool,?TRUE}, Bs1};
%%    build__({'and',{'ALL',Ls},cnf_to_formula(Cs)},Bs);

build_({snf,{[],[],_Sections}},Bs) ->
    build__(false, Bs);
build_({snf,{_Vars,_Clauses,_Sections,Units,Cs}},Bs) 
  when is_list(Cs), is_list(Units) ->
    Bs1 = build_cnf(Cs, Bs),
    {{bool,?TRUE}, Bs1};


build_({subst,Rx,Py,F},Bs) ->
    Bs1 = Bs#bs { subst = [{Rx,Py}|Bs#bs.subst]},
    build__(F, Bs1);
build_({subst,SList,F},Bs) ->
    Bs1 = Bs#bs { subst = SList++Bs#bs.subst},
    build__(F, Bs1);
build_({Op,A,B}, Bs) ->
    {Y,Bs1} = build__(A, Bs),
    {Z,Bs2} = build__(B, Bs1),
    operation_(Op,Y,Z,Bs2);
build_({ite,C,T,E}, Bs) ->
    {Cf,Bs1} = build__(C, Bs),
    {Tf,Bs2} = build__(T, Bs1),
    {Ef,Bs3} = build__(E, Bs2),
    ite(Cf, Tf, Ef, Bs3);

build_({'abs',[A]}, Bs) ->
    {Y,Bs1} = build__(A, Bs),
    operation_('abs', Y, Bs1);
build_({'min',[A,B]}, Bs) ->
    {A1,Bs1} = build__(A, Bs),
    {B1,Bs2} = build__(B, Bs1),
    operation_('min', A1, B1, Bs2);
build_({'max',[A,B]}, Bs) ->
    {A1,Bs1} = build__(A, Bs),
    {B1,Bs2} = build__(B, Bs1),
    operation_('max', A1, B1, Bs2);
build_({'ALL',Fs}, Bs) ->
    {Xs,Bs1} = args(Fs,Bs),
    all(Xs, Bs1);
build_({'ANY',Fs}, Bs) ->
    {Xs,Bs1} = args(Fs,Bs),
    any(Xs, Bs1);
build_({'NONE',Fs}, Bs) ->
    {Xs,Bs1} = args(Fs,Bs),
    none(Xs, Bs1);
build_({'ONE',Fs}, Bs) ->
    {Xs,Bs1} = args(Fs,Bs),
    one(Xs, Bs1);
build_({'SUM',Ys}, Bs) ->
    {Xs,Bs1} = args(Ys,Bs),
    sum(Xs, Bs1);
build_({'PROD',Ys}, Bs) ->
    {Xs,Bs1} = args(Ys,Bs),
    prod(Xs, Bs1);

%% Quatifer version
build_({{'ALL',Qs}, F}, Bs) ->
    {Ys,Bs1} = build_quant(F,Qs,Bs),
    all(Ys,Bs1);
build_({{'ANY',Qs},F}, Bs) ->
    {Ys,Bs1} = build_quant(F,Qs,Bs),
    any(Ys,Bs1);
build_({{'NONE',Qs},F}, Bs) ->
    {Ys,Bs1} = build_quant(F,Qs,Bs),
    none(Ys,Bs1);
build_({{'ONE',Qs},F}, Bs) ->
    {Ys,Bs1} = build_quant(F,Qs,Bs),
    eqk(1, length(Ys), Ys, Bs1);

build_({{'EQ',[X1|Qs]},F}, Bs) ->
    K = eval_meta(X1,Bs),
    {Ys,Bs1} = build_quant(F,Qs,Bs),
    if is_integer(K),K >= 0 ->
	    eqk(K, length(Ys), Ys, Bs1)
    end;
build_({{'NEQ',[X1|Qs]},F}, Bs) ->
    K = eval_meta(X1,Bs),
    {Ys,Bs1} = build_quant(F,Qs,Bs),
    if is_integer(K),K >= 0 ->
	    {X,Bs2} = eqk(K, length(Ys), Ys, Bs1),
	    {negate(X),Bs2}
    end;
build_({{'GT',[X1|Qs]},F}, Bs) ->
    K = eval_meta(X1,Bs),
    {Ys,Bs1} = build_quant(F,Qs,Bs),
    if is_integer(K),K >= 0 ->
	    gtk(K, length(Ys), Ys, Bs1)
    end;
build_({{'GTE',[X1|Qs]},F}, Bs) ->
    K = eval_meta(X1,Bs),
    {Ys,Bs1} = build_quant(F,Qs,Bs),
    if K =:= 0 ->
	    any(Ys,Bs1);
       is_integer(K),K >= 0 ->
	    gtk(K-1, length(Ys), Ys, Bs1)
    end;
build_({{'LT',[X1|Qs]},F}, Bs) ->
    K = eval_meta(X1,Bs),
    {Ys,Bs1} = build_quant(F,Qs,Bs),
    if K =:= 1 ->
	    none(Ys,Bs1);
       is_integer(K),K > 1 ->
	    N = length(Ys),
	    gtk(N-K, N, map(fun(Y) -> negate(Y) end, Ys), Bs1)
    end;
build_({{'LTE',[X1|Qs]},F}, Bs) ->
    K = eval_meta(X1,Bs),
    {Ys,Bs1} = build_quant(F,Qs,Bs),
    if K =:= 0 ->
	    none(Ys,Bs1);
       is_integer(K),K > 0 ->
	    N = length(Ys),
	    gtk(N-K-1, N, map(fun(Y) -> negate(Y) end, Ys), Bs1)
    end;
build_({{'SUM',Qs}, F}, Bs) ->
    {Xs,Bs1} = build_iquant(F,Qs,Bs),
    sum(Xs,Bs1);
build_({{'PROD',Qs}, F}, Bs) ->
    {Xs,Bs1} = build_iquant(F,Qs,Bs),
    prod(Xs,Bs1).

%%
%% Special build of cnf/snf
%%
build_cnf([CL|CLs], Bs) ->
    Bs1 = build_or_clause(CL, Bs),
    build_cnf(CLs, Bs1);
build_cnf([], Bs) ->
    Bs.

build_or_clause(CL, Bs) ->
    build_or_clause(CL,[],Bs).

build_or_clause([L|Ls], Acc, Bs) ->
    {L1,Bs1} = build_(L, Bs),
    build_or_clause(Ls, [L1|Acc], Bs1);
build_or_clause([], Acc, Bs) ->
    As1 = [A || {bool,A} <- lists:reverse(Acc)],
    or_clause(Bs, As1).


-ifdef(__UNUSED__).
build_meta(F,X,[Xi|Xs],Acc,Bs) ->
    Bs1 = push_meta(X, Xi, Bs),
    case build__(F,Bs1) of
	{0,Bs2} ->
	    Bs3 = pop_meta(Bs2),
	    build_meta(F,X,Xs,Acc,Bs3);
	{Vs,Bs2} when is_list(Vs) ->
	    Bs3 = pop_meta(Bs2),
	    build_meta(F,X,Xs,Vs++Acc,Bs3);
	{V,Bs2} ->
	    Bs3 = pop_meta(Bs2),
	    build_meta(F,X,Xs,[V|Acc],Bs3)
    end;
build_meta(_F,_X,[],Acc,Bs) ->
    {Acc,Bs}.
-endif.

%% boolean version
build_quant(Fs, Qs, Bs) when is_list(Fs), is_list(Qs) ->
    build_quant_list(Fs, Qs, Bs);
build_quant(F, Qs, Bs) when is_list(Qs) ->
    build_quant_(F, Qs, Bs).

build_quant_(F,[#cassign{op='=',lhs=V,rhs=D}|Qs], Bs) ->
    Ds = eval_domain(D, Bs),
    build_quant_domain(F, V, Ds, Qs, Bs);
%% predicate expansion
build_quant_(F, [#ccall{ func=#cid{name=Def},args=Args}|Qs], Bs) ->
    %% lookup Def
    {[], Bs};

build_quant_(F, [Expr|Qs], Bs) ->
    case eval_meta(Expr, Bs) of
	false -> {[],Bs};
	true -> build_quant_(F, Qs, Bs)
    end;
build_quant_(F, [], Bs) ->
    case build__(F, Bs) of
	{{uint,_N,Xs}, Bs1} -> {[{bool,X}||X<-Xs],Bs1};
	{{int,_N,Xs}, Bs1}  -> {[{bool,X}||X<-Xs],Bs1};
	{{bit,_N,Xs}, Bs1}  -> {[{bool,X}||X<-Xs],Bs1};
	{X,Bs1} -> {[X],Bs1}
    end.

build_quant_domain(F, V=#cid{name=Vn}, [Y|Ys], Xs, Bs) ->
    Bs1 = push_meta(Vn, Y, Bs),
    {Zs1,Bs2} = build_quant_(F, Xs, Bs1),
    Bs3 = pop_meta(Bs2),
    {Zs2,Bs4} = build_quant_domain(F, V, Ys, Xs, Bs3),
    {Zs1++Zs2,Bs4};
%% fixme handle arbitrary vector!
build_quant_domain(F, V={vec,[#cid{name=Vn1},#cid{name=Vn2}]},
		   [{vec,[Y1,Y2]}|Ys], Xs, Bs) ->
    ?dbg("Bind ~s=~w, ~s=~w\n", [Vn1,Y1,Vn2,Y2]),
    Bs1 = push_meta(Vn1, Y1, Bs),
    Bs2 = push_meta(Vn2, Y2, Bs1),
    {Zs1,Bs3} = build_quant_(F, Xs, Bs2),
    Bs4 = pop_meta(Bs3),
    Bs5 = pop_meta(Bs4),
    {Zs2,Bs6} = build_quant_domain(F, V, Ys, Xs, Bs5),
    {Zs1++Zs2,Bs6};
build_quant_domain(_F, _V, [], _Xs, Bs) ->
    {[], Bs}.

build_quant_list([F|Fs], Xs, Bs) ->
    {Xs0,Bs1} = build_quant(F, Xs, Bs),
    {Xs1,Bs2} = build_quant_list(Fs,Xs,Bs1),
    {Xs0++Xs1,Bs2};
build_quant_list([], _Xs, Bs) ->
    {[],Bs}.

%% integer/vector version

build_iquant(Fs, Qs, Bs) when is_list(Fs), is_list(Qs) ->
    build_iquant_list(Fs, Qs, Bs);
build_iquant(F, Qs, Bs) when is_list(Qs) ->
    build_iquant_(F, Qs, Bs).

build_iquant_(F,[#cassign{op='=',lhs=V,rhs=D}|Qs], Bs) ->
    Ds = eval_domain(D, Bs),
    build_iquant_domain(F, V, Ds, Qs, Bs);
build_iquant_(F, [Expr|Qs], Bs) ->
    case eval_meta(Expr, Bs) of
	false -> {[],Bs};
	true -> build_iquant_(F, Qs, Bs)
    end;
build_iquant_(F, [], Bs) ->
    case build__(F, Bs) of
	{{bool,X},Bs1} -> {[{uint,1,[X]}], Bs1};
	{X,Bs1} -> {[X],Bs1}
    end.

build_iquant_domain(F, V=#cid{name=Vn}, [Y|Ys], Xs, Bs) ->
    Bs1 = push_meta(Vn, Y, Bs),
    {Zs1,Bs2} = build_iquant_(F, Xs, Bs1),
    Bs3 = pop_meta(Bs2),
    {Zs2,Bs4} = build_iquant_domain(F, V, Ys, Xs, Bs3),
    {Zs1++Zs2,Bs4};
build_iquant_domain(_F, _V, [], _Xs, Bs) ->
    {[], Bs}.

build_iquant_list([F|Fs], Xs, Bs) ->
    {Xs0,Bs1} = build_iquant(F, Xs, Bs),
    {Xs1,Bs2} = build_iquant_list(Fs,Xs,Bs1),
    {Xs0++Xs1,Bs2};
build_iquant_list([], _Xs, Bs) ->
    {[],Bs}.

%% expand domain expressions
eval_domain(#crange{from=A,to=B}, Bs) ->
    A1 = eval_meta(A,Bs),
    B1 = eval_meta(B,Bs),
    if A1 =< B1 -> lists:seq(A1, B1);
       true -> lists:reverse(lists:seq(B1,A1))
    end;
eval_domain(#ccall{func=#cid{name="union"},args=[A,B]}, Bs) ->
    A1 = eval_domain(A,Bs),
    B1 = eval_domain(B,Bs),
    ordsets:union(A1,B1);
eval_domain(#ccall{func=#cid{name="subtract"},args=[A,B]}, Bs) ->
    A1 = eval_domain(A,Bs),
    B1 = eval_domain(B,Bs),
    ordsets:subtract(A1,B1);
eval_domain(#ccall{func=#cid{name="intersect"},args=[A,B]}, Bs) ->
    A1 = eval_domain(A,Bs),
    B1 = eval_domain(B,Bs),
    ordsets:intersection(A1,B1);
eval_domain(#ccall{func=#cid{name="product"},args=[A,B]}, Bs) ->
    A1 = eval_domain(A,Bs),
    B1 = eval_domain(B,Bs),
    [ [Ai,Bi] || Ai <- A1, Bi <- B1 ];
eval_domain(#ccall{func=#cid{name="subsets"},args=[A]}, Bs) ->
    A1 = eval_domain(A,Bs),
    subsets(A1);
eval_domain(#ccall{func=#cid{name="subsets"},args=[K,A]}, Bs) ->
    K1 = eval_meta(K,Bs),
    A1 = eval_domain(A,Bs),
    subsets(K1,A1);
eval_domain(Expr, Bs) ->
    D = eval_meta(Expr,Bs),
    case D of
	{vec,Elems} -> Elems;   %% assume set notation
	Elems when is_list(Elems) -> Elems;
	_ -> [D]
    end.

eval_meta(V, _Bs) when is_integer(V) -> V;
eval_meta(#cconst{base=B,value=V}, _Bs) -> list_to_integer(V,B);
eval_meta(#crange{from=A,to=B}, Bs) ->
    A1 = eval_meta(A,Bs),
    B1 = eval_meta(B,Bs),
    if A1 =< B1 -> lists:seq(A1, B1);
       true -> lists:reverse(lists:seq(B1,A1))
    end;
eval_meta(#cid {name="true"}, _Bs)  -> true;
eval_meta(#cid {name="false"}, _Bs) -> false;
eval_meta(#cid {name=Vn}, Bs) ->
    case proplists:lookup(Vn,Bs#bs.meta) of
	none ->
	    try list_to_existing_atom(Vn) of
		L ->
		    case lists:member(L, Bs#bs.literals) of
			true ->
			    L;
			false ->
			    case find_def(L, Bs#bs.defs) of
				false ->
				    io:format("variable '~s' is not bound\n", [Vn]),
				    error({unbound, Vn});
				{{p,L,[]},Def} ->
				    %% io:format("Def = ~p\n", [Def]),
				    Def
			    end
		    end
	    catch
		error:_ ->
		    io:format("variable '~s' is not bound\n", [Vn]),
		    error({unbound, Vn})
	    end;
	{_,W} -> 
	    W
    end;
eval_meta(V, Bs) when is_atom(V) -> %% old format still around
    Vn = atom_to_list(V),
    case proplists:lookup(Vn,Bs#bs.meta) of
	none ->
	    io:format("variable '~s' is not bound\n", [Vn]),
	    error({unbound, Vn});
	{_,W} -> 
	    W
    end;
eval_meta(#ccall{func=F,args=As},Bs) ->
    case {F,eval_meta_list(As,Bs)} of
	{#cid{name="factorial"},[N]} -> varp_math:factorial(N);
	{#cid{name="binom"},[A,B]} -> varp_math:binom(A,B);
	{#cid{name="sqrt"},[A]}    -> math:sqrt(A);
	{#cid{name="isqrt"},[A]}    -> imath:isqrt(A);
	{#cid{name="nroot"},[A,N]} -> varp_math:nroot(A,N);
	{#cid{name="ln"},[A]}      -> math:log(A);
	{#cid{name="log"},[A,N]}   -> math:log(A)/math:log(N);
	{#cid{name="log2"},[A]}    -> math:log(A)/math:log(2);
	{#cid{name="log10"},[A]}   -> math:log10(A);
	{#cid{name="ilog2"},[A]}   -> imath:ilog2(A);
	{#cid{name="isize"},[A]}   -> varp_math:integer_size(A);
	{#cid{name="usize"},[A]}   -> varp_math:unsigned_size(A);
	{#cid{name="pi"},[]}       -> math:pi();
	{#cid{name="e"},[]}        -> math:exp(1);
	{#cid{name="pow"},[A,B]}   -> 
	    if is_integer(A), is_integer(B) ->
		    varp_math:pow(A,B);
	       true ->
		    math:pow(A,B)
	    end;
	{#cid{name="sin"},[A]}     -> math:sin(A);
	{#cid{name="cos"},[A]}     -> math:cos(A);
	{#cid{name="trunc"},[A]}   -> trunc(A);
	{#cid{name="round"},[A]}   -> round(A);
	{#cid{name="abs"},[A]}     -> abs(A);
	{#cid{name="max"},[A,B]}   -> max(A,B);
	{#cid{name="min"},[A,B]}   -> min(A,B);
	{#cid{name="sum"},As}      ->
	    lists:foldl(fun(Ai,Sum) -> eval_meta(Ai,Bs)+Sum end, 0, As);
	%% ordsets
	{#cid{name="union"},[A,B]}   -> ordsets:union(A,B);
	{#cid{name="subtract"},[A,B]}   -> ordsets:subtract(A,B);
	{#cid{name="intersect"},[A,B]}   -> ordsets:intersect(A,B);
	{#cid{name="product"},[A,B]}   -> [ [Ai,Bi] || Ai <- A, Bi <- B ];
	%% function symbol
	{#cid{name=Func},As1} -> {f,Func,As1}
    end;

eval_meta(#cbinary{op=Op,arg1=A,arg2=B},Bs) ->
    case {Op,eval_meta(A,Bs),eval_meta(B,Bs)} of
	{'<',A1,B1} -> A1 < B1;
	{'<=', A1, B1} -> A1 =< B1;
	{'>',A1,B1} -> A1 > B1;
	{'>=', A1, B1} -> A1 >= B1;
	{'==', A1, B1} -> A1 == B1;
	{'!=', A1, B1} -> A1 =/= B1;
	{'&&',A1,B1} -> A1 and B1;
	{'||',A1,B1} -> A1 or B1;
	{'&',A1,B1} -> A1 band B1;
	{'|',A1,B1} -> A1 bor B1;
	{'^',A1,B1} -> A1 bxor B1;
	{'<<',A1,B1} -> A1 bsl B1;
	{'>>',A1,B1} -> A1 bsr B1;
	{'+',A1,B1} -> A1+B1;
	{'-',A1,B1} -> A1-B1;
	{'*',A1,B1} -> A1*B1;
	{'/',A1,B1} -> A1 div B1;
	{'%',A1,B1} -> A1 rem B1
    end;

eval_meta(#cunary{op=Op,arg=A},Bs) ->
    case {Op,eval_meta(A,Bs)} of
	{'-',A1} -> -A1;
	{'+',A1} -> +A1;
	{'~',A1} ->  bnot A1;
	{'!',A1} -> not A1
    end.

eval_meta_list(As,Bs) ->
    map(fun(A) -> eval_meta(A,Bs) end, As).

%% Generate a set/list of all subsets of a set
subsets([A|As]) ->
    Bs = subsets(As),
    [[A]] ++ [[A|B] || B <- Bs] ++ Bs;
subsets([]) ->
    [].

%% subsets of size K
subsets(1, As) ->
    [[A] || A <- As];
subsets(K, As0=[A|As]) ->
    L = length(As0),
    if K =:= L -> [As0];
       K < L ->
	    Bs = subsets(K-1,As),
	    subsets(K, As) ++ [[A|B] || B <- Bs]
    end.

uint64(I,Bs) when is_integer(I) ->
    const_vector(uint,I,64,Bs);
uint64(V,Bs) ->
    var_vector(uint,V,64,Bs).

uint32(I,Bs) when is_integer(I) ->
    const_vector(uint,I,32,Bs);
uint32(V,Bs) ->
    var_vector(uint,V,32,Bs).

uint16(I,Bs) when is_integer(I) ->
    const_vector(uint,I,16,Bs);
uint16(V,Bs) ->
    var_vector(uint,V,16,Bs).

uint8(I,Bs) when is_integer(I) ->
    const_vector(uint,I,8,Bs);
uint8(V,Bs) ->
    var_vector(uint,V,8,Bs).


%% generate a constant vector
const_vector(Type,Value,Size,Bs) when is_integer(Value) ->
    N = eval_meta(Size,Bs),
    const_vector_(N-1,Type,N,[],Value,Bs).

const_vector_(-1,Type,N,Cs,_Value,Bs) ->
    {{Type,N,reverse(Cs)},Bs};
const_vector_(I,Type,N,Cs,Value,Bs) ->
    if Value band 1 =:= 1 ->
	    const_vector_(I-1,Type,N,[?TRUE|Cs],Value bsr 1, Bs);
       true ->
	    const_vector_(I-1,Type,N,[?FALSE|Cs],Value bsr 1, Bs)
    end.

%% Install alias vector
alias_vector(Bs,T,V,Size,Xs) ->
    N = eval_meta(Size,Bs),
    alias_vector_(Bs,0,T,N,Xs,V).

alias_vector_(Bs,I,T,N,[X|Xs],V) ->
    Bs1 = alias({T,V,N,I},X,Bs),
    alias_vector_(Bs1,I+1,T,N,Xs,V);
alias_vector_(Bs,_I,_T,_N,[],_V) ->
    Bs.
    
%% generate a variable vector
var_vector(Type,V,Size,Bs) ->
    VV = expand_meta(V,Bs),
    N = eval_meta(Size,Bs),
    var_vector_(N-1,Type,N,[],VV,Bs).

var_vector_(-1,Type,N,Xs,_V,Bs) -> 
    {{Type,N,Xs},Bs};
var_vector_(I,Type,N,Xs,V,Bs) ->
    {Xi,Bs1} = variable({Type,V,N,I},Bs),
    var_vector_(I-1,Type,N,[Xi|Xs],V,Bs1).

%% Fold operator Op over a variable vector
vfold_op(Bs,_Op,_D,[A]) ->
    {{bool,A},Bs};
vfold_op(Bs,Op,D,[Y|As]) ->
    {Z,Bs1} = vfold_op(Bs,Op,D,As),
    operation_(Op,{bool,Y},Z,Bs1);
vfold_op(Bs,_Op,D,[]) ->
    {D,Bs}.

all([], Bs) ->
    {{bool,?TRUE}, Bs};
all([A], Bs) ->
    {A, Bs};
all(As, Bs) ->
    As1 = [A || {bool,A} <- As],
    {X,Bs1} = fresh_var(Bs),
    {{bool,X}, and_gate(Bs1,X,As1)}.

any([], Bs) ->
    {{bool,?FALSE}, Bs};
any([A], Bs) ->
    {A, Bs};
any(As, Bs) ->
    As1 = [A || {bool,A} <- As],
    {X,Bs1} = fresh_var(Bs),
    {{bool,X}, or_gate(Bs1,X,As1)}.

none(As,Bs) ->
    {A,Bs1} = any(As,Bs),
    operation_('not',A,Bs1).

one(Xs, Bs) ->
    eqk(1,length(Xs),Xs,Bs).

sum([], Bs) ->
    const_vector(uint,0,1,Bs);
sum([X], Bs) ->
    {X, Bs};
sum([X|Xs], Bs) ->
    {Xn,Bs1} = sum(Xs,Bs),
    operation_('+', X, Xn, Bs1).

prod([], Bs) ->
    const_vector(uint,1,1,Bs);
prod([X], Bs) ->
    {X, Bs};
prod([X|Xs], Bs) ->
    {Xn,Bs1} = prod(Xs,Bs),
    operation_('*', X, Xn, Bs1).

-ifdef(__UNDEFINE__).
%% Not used - size = 5n
%% special version of eqk(1,length(Xs),Xs,Bs)
one_(Xs, Bs) ->
    {{One,_},Bs1} = one__(Xs, Bs),
    {One,Bs1}.

one__([], Bs) -> {{{bool,?FALSE},{bool,?FALSE}},Bs};
one__([A],Bs) -> {{A,A}, Bs};
one__([A|As],Bs) ->
    {{One,Or},Bs1} = one__(As,Bs),
    {A1,Bs2} = operation_('and',negate(A),One,Bs1),
    {A2,Bs3} = operation_('and',negate(One),negate(Or),Bs2),
    {A3,Bs4} = operation_('and',A,A2,Bs3),
    {One1,Bs5} = operation_('or',A1,A3,Bs4),
    {O1,Bs6} = operation_('or',A,Or,Bs5),
    {{One1,O1},Bs6}.
-endif.

%% Generate a formula where exact K out of N formulas are true.
eqk(0,_N, Xs, Bs) ->
    {A,Bs1} = any(Xs,Bs), {negate(A),Bs1};
eqk(K,N,_Xs,Bs) when K > N -> %% no models
    {{bool,?FALSE}, Bs};
eqk(K,N,Xs,Bs) when K =:= N ->
    all(Xs,Bs);
eqk(K,N,Xs,Bs) ->
    {Xs1,Bs1} = sort(Xs,K,Bs),
    {A,B} = lists:split(N-K, Xs1),
    {A1,Bs2} = any(A,Bs1),
    {B1,Bs3} = all(B,Bs2),
    operation_('and', negate(A1), B1, Bs3).

gtk(0,_N, Xs, Bs) ->
    any(Xs,Bs);
gtk(K,N,_Xs,Bs) when K >= N -> %% no models
    {{bool,?FALSE}, Bs};
gtk(K,N,Xs,Bs) ->
    {Xs1,Bs1} = sort(Xs,K,Bs),
    {A,B} = lists:split(N-K, Xs1),
    {A1,Bs2} = any(A,Bs1),
    {B1,Bs3} = all(B,Bs2),
    operation_('and', A1, B1, Bs3).

%% negate all input variables
negate({bool,X}) -> {bool,-X}.
     
vnot(Xs) ->
    map(fun(X) -> -X end, Xs).

%% negate "high" bit
vsnot([X]) -> [-X];
vsnot([X|Xs]) -> [X|vsnot(Xs)];
vsnot([]) -> [].


vextend(int,Xs,N,K) ->
    vset_size(Xs,K,lists:nth(N,Xs));
vextend(uint,Xs,_N,K) ->
    vset_size(Xs,K,?FALSE);
vextend(bit,Xs,_N,K) ->
    vset_size(Xs,K,?FALSE);
vextend(bool,Xs,1,K) ->
    vset_size(Xs,K,?FALSE).

-ifdef(__UNUSED__).
vtype({uint,_,_}) -> uint;
vtype({int,_,_})  -> int;
vtype({bit,_,_})  -> bit;
vtype({bool,_})   -> bool.
-endif.

-ifdef(__UNUSED__).
vsize({uint,N,_}) -> N;
vsize({int,N,_})  -> N;
vsize({bit,N,_})  -> N;
vsize({bool,_})   -> 1.
-endif.

varg(V={uint,_,_}) -> V;
varg(V={int,_,_}) -> V;
varg(V={bit,_,_}) -> V;
varg({bool,X}) -> {bool,1,[X]}.

vconst({uint,_,Xs}) -> vunsigned(Xs);
vconst({int,_,Xs}) -> vsigned(Xs);
vconst({bit,_,Xs}) -> vunsigned(Xs);
vconst({bool,X}) -> vunsigned([X]).

bit({uint,1,[X]}) -> X;
bit({bit,1,[X]}) -> X;
bit({bool,X}) -> X.
    

vsigned(Xs) ->
    N = (1 bsl (length(Xs)-1)),
    R = vunsigned(Xs),
    if R =:= false -> false;
       R < N -> R;
       true -> R - 2*N
    end.

vunsigned(Xs) ->
    vunsigned_(reverse(Xs), 0).

vunsigned_([?TRUE|Xs],N)  -> vunsigned_(Xs,(N bsl 1)+1);
vunsigned_([?FALSE|Xs],N) -> vunsigned_(Xs,(N bsl 1)+0);
vunsigned_([_|_],_N) -> false;
vunsigned_([],N) -> N.

%% set vector size to N  extend (with FALSE) at end / cut at end
vset_size(Xs,N) ->
    vset_size(Xs,N,?FALSE).

vset_size(_Xs,0,_D) -> [];
vset_size([],I,D) -> lists:duplicate(I,D);
vset_size([X|Xs],I,D) -> [X|vset_size(Xs,I-1,D)].

args(Fs,Bs) when is_list(Fs) ->
    build_list(Fs, Bs);
args(F,Bs) ->
    case build__(F, Bs) of
	{{uint,_N,Xs}, Bs1} -> {[{bool,X}||X<-Xs],Bs1};
	{{int,_N,Xs}, Bs1}  -> {[{bool,X}||X<-Xs],Bs1};
	{{bit,_N,Xs}, Bs1}  -> {[{bool,X}||X<-Xs],Bs1}
    end.

%% select the I'th bit in a bit vector
select_bool(I,N,Xs) when I >= 0, I < N ->
    {bool,lists:nth(I+1,Xs)};
select_bool(_I,_N,_Xs) ->
    {bool,?FALSE}.



%% FIXME: Extend Xs with ?FALSE as needed
select_range(J,I,N,Xs) when J >= I, I>=0, J<N ->
    N1 = (J-I)+1,
    {uint,N1,lists:sublist(Xs,I+1,N1)};
select_range(I,J,N,Xs) when J >= I, I>=0, J<N ->
    N1 = (J-I)+1,
    {uint,N1,lists:reverse(lists:sublist(Xs,I+1,N1))};
select_range(I,J,_N,_Xs) ->
    N1 = abs(I-J)+1,
    {uint,N1,lists:duplicate(N1,?FALSE)}.


build_list(Fs, Bs) ->
    build_list_(Fs, [], Bs).
    
build_list_([F|Fs],Acc,Bs) ->
    {X,Bs1} = build__(F,Bs),
    build_list_(Fs,[X|Acc],Bs1);
build_list_([],Acc,Bs) ->
    {reverse(Acc),Bs}.

%%
%% 
%%
operation_(Op, A, Bs) ->
    %% io:format("operation: ~w ~w\n", [Op,[A]]),
    operation(Op,A,Bs).

operation_(Op, A,B, Bs) ->
    %% io:format("operation: ~w ~w\n", [Op,[A,B]]),
    operation(Op,A,B,Bs).

%%
%% Unary operator
%%
operation('not',{bool,Y},Bs) ->
    {{bool,-Y},Bs};
operation('!',{bool,Y},Bs) ->
    {{bool,-Y},Bs};
operation('~',Y={bool,_Y},Bs) ->
    operation('not',Y,Bs);
operation('~', {Type,N,Ys}, Bs) when ?is_vec_type(Type) ->
    Ys1 = vnot(Ys),
    {{Type,N,Ys1}, Bs};

operation('-', A, Bs) ->
    {_At,An,Ax} = varg(A),
    case vconst(A) of
	false ->
	    Ax1 = vnot(Ax),
	    Zs1 = vset_size([?TRUE],An),
	    {{bool,_Co},Xs,Bs1} = vadd(Ax1,Zs1,Bs),
	    {{int,An,Xs},Bs1};
	Av ->
	    Av1 = -Av,
	    An1 = varp_math:integer_size(Av1),
	    const_vector_(An1-1,int,An1,[],Av1,Bs)
    end;

operation('abs', A={int,N,Ys}, Bs) ->
    Sign = sign_bit(A),
    {{_,_,Zs},Bs1} = operation_('-',A,Bs),
    {Xs,Bs2} = vite(Sign, Zs, Ys, Bs1),
    {{int,N,Xs},Bs2};
operation('abs', A={uint,_N,_Ys}, Bs) ->
    {A,Bs}.
    
%%
%% Binary operator
%%
operation('&&', A, B, Bs) ->
    operation_('and', A, B, Bs);

operation('and',{bool,?TRUE},{bool,?TRUE}, Bs) ->
    {{bool,?TRUE},Bs};
operation('and',{bool,?FALSE},{bool,_Z}, Bs) ->
    {{bool,?FALSE},Bs};
operation('and',{bool,_Y},{bool,?FALSE}, Bs) ->
    {{bool,?FALSE},Bs};
operation('and',{bool,Y},{bool,Z}, Bs) ->
    {X,Bs1} = fresh_var(Bs),
    {{bool,X},and_gate(Bs1,X,[Y,Z])};

operation('and',A,B,Bs) ->
    operation_('&',A,B,Bs);
operation('&',A,B,Bs) ->
    {At,An,Ax} = varg(A),
    {Bt,Bn,Bx} = varg(B),
    Cn = erlang:max(An,Bn),
    Ax1 = vextend(At,Ax,An,Cn),
    Bx1 = vextend(Bt,Bx,Bn,Cn),
    {Cx,Bs1} = vmap_op('and',Ax1,Bx1,Bs),
    Ct = mix_type(At,Bt),
    if Ct =:= bool ->
	    [C1] = Cx,
	    {{bool,C1},Bs1};
       true ->
	    {{Ct,Cn,Cx},Bs1}
    end;

operation('||', A, B, Bs) ->
    operation_('or', A, B, Bs);

operation('or',{bool,?FALSE},{bool,?FALSE}, Bs) ->
    {{bool,?FALSE},Bs};
operation('or',{bool,?TRUE},{bool,_Z}, Bs) ->
    {{bool,?TRUE},Bs};
operation('or',{bool,_Y},{bool,?TRUE}, Bs) ->
    {{bool,?TRUE},Bs};
operation('or',{bool,Y},{bool,Z}, Bs) ->
    {X,Bs1} = fresh_var(Bs),
    {{bool,X},or_gate(Bs1,X,[Y,Z])};

operation('or',A,B,Bs) ->
    operation_('|',A,B,Bs);
operation('|',A,B,Bs) ->
    {At,An,Ax} = varg(A),
    {Bt,Bn,Bx} = varg(B),
    Cn = erlang:max(An,Bn),
    Ax1 = vextend(At,Ax,An,Cn),
    Bx1 = vextend(Bt,Bx,Bn,Cn),
    {Cx,Bs1} = vmap_op('or',Ax1,Bx1,Bs),
    Ct = mix_type(At,Bt),
    if Ct =:= bool ->
	    [C1] = Cx,
	    {{bool,C1},Bs1};
       true ->
	    {{Ct,Cn,Cx},Bs1}
    end;

operation('imp',{bool,?FALSE},{bool,?TRUE}, Bs) ->
    {{bool,?TRUE},Bs};
operation('imp',{bool,?FALSE},{bool,?FALSE}, Bs) ->
    {{bool,?TRUE},Bs};
operation('imp',{bool,?TRUE},{bool,?TRUE}, Bs) ->
    {{bool,?TRUE},Bs};
operation('imp',{bool,?TRUE},{bool,?FALSE}, Bs) ->
    {{bool,?FALSE},Bs};
operation('imp',{bool,Y},{bool,Z}, Bs) ->
    {X,Bs1} = fresh_var(Bs),
    {{bool,X},or_gate(Bs1,X,[-Y,Z])};
operation('imp',A,B,Bs) ->
    {An,Bs1} = operation_('~',A,Bs),
    operation_('|',An,B,Bs1);

operation('equ',{bool,?TRUE},{bool,?FALSE},Bs) ->
    {{bool,?FALSE},Bs};    
operation('equ',{bool,?FALSE},{bool,?TRUE},Bs) ->
    {{bool,?FALSE},Bs};
operation('equ',{bool,?TRUE},{bool,?TRUE},Bs) ->
    {{bool,?TRUE},Bs};
operation('equ',{bool,?FALSE},{bool,?FALSE},Bs) ->
    {{bool,?TRUE},Bs};
operation('equ',{bool,Y},{bool,Z},Bs) ->
    {X,Bs1} = fresh_var(Bs),
    {{bool,X},xor_gate(Bs1,X,[-Y,Z])};

operation('equ',A,B,Bs) ->
    {At,An,Ax} = varg(A),
    {Bt,Bn,Bx} = varg(B),
    Cn = erlang:max(An,Bn),
    Ax1 = vextend(At,Ax,An,Cn),
    Bx1 = vextend(Bt,Bx,Bn,Cn),
    {Cx,Bs1} = vmap_op('equ',Ax1,Bx1,Bs),
    Ct = mix_type(At,Bt),
    if Ct =:= bool ->
	    [C1] = Cx,
	    {{bool,C1},Bs1};
       true ->
	    {{Ct,Cn,Cx},Bs1}
    end;

operation('xor',{bool,Y},{bool,Z},Bs) ->
    {X,Bs1} = fresh_var(Bs),
    {{bool,X},xor_gate(Bs1,X,[Y,Z])};
operation('xor',A,B,Bs) ->
    operation_('^',A,B,Bs);
operation('^',A,B,Bs) ->
    {At,An,Ax} = varg(A),
    {Bt,Bn,Bx} = varg(B),
    Cn = erlang:max(An,Bn),
    Ax1 = vextend(At,Ax,An,Cn),
    Bx1 = vextend(Bt,Bx,Bn,Cn),
    {Cx,Bs1} = vmap_op('xor',Ax1,Bx1,Bs),
    Ct = mix_type(At,Bt),
    if Ct =:= bool ->
	    [C1] = Cx,
	    {{bool,C1},Bs1};
       true ->
	    {{Ct,Cn,Cx},Bs1}
    end;

operation('+',A,B,Bs) ->
    {At,An,Ax} = varg(A),
    {Bt,Bn,Bx} = varg(B),
    Cn = erlang:max(An,Bn),
    Ax1 = vextend(At,Ax,An,Cn),
    Bx1 = vextend(Bt,Bx,Bn,Cn),
    {Carry,Cx,Bs1} = vadd(Ax1,Bx1,Bs),
    Bs2 = set_carry_(Carry,maps:get(carry,Bs1#bs.option),Bs1),
    Ct = mix_type(At,Bt),
    {{Ct,Cn,Cx},Bs2};

%% FIXME:
%% A < B  <=>  A - B < 0
operation('<',{bool,Y},{bool,Z},Bs) ->  %% Y < Z
    operation_('and', negate({bool,Y}),{bool,Z}, Bs);
operation('<',{int,An,Ax},{int,Bn,Bx},Bs) when An>1, Bn>1 ->
    Cn = erlang:max(An,Bn),
    Ax1 = vextend(int,Ax,An,Cn),
    Bx1 = vextend(int,Bx,Bn,Cn),
    {Ax2,[Ak]} = lists:split(Cn-1,Ax1),
    {Bx2,[Bk]} = lists:split(Cn-1,Bx1),
    %% abs(X) < abs(Y)
    {Q,Bs1}  = operation_('equ',{bool,Ak},{bool,Bk},Bs),
    {Lt,Bs2} = vless(Ax2,Bx2,Bs1),
    {A1,Bs3} = operation_('and',Q,Lt,Bs2),
    %%  Y<0  AND Z>=0
    {L,Bs4} = operation_('<',{bool,Bk},{bool,Ak},Bs3),
    any([A1,L],Bs4);
operation('<',A,B,Bs) ->
    {At,An,Ax} = varg(A),
    {Bt,Bn,Bx} = varg(B),
    Cn = erlang:max(An,Bn),
    Ax1 = vextend(At,Ax,An,Cn),
    Bx1 = vextend(Bt,Bx,Bn,Cn),
    vless(Ax1,Bx1,Bs);
%%    K = erlang:max(N,M),
%%    Ys1 = vextend(Type1,Ys,N,K),
%%    Zs1 = vextend(Type2,Zs,M,K),
%%    vless(Ys1,Zs1,Bs);
operation('>',{bool,Y},{bool,Z},Bs) ->  %% Y > Z
    operation_('and', {bool,Y}, negate({bool,Z}), Bs);
operation('>',Y,Z,Bs) ->
    operation_('<', Z, Y, Bs);
operation('<=',Y,Z,Bs) ->
    {C,Bs1} = operation_('<', Z, Y, Bs),
    {negate(C),Bs1};
operation('>=',Y,Z,Bs) ->
    operation_('<=',Z,Y,Bs);

operation('!=',{bool,Y},{bool,Z},Bs) ->
    operation_('xor',{bool,Y},{bool,Z},Bs);
operation('!=',Y,Z,Bs) ->
    {C,Bs1} = operation_('==', Y, Z, Bs),
    {negate(C),Bs1};

operation('==',{bool,Y},{bool,Z},Bs) ->
    operation_('equ',{bool,Y},{bool,Z},Bs);
operation('==',A,B,Bs) ->
    %% fixme: warn about different sign (uint == int) ?
    {At,An,Ax} = varg(A),
    {Bt,Bn,Bx} = varg(B),
    Cn = erlang:max(An,Bn),
    Ax1 = vextend(At,Ax,An,Cn),
    Bx1 = vextend(Bt,Bx,Bn,Cn),
    veq(Ax1,Bx1,Bs);

operation('<->', A, B, Bs) ->
    operation_('==', A, B, Bs);

operation('->', A, B, Bs) ->
    operation_('imp', A, B, Bs);

%%
%% Alias operation
%%
operation('=',V,X={T,Size,Xs},Bs) when is_atom(V), ?is_vec_type(T) ->
    {X, alias_vector(Bs,T,V,Size,Xs)};
operation('=',V,X={bool,Xb},Bs) when is_atom(V) ->
    {X, alias(V,Xb,Bs)};

operation('<<',A,B,Bs) ->
    {At,An,Ax} = varg(A),
    K = vconst(B),
    Ax1 = if K =:= false ->
		  error({shift_not_constant, B});
	     K >=0 ->
		  vshift_left(K,An,Ax);
	     At =:= int ->
		  vshift_right(-K,An,Ax);
	     true ->
		  vushift_right(-K,An,Ax)
	  end,
    {{At,An,Ax1}, Bs};

operation('>>',A,B,Bs) ->
    {At,An,Ax} = varg(A),
    K = vconst(B),
    Ax1 = if K =:= false ->
		  error({shift_not_constant, B});
	     K >=0, At =:= int ->
		  vshift_right(K,An,Ax);
	     K >= 0 ->
		  vushift_right(K,An,Ax);
	     K < 0 ->
		  vshift_left(-K,An,Ax)
	  end,
    {{At,An,Ax1}, Bs};
	    
%% rotate left
operation('<<<',A,B,Bs) ->
    {At,An,Ax} = varg(A),
    K = vconst(B),
    if K =:= false ->
	    error({shift_not_constant, B});
       K >= 0 ->
	    K1 = K rem An,
	    {Ax1,Ax2} = lists:split(K1, Ax),
	    Ax3 = Ax2++Ax1,
	    {{At,An,Ax3},Bs}
    end;

%% rotate right
operation('>>>',A,B,Bs) ->
    {At,An,Ax} = varg(A),
    K = vconst(B),
    if K =:= false ->
	    error({shift_not_constant, B});
       K >= 0 ->
	    K1 = K rem An,
	    {Ax1,Ax2} = lists:split(An-K1, Ax),
	    Ax3 = Ax2++Ax1,
	    {{At,An,Ax3},Bs}
    end;

operation('-',A,B,Bs) ->
    {At,An,Ax} = varg(A),
    {Bt,Bn,Bx} = varg(B),
    Cn = erlang:max(An,Bn),
    Ax1 = vextend(At,Ax,An,Cn),
    Bx1 = vextend(Bt,Bx,Bn,Cn),
    {BorrowNot,Cx,Bs1} = vsub(Ax1,Bx1,Bs),
    Bs2 = set_carry_(negate(BorrowNot),
		     maps:get(borrow,Bs1#bs.option),Bs1),
    Ct = mix_type(At,Bt),
    {{Ct,Cn,Cx},Bs2};

operation('*',A,B,Bs) ->
    %% integer type? 
    %% FIXME: abs(A) * abs(B) !!
    {At,An,Ax} = varg(A),
    {Bt,Bn,Bx} = varg(B),
    Cn = erlang:max(An,Bn),
    Ax1 = vextend(At,Ax,An,Cn),
    Bx1 = vextend(Bt,Bx,Bn,Cn),
    Ct = mix_type(At,Bt),
    {Cx,Bs1} = 
	if Ct =:= int ->
		vsmul(Ax1,Bx1,Bs);
	   true ->
		vmul(Ax1,Bx1,Bs)
	end,
    {{Ct,Cn+Cn,Cx},Bs1};

%% DivZero  coould be used to generate a Exception output
operation('/',{uint,N,Ys},{uint,M,Zs},Bs) ->
    K = erlang:max(N,M),
    Ys1 = vextend(uint,Ys,N,K),
    Zs1 = vextend(uint,Zs,M,K),
    {Qs,_Rs,DivZero,Bs1} = vdivrem(Ys1,Zs1,Bs),
    Bs2 = set_carry_(DivZero,maps:get(divz,Bs1#bs.option),Bs1),
    {{uint,K,Qs},Bs2};

%% DivZero  coould be used to generate a Exception output
operation('%',{uint,N,Ys},{uint,M,Zs},Bs) ->
    K = erlang:max(N,M),
    Ys1 = vextend(uint,Ys,N,K),
    Zs1 = vextend(uint,Zs,M,K),
    {_Qs,Rs,DivZero,Bs1} = vdivrem(Ys1,Zs1,Bs), %% fixme vrem! 
    Bs2 = set_carry_(DivZero,maps:get(divz,Bs1#bs.option),Bs1),
    {{uint,K,Rs},Bs2};

operation('min',Y={bool,_Y},Z={bool,_Z},Bs) ->
    operation_('and',Y,Z,Bs);
operation('min',A,B,Bs) ->
    %% integer type?
    {At,An,Ax} = varg(A),
    {Bt,Bn,Bx} = varg(B),
    Cn = erlang:max(An,Bn),
    Ax1 = vextend(At,Ax,An,Cn),
    Bx1 = vextend(Bt,Bx,Bn,Cn),
    {Cond,Bs1} = vless(Ax1,Bx1,Bs),
    {Cx,Bs2} = vite(Cond, Ax1, Bx1, Bs1),
    Ct = mix_type(At,Bt),
    {{Ct,Cn,Cx},Bs2};

operation('max',Y={bool,_Y},Z={bool,_Z},Bs) ->
    operation_('or',Y,Z,Bs);
operation('max',A,B,Bs) ->
    %% integer type?
    {At,An,Ax} = varg(A),
    {Bt,Bn,Bx} = varg(B),
    Cn = erlang:max(An,Bn),
    Ax1 = vextend(At,Ax,An,Cn),
    Bx1 = vextend(Bt,Bx,Bn,Cn),
    {Cond,Bs1} = vless(Bx1,Ax1,Bs),
    {Cx,Bs2} = vite(Cond, Ax1, Bx1, Bs1),
    Ct = mix_type(At,Bt),
    {{Ct,Cn,Cx},Bs2}.


%% Handle carry (Is it wise to backtrack over a Carry variable?)
set_carry_({bool,Carry}, false, Bs) ->    %% never overflow
    xor_gate(Bs,?FALSE,[Carry,?FALSE]);
set_carry_({bool,Carry}, true, Bs) ->     %% only overflow
    xor_gate(Bs,?FALSE,[Carry,?TRUE]);
set_carry_({bool,_Carry}, ignore, Bs) ->  %% allow carry overflow
    Bs.

%% sign bit as boolean
sign_bit({Type,N,Xs}) when ?is_int_type(Type) ->
    {bool,lists:nth(N,Xs)}.

%% Mix integer type (cast?)
mix_type(T,T) -> T;
mix_type(uint,int)  -> uint;
mix_type(uint,bit)  -> uint;
mix_type(uint,bool) -> uint;

mix_type(int,uint)  -> uint;
mix_type(int,bit)   -> int;
mix_type(int,bool)  -> uint;

mix_type(bit,uint)  -> uint;
mix_type(bit,int)   -> int;
mix_type(bit,bool)  -> bit;

mix_type(bool,uint) -> uint;
mix_type(bool,int)  -> int;
mix_type(bool,bit)  -> bit.

%%
%% Multiplier circuit: Y*Z
%%
%%  Y = (y0 + y1*2^1 + y2*2^2 + ... yk*2^k)
%%  Z = (z0 + z1*2^1 + z2*2^2 + ... zl*2^l)
%% 
%%  Y*Z = y0*Z + y1*2^1*Z + ... yk*2^k*Z
%%
%%  yi*2^i*Z = yi*z0*2^(i+0) + yi*z1*2^(i+1) + yi*zj*2^(i+j)
%%
%% Ex1
%% Y=7:3 [1,1,1] * Z=5:3[1,0,1]
%%
%% 0: Xs=[0,0,0]
%% 1: [0,0,0]     + [1,0,1]     = [1,0,1,0]
%% 2: [1,0,1,0]   + [0,1,0,1]   = [1,1,1,1,0]
%% 3: [1,1,1,1,0] + [0,0,1,0,1] = [1,1,0,0,0,1]
%%
vmul([Y|Ys], Zs, Bs) ->
    {Xs,Bs1} = vmap_opx('and',Zs,Y,Bs),
    vmul(Ys, Zs, 1, Xs++[?FALSE], Bs1).

vmul([Y|Ys], Zs, I, Xs, Bs) ->
    {YZs,Bs1} = vmap_opx('and',Zs,Y,Bs),
    YZs1 = lists:duplicate(I,?FALSE)++YZs,
    {{bool,Co},Xs1,Bs2} = vadd(Xs,YZs1,Bs1),
    vmul(Ys, Zs, I+1, Xs1++[Co], Bs2);
vmul([], _Zs, _I, Xs, Bs) ->
    {Xs, Bs}.

%%
%% Signed multiply
%%
vsmul([Y|Ys], Zs, Bs) ->
    %% N = length(Ys)+1,
    {YZs,Bs1} = vmap_opx('and',Zs,Y,Bs),
    Xs1 = vsnot(YZs)++[?TRUE],
    vsmul(Ys, Zs, 1, Xs1, Bs1).

vsmul([Y], Zs, I, Xs, Bs) ->
    {YZs,Bs1} = vmap_opx('and',Zs,Y,Bs),
    YZs1 = lists:duplicate(I,?FALSE)++vsnot(vnot(YZs))++[?TRUE],
    {{bool,Co},Xs1,Bs2} = vadd(Xs++[?FALSE],YZs1,Bs1),
    {Xs1++[Co], Bs2};
vsmul([Y|Ys], Zs, I, Xs, Bs) ->
    {YZs,Bs1} = vmap_opx('and',Zs,Y,Bs),
    YZs1 = lists:duplicate(I,?FALSE)++vsnot(YZs),
    {{bool,Co},Xs1,Bs2} = vadd(Xs,YZs1,Bs1),
    vsmul(Ys, Zs, I+1, Xs1++[Co], Bs2);
vsmul([], _Zs, _I, Xs, Bs) ->
    {Xs, Bs}.

%%
%% Divider/Reminder circuit  (X/Y)
%%   X : N bits
%%   Y : N bits
%%
%%   R = 0
%%   for (i = 0; i < N; i++) {
%%	R <<= 1;
%%	if (HIGHBIT(X))
%%	    R |= 1;
%%	X <<= 1;
%%	if (R < Y)
%%	    X &= ~1; %% clear low bit
%%	else {
%%	    R -= Y;
%%	    X |= 1;
%%	}
%%
vdivrem(X, Y, Bs) ->
    N = length(Y),
    Zs = vextend(uint,[],0,N),  %% R = 0
    {Q,R,Bs1} = vdivrem(X, Y, Zs, N, N, Bs),
    {DivZero,Bs2} = veq(Y, Zs,Bs1),
    {Q,R,DivZero,Bs2}.

vdivrem(X, _Y, R, _N, 0, Bs) ->
    {X, R, Bs};
vdivrem(X, Y, R, N, I, Bs) ->
    %% R << 1
    [R0|Rs] = vshift_left(1, N, R),      
    Xn = lists:last(X),
    %% if (HIGHBIT(X)) R |= 1;
    {{bool,R00},Bs1} = ite({bool,Xn}, {bool,?TRUE}, {bool,R0},Bs),
    R1 = [R00|Rs],
    %% X <<= 1;
    [_X10|X1] = vshift_left(1, N, X),
    %% if (R < Y)  X &= ~1; else X |= 1;
    {{bool,Lt},Bs2} = vless(R1, Y, Bs1),
    X2 = [-Lt|X1],
    %% R = R - Y
    {BorrowNot,R2,Bs3} = vsub(R1, Y, Bs2),
    Bs4 = set_carry_(negate(BorrowNot),ignore,Bs3),
    %% if (R < Y) R=R; R = R - Y
    {R3,Bs5} = vite({bool,Lt}, R1, R2, Bs4),
    vdivrem(X2, Y, R3, N, I-1, Bs5).

%%
%% Reminder circuit  (X%Y)
%%   X : N bits
%%   Y : N bits
%%
%%   R = 0
%%   for (i = 0; i < N; i++) {
%%	R <<= 1;
%%	if (HIGHBIT(X))
%%	    R |= 1;
%%	X <<= 1;
%%	if (R >= Y)
%%	    R -= Y;
%%   }
%%
-ifdef(__UNUSED__).

vrem(X, Y, Bs) ->
    N = length(Y),
    Zs = vextend(uint,[],0,N),  %% R = 0
    {R,Bs1} = vrem(X, Y, Zs, N, N, Bs),
    {DivZero,Bs2} = veq(Y, Zs,Bs1),
    {R,DivZero,Bs2}.

vrem(_X, _Y, R, _N, 0, Bs) ->
    {R, Bs};
vrem(X, Y, R, N, I, Bs) ->
    %% R << 1
    [R0|Rs] = vshift_left(1, N, R),      
    Xn = lists:last(X),
    %% if (HIGHBIT(X)) R |= 1;
    {{bool,R00},Bs1} = ite({bool,Xn}, {bool,?TRUE}, {bool,R0},Bs),
    R1 = [R00|Rs],
    {{bool,Lt},Bs2} = vless(R1, Y, Bs1),
    %% R = R - Y
    {BorrowNot,R2,Bs3} = vsub(R1, Y, Bs2),
    Bs4 = set_carry_(negate(BorrowNot),ignore,Bs3),
    %% if (R < Y) R=R; R = R - Y
    {R3,Bs5} = vite({bool,Lt}, R1, R2, Bs4),
    vrem(tl(X), Y, R3, N, I-1, Bs5).
-endif.

%%
%% Subtraction 
%%
vsub(Ys, Zs, Bs) ->
    Zs1 = vnot(Zs),
    vadd(Ys,Zs1,[],{bool,?TRUE},Bs).

%%
%% Adder circuit
%%
vadd(Ys,Zs,Bs) ->
    vadd(Ys,Zs,[],{bool,?FALSE},Bs).

vadd([?FALSE|Ys],[?FALSE|Zs],Xs,{bool,Ci},Bs) ->
    vadd(Ys,Zs,[Ci|Xs],{bool,?FALSE},Bs);
vadd([?FALSE|Ys],[Z|Zs],Xs,Ci,Bs) ->
    {{bool,X},Co,Bs1} = half_adder({bool,Z},Ci,Bs),
    vadd(Ys,Zs,[X|Xs],Co,Bs1);
vadd([Y|Ys],[?FALSE|Zs],Xs,Ci,Bs) ->
    {{bool,X},Co,Bs1} = half_adder({bool,Y},Ci,Bs),
    vadd(Ys,Zs,[X|Xs],Co,Bs1);
vadd([Y|Ys],[Z|Zs],Xs,Ci,Bs) ->
    {{bool,X},Co,Bs1} = full_adder({bool,Y},{bool,Z},Ci,Bs),
    vadd(Ys,Zs,[X|Xs],Co,Bs1);
vadd([],[],Xs,Ci,Bs) -> 
    {Ci,reverse(Xs),Bs}.

%% Full adder circuit.
full_adder(Y,Z,Ci,Bs) ->
    {X1,Bs1} = operation('xor',Y,Z,Bs),
    {X2,Bs2} = operation('xor',X1,Ci,Bs1),
    {A1,Bs3} = operation('and',X1,Ci,Bs2),
    {A2,Bs4} = operation('and',Y,Z,Bs3),
    {Co,Bs5} = operation('or',A1,A2,Bs4),
    {X2,Co,Bs5}.

half_adder(Y,Z,Bs) ->
    {X1,Bs1} = operation('xor',Y,Z,Bs),
    {Co,Bs2} = operation('and',Y,Z,Bs1),
    {X1,Co,Bs2}.

%%
%% if-then-else circuit
%%  (I & T) | (~I & E)
%%
ite({bool,?TRUE},T,_E, Bs) ->
    {T,Bs};
ite({bool,?FALSE},_T,E, Bs) -> 
    {E,Bs};
ite(_I,X,X, Bs) ->
    {X,Bs};
%% (I & false) | (~I & E) == ~I & E
ite(I,{bool,?FALSE},E, Bs) ->
    operation('and',negate(I),E,Bs);
%% (I & T) | (~I & false) == I & T
ite(I,T,{bool,?FALSE}, Bs) ->
    operation('and',I,T,Bs);
ite(I,T,E, Bs) ->
    {A1,Bs1} = operation('and',I,T,Bs),
    {A2,Bs2} = operation('and',negate(I),E,Bs1),
    operation('or',A1,A2,Bs2).

%% vector version of ite condition control if Ys or Zs is passed
vite(I,Ys,Zs,Bs) ->
    vite_(I,Ys,Zs,[],Bs).
    
vite_(I,[Y|Ys],[Z|Zs],Xs,Bs) ->
    {{bool,X}, Bs1} = ite(I,{bool,Y},{bool,Z},Bs),
    vite_(I,Ys,Zs,[X|Xs],Bs1);
vite_(_I,[],[],Xs,Bs) ->
    {reverse(Xs),Bs}.

%% conditional vector Ys or variable value Z
-ifdef(__UNUSED__).
vitex(I,Ys,Z,Bs) when is_list(Ys), is_integer(Z) ->
    vitex_(I,Ys,Z,[],Bs).
    
vitex_(I,[Y|Ys],Z,Xs,Bs) ->
    {{bool,X}, Bs1} = ite(I,{bool,Y},{bool,Z},Bs),
    vitex_(I,Ys,Z,[X|Xs],Bs1);
vitex_(_I,[],_Z,Xs,Bs) ->
    {reverse(Xs),Bs}.
-endif.
%% 
%% shift_left 2 [X0,X1,X2,X3,X4,X5,X6,X7]  ==
%%              [FALSE,FALSE,X0,X1,X2,X3,X4,X5]
vshift_left(K,N,Xs) when K >= 0 ->
    K1 = erlang:min(K,N),
    lists:duplicate(K1,?FALSE) ++ lists:sublist(Xs,1,N-K1).

%% unsigned shift right (ignoring sign bit) 
%% shift_right 2 [X0,X1,X2,X3,X4,X5,X6,X7]  ==
%%               [X2,X3,X4,X5,X6,X7,FALSE,FALSE]
vushift_right(K,N,Xs) when K >= 0 ->
    K1 = erlang:min(K,N),
    lists:sublist(Xs, K1+1, N) ++ lists:duplicate(K1,?FALSE).

%% signed shift right (shifing in sign bit)
%% shift_right 2 [X0,X1,X2,X3,X4,X5,X6,X7]  ==
%%               [X2,X3,X4,X5,X6,X7,X7,X7]
vshift_right(K,N,Xs) when K >= 0 ->
    K1 = erlang:min(K,N),
    Sign = lists:nth(N, Xs),
    lists:sublist(Xs, K1+1, N) ++ lists:duplicate(K1,Sign).

%% Compare equal
veq(Ys, Zs, Bs) ->
    {Xs,Bs1} = vmap_op('equ',Ys,Zs,Bs),
    vfold_op(Bs1,'and',{bool,?TRUE},Xs).
    
%% Compare less
vless([Y],[Z],Bs) ->
    operation('<',{bool,Y},{bool,Z},Bs);
vless([Y|Ys],[Z|Zs],Bs) ->
    {Lv,Ev,Bs1} = vlteq(Ys,Zs,Bs),
    {L1,Bs2} = operation('<',{bool,Y},{bool,Z},Bs1),
    {L2,Bs3} = operation('and',Ev,L1,Bs2),
    operation('or',L2,Lv,Bs3).

vlteq([Y],[Z],Bs) ->
    {Lt,Bs1} = operation('<', {bool,Y},{bool,Z},Bs),
    {Eq,Bs2} = operation('equ',{bool,Y},{bool,Z},Bs1),
    {Lt,Eq,Bs2};
vlteq([Y|Ys],[Z|Zs],Bs) ->
    {Lv,Ev,Bs1} = vlteq(Ys,Zs,Bs),
    {L1,Bs2} = operation('<',{bool,Y},{bool,Z},Bs1),
    {E1,Bs3} = operation('equ',{bool,Y},{bool,Z},Bs2),
    {L2,Bs4} = operation('and',Ev,L1,Bs3),
    {Lv2,Bs5} = operation('or',L2,Lv,Bs4),
    {Ev2,Bs6} = operation('and',Ev,E1,Bs5),
    {Lv2,Ev2,Bs6}.

%% Apply same operator on two vectors
vmap_op(Op,Ys,Zs,Bs) ->
    vmap_op(Op,Ys,Zs,[],Bs).

vmap_op(Op,[Y|Ys],[Z|Zs],Xs,Bs) ->
    {{bool,X},Bs1} = operation(Op,{bool,Y},{bool,Z},Bs),
    vmap_op(Op,Ys,Zs,[X|Xs],Bs1);
vmap_op(_Op,[],[],Xs,Bs) ->
    {reverse(Xs),Bs}.

%% Apply same operator on one vector and one variable
vmap_opx(Op,Ys,Z,Bs) ->
    vmap_opx(Op,Ys,Z,[],Bs).

vmap_opx(Op,[Y|Ys],Z,Xs,Bs) ->
    {{bool,X},Bs1} = operation(Op,{bool,Y},{bool,Z},Bs),
    vmap_opx(Op,Ys,Z,[X|Xs],Bs1);
vmap_opx(_Op,[],_Z,Xs,Bs) ->
    {reverse(Xs),Bs}.


%% circuit for Ys < Zs
%% vless([Y|Ys],[Z|Zs],Xs,Bs) ->

sort(Xs,0,Bs) -> 
    {Xs,Bs};
sort(Xs,I,Bs) ->
    {[X|Xs1],Bs1} = minmax(Xs,Bs),
    {Xs2,Bs2} = sort(reverse(Xs1),I-1,Bs1),
    {Xs2++[X],Bs2}.

%% create a single pass minmax circuit over input
%% return the result reversed.
minmax(Xs, Bs) ->
    minmax(Xs,[],Bs).

minmax([X1],_Ys,Bs) ->
    {[X1],Bs};
minmax([X1,X2],Ys,Bs) ->
    {Min,Max,Bs1} = minmax2(X1,X2,Bs),
    {[Max,Min|Ys], Bs1};
minmax([X1,X2|Xs],Ys,Bs) ->
    {Min,Max,Bs1} = minmax2(X1,X2,Bs),
    minmax([Max|Xs],[Min|Ys],Bs1).

%% min/max circuit
minmax2(X1,X2,Bs) ->
    {Max,Bs1} = operation('or',X1,X2,Bs),
    {Min,Bs2} = operation('and',X1,X2,Bs1),
    {Min,Max,Bs2}.

%% cnf_to_formula(Cs) ->
%%    {'ALL', [{'ANY', C} || C <- Cs]}.

is_equivalent(Bs, X, Y) ->
    class(Bs,X) =:= class(Bs,Y).

%% Return a list of input variables

model_variables(Bs,[]) ->
    List = fold_var(
	     fun(true,_,Acc) -> Acc;
		(false,_,Acc) -> Acc;
		(_X,Y,Acc) when is_integer(Y) ->
		     [Y | Acc];
		(_,_, Acc) -> Acc
	     end, [], Bs),
    lists:sort(List);
model_variables(Bs,Ws) ->
    lists:map(fun(W) -> get_var(W,Bs) end, Ws).

%%
%% collect the model
%% Boolean:  [{x,true},{y,false}]
%% Integer:  [{a,15},{b,-7},{c,0}]
%%
model(Bs) ->
    model(Bs#bs.vp, Bs#bs.vs).
    
model(Vp, Vs) ->
    lists:keysort(1, collect_model(Vp,Vs)).

collect_model(Vp,Vs) ->
    maps:fold(
      fun (?TRUE,_,Ms) -> Ms;
	  (?FALSE,_,Ms) -> Ms;
	  (Y,Xs,Ms) when is_integer(Y) ->
	      model_vars(Vp,Vs,Xs,Y,Ms);
	  (_, _, Ms) -> Ms
      end, [], Vs).

%% collect all alias variables    
model_vars(Vp,Vs,[{bit,X,N,I}|Xs],Y,Ms) ->
    case varc:get(Vp, Y) of
	?TRUE ->
	    model_vars(Vp,Vs,Xs,Y,model_bitset(X,N,I,1,Ms));
	?FALSE ->
	    model_vars(Vp,Vs,Xs,Y,model_bitset(X,N,I,0,Ms))
    end;
model_vars(Vp,Vs,[{uint,X,_N,I}|Xs],Y,Ms) ->
    case varc:get(Vp,Y) of
	?TRUE ->
	    model_vars(Vp,Vs,Xs,Y,model_bor({X,(1 bsl I)}, Ms));
	?FALSE ->
	    model_vars(Vp,Vs,Xs,Y,model_bor({X,0}, Ms))
    end;
model_vars(Vp,Vs,[{int,X,N,I}|Xs],Y,Ms) ->
    case varc:get(Vp,Y) of
	?TRUE ->
	    if I =:= N-1 ->
		    model_vars(Vp,Vs,Xs,Y,model_bor({X,(-1 bsl I)}, Ms));
	       true ->
		    model_vars(Vp,Vs,Xs,Y,model_bor({X,(1 bsl I)}, Ms))
	    end;
	?FALSE ->
	    model_vars(Vp,Vs,Xs,Y,model_bor({X,0}, Ms))
    end;
model_vars(Vp,Vs,[X|Xs],Y,Ms) when is_integer(Y) ->
    case varc:get(Vp,Y) of
	?TRUE -> 
	    model_vars(Vp,Vs,Xs,Y,[{X,true}|Ms]);
	?FALSE ->
	    model_vars(Vp,Vs,Xs,Y,[{X,false}|Ms]);
	_Z -> %% unbound...
	    %%model_vars(Xs,Y,Bs,[{X,Z} | Ms])
	    model_vars(Vp,Vs,Xs,Y,Ms)
    end;
model_vars(_Vp,_Vs,[],_Y,Ms) ->
    Ms.

model_bitset(X,N,I,V,Ms) ->
    case lists:keytake(X, 1, Ms) of
	{value,{_,Bits},Ms1} ->
	    <<A:I,_:1,B/bitstring>> = Bits,
	    [{X,<<A:I,V:1,B/bitstring>>} | Ms1];
	false ->
	    J = (N-I)-1,
	    [{X,<<0:I,V:1,0:J>>}, Ms]
    end.    
    
model_bor({X,Bit}, Ms) ->
    case lists:keytake(X, 1, Ms) of
	{value,{_,Bits},Ms1} ->
	    try Bit bor Bits of
		Bits1 -> [{X,Bits1} | Ms1]
	    catch
		error:_ ->
		    error({internal_error, {'bor',Bit,{X,Bits}}})
	    end;
	false ->
	    [{X,Bit} | Ms]
    end.

print(true,I,Bindings) ->
    Bindings1 = filter_bindings(Bindings),
    io:format("~w: ~s\n",
	      [I,concat([ format_binding(Bound) || Bound <- Bindings1 ], ",")]);
print(literal,I,Bindings) ->
    Bindings1 = filter_bindings(Bindings),
    io:format("~w: ~s\n",
	      [I,concat([ format_binding(Bound) || Bound <- Bindings1 ], ",")]);
print(model,I,Bindings) ->
    Bindings1 = filter_bindings(Bindings),
    io:format("~w: ~s\n",
	      [I,concat([ format_binding(Bound) || 
			    Bound <- Bindings1,
			    element(2,Bound) =/= false ], ",")]);
print(umodel,I,Bindings) ->
    io:format("~w: ~s\n",
	      [I,concat([ format_binding(Bound) || 
			    Bound <- Bindings,
			    element(2,Bound) =/= false ], ",")]);
print(erlang,_I,Bindings) ->
    Bindings1 = filter_bindings(Bindings),
    io:format("~w.\n", [Bindings1]);
print(false,_I,_Bindings) ->
    ok.

filter_bindings([B={{p,V,_},_}|Bs]) when is_atom(V) ->
    case hd(atom_to_list(V)) of
	$_ -> filter_bindings(Bs);
	_  -> [B|filter_bindings(Bs)]
    end;
filter_bindings([B|Bs]) ->
    [B|filter_bindings(Bs)];
filter_bindings([]) ->
    [].

format_binding({Var,Value}) ->
    VarFmt = format_p(Var),
    if Value =:= true -> VarFmt;
       Value =:= false -> [$!|VarFmt];
       is_integer(Value) -> [VarFmt,"=",integer_to_list(Value)]
    end.

format_p({p,T,As}) when is_integer(T) ->
    [$T,integer_to_list(As)|format_params(As)];
format_p({p,V,As}) when is_atom(V) ->
    [atom_to_list(V)|format_params(As)];
format_p({p,Name,As}) when is_list(Name); is_binary(Name) ->
    [Name|format_params(As)];
format_p({bit_index,Var,Index}) ->
    [format_p(Var),"[",integer_to_list(Index), "]"].

format_params([]) -> "";
format_params(As) when is_list(As) ->
    ["(",fmt_index_list(As),")"].

format_clause(Bs,CL) ->
    format_clause(Bs,CL,false).

format_clause(Bs,CL,Bound) ->
    List = format_literals(Bs,CL,Bound),
    ["{",List,"}"].

format_literals(Bs,Ls) ->
    format_literals(Bs,Ls,false).

format_literals(Bs,Ls,Bound) ->
    concat([format_literal(Bs,L,Bound)||L<-Ls],",").

format_literal(Bs,X) when is_integer(X) ->
    format_literal(Bs,X,false).

format_literal(Bs,X,Bound) when is_integer(X), X<0 ->
    ["!",format_var(Bs,-X,Bound)];
format_literal(Bs,X,Bound) when is_integer(X) ->
    format_var(Bs,X,Bound).

format_var(Bs,X) ->
    format_var(Bs,X,false).

format_var(_Bs,?TRUE,_Bound) -> "TRUE";
format_var(_Bs,?FALSE,_Bound) -> "FALSE";
format_var(Bs,X,Bound) ->    
    case find_var(X,Bs) of
	error ->
	    format_bnd(Bs, X, X, Bound);
	{ok,[Var]} ->
	    format_bnd(Bs, X, Var, Bound)
    end.

format_bnd(_Bs, _X, Var, false) ->
    format_symbol(Var);
format_bnd(Bs, X, Var, _Bound) ->
    L = implication_level(Bs, X), 
    Value = case value(Bs, X) of
		true -> "=1@"++integer_to_list(L);
		false -> "=0@"++integer_to_list(L);
		_ -> ""
	    end,
    format_symbol(Var) ++ Value.

implication_level(Bs,Imp) ->
    {_,_,ImpLev} = implication_clause(Bs,Imp),
    ImpLev.

format_symbol(true) -> "true";
format_symbol(false) -> "false";
format_symbol(V) when is_atom(V) -> atom_to_list(V);
format_symbol(I) when is_integer(I) -> [$$|integer_to_list(I)];
format_symbol({bit,V,_N,I}) ->
    format_symbol(V)++"["++integer_to_list(I)++"]";
format_symbol({uint,V,_N,I}) ->
    format_symbol(V)++"["++integer_to_list(I)++"]";
format_symbol({int,V,_N,I}) ->
    format_symbol(V)++"["++integer_to_list(I)++"]";
format_symbol({bit_index,V,I}) ->
    format_symbol(V)++"["++integer_to_list(I)++"]";
format_symbol(Var={p,_,_}) ->
    format_p(Var).

concat([], _) -> [];
concat([H],_) -> [H];
concat([H|T],S) -> [H,S | concat(T,S)].

fmt_bind(Bs,X,Y,D) ->
    io_lib:format("~s/~s(~w)", [fmt_v(Bs,X),fmt_v(Bs,Y),D]).

fmt_bind(Bs,X,Y) ->
    io_lib:format("~s/~s", [fmt_v(Bs,X),fmt_v(Bs,Y)]).

fmt_bind_list(Bs,Xs) ->
    concat([fmt_bind(Bs,X,Y) || {X,Y} <- Xs],",").
