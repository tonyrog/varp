%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2012, Tony Rogvall
%%% @doc
%%%    Building formulas
%%% @end
%%% Created :  2 Sep 2012 by Tony Rogvall <tony@rogvall.se>

-module(varp_formula).

%%-define(DEBUG, true).
%% -compile(export_all).
-export([build/1, build/2]).
-export([new/0, new/1]).
-export([add_variable/1, add_variable/2]).
-export([variable/2, alias/3]).
-export([value/2]).
-export([info/1, info/2]).
-export([fmt_var/2, fmt_v/2, fmt_q/2]).
-export([fmt_var_list/2]).
-export([fmt_bind/4]).
-export([fmt_bind/3]).
-export([fmt_bind_list/2]).
-export([print_model/4]).
-export([find_var/2, get_var/2]).
-export([uint64/2, uint32/2, uint16/2, uint8/2]).
-export([format_p/1]).
-export([format_meta/1]).
-export([or_gate/3, and_gate/3, xor_gate/3]).
-export([or_clause/2]).
-export([format_lit/2, format_lit/3]).
-export([format_literals/2, format_literals/3]).
-export([format_var/2]).
-export([format_symbol/1]).
-export([format_binding/1]).
-export([filter_bindings/1]).
-export([format_clause/2, format_clause/3]).
-export([log_clause/2]).
-export([proof_output/3]).
-export([want_proof_output/1]).
-export([clear_user_count/1]).

%% building with operations
-export([operation/4, operation/3]).
-export([all/2, any/2]).
-export([eqk/4, gtk/4]).
-export([subst/3]).

%% varc wrappers
-export([is_equal/3]).
-export([is_bound/2]).
-export([is_unbound/2]).
-export([getopt/2]).
-export([number_of_variables/1]).
-export([number_of_clauses/1]).
-export([number_of_dead_clauses/1]).
-export([number_of_bound/1]).
-export([number_of_unbound/1]).
-export([clause_bcp_counter/1]).
-export([clause_bcp_counter/2]).
-export([conflict_counter/1]).
-export([bcp_counter/1]).
-export([order_sort/2, order_sort/4]).
-export([order_first/2]).
-export([order_last/2]).
-export([model/1, model/2]).
-export([next_unbound/1, next_unbound/2]).
-export([info/3, debug/3]).
-export([get_bindings/2]).
-export([intersect_bindings/3]).
-export([install_bindings/3]).
-export([model_variables/2]).
-export([each_unbound/2]).
-export([each_variable/2]).
-export([fold_unbound/3]).
-export([eval_meta/2]).
-export([vfold_op/4]).
-export([conflicting_clause/1]).
-export([conflicting_clause/2]).
-export([get_clauses/3]).
-export([get_clause_info/2, get_clause_info/3]).
-export([add_clause/2, add_clause/3]).
-export([del_clause/2]).
-export([del_unused_clauses/1]).
-export([clean_clauses/1, clean_clauses/2]).
-export([set_var/3, add_var/4]).
-export([config/3]).
-export([const_vector/2, const_vector/3]).
-export([const_vector/4]).

-export([vconst/1]).
-export([normalize/3]).
-export([cix/1]).

-import(lists, [foldl/3]).

-include("varp.hrl").

-define(is_int_type(T),   (((T)=:=int) orelse ((T)=:=uint))).
-define(is_vec_type(T), (((T)=:=int) orelse ((T)=:=uint) orelse ((T)=:=bit))).


new() ->
    new(varp:default_options()).

new(Options) when is_list(Options) ->
    new(maps:from_list(Options));  %% fixme validate?
new(OptMap) when is_map(OptMap) ->
    NewOpts = #{ qtype      => maps:get(qtype,OptMap),
		 xref       => maps:get(xref,OptMap),
		 hash       => maps:get(hash,OptMap),
		 init_phase => maps:get(phase,OptMap),
		 use_phase  => maps:get(use_phase,OptMap),
		 seed       => maps:get(seed,OptMap)
	       },
    %% io:format("new(~w)\n", [NewOpts]),
    Vp  = varp_nif:new(NewOpts),
    Symbols  = maps:get(syms,OptMap),
    Counters = counters:new(?NUM_COUNTERS, []),
    Delta1   = counters:new(1024, []),
    Delta2   = counters:new(1024, []),
    CLen     = counters:new(1024, []),
    Proof_Output = maps:get(proof_output, OptMap),
    Proof_Filename = maps:get(proof_file, OptMap),
    Proof_Dirname  = maps:get(outdir, OptMap),
    Filename = if Proof_Dirname =:= "" -> Proof_Filename;
		  true -> filename:join(Proof_Dirname,Proof_Filename)
	       end,
    Proof_Fd = case Proof_Output of
		   none -> 
		       undefined;
		   user ->
		       user;
		   text ->
		       {ok,Fd} = 
			   file:open(Filename, [raw,write,delayed_write]),
		       Fd;
		   binary ->
		       {ok,Fd} = 
			   file:open(Filename, [raw,write,delayed_write]),
		       Fd
	       end,
    #bs {
       option = OptMap,
       vs = Symbols,
       meta     = maps:get(meta,OptMap),
       defs     = maps:get(defs,OptMap),
       decls    = maps:get(decls,OptMap),
       literals = maps:get(literals,OptMap),
       assert   = maps:get(assert,OptMap),
       input    = maps:get(input,OptMap),
       output   = maps:get(output,OptMap),
       counters = Counters,
       d1       = Delta1,
       d2       = Delta2,
       clen     = CLen,
       vp       = Vp,
       proof_fd = Proof_Fd
      }.

add_variable(Bs) ->
    Var = varp_nif:add_variable(Bs#bs.vp, false),
    varp_nif:isused(Bs#bs.vp, Var, true),
    Var.    

%% Create a variable and mark all atoms as used
add_variable(Bs, IsAtom) ->
    Var = varp_nif:add_variable(Bs#bs.vp, IsAtom),
    varp_nif:isused(Bs#bs.vp, Var, true),
    Var.

%% add symbol name to literal 
-spec add_symbol(Bs::#bs{}, L::integer(), Sym::term()|iolist()) ->
		       ok.
add_symbol(Bs, L, Sym) ->
    varp_nif:add_symbol(Bs#bs.vp, L, Sym).


%% build an OR gate with Y as output and Xs as input
%% Y = X1 or X2 .. or Xn
or_gate(Bs,Y,Xs) ->
    gate(Bs, 'or', Y, Xs).

%% build an AND gate with Y as output and Xs as input
%% Y = X1 and X2 .. and Xn =>  !Y = !X1 or !X2 ... !Xn
%%
and_gate(Bs,Y,Xs) ->
    gate(Bs, 'or', lnot(Y), [lnot(Xi)||Xi<-Xs]).

%% build an OR gate with Y as output and Xs as input
%% Y = X1 xor X2 .. xor Xn
xor_gate(Bs,Y,Xs) ->
    gate(Bs, 'xor', Y, Xs).

gate(Bs, 'or', X, [Y,Z]) when abs(X) =/= 1 ->  %% 2-gate
    add_clause(Bs,[lnot(X),Y,Z]),
    add_clause(Bs,[X,lnot(Y)]),
    add_clause(Bs,[X,lnot(Z)]),
    Bs;
gate(Bs,'or', X, Xs) when abs(X) =/= 1 -> %% or n-gate
    gate_tree(Bs,'or',X,Xs);
gate(Bs,'or', ?T, Xs) ->
    add_clause(Bs, Xs),
    Bs;
gate(Bs,'xor',X, [Y,Z]) ->
    if X =:= ?T ->
	    add_clause(Bs,[lnot(Y),lnot(Z)]),
	    add_clause(Bs,[Y,Z]),
	    Bs;
       X =:= ?F ->
	    add_clause(Bs,[lnot(Y),Z]),
	    add_clause(Bs,[Y,lnot(Z)]),
	    Bs;
       true -> %% install as clauses
	    add_clause(Bs,[X,lnot(Y),Z]),
	    add_clause(Bs,[X,Y,lnot(Z)]),
	    add_clause(Bs,[lnot(X),lnot(Y),lnot(Z)]),
	    add_clause(Bs,[lnot(X),Y,Z]),
	    Bs
    end;
gate(Bs, 'xor',X, Xs) when abs(X) =/= 1 -> %% or n-gate
    gate_tree(Bs,'xor',X,Xs).

add_clause(Bs,Ls) ->
    add_clause(Bs,Ls,?DELTA).

add_clause(Bs,Ls,Set) ->
    ?dbg("add clause: ~s\n", [format_clause(Bs,Ls)]),
    case varp_nif:add_clause(Bs#bs.vp,Ls,Set) of
	{false,_I} ->
	    throw(contradiction);
	false ->
	    throw(contradiction);
	{true,I} -> %% non conflict
	    ?dcall(fun() ->
			   CL = varp_nif:get_clause(Bs#bs.vp, I),
			   Flags = varp_nif:clause_info(Bs#bs.vp, I),
			   {W0,W1} = proplists:get_value(watch, Flags, {-1,-1}),
			   io:format("~w:(~w,~w) ~s\n",
				     [I,W0,W1,format_clause(Bs,CL)])
		   end),
	    I;
	true ->
	    %% io:format("clause : DEAD {~w,~w}\n", [Op,Ls]),
	    ?dcall(fun() ->
			   io:format("dead clause: ~s\n", 
				     [format_clause(Bs,Ls)])
		   end),
	    true
    end.

%% build an OR clause with Xs as input
%% 1 = X1 or X2 .. or Xn
or_clause(Bs,Xs) ->
    add_clause(Bs, Xs),
    Bs.

%% Check if proof output is active
want_proof_output(Bs) ->
    case ?GETOPT_BS(Bs, proof_output) of
	none -> false;
	Type -> Type
    end.

cix(I) ->
    {case (I bsr 30) band 3 of 
	 ?DELTA -> delta;
	 ?GAMMA -> gamma;
	 ?BETA -> beta;
	 ?ALPHA -> alpha
     end,
     I band 16#3fffffff}.


%% delete clause by index or list of literals
del_clause(Bs, IndexOrClause) ->
    varp_nif:del_clause(Bs#bs.vp, IndexOrClause).

del_unused_clauses(Bs) ->
    V = Bs#bs.vp,
    ?dbg("del_unused_clause gamma offset=~w, size=~w\n", 
	 [varp_nif:clauseset_offset(V, ?GAMMA), 
	  varp_nif:clauseset_size(V, ?GAMMA)]),
    varp_nif:clauseset_sort(V, ?GAMMA),  %% learnt clauses
    case want_proof_output(Bs) of
	false ->
	    del_clauses(V, varp_nif:clauseset_first(V, ?GAMMA));
	_ ->
	    del_proof_clauses(Bs, V, varp_nif:clauseset_first(V, ?GAMMA))
    end,
    ?dbg("del_unused_clause size=~w\n", 
	 [varp_nif:clauseset_size(V, ?GAMMA)]),
    ok.
    

del_clauses(_V, false) ->
    ok;
del_clauses(V, I) ->
    varp_nif:del_clause(V, I),
    ?dbg0("del_clause: ~w\n", [cix(I)]),
    del_clauses(V, varp_nif:clauseset_next(V, I)).

del_proof_clauses(_Bs, _V, false) ->
    ok;
del_proof_clauses(Bs, V, I) ->
    proof_output(Bs, $d, I),  
    varp_nif:del_clause(V, I),
    ?dbg0("proof del_clause: ~w\n", [cix(I)]),
    del_proof_clauses(Bs, V, varp_nif:clauseset_next(V, I)).

clean_clauses(Bs) ->
    clean_clauses(Bs, ?DELTA).

clean_clauses(Bs, Set) ->
    clean_clauses_(Bs, varp_nif:clauseset_first(Bs#bs.vp, Set)).

clean_clauses_(Bs, false) ->
    Bs;
clean_clauses_(Bs, I) ->
    varp_nif:clean_clause(Bs#bs.vp, I),
    clean_clauses_(Bs, varp_nif:clauseset_next(Bs#bs.vp, I)).

%% "balanced tree"
gate_tree(Bs,Op,X,Xs) ->
    case ?GETOPT_BS(Bs,assoc) of
	balanced -> gate_tree_b(Bs,Op,X,Xs);
	left  -> gate_tree_l(Bs,Op,X,Xs);
	right -> gate_tree_r(Bs,Op,X,Xs);
	none  -> gate_tree_n(Bs,Op,X,Xs)
    end.

%% left balanced 
gate_tree_l(Bs,Op,X,[X1,X2|Xs]) ->
    Y1 = add_variable(Bs),
    gate(Bs,Op,Y1,[X1,X2]),
    gate_tree_l_(Bs,Op,X,Xs,[Y1]).

gate_tree_l_(Bs,Op,X,[Xn],[Yi|_Ys]) ->
    gate(Bs,Op,X,[Yi,Xn]);
gate_tree_l_(Bs,Op,X,[Xi|Xs],Ys=[Yi|_]) ->
    Yj = add_variable(Bs),
    gate(Bs,Op,Yj,[Yi,Xi]),
    gate_tree_l_(Bs,Op,X,Xs,[Yj|Ys]).

%% right balanced 
gate_tree_r(Bs,Op,X,Xs) ->
    gate_tree_l(Bs,Op,X,lists:reverse(Xs)).

%% none balanced, install as a number of clauses
%% install as n+1 clauses
gate_tree_n(Bs,'or',X,Xs) ->
    add_clause(Bs,[-X|Xs]),  %% all Xi false => X is false
    lists:foreach(
      fun(Xi) ->
	      add_clause(Bs,[X,-Xi])  %% any Xi true => X is true
      end, Xs),
    Bs;
gate_tree_n(Bs,'xor',X,Xs) ->
    gate_tree_b(Bs,'xor',X,Xs).

%% balanced
gate_tree_b(Bs,Op,X,Xs) ->
    case lists:split(length(Xs) div 2,Xs) of
	{[U],[V]} ->
	    gate(Bs,Op,X,[U,V]);
	{[U],[V1,V2]} ->
	    X1 = add_variable(Bs),
	    Bs1 = gate(Bs,Op,X1,[V1,V2]),
	    gate(Bs1,Op,X,[U,X1]);
	{Us,Vs} ->
	    X1 = add_variable(Bs),
	    Bs2 = gate_tree_b(Bs,Op,X1,Us),
	    X2 = add_variable(Bs),
	    Bs3 = gate_tree_b(Bs2,Op,X2,Vs),
	    gate(Bs3,Op,X,[X1,X2])
    end.

is_temporary({p,V,_}) ->
    case atom_to_list(V) of
	[$$|_] -> true;
	_ -> false
    end;
is_temporary(_) ->
    false.

make_variable(V, Bs) ->
    case is_temporary(V) of
	true ->
	    N = add_variable(Bs, false),
	    add_symbol(Bs, N, format_symbol(V)),
	    {{bool,N}, alias(V,N,Bs)};
	false ->
	    N = add_variable(Bs, true),
	    add_symbol(Bs, N, format_symbol(V)),
	    {{bool,N}, alias(V,N,Bs)}
    end.

order_last(Bs, VarList) ->
    {RevLast,Bs1} = variable_list_(Bs,VarList,[]),
    ?dbg("last=~w\n",[lists:reverse(RevLast)]),
    ok = varp_nif:order_last(Bs#bs.vp, lists:reverse(RevLast)),
    Bs1.

order_first(Bs, VarList) ->
    {RevFirst,Bs1} = variable_list_(Bs,VarList,[]),
    ?dbg("first=~w\n",[lists:reverse(RevFirst)]),
    ok = varp_nif:order_first(Bs#bs.vp, lists:reverse(RevFirst)),
    Bs1.

variable_list_(Bs, [X|Vs], Acc) when is_integer(X) ->
    variable_list_(Bs, Vs, [X|Acc]);
variable_list_(Bs, [V|Vs], Acc) ->
    case build_(V, Bs) of
	{{bool,X}, Bs1} ->
	    ?dbg0("~w = ~w\n", [V, X]),
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

%% get_variable_info(Bs, [X|Xs]) ->
%%     U  = varp_nif:literal_info(Bs#bs.vp, X, user),
%%     Un = varp_nif:literal_info(Bs#bs.vp, -X, user),
%%     if U >= Un ->
%% 	    [{X,U}|get_variable_info(Bs, Xs)];
%%        true ->
%% 	    [{-X,Un}|get_variable_info(Bs, Xs)]
%%     end;
%% get_variable_info(_Bs, []) ->
%%     [].

cat([X|Xs], Ys) -> cat(Xs, [X|Ys]);
cat([], Ys) -> Ys.

order_sort(Bs,[Key1,Key2]) -> order_sort(Bs,Key1,Key2,-1);
order_sort(Bs,[Key1]) -> order_sort(Bs,Key1,?ORDER_UNDEFINED,-1).

order_sort(Bs,Key1,Key2,Arg) 
  when is_integer(Key1), is_integer(Key2), is_integer(Arg) ->
    varp_nif:order_sort(Bs#bs.vp,Key1,Key2,Arg).

value(Bs,V) ->
    varp_nif:value(Bs#bs.vp, V).

config(Bs, Item, Value) ->
    varp_nif:config(Bs#bs.vp, Item, Value).

info(Bs) ->
    varp:info(Bs#bs.vp).

info(Bs, Key) ->
    varp_nif:info(Bs#bs.vp, Key).

is_bound(Bs,Lit) ->
    varp_nif:is_bound(Bs#bs.vp,Lit).

is_unbound(Bs,Lit) ->
    not varp_nif:is_bound(Bs#bs.vp,Lit).

is_equal(Bs,LitA, LitB) ->
    not varp_nif:is_equal(Bs#bs.vp,LitA,LitB).

subst(Bs, X, Y) ->
    varp_nif:subst(Bs#bs.vp,X,Y).

getopt(Bs,Key) ->
    ?GETOPT_BS(Bs, Key).

number_of_variables(Bs) ->
    varp:get_number_of_variables(Bs#bs.vp).

number_of_clauses(Bs) ->
    varp:get_number_of_clauses(Bs#bs.vp).

number_of_dead_clauses(Bs) ->
    varp:get_number_of_dead_clauses(Bs#bs.vp).

number_of_bound(Bs) ->
    varp:get_number_of_bound_variables(Bs#bs.vp).

number_of_unbound(Bs) ->
    varp:get_number_of_unbound_variables(Bs#bs.vp).

clause_bcp_counter(Bs) ->
    varp:get_clause_bcp_counter(Bs#bs.vp).

clause_bcp_counter(Bs,N) ->
    varp:get_clause_bcp_counter(Bs#bs.vp,N).

bcp_counter(Bs) ->
    varp:get_bcp_counter(Bs#bs.vp).

conflict_counter(Bs) ->
    varp:get_conflict_counter(Bs#bs.vp).

next_unbound(Bs) ->
    varp_nif:next_unbound(Bs#bs.vp).

next_unbound(Bs, X) ->
    varp_nif:next_unbound(Bs#bs.vp, X).

get_bindings(Bs,Level) when is_integer(Level) ->
    varp_nif:get_bindings(Bs#bs.vp, Level).

info(Bs,Fmt,As) -> ?info(Bs#bs.option, Fmt, As).

debug(Bs,Fmt,As) ->  ?debug(Bs#bs.option, Fmt, As).

conflicting_clause(Bs) ->
    conflicting_clause(Bs,0).

conflicting_clause(Bs,I) ->
    varp_nif:conflicting_clause(Bs#bs.vp,I).

%% How = watch|literal|variable
get_clauses(Bs, L, How) ->
    varp_nif:get_clauses(Bs#bs.vp, L, How).

get_clause_info(Bs, I) ->
    varp_nif:clause_info(Bs#bs.vp, I).

get_clause_info(Bs, I, What) ->
    varp_nif:clause_info(Bs#bs.vp, I, What).

%% Bs is under the assumption that Var = TRUE
intersect_bindings(Bs, Var, Bs0) ->
    intersect_(Bs, Var, Bs0).

intersect_(Bs,Var,[X|B0]) when is_integer(X) -> %% , X > 0 ->
    %% !Var -> X
    case varp_nif:value(Bs#bs.vp, X) of
	?T ->  %% Var -> X, !Var -> X   =>  X
	    [X | intersect_(Bs,Var,B0)];
	?F -> %% Var -> !X, !Var -> X  =>  Var=!X
	    [{Var,-X} | intersect_(Bs,Var,B0)];
	_ ->
	    intersect_(Bs,Var,B0)
    end;
intersect_(Bs,Var,[{X,Y}|B0]) ->  %% not used in varp prover
    Y1 = varp_nif:value(Bs#bs.vp, X),
    if Y =:= ?T,  Y1 =:= ?F -> %% !Var => X, Var => !X
	    [{Var,-X} | intersect_(Bs,Var,B0)];
       Y =:= ?F, Y1 =:= ?T -> %% !Var => !X, Var => X
	    [{Var,X} | intersect_(Bs,Var,B0)];
       true ->
	    intersect_(Bs,Var,B0)
    end;
intersect_(Bs,Var,[_|B0]) ->
    intersect_(Bs,Var,B0);
intersect_(_Bs,_Var,[]) ->
    [].

install_bindings(_Bs,_Level,[]) ->
    ok;
install_bindings(Bs,Level,Bnds) ->
    install_(Bs,Level,Bnds).

install_(Bs,Level,[X|Xs]) when is_integer(X) ->
    true = varp_nif:bind(Bs#bs.vp, X),
    install_(Bs,Level,Xs);
install_(Bs,Level,[{X,X}|Xs]) ->
    install_(Bs,Level,Xs);
install_(Bs,Level=?TOP_LEVEL,[{X,?T}|Xs]) ->
    true = varp_nif:bind(Bs#bs.vp, X),
    install_(Bs,Level,Xs);
install_(Bs,Level=?TOP_LEVEL,[{X,?F}|Xs]) ->
    true = varp_nif:bind(Bs#bs.vp, -X),
    install_(Bs,Level,Xs);
install_(Bs,?TOP_LEVEL,[{X,Y}|Xs]) ->
    Xa = varp_nif:variable_info(Bs#bs.vp, X, is_atom),
    Ya = varp_nif:variable_info(Bs#bs.vp, Y, is_atom),
    if Ya, not Xa ->
	    ?dbg("subst: ~s/~s\n", [format_lit(Bs,Y), format_lit(Bs,X)]),
	    subst(Bs, Y, X);
       true ->
	    ?dbg("subst: ~s/~s\n", [format_lit(Bs,X), format_lit(Bs,Y)]),
	    subst(Bs, X, Y)
    end,
    install_(Bs,?TOP_LEVEL,Xs);
install_(Bs,_Level,[{_X,_Y}|Xs]) ->
    %% can not install X=Y on level > 0
    install_(Bs,_Level,Xs);
%%install_(Bs,Level,[_B|Xs]) ->
%%    ?dbg("install: did not handle ~p\n", [_B]),
%%    install_(Bs,Level,Xs);
install_(Bs,_Level,[]) ->
    Bs.

%% compact version of fmt_var
fmt_v(_,?T)  -> "1";
fmt_v(_,?F) -> "0";
fmt_v(Bs,X) ->
    if X < 0 -> fmt_var_(Bs,-X, "!", "");
       true ->  fmt_var_(Bs,X, "", "")
    end.

fmt_q(Bs,X) ->
    fmt_var(Bs,X, "\"").

fmt_var(Bs,X) ->
    fmt_var(Bs,X, "").

fmt_var(_Bs,?T,_Q)  -> "1";
fmt_var(_Bs,?F,_Q) -> "0";
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
	{ok,?T} -> "true";
	{ok,?F} -> "false"
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
fmt_index({const,I}) ->
    integer_to_list(I);
fmt_index(A) when is_atom(A) ->
    atom_to_list(A);
fmt_index(Set) when is_list(Set) ->
    ["{",fmt_set(Set),"}"];
fmt_index({f,F,Is}) ->
    fmt_func(F,Is).

fmt_func(F,Is) when is_atom(F) ->
    [atom_to_list(F)|fmt_fargs(Is)];
fmt_func(F,Is) when is_list(F); is_binary(F) ->
    [F|fmt_fargs(Is)].
    
fmt_fargs([]) -> [];
fmt_fargs(Is) ->
    ["(",fmt_index_list(Is),")"].

fmt_set([]) -> [];
fmt_set([I]) when is_integer(I) ->
    integer_to_list(I);
fmt_set([I|Is=[J|_]]) when is_integer(I), is_integer(J) ->
    [integer_to_list(I),","|fmt_set(Is)].
    
fmt_var_list(Bs,Xs) ->
    lists:join(",", [fmt_var(Bs,X)||X<-Xs]).

variable(V, Bs) ->
    W = expand_meta(V, Bs),
    ?dbg("variable expand: ~p -> ~w\n", [V,W]),
    case find_var(W, Bs) of
	error ->
	    case W of
		{p,P,Rs} ->
		    %% check for a definition of P(x1,..xn)
		    case match_def(P, Rs, Bs#bs.defs) of
			false ->
			    make_variable(W, Bs);
			{Bnd2,Def} ->
			    ?dbg0("~p = ~p\n", [Bnd2,Def]),
			    %% Names = [Name || {id,Name}<-Ps],
			    %% Bnd2 = lists:zip(Names,Rs),
			    Meta = maps:merge(Bs#bs.meta,maps:from_list(Bnd2)),
			    ?dbg0("meta bind: ~p\n", [Meta]),
			    {R,Bs1} = build__(Def, Bs#bs { meta=Meta}),
			    ?dbg0("R = ~p\n", [R]),
			    %% Meta1 = lists:nthtail(length(Bnd2),Bs1#bs.meta),
			    {R,Bs1#bs { meta=Bs#bs.meta}}
		    end;
		_ ->
		    make_variable(W, Bs)
	    end;
	{ok,N} when is_integer(N) ->
	    {{bool,N},Bs};
	{ok,Val} ->
	    {Val,Bs}
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

match_def(P, As, Defs) ->
    PSym = {P,length(As)},
    List = maps:get(PSym, Defs, []),
    %% io:format("match_def: ~p = ~p\n", [PSym, List]),
    match_def_list(List,As).

match_def_list([{Fs,Def}|Ds],As) ->
    %% io:format("match_def_args: ~p ~p\n", [Fs, As]),
    case match_def_args(Fs, As) of
	false -> match_def_list(Ds, As);
	Bnd -> {Bnd,Def}
    end;
match_def_list([], _As) -> false.

match_def_args(Fs, As) ->
    match_def_args(Fs, As, []).
    
match_def_args([F|Fs], [A|As], Acc) ->
    case {match_eval(F), match_eval(A)} of
	{Fi,Ai} when is_atom(Fi), is_integer(Ai) ->
	    match_def_args(Fs,As,[{atom_to_list(Fi),Ai}|Acc]);
	{Fi,Fi} when is_integer(Fi) ->
	    match_def_args(Fs,As,Acc);
	_ ->
	    false
    end;
match_def_args([],[],Acc) ->
    lists:reverse(Acc);
match_def_args(_, _, _Acc) ->
    false.

%% sub eval for match
match_eval({const,V}) -> V;
match_eval({id,Name}) -> list_to_atom(Name);
match_eval(X) when is_integer(X) -> X;
match_eval(X) when is_atom(X) -> X.

%% find propositional variable defintion P() or P
find_prop_def(P, Defs) ->
    case maps:get({P,0}, Defs, []) of
	[{[],Def}] -> Def;
	_ -> false
    end.

find_subst(P, [E={_Qy,{p,P,_}}|_]) -> E;
find_subst(P, [_|Bnd]) -> find_subst(P, Bnd);
find_subst(_P ,[]) -> false.

bind_meta([V={id,N}|Vs], Bs, Acc, Bnd) ->
    W = eval_meta(V,Bs),
    bind_meta(Vs, Bs, [W|Acc], [{N,W}|Bnd]);
bind_meta([V|Vs], Bs, Acc, Bnd) ->
    W = eval_meta(V,Bs),
    bind_meta(Vs, Bs, [W|Acc], Bnd);
bind_meta([], _Bs, Acc, Bnd) ->
    {lists:reverse(Acc),lists:reverse(Bnd)}.


%% bind a "meta" variable
push_meta(V,I,Bs) ->
    Bs#bs { meta = maps:put(V, I, Bs#bs.meta)}.

pop_meta(Bs, Meta) ->
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
    ?dbg("set_var ~w => ~w\n", [Var, Vi]),
    Vs1 = Vs#{ Var => Vi,  Vi => [Var] },
    Bs#bs { vs = Vs1 }.

add_var(Var, Vi, Alias,Bs) ->
    Vs = Bs#bs.vs,
    ?dbg("add_var ~w => ~w\n", [Var, Vi]),
    Vs1 = Vs#{ Var => Vi, Vi => [Var|Alias] },
    Bs#bs { vs = Vs1 }.

fold_var(Fun, Acc, Bs) ->
    maps:fold(Fun, Acc, Bs#bs.vs).

%%
%% Generate the variable rules from a formula
%%
build(F) ->
    build(F,varp:default_options()).

build(F,Opts) when is_list(Opts) ->
    build1(F, new(Opts));
build(F,Opts) when is_map(Opts) ->
    build1(F, new(Opts));
build(F,Bs) when is_record(Bs, bs) ->
    build1(F, Bs).

build1(F, Bs) ->
    try build__(F, Bs) of
      	Value -> Value
    catch
      	throw:contradiction -> 
     	    {{bool,?F},Bs}
    end.

build__(F, Bs) ->
    %% io:format("build__ ~p\n", [F]),
    R={_F1,_Bs1} = build_(F, Bs),
    %% io:format("build__ => ~p\n", [_F1]),
    %% io:format("Bs1 = ~p\n", [_Bs1]),
    R.

build_(undefined, Bs) ->
    {undefined, Bs};
build_(true, Bs) ->
    {{bool,?T}, Bs};
build_(false, Bs) ->
    {{bool,?F}, Bs};
build_({literal,X}, Bs) when is_integer(X) ->
    {{bool,X}, Bs};

build_(V={id,_}, Bs) -> %% meta variable
    W = eval_meta(V,Bs),
    if W >=0 ->
	    N = varp_math:unsigned_size(W),
	    const_vector(uint,W,N,Bs);
       W < 0 ->
	    N = varp_math:signed_size(W),
	    const_vector(int,W,N,Bs)
    end;
build_(W, Bs) when is_integer(W) ->
    if W < 0 ->
	    N = varp_math:signed_size(W),
	    const_vector(int,W,N,Bs);
       true ->
	    N = varp_math:unsigned_size(W),
	    const_vector(uint,W,N,Bs)
    end;

build_(V={p,P,Ps}, Bs) ->
    PSym = varp:make_psym(P, Ps),
    Arity = length(Ps),
    case maps:find(PSym,Bs#bs.decls) of
	error ->
	    Decls1 = maps:put(PSym,{bool,Arity,1},Bs#bs.decls),
	    variable(V, Bs#bs { decls = Decls1 });
	{ok,{bool,Arity1,1}} when Arity =/= Arity1 ->
	    error({arity_mismatch,P});
	{ok,{bool,Arity,1}} ->
	    variable(V, Bs);
	{ok,{PType,_Arity,Size}} ->
	    var_vector(PType,V,Size,Bs)
    end;
build_({PType,SExpr,PExpr},Bs) when
      PType =:= uint; PType =:= int; PType =:= bit ->
    if is_atom(PExpr) ->
	    Vn = atom_to_list(PExpr),
	    case maps:find(Vn,Bs#bs.meta) of
		error ->
		    io:format("variable '~s' is not bound\n", [Vn]),
		    error({unbound, Vn});
		{ok,W} ->
		    const_vector(PType,W,SExpr,Bs)
	    end;
       is_integer(PExpr) ->
	    const_vector(PType,PExpr,SExpr,Bs);
       true ->
	    Size = eval_meta(SExpr, Bs),
	    case lookup_or_add_decl(PExpr,PType,Size,Bs) of
		{ok,{PType1,_Arity,Size},Bs1} ->
		    var_vector(PType1,PExpr,Size,Bs1);
		Error ->
		    Error
	    end
    end;
build_({expr,Expr}, Bs) ->
    W = eval_meta(Expr,Bs),
    if W >=0 ->
	    N = varp_math:unsigned_size(W),
	    const_vector(uint,W,N,Bs);
       W < 0 ->
	    N = varp_math:signed_size(W),
	    const_vector(int,W,N,Bs)
    end;
build_({vec,Fs}, Bs) ->
    {Xs,Bs1} = build_list(Fs, Bs),
    Xs1 = join_vector(Xs),
    %% io:format("vec=~p, join=~p\n", [Xs, Xs1]),
    {{bit,length(Xs1),[bit(X)||X <- Xs1]},Bs1};
build_({'alias', L, R}, Bs) ->
    {Y,Bs1} = build__(R, Bs),
    operation_('alias', L, Y, Bs1);
build_({'assign', L, R}, Bs) ->
    {Y,Bs1} = build__(R, Bs),
    operation_('assign', L, Y, Bs1);
build_({'neg',F}, Bs) ->
    {Y,Bs1} = build__(F, Bs),
    operation_('neg', Y, Bs1);
build_({'not',A}, Bs) ->
    {Y,Bs1} = build__(A, Bs),
    operation_('not', Y, Bs1);
build_({'bnot',A}, Bs) ->
    {Y,Bs1} = build__(A, Bs),
    operation_('bnot', Y, Bs1);

build_({bitindex,A,I},Bs) ->
    I1 = eval_meta(I,Bs),
    case A of
	{p,P,Ps} ->  %% check if declared
	    PSym = varp:make_psym(P, Ps),
	    case maps:find(PSym, Bs#bs.decls) of
		error ->
		    variable({index,A,I1}, Bs);
		{ok,{PType,_,PSize}} ->
		    case var_vector(PType,A,PSize,Bs) of
			{{uint,N,Xs},Bs1} -> {select_bool(I1,N,Xs), Bs1};
			{{int,N,Xs},Bs1}  -> {select_bool(I1,N,Xs), Bs1};
			{{bit,N,Xs},Bs1}  -> {select_bool(I1,N,Xs), Bs1};
			{{bool,X},Bs1}    -> {{bool,X},Bs1}
		    end
	    end;
	_ ->
	    case build__(A, Bs) of
		{{uint,N,Xs},Bs1} -> {select_bool(I1,N,Xs), Bs1};
		{{int,N,Xs},Bs1}  -> {select_bool(I1,N,Xs), Bs1};
		{{bit,N,Xs},Bs1}  -> {select_bool(I1,N,Xs), Bs1};
		{{bool,X},Bs1}    -> {{bool,X},Bs1}
                %% X -> {select_bool(I1,1,[X]),Bs}
	    end
    end;

build_({bitrange,A,I,J,S},Bs) ->
    I1 = eval_meta(I,Bs),
    J1 = eval_meta(J,Bs),
    S1 = eval_meta(S,Bs),
    case build__(A, Bs) of
	{{uint,N,Xs}, Bs1} -> {select_range(I1,J1,S1,N,Xs), Bs1};
	{{int,N,Xs}, Bs1}  -> {select_range(I1,J1,S1,N,Xs), Bs1};
	{{bit,N,Xs}, Bs1}  -> {select_range(I1,J1,S1,N,Xs), Bs1};
	{{bool,X}, Bs1}    -> {select_range(I1,J1,S1,1,[X]), Bs1}
    end;

%% Fixme: implement shift for variable argument
build_({'shl',A,K},Bs) ->
    {Y,Bs1} = build__(A,Bs),
    {Z,Bs2} = build__(K,Bs1),
    operation_('shl',Y,Z,Bs2);
build_({'rol',A,K},Bs) ->
    {Y,Bs1} = build__(A,Bs),
    {Z,Bs2} = build__(K,Bs1),
    operation_('rol',Y,Z,Bs2);
build_({'shr',A,K},Bs) ->
    {Y,Bs1} = build__(A,Bs),
    {Z,Bs2} = build__(K,Bs1),
    operation_('shr',Y,Z,Bs2);
build_({'ror',A,K},Bs) ->
    {Y,Bs1} = build__(A,Bs),
    {Z,Bs2} = build__(K,Bs1),
    operation_('ror',Y,Z,Bs2);

build_({cnf,{[],[],_Sections}},Bs) ->
    build__(false, Bs);
build_({cnf,{Vars,_Clauses,_Sections,Cs}},Bs) 
  when is_list(Cs) ->
    %% CNF only works as first formula! variables
    %% must be numerated 1..Vars
    {1,Vars} = varp_nif:add_variables(Bs#bs.vp, Vars),
    %% fixme bind all literals in Ls = TRUE
    lists:foreach(fun(CL) ->
			  use_clause(Bs#bs.vp, CL),
			  try varp_nif:add_clause(Bs#bs.vp, CL) of
			      {false,_I} ->
				  throw(contradiction);
			      false ->
				  throw(contradiction);
			      _ -> ok
			  catch
			      error:_ ->
				  if CL =:= [] -> 
					  error(empty_clause);
				     true ->
					  MV = lists:max([abs(L)||L<-CL]),
					  if MV > Vars ->
						  error({var_out_of_range,MV});
					     true ->
						  error(add_clause)
					  end
				  end
			  end
		  end, Cs),
    %% Bs1 = build_snf(Cs, Bs),
    {{bool,?T}, Bs};
%%    build__({'and',{'ALL',Ls},cnf_to_formula(Cs)},Bs);

build_({snf,{[],[],_Sections}},Bs) ->
    build__(false, Bs);
build_({snf,{_Vars,_Clauses,_Sections,Cs}},Bs) 
  when is_list(Cs) ->
    Bs1 = build_snf(Cs, Bs),
    {{bool,?T}, Bs1};

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
build_({'PARITY',Ys}, Bs) ->
    {Xs,Bs1} = args(Ys,Bs),
    parity(Xs, Bs1);
build_({'ODD',Ys}, Bs) ->
    {Xs,Bs1} = args(Ys,Bs),
    parity(Xs, Bs1);
build_({'EVEN',Ys}, Bs) ->
    {Xs,Bs1} = args(Ys,Bs),
    {Y,Bs2} = parity(Xs, Bs1),
    {negate(Y),Bs2};

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
	    gtk(N-K, N, lists:map(fun(Y) -> negate(Y) end, Ys), Bs1)
    end;
build_({{'LTE',[X1|Qs]},F}, Bs) ->
    K = eval_meta(X1,Bs),
    {Ys,Bs1} = build_quant(F,Qs,Bs),
    if K =:= 0 ->
	    none(Ys,Bs1);
       is_integer(K),K > 0 ->
	    N = length(Ys),
	    gtk(N-K-1, N, lists:map(fun(Y) -> negate(Y) end, Ys), Bs1)
    end;
build_({{'SUM',Qs}, F}, Bs) ->
    {Xs,Bs1} = build_iquant(F,Qs,Bs),
    sum(Xs,Bs1);
build_({{'PROD',Qs}, F}, Bs) ->
    {Xs,Bs1} = build_iquant(F,Qs,Bs),
    prod(Xs,Bs1);
build_({{'PARITY',Qs}, F}, Bs) ->
    {Xs,Bs1} = build_quant(F,Qs,Bs),
    parity(Xs,Bs1);
build_({{'ODD',Qs}, F}, Bs) ->
    {Xs,Bs1} = build_quant(F,Qs,Bs),
    parity(Xs,Bs1);
build_({{'EVEN',Qs}, F}, Bs) ->
    {Xs,Bs1} = build_quant(F,Qs,Bs),
    {Y,Bs2} = parity(Xs,Bs1),
    {negate(Y),Bs2}.

%%
%% Special build of cnf/snf
%% in the cnf case assume that the clause are the
%% literal integers
%% in the snf case the literals are symbols
%%
build_snf([CL|CLs], Bs) ->
    {Xs,Bs1} = args(CL,Bs),
    Ls = [L || {bool,L} <- Xs],
    try add_clause(Bs1,Ls) of
	{false,_I} ->
	    throw(contradiction);
	false ->
	    throw(contradiction);
	_ ->
	    build_snf(CLs, Bs1)
    catch
	error:Reason ->
	    error(Reason)
    end;
build_snf([], Bs) ->
    Bs.

use_clause(Vp, CL) ->
    lists:foreach(fun(Li) -> varp_nif:isused(Vp, abs(Li), true) end, CL).

-ifdef(__UNUSED__).
build_meta(F,X,[Xi|Xs],Acc,Bs) ->
    Bs1 = push_meta(X, Xi, Bs),
    case build__(F,Bs1) of
	{0,Bs2} ->
	    Bs3 = pop_meta(Bs2, Bs#bs.meta),
	    build_meta(F,X,Xs,Acc,Bs3);
	{Vs,Bs2} when is_list(Vs) ->
	    Bs3 = pop_meta(Bs2, Bs#bs.meta),
	    build_meta(F,X,Xs,Vs++Acc,Bs3);
	{V,Bs2} ->
	    Bs3 = pop_meta(Bs2, Bs#bs.meta),
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

build_quant_(F,[{'assign',V,D}|Qs], Bs) ->
    Ds = eval_domain(D, Bs),
    build_quant_domain(F, V, Ds, Qs, Bs);
%% predicate expansion
build_quant_(_F, [{call,{id,_Def},_Args}|_Qs], Bs) ->
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

build_quant_domain(F, V={id,Vn}, [Y|Ys], Xs, Bs) ->
    %% io:format("build Vn=~p Y=~w\n", [Vn,Y]),
    Bs1 = push_meta(Vn, Y, Bs),
    {Zs1,Bs2} = build_quant_(F, Xs, Bs1),
    Bs3 = pop_meta(Bs2, Bs#bs.meta),
    {Zs2,Bs4} = build_quant_domain(F, V, Ys, Xs, Bs3),
    {Zs1++Zs2,Bs4};
%% fixme handle arbitrary vector!
build_quant_domain(F, V={vec,[{id,Vn1},{id,Vn2}]},
		   [{vec,[Y1,Y2]}|Ys], Xs, Bs) ->
    ?dbg("Bind ~s=~w, ~s=~w\n", [Vn1,Y1,Vn2,Y2]),
    Bs1 = push_meta(Vn1, Y1, Bs),
    Bs2 = push_meta(Vn2, Y2, Bs1),
    {Zs1,Bs3} = build_quant_(F, Xs, Bs2),
    Bs4 = pop_meta(Bs3, Bs#bs.meta),
    {Zs2,Bs5} = build_quant_domain(F, V, Ys, Xs, Bs4),
    {Zs1++Zs2,Bs5};
%% fixme handle arbitrary vector! handle set/seqeuences properly
build_quant_domain(F, V={vec,[{id,Vn1},{id,Vn2}]},
		   [[Y1,Y2]|Ys], Xs, Bs) ->
    ?dbg("Bind ~s=~w, ~s=~w\n", [Vn1,Y1,Vn2,Y2]),
    Bs1 = push_meta(Vn1, Y1, Bs),
    Bs2 = push_meta(Vn2, Y2, Bs1),
    {Zs1,Bs3} = build_quant_(F, Xs, Bs2),
    Bs4 = pop_meta(Bs3, Bs#bs.meta),
    {Zs2,Bs5} = build_quant_domain(F, V, Ys, Xs, Bs4),
    {Zs1++Zs2,Bs5};

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

build_iquant_(F,[{assign,V,D}|Qs], Bs) ->
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

build_iquant_domain(F, V={id,Vn}, [Y|Ys], Xs, Bs) ->
    Bs1 = push_meta(Vn, Y, Bs),
    {Zs1,Bs2} = build_iquant_(F, Xs, Bs1),
    Bs3 = pop_meta(Bs2, Bs#bs.meta),
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
eval_domain({range,A,B}, Bs) ->
    A1 = eval_meta(A,Bs),
    B1 = eval_meta(B,Bs),
    if A1 =< B1 -> lists:seq(A1, B1);
       true -> lists:reverse(lists:seq(B1,A1))
    end;
eval_domain({call,{id,"union"},[A,B]}, Bs) ->
    A1 = eval_domain(A,Bs),
    B1 = eval_domain(B,Bs),
    ordsets:union(A1,B1);
eval_domain({call,{id,"subtract"},[A,B]}, Bs) ->
    A1 = eval_domain(A,Bs),
    B1 = eval_domain(B,Bs),
    ordsets:subtract(A1,B1);
eval_domain({call,{id,"intersect"},[A,B]}, Bs) ->
    A1 = eval_domain(A,Bs),
    B1 = eval_domain(B,Bs),
    ordsets:intersection(A1,B1);
eval_domain({call,{id,"product"},[A,B]}, Bs) ->
    A1 = eval_domain(A,Bs),
    B1 = eval_domain(B,Bs),
    [ [Ai,Bi] || Ai <- A1, Bi <- B1 ];
eval_domain({call,{id,"subsets"},[A]}, Bs) ->
    A1 = eval_domain(A,Bs),
    subsets(A1);
eval_domain({call,{id,"subsets"},[K,A]}, Bs) ->
    K1 = eval_meta(K,Bs),
    A1 = eval_domain(A,Bs),
    subsets(K1,A1);
eval_domain({call,{id,"permutations"},[A]}, Bs) ->
    A1 = eval_domain(A,Bs),
    permute(A1);
eval_domain({call,{id,"zip"},[A,B]}, Bs) ->
    A1 = eval_domain(A,Bs),
    B1 = eval_domain(B,Bs),
    [{vec,[Ai,Bi]} || {Ai,Bi} <- lists:zip(A1,B1)];
eval_domain(Expr, Bs) ->
    D = eval_meta(Expr,Bs),
    case D of
	{vec,Elems} -> Elems;   %% assume set notation
	Elems when is_list(Elems) -> Elems;
	_ -> [D]
    end.

eval_meta(V, _Bs) when is_integer(V) -> V;
eval_meta({const,V}, _Bs) -> V;
eval_meta({range,A,B}, Bs) ->
    A1 = eval_meta(A,Bs),
    B1 = eval_meta(B,Bs),
    if A1 =< B1 -> lists:seq(A1, B1);
       true -> lists:reverse(lists:seq(B1,A1))
    end;
eval_meta({id,"true"}, _Bs)  -> true;
eval_meta({id,"false"}, _Bs) -> false;
eval_meta({id,Vn}, Bs) ->
    case maps:find(Vn,Bs#bs.meta) of
	error ->
	    try list_to_existing_atom(Vn) of
		L ->
		    case maps:find(L, Bs#bs.literals) of
			{ok,true} ->
			    L;
			error ->
			    case find_prop_def(L, Bs#bs.defs) of
				false ->
				    error({unbound, Vn});
				Def ->
				    eval_meta(Def, Bs)
			    end
		    end
	    catch
		error:_ ->
		    error({unbound, Vn})
	    end;
	{ok,W} -> 
	    W
    end;
eval_meta({call,F,As},Bs) ->
    case {F,eval_meta_list(As,Bs)} of
	{{id,"factorial"},[N]} -> varp_math:factorial(N);
	{{id,"binom"},[A,B]} -> varp_math:binom(A,B);
	{{id,"sqrt"},[A]}    -> math:sqrt(A);
	{{id,"isqrt"},[A]}   -> imath:isqrt(A);
	{{id,"sqr"},[A]}     -> A*A;
	{{id,"nroot"},[A,N]} -> imath:nroot(A,N);
	{{id,"ln"},[A]}      -> math:log(A);
	{{id,"log"},[A,N]}   -> math:log(A)/math:log(N);
	{{id,"log2"},[A]}    -> math:log(A)/math:log(2);
	{{id,"log10"},[A]}   -> math:log10(A);
	{{id,"ilog2"},[A]}   -> imath:ilog2(A);
	{{id,"isize"},[A]}   -> varp_math:signed_size(A);
	{{id,"usize"},[A]}   -> varp_math:unsigned_size(A);
	{{id,"pi"},[]}       -> math:pi();
	{{id,"e"},[]}        -> math:exp(1);
	{{id,"pow"},[A,B]}   -> 
	    if is_integer(A), is_integer(B) ->
		    varp_math:pow(A,B);
	       true ->
		    math:pow(A,B)
	    end;
	{{id,"sin"},[A]}     -> math:sin(A);
	{{id,"cos"},[A]}     -> math:cos(A);
	{{id,"trunc"},[A]}   -> trunc(A);
	{{id,"round"},[A]}   -> round(A);
	{{id,"abs"},[A]}     -> abs(A);
	{{id,"max"},[A,B]}   -> max(A,B);
	{{id,"min"},[A,B]}   -> min(A,B);
	{{id,"sum"},As}      ->
	    lists:foldl(fun(Ai,Sum) -> eval_meta(Ai,Bs)+Sum end, 0, As);
	%% ordsets
	{{id,"union"},[A,B]}   -> ordsets:union(A,B);
	{{id,"subtract"},[A,B]}   -> ordsets:subtract(A,B);
	{{id,"intersect"},[A,B]}   -> ordsets:intersection(A,B);
	{{id,"product"},[A,B]}   -> [ [Ai,Bi] || Ai <- A, Bi <- B ];
	%% function symbol
	{{id,Func},As1} -> {f,Func,As1}
    end;

eval_meta({Op,A,B},Bs) ->
    case {Op,eval_meta(A,Bs),eval_meta(B,Bs)} of
	{'lt',A1,B1} -> A1 < B1;
	{'lte', A1, B1} -> A1 =< B1;
	{'gt',A1,B1} -> A1 > B1;
	{'gte', A1, B1} -> A1 >= B1;
	{'eq', A1, B1} -> A1 == B1;
	{'neq', A1, B1} -> A1 =/= B1;
	{'and',A1,B1} -> A1 and B1;
	{'or',A1,B1} -> A1 or B1;
	{'band',A1,B1} -> A1 band B1;
	{'bor',A1,B1} -> A1 bor B1;
	{'bxor',A1,B1} -> A1 bxor B1;
	{'shl',A1,B1} -> A1 bsl B1;
	{'shr',A1,B1} -> A1 bsr B1;
	{'add',A1,B1} -> A1+B1;
	{'sub',A1,B1} -> A1-B1;
	{'mul',A1,B1} -> A1*B1;
	{'div',A1,B1} -> A1 div B1;
	{'rem',A1,B1} -> A1 rem B1
    end;

eval_meta({vec,Ls}, Bs) -> %% literal vector
    eval_meta_list(Ls, Bs);
eval_meta({Op,A},Bs) ->
    case {Op,eval_meta(A,Bs)} of
	{'neg',A1} -> -A1;
	{'pos',A1} -> +A1;
	{'bnot',A1} ->  bnot A1;
	{'not',A1} -> not A1
    end.

eval_meta_list(As,Bs) ->
    lists:map(fun(A) -> eval_meta(A,Bs) end, As).

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

permute(List) ->
    permute_(lists:sort(List), []).

permute_([], Acc) ->
    lists:reverse(Acc);
permute_(P, Acc) ->
    permute_(next(P), [P|Acc]).

next(List) ->
    next(lists:reverse(List), []).

next([Aj1 | List=[Aj|_]], Acc) when Aj1 =< Aj ->
    next(List, [Aj1|Acc]);
next([Aj1,Aj|List],Acc) ->
    {A1,[Al|A2]} = lists:splitwith(fun(Ai) -> 
					   Ai =< Aj 
				   end, 
				   lists:reverse([Aj1|Acc])),
    lists:reverse(List)++[Al|A1]++[Aj|A2];
next([_Aj], _Acc) -> [].
    


-define(MAX_PRIO, 0).

priority('mul') -> 10;
priority('div') -> 10;
priority('rem') -> 10;
priority('add') -> 20;
priority('sub') -> 20;
priority('shl') -> 30;
priority('shr') -> 30;
priority('lt') -> 40;
priority('lte') -> 40;
priority('gt') -> 40;
priority('gte') -> 40;
priority('eq') -> 41;
priority('neq') -> 41;
priority('band') -> 43;
priority('bxor') -> 45;
priority('bor') -> 47;
priority('and') -> 50;
priority('or') -> 70.

upriority('neg')   -> 1;
upriority('pos')   -> 1;
upriority('not')   -> 1;
upriority('bnot')   -> 1.

format_op(Op) ->
    T =
	#{  'mul' => "*",'div' => "/",'rem' => "%",'add' => "+",'sub' => "-",
	    'shl' => "<<", 'shr' => "<<",
	    'lt'  => "<", 'lte' => "<=", 'gt' => ">", 'gte' => ">=",
	    'eq' => "==", 'neq' => "!=", 
	    'band' => "&", 'bxor' => "^", 'bor' => "|",
	    'and' => "&&", 'or' => "||",
	    'neg' => "-", 'pos' => "+",
	    'bnot' => "~", 'not' => "!"
	 },
    maps:get(Op, T).


lookup_or_add_decl({p,P,Ps},PType,Size,Bs) ->
    PSym = varp:make_psym(P,Ps),
    Arity = length(Ps),
    case maps:find(PSym,Bs#bs.decls) of
	{ok,Type={PType,Arity,Size}} ->
	    {ok,Type,Bs};
	{ok,Type={_PType1,Arity1,Size1}} ->
	    if Arity =/= Arity1 ->
		    error({arity_mismatch,P});
	       Size =/= Size1 ->
		    error({bitsize_mismatch,P});
	       true ->
		    {ok,Type,Bs}
	    end;
	error ->
	    Type = {PType,Arity,Size},
	    Decls1 = maps:put(PSym, Type, Bs#bs.decls),
	    {ok, Type, Bs#bs { decls = Decls1 }}
    end.


format_meta(Expr) ->
    format_meta_(Expr, ?MAX_PRIO).

format_meta_(I,_P) when is_integer(I) -> integer_to_list(I);
format_meta_(V,_P) when is_atom(V) -> atom_to_list(V);
format_meta_({id,Name},_P) -> Name;
format_meta_({const,V},_P) -> integer_to_list(V);
format_meta_({range,A,B},_P) ->
    if A =:= B -> A;
       true -> [format_meta(A),"..",format_meta(B)]
    end;
format_meta_({call,{id,F},As},_P) ->
    [F,"(", format_meta_list(As), ")"];
format_meta_({Op,A,B},P) ->
    P1 = priority(Op),
    Fa = format_meta_(A,P1),
    Fb = format_meta_(B,P1),
    if P1 > P ->
	    ["(",Fa," ",format_op(Op)," ",Fb,")"];
       true ->
	    [Fa," ",format_op(Op)," ",Fb]
    end;
format_meta_({Op,A},P) ->
    P1 = upriority(Op),
    Fa = format_meta_(A,P1),
    if P1 > P ->
	    ["(",format_op(Op)," ",Fa,")"];
       true ->
	    [format_op(Op)," ",Fa]
    end.

format_meta_list([]) -> [];
format_meta_list([A]) -> [format_meta(A)];
format_meta_list([A|As]) -> [format_meta(A),","|format_meta_list(As)].


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
    {const_vector_(N-1,Type,N,[],Value),Bs}.

const_vector(Type,Value,N) when is_integer(Value), is_integer(N) ->
    const_vector_(N-1,Type,N,[],Value).

const_vector(Type,Value) when is_integer(Value) ->
    N = case Type of
	    uint -> varp_math:unsigned_size(Value);
	    bit  -> varp_math:unsigned_size(Value);
	    int -> varp_math:signed_size(Value)
	end,
    const_vector_(N-1,Type,N,[],Value).

const_vector_(-1,Type,N,Cs,_Value) ->
    {Type,N,lists:reverse(Cs)};
const_vector_(I,Type,N,Cs,Value) ->
    if Value band 1 =:= 1 ->
	    const_vector_(I-1,Type,N,[?T|Cs],Value bsr 1);
       true ->
	    const_vector_(I-1,Type,N,[?F|Cs],Value bsr 1)
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
    
%% generate a variable vector, bits 
%% X[3] X[2] X[1] X[0]  return as little endian [X[0],X[1],X[2],X[3]]
var_vector(Type,V,Size,Bs) ->
    VV = expand_meta(V,Bs),
    Size1 = eval_meta(Size,Bs),
    var_vector_(0,Size1,Type,[],VV,Bs).

var_vector_(Size,Size,Type,Xs,_V,Bs) -> 
    {{Type,Size,lists:reverse(Xs)},Bs};
var_vector_(I,Size,Type,Xs,V,Bs) ->
    {{bool,Xi},Bs1} = variable({Type,V,Size,I},Bs),
    var_vector_(I+1,Size,Type,[Xi|Xs],V,Bs1).

%% Fold operator Op over a variable vector
vfold_op(Bs,_Op,_D,[A]) ->
    {{bool,A},Bs};
vfold_op(Bs,Op,D,[Y|As]) ->
    {Z,Bs1} = vfold_op(Bs,Op,D,As),
    operation_(Op,{bool,Y},Z,Bs1);
vfold_op(Bs,_Op,D,[]) ->
    {D,Bs}.

all(As, Bs) ->
    all_(As, [], Bs).

all_([{bool,?F}|_], _Xs, Bs) ->
    {{bool,?F},Bs};
all_([{bool,?T}|As], Xs, Bs) ->
    all_(As, Xs,Bs);
all_([{bool,A}|As], Xs, Bs) ->
    all_(As, [A|Xs],Bs);
all_([], [], Bs) ->
    {{bool,?T},Bs};    
all_([], [X], Bs) ->
    {{bool,X},Bs};    
all_([], Xs, Bs) ->
    X = add_variable(Bs),
    {{bool,X}, and_gate(Bs,X,Xs)}.


any(As, Bs) ->
    any_(As, [], Bs).

any_([{bool,?T}|_], _Xs, Bs) ->
    {{bool,?T},Bs};
any_([{bool,?F}|As], Xs, Bs) ->
    any_(As, Xs,Bs);
any_([{bool,A}|As], Xs, Bs) ->
    any_(As, [A|Xs],Bs);
any_([], [], Bs) ->
    {{bool,?F},Bs};
any_([], [X], Bs) ->
    {{bool,X},Bs};
any_([], Xs, Bs) ->
    X = add_variable(Bs),
    {{bool,X}, or_gate(Bs,X,Xs)}.

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
    operation_('add', X, Xn, Bs1).

prod([], Bs) ->
    const_vector(uint,1,1,Bs);
prod([X], Bs) ->
    {X, Bs};
prod([X|Xs], Bs) ->
    {Xn,Bs1} = prod(Xs,Bs),
    operation_('mul', X, Xn, Bs1).

parity([], Bs) ->
    {{bool,?F},Bs};
parity([X|Xs],Bs) ->
    parity(X, Xs, Bs).

parity(X, [], Bs) ->
    {X, Bs};
parity(X, [Xi|Xs], Bs) ->
    {Y,Bs1} = operation('xor',X,Xi,Bs),
    parity(Y,Xs,Bs1).

-ifdef(__UNDEFINE__).
%% Not used - size = 5n
%% special version of eqk(1,length(Xs),Xs,Bs)
one_(Xs, Bs) ->
    {{One,_},Bs1} = one__(Xs, Bs),
    {One,Bs1}.

one__([], Bs) -> {{{bool,?F},{bool,?F}},Bs};
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
    {{bool,?F}, Bs};
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
    {{bool,?F}, Bs};
gtk(K,N,Xs,Bs) ->
    {Xs1,Bs1} = sort(Xs,K,Bs),
    {A,B} = lists:split(N-K, Xs1),
    {A1,Bs2} = any(A,Bs1),
    {B1,Bs3} = all(B,Bs2),
    operation_('and', A1, B1, Bs3).

%% negate all input variables
negate({bool,?T}) -> {bool,?F};
negate({bool,?F}) -> {bool,?T};
negate({bool,X}) -> {bool,-X}.

lnot(?T) -> ?F;
lnot(?F) -> ?T;
lnot(X) -> -X.
     
vnot(Xs) ->
    lists:map(fun(X) -> lnot(X) end, Xs).

%% negate "high" bit
vsnot([X]) -> [lnot(X)];
vsnot([X|Xs]) -> [X|vsnot(Xs)];
vsnot([]) -> [].

vextend(int,Xs,N,K) ->
    vset_size(Xs,K,lists:nth(N,Xs));
vextend(uint,Xs,_N,K) ->
    vset_size(Xs,K,?F);
vextend(bit,Xs,_N,K) ->
    vset_size(Xs,K,?F);
vextend(bool,Xs,1,K) ->
    vset_size(Xs,K,?F).

%%
%% normalize by remove multiple sign bits (MSB)
%% int:
%%   xyzF...F => xyzF
%%   xyzT...T => xyzT
%%   xyzB...B => xyzB
%% uint: (only remove zeros)
%%   xyzF...F => xyz
%%
normalize(Type,Cx) ->
    normalize(Type,length(Cx),Cx).

normalize(uint,Cn,Cx) ->
    u_norm(Cn,lists:reverse(Cx));
normalize(int,Cn,Cx) ->
    RCx = lists:reverse(Cx),
    i_norm(Cn,hd(RCx),RCx);
normalize(Ct,Cn,Cx) ->
    {Ct,Cn,Cx}.

u_norm(N,[?F|Cx=[_|_]]) -> u_norm(N-1,Cx);
u_norm(N,Cx) -> {uint,N,lists:reverse(Cx)}.

i_norm(N,S,[S|Cx=[S|_]]) -> i_norm(N-1,S,Cx);
i_norm(N,_S,Cx) -> {int,N,lists:reverse(Cx)}.

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
varg({bool,X}) -> {uint,1,[X]}.

iarg(A={int,_An,_Ax}) -> A;
iarg({uint,An,Ax}) -> {int,An+1,Ax++[?F]};
iarg({bit,An,Ax}) -> {int,An,Ax};
iarg({bool,X}) -> {int,2,[X,?F]}.

uarg(A={uint,_An,_Ax}) -> A;
uarg({int,An,Ax}) -> {uint,An,Ax};  %% cast!!
uarg({bit,An,Ax}) -> {uint,An,Ax};
uarg({bool,X}) -> {uint,1,[X]}.

%% convert A into destination type
-spec xarg(Type::ptype(), Src::pbits()) -> Dst::pbits().
xarg(int, A) -> iarg(A);
xarg(uint,A) -> uarg(A);
 %% mix_type should only return bool when boolxbool
xarg(bool,A={bool,_}) -> A;
xarg(bit,{bool,X}) -> {bit,1,[X]};
xarg(bit,A={bit,_,_}) -> A.

vconst({uint,_,Xs}) -> vunsigned(Xs);
vconst({int,_,Xs}) -> vsigned(Xs);
vconst({bit,_,Xs}) -> vunsigned(Xs);
vconst({bool,X}) -> vunsigned([X]).

bit({uint,1,[X]}) -> X;
bit({bit,1,[X]}) -> X;
bit({bool,X}) -> X.

%% convert a "vector" with boolean constants to a signed number
%% return false if not all elements are constants
vsigned(Xs) ->
    N = (1 bsl (length(Xs)-1)),
    R = vunsigned(Xs),
    if R =:= false -> false;
       R < N -> R;
       true -> R - 2*N
    end.

%% convert a "vector" with boolean constants to a unsigned number
%% return false if not all elements are constants
vunsigned(Xs) ->
    vunsigned_(lists:reverse(Xs), 0).

vunsigned_([?T|Xs],N)  -> vunsigned_(Xs,(N bsl 1)+1);
vunsigned_([?F|Xs],N) -> vunsigned_(Xs,(N bsl 1)+0);
vunsigned_([_|_],_N) -> false;
vunsigned_([],N) -> N.

%% set vector size to N  extend (with FALSE) at end / cut at end
vset_size(Xs,N) ->
    vset_size(Xs,N,?F).

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
    {bool,?F}.

%% X[0:4] = {X[0],X[1],X[2],X[3],X[4]}
%% X[4:0] = {X[4],X[3],X[2],X[1],X[0]}
%% X[5:5] = {X[5]}
%% X[0:-1] = {}
 
select_range(I,J,Step,N,Xs) ->
    M = max(max(I,J)+1,N),
    %% FIXME? Maybe error on overflow, now we just extend Xs
    Xs1 = list_to_tuple(vset_size(Xs, M)),
    Range = lists:seq(I,J,Step),
    {uint,length(Range), select_range_(Range,Xs1)}.

select_range_([I|Is],Xs) ->
    [element(I+1,Xs) | select_range_(Is, Xs)];
select_range_([],_Xs) ->
    [].

%% given a list of mixed boolean and vector expression
%% return a list of just booleans (expand vectors)
join_vector([X|Xs]) ->
    case X of
	{bool,_} -> [X | join_vector(Xs)];
	{bit,_N,Ys} -> [{bool,Y}||Y<-Ys] ++ join_vector(Xs);
	{int,_N,Ys} -> [{bool,Y}||Y<-Ys] ++ join_vector(Xs);
	{uint,_N,Ys} -> [{bool,Y}||Y<-Ys] ++ join_vector(Xs)
    end;
join_vector([]) ->
    [].

build_list(Fs, Bs) ->
    build_list_(Fs, [], Bs).
    
build_list_([F|Fs],Acc,Bs) ->
    {X,Bs1} = build__(F,Bs),
    build_list_(Fs,[X|Acc],Bs1);
build_list_([],Acc,Bs) ->
    {lists:reverse(Acc),Bs}.


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
    {{bool,lnot(Y)},Bs};
operation('bnot',Y={bool,_Y},Bs) ->
    operation('not',Y,Bs);
operation('bnot', {Type,N,Ys}, Bs) when ?is_vec_type(Type) ->
    Ys1 = vnot(Ys),
    {{Type,N,Ys1}, Bs};

operation('neg', A, Bs) ->
    {_At,An,Ax} = varg(A),
    case vconst(A) of
	false ->
	    Ax1 = vnot(Ax),
	    Zs1 = vset_size([?T],An),
	    {[{bool,_Co}|_],Xs,Bs1} = vadd(Ax1,Zs1,Bs),
	    {{int,An,Xs},Bs1};
	Av ->
	    Av1 = -Av,
	    An1 = varp_math:signed_size(Av1),
	    {const_vector_(An1-1,int,An1,[],Av1),Bs}
    end;

operation('abs', A={int,N,Ys}, Bs) ->
    SignBit = sign_bit(A),
    {{_,_,Zs},Bs1} = operation_('neg',A,Bs),
    {Xs,Bs2} = vite(SignBit, Zs, Ys, Bs1),
    {{int,N,Xs},Bs2};
operation('abs', A={uint,_N,_Ys}, Bs) ->
    {A,Bs}.
    
%%
%% Binary operator
%%
operation('and',{bool,?T},{bool,?T}, Bs) ->
    {{bool,?T},Bs};
operation('and',{bool,?F},{bool,_Z}, Bs) ->
    {{bool,?F},Bs};
operation('and',{bool,_Y},{bool,?F}, Bs) ->
    {{bool,?F},Bs};
operation('and',{bool,?T},{bool,Z}, Bs) ->
    {{bool,Z},Bs};
operation('and',{bool,Y},{bool,?T}, Bs) ->
    {{bool,Y},Bs};
operation('and',{bool,Y},{bool,Z}, Bs) ->
    X = add_variable(Bs),
    {{bool,X},and_gate(Bs,X,[Y,Z])};

operation('band',A,B,Bs) ->
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

operation('or',{bool,?F},{bool,?F}, Bs) -> {{bool,?F},Bs};
operation('or',{bool,?T},{bool,_Z}, Bs) -> {{bool,?T},Bs};
operation('or',{bool,_Y},{bool,?T}, Bs) -> {{bool,?T},Bs};
operation('or',{bool,?F},{bool,Z}, Bs) -> {{bool,Z},Bs};
operation('or',{bool,Y},{bool,?F}, Bs) -> {{bool,Y},Bs};
operation('or',{bool,Y},{bool,Z}, Bs) ->
    X = add_variable(Bs),
    {{bool,X},or_gate(Bs,X,[Y,Z])};

operation('bor',A,B,Bs) ->
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

operation('imp',{bool,?F},{bool,?T}, Bs) ->  {{bool,?T},Bs};
operation('imp',{bool,?F},{bool,?F}, Bs) -> {{bool,?T},Bs};
operation('imp',{bool,?T},{bool,?T}, Bs) ->   {{bool,?T},Bs};
operation('imp',{bool,?T},{bool,?F}, Bs) ->  {{bool,?F},Bs};
operation('imp',{bool,Y},{bool,Z}, Bs) ->
    X = add_variable(Bs),
    {{bool,X},or_gate(Bs,X,[lnot(Y),Z])};
operation('imp',A,B,Bs) ->
    {An,Bs1} = operation_('~',A,Bs),
    operation_('|',An,B,Bs1);

operation('equ',{bool,?T},{bool,?F},Bs) -> {{bool,?F},Bs};    
operation('equ',{bool,?F},{bool,?T},Bs) -> {{bool,?F},Bs};
operation('equ',{bool,?T},{bool,?T},Bs) ->  {{bool,?T},Bs};
operation('equ',{bool,?F},{bool,?F},Bs) -> {{bool,?T},Bs};
operation('equ',{bool,?T},{bool,Z},Bs) -> {{bool,Z},Bs};
operation('equ',{bool,Y},{bool,?T},Bs) -> {{bool,Y},Bs};
operation('equ',{bool,?F},{bool,Z},Bs) -> {{bool,lnot(Z)},Bs};
operation('equ',{bool,Y},{bool,?F},Bs) -> {{bool,lnot(Y)},Bs};
operation('equ',{bool,Y},{bool,Z},Bs) ->
    X = add_variable(Bs),
    {{bool,X},xor_gate(Bs,X,[lnot(Y),Z])};

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

operation('xor',{bool,?T},{bool,?T}, Bs) -> {{bool,?F},Bs};
operation('xor',{bool,?F},{bool,?F}, Bs) -> {{bool,?F},Bs};
operation('xor',{bool,?F},{bool,?T}, Bs) -> {{bool,?T},Bs};
operation('xor',{bool,?T},{bool,?F}, Bs) -> {{bool,?T},Bs};
operation('xor',{bool,?F},{bool,Z}, Bs) -> {{bool,Z},Bs};
operation('xor',{bool,?T},{bool,Z}, Bs) -> {{bool,-Z},Bs};
operation('xor',{bool,Z},{bool,?F}, Bs) -> {{bool,Z},Bs};
operation('xor',{bool,Z},{bool,?T}, Bs) -> {{bool,-Z},Bs};
operation('xor',{bool,Y},{bool,Z}, Bs) ->
    X = add_variable(Bs),
    {{bool,X},xor_gate(Bs,X,[Y,Z])};

operation('bxor',A,B,Bs) ->
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

%% FIXME:
%% A < B  <=>  A - B < 0
operation('lt',{bool,Y},{bool,Z},Bs) ->  %% Y < Z
    operation_('and', negate({bool,Y}),{bool,Z}, Bs);
operation('lt',{uint,An,Ax},{uint,Bn,Bx},Bs) ->
    Cn = erlang:max(An,Bn),
    Ax1 = vextend(uint,Ax,An,Cn),
    Bx1 = vextend(uint,Bx,Bn,Cn),
    vless(Ax1,Bx1,Bs);
operation('lt',A,B,Bs) ->
    {_At,An,Ax} = iarg(A),
    {_Bt,Bn,Bx} = iarg(B),
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
    {L,Bs4} = operation_('lt',{bool,Bk},{bool,Ak},Bs3),
    any([A1,L],Bs4);
operation('gt',{bool,Y},{bool,Z},Bs) ->  %% Y > Z
    operation_('and', {bool,Y}, negate({bool,Z}), Bs);
operation('gt',Y,Z,Bs) ->
    operation_('lt', Z, Y, Bs);
operation('lte',Y,Z,Bs) ->
    {C,Bs1} = operation_('lt', Z, Y, Bs),
    {negate(C),Bs1};
operation('gte',Y,Z,Bs) ->
    operation_('lte',Z,Y,Bs);

operation('neq',A={bool,_},B={bool,_},Bs) ->
    operation_('xor',A,B,Bs);
operation('neq',Y,Z,Bs) ->
    {C,Bs1} = operation_('eq', Y, Z, Bs),
    {negate(C),Bs1};

operation('eq',A={bool,_},B={bool,_},Bs) ->
    operation_('equ',A,B,Bs);
operation('eq',{uint,An,Ax},{uint,Bn,Bx},Bs) ->
    Cn = erlang:max(An,Bn),
    Ax1 = vextend(uint,Ax,An,Cn),
    Bx1 = vextend(uint,Bx,Bn,Cn),    
    veq(Ax1,Bx1,Bs);
operation('eq',A,B,Bs) ->
    {At,An,Ax} = iarg(A),
    {Bt,Bn,Bx} = iarg(B),
    Cn = erlang:max(An,Bn),
    Ax1 = vextend(At,Ax,An,Cn),
    Bx1 = vextend(Bt,Bx,Bn,Cn),
%%    io:format("~w == ~w : ~w == ~w\n",
%%	      [A, B, {At,length(Ax1),Ax1}, {Bt,length(Bx1),Bx1}]),
    veq(Ax1,Bx1,Bs);

%%
%% Alias operation
%%
operation('alias',V,X={T,Size,Xs},Bs) when ?is_vec_type(T) ->
    {X, alias_vector(Bs,T,V,Size,Xs)};
operation('alias',V,X={bool,Xb},Bs) ->
    {X, alias(V,Xb,Bs)};

%% operator '=' is kind of assignment but really a 
%% equality test and check of overflow bits
operation('assign',R,L,Bs) ->
    %% FIXME: same as '==' but check overflow / truncate 
    operation('equ',R,L,Bs);

operation('shl',A,B,Bs) ->
    {At,An,Ax} = varg(A),
    K = vconst(B),
    Ax1 = if K =:= false ->
		  error({shift_not_constant, B});
	     K >=0 ->
		  vshift_left(K,Ax);
	     At =:= int ->
		  vshift_right(-K,An,Ax);
	     true ->
		  vushift_right(-K,An,Ax)
	  end,
    Shift = normalize(At,Ax1),
    {Shift, Bs};

operation('shr',A,B,Bs) ->
    {At,An,Ax} = varg(A),
    K = vconst(B),
    Ax1 = if K =:= false ->
		  error({shift_not_constant, B});
	     K >=0, At =:= int ->
		  vshift_right(K,An,Ax);
	     K >= 0 ->
		  vushift_right(K,An,Ax);
	     K < 0 ->
		  vshift_left(-K,Ax)
	  end,
    Shift = normalize(At,Ax1),
    {Shift, Bs};
	    
%% rotate left
operation('rol',A,B,Bs) ->
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
operation('ror',A,B,Bs) ->
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


operation('add',A,B,Bs) ->
    Ct = case mix_type(A,B) of
	     bool -> uint;
	     Ct0 -> Ct0
	 end,
    {At,An,Ax} = xarg(Ct,A),
    {Bt,Bn,Bx} = xarg(Ct,B),
    Cn = erlang:max(An,Bn)+1,
    Ax1 = vextend(At,Ax,An,Cn),
    Bx1 = vextend(Bt,Bx,Bn,Cn),
    {Cs,Cx,Bs1} = vadd(Ax1,Bx1,Bs),
    [Ci,Cj|_] = Cs,
    %% io:format("plus: ~w,~w, carry=~w, Xs=~w\n", [At,Bt,Ci,Cx]),
    Bs2 = set_status_(Ci,maps:get(carry,Bs1#bs.option),Bs1),
    Bs3 = set_overflow_(Ct,Ci,Cj,maps:get(overflow,Bs1#bs.option),Bs2),
    Sum = normalize(Ct,length(Cx),Cx),
%%    io:format("~w + ~w : ~w + ~w = ~w\n",
%%	      [A, B, {At,length(Ax1),Ax1}, {Bt,length(Bx1),Bx1}, Sum]),
    {Sum,Bs3};

operation('sub',A,B,Bs) ->
    Ct = case mix_type(A,B) of
	     bool -> int;
	     uint -> int;
	     T -> T
	 end,
    {At,An,Ax} = xarg(Ct,A),
    {Bt,Bn,Bx} = xarg(Ct,B),
    Cn = erlang:max(An,Bn)+1,
    Ax1 = vextend(At,Ax,An,Cn),
    Bx1 = vextend(Bt,Bx,Bn,Cn),
    {Cs,Cx,Bs1} = vsub(Ax1,Bx1,Bs),
    [Ci,Cj|_] = Cs,
    Bs2 = set_status_(negate(Ci),maps:get(borrow,Bs1#bs.option),Bs1),
    Bs3 = set_overflow_(Ct,Ci,Cj,maps:get(overflow,Bs1#bs.option),Bs2),
    Diff = normalize(Ct,length(Cx),Cx),
    {Diff,Bs3};

operation('mul',A,B,Bs) ->
    Ct = case mix_type(A,B) of
	     bool -> uint;
	     Ct0 -> Ct0
	 end,
    {At,An,Ax} = xarg(Ct,A),
    {Bt,Bn,Bx} = xarg(Ct,B),
    {Cx,Bs1} =
	if Ct =:= int ->
		Cn0 = erlang:max(An,Bn),
		Ax1 = vextend(At,Ax,An,Cn0),
		Bx1 = vextend(Bt,Bx,Bn,Cn0),
		%% io:format("Ax1=~w, Bx1=~w\n", [Ax1,Bx1]),
		vsmul(Ax1, Bx1, Bs);
	   An < Bn ->
		vmul(Ax,Bx,Bs);
	   true ->
		vmul(Bx,Ax,Bs)
	end,
    Cn = length(Cx),
    %% io:format("Cx=~w\n", [Cx]),
    Prod = normalize(Ct,Cn,Cx),
    %% io:format("Prod=~w\n", [Prod]),
    {Prod,Bs1};

%% DivZero  coould be used to generate a Exception output
%% Signed?
operation('div',Y,{uint,Zm,Zs},Bs) ->
    {Yt,Yn,Ys} = varg(Y),
    K = erlang:max(Yn,Zm),
    Ys1 = vextend(Yt,Ys,Yn,K),
    Zs1 = vextend(uint,Zs,Zm,K),
    {Qs,_Rs,DivZero,Bs1} = vdivrem(Ys1,Zs1,Bs),
    Bs2 = set_status_(DivZero,maps:get(divz,Bs1#bs.option),Bs1),
    Div = normalize(Yt,K,Qs),
    {Div,Bs2};

%% DivZero  coould be used to generate a Exception output
%% Signed?
operation('rem',{uint,N,Ys},{uint,M,Zs},Bs) ->
    K = erlang:max(N,M),
    Ys1 = vextend(uint,Ys,N,K),
    Zs1 = vextend(uint,Zs,M,K),
    {_Qs,Rs,DivZero,Bs1} = vdivrem(Ys1,Zs1,Bs), %% fixme vrem! 
    Bs2 = set_status_(DivZero,maps:get(divz,Bs1#bs.option),Bs1),
    {{uint,K,Rs},Bs2};

operation('min',Y={bool,_Y},Z={bool,_Z},Bs) ->
    operation_('and',Y,Z,Bs);
operation('min',A,B,Bs) ->
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
set_status_({bool,Ci}, false, Bs) ->    %% never generate carry
    xor_gate(Bs,?F,[Ci,?F]);
set_status_({bool,Ci}, true, Bs) ->     %% always generate carry
    xor_gate(Bs,?F,[Ci,?T]);
set_status_({bool,_Ci}, ignore, Bs) ->  %% allow carry overflow
    Bs.

%% Handle carry (Is it wise to backtrack over a Carry variable?)
set_overflow_(int,{bool,Ci},{bool,Cj}, false, Bs) -> %% never generate overflow
    xor_gate(Bs,?F,[Ci,Cj]);
set_overflow_(int,{bool,Ci},{bool,Cj}, true, Bs) -> %% always generate overflow
    xor_gate(Bs,?T,[Ci,Cj]);
set_overflow_(_,{bool,Ci},{bool,_Cj},false,Bs) -> %% never generate overflow
    xor_gate(Bs,?F,[Ci,?F]);
set_overflow_(_,{bool,Ci},{bool,_Cj},true,Bs) -> %% never generate overflow
    xor_gate(Bs,?F,[Ci,?T]);
set_overflow_(_,{bool,_Ci}, {bool,_Cj}, ignore, Bs) ->  %% allow carry overflow
    Bs.

%% sign bit as boolean
sign_bit({Type,N,Xs}) when ?is_int_type(Type) ->
    {bool,lists:nth(N,Xs)}.

%% Mix integer type (cast?)
mix_type({At,_,_},{Bt,_,_}) -> mix_type(At,Bt);
mix_type({At,_,_},{Bt,_}) -> mix_type(At,Bt);
mix_type({At,_},{Bt,_,_}) -> mix_type(At,Bt);
mix_type({At,_},{Bt,_}) -> mix_type(At,Bt);
mix_type(T,T) -> T;
mix_type(uint,int)  -> int;
mix_type(uint,bit)  -> uint;
mix_type(uint,bool) -> uint;

mix_type(int,uint)  -> int;
mix_type(int,bit)   -> int;
mix_type(int,bool)  -> int;

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
    vmul(Ys, Zs, 1, Xs++[?F], Bs1).

vmul([Y|Ys], Zs, I, Xs, Bs) ->
    {YZs,Bs1} = vmap_opx('and',Zs,Y,Bs),
    YZs1 = lists:duplicate(I,?F)++YZs,
    {[{bool,Co}|_],Xs1,Bs2} = vadd(Xs,YZs1,Bs1),
    vmul(Ys, Zs, I+1, Xs1++[Co], Bs2);
vmul([], _Zs, _I, Xs, Bs) ->
    {Xs, Bs}.

%%
%% Signed multiply
%%
vsmul([Y|Ys], Zs, Bs) ->
    {YZs,Bs1} = vmap_opx('and',Zs,Y,Bs),
    Xs1 = vsnot(YZs)++[?T],
    vsmul(Ys, Zs, 1, Xs1, Bs1).

vsmul([Y], Zs, I, Xs, Bs) ->
    {YZs,Bs1} = vmap_opx('and',Zs,Y,Bs),
    YZs1 = lists:duplicate(I,?F)++vsnot(vnot(YZs))++[?T],
    {[{bool,_Co}|_],Xs1,Bs2} = vadd(Xs++[?F],YZs1,Bs1),
    %%{Xs1++[Co], Bs2};
    {Xs1, Bs2};
vsmul([Y|Ys], Zs, I, Xs, Bs) ->
    {YZs,Bs1} = vmap_opx('and',Zs,Y,Bs),
    YZs1 = lists:duplicate(I,?F)++vsnot(YZs),
    {[{bool,Co}|_],Xs1,Bs2} = vadd(Xs,YZs1,Bs1),
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
%%    io:format("vdivrem: ~w / ~w = q=~w, r=~w\n", [X,Y,Q,R]),
    {Q,R,DivZero,Bs2}.

vdivrem(X, _Y, R, _N, 0, Bs) ->
    {X, R, Bs};
vdivrem(X, Y, R, N, I, Bs) ->
    %% R << 1
    [R0|Rs] = vshift_left(1, N, R),      
    Xn = lists:last(X),
    %% if (HIGHBIT(X)) R |= 1;
    {{bool,R00},Bs1} = ite({bool,Xn}, {bool,?T}, {bool,R0},Bs),
    R1 = [R00|Rs],
    %% X <<= 1;
    [_X10|X1] = vshift_left(1, N, X),
    %% if (R < Y)  X &= ~1; else X |= 1;
    {{bool,Lt},Bs2} = vless(R1, Y, Bs1),
    X2 = [lnot(Lt)|X1],
    %% R = R - Y
    {[BorrowNot|_],R2,Bs3} = vsub(R1, Y, Bs2),
    Bs4 = set_status_(negate(BorrowNot),ignore,Bs3),
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
    {{bool,R00},Bs1} = ite({bool,Xn}, {bool,?T}, {bool,R0},Bs),
    R1 = [R00|Rs],
    {{bool,Lt},Bs2} = vless(R1, Y, Bs1),
    %% R = R - Y
    {[BorrowNot|_],R2,Bs3} = vsub(R1, Y, Bs2),
    Bs4 = set_status_(negate(BorrowNot),ignore,Bs3),
    %% if (R < Y) R=R; R = R - Y
    {R3,Bs5} = vite({bool,Lt}, R1, R2, Bs4),
    vrem(tl(X), Y, R3, N, I-1, Bs5).
-endif.

%%
%% Subtraction 
%%
vsub(Ys, Zs, Bs) ->
    Zs1 = vnot(Zs),
    case ?GETOPT_BS(Bs,adder) of
	plain ->
	    vadd_plain(Ys,Zs1,?T,Bs);
	fast ->
	    vadd_fast(Ys,Zs1,?T,Bs)
    end.

%%
%% Adder circuit
%%
vadd(Ys,Zs,Bs) ->
%%    io:format("vadd: ~w/~w ~w/~w\n", [Ys,length(Ys),Zs,length(Zs)]),
    case ?GETOPT_BS(Bs,adder) of
	plain ->
	    vadd_plain(Ys,Zs,?F,Bs);
	fast ->
	    vadd_fast(Ys,Zs,?F,Bs)
    end.

vadd_plain(Ys,Zs,C0,Bs) ->
    vadd_plain_(Ys,Zs,[],[{bool,C0}],Bs).

vadd_plain_([?F|Ys],[?F|Zs],Xs,Cs=[{bool,Ci}|_],Bs) ->
    vadd_plain_(Ys,Zs,[Ci|Xs],[{bool,?F}|Cs],Bs);
vadd_plain_([?F|Ys],[Z|Zs],Xs,Cs=[Ci|_],Bs) ->
    {{bool,X},Co,Bs1} = half_adder({bool,Z},Ci,Bs),
    vadd_plain_(Ys,Zs,[X|Xs],[Co|Cs],Bs1);
vadd_plain_([Y|Ys],[?F|Zs],Xs,Cs=[Ci|_],Bs) ->
    {{bool,X},Co,Bs1} = half_adder({bool,Y},Ci,Bs),
    vadd_plain_(Ys,Zs,[X|Xs],[Co|Cs],Bs1);
vadd_plain_([Y|Ys],[Z|Zs],Xs,Cs=[Ci|_],Bs) ->
    {{bool,X},Co,Bs1} = full_adder({bool,Y},{bool,Z},Ci,Bs),
    vadd_plain_(Ys,Zs,[X|Xs],[Co|Cs],Bs1);
vadd_plain_([],[],Xs,Cs,Bs) -> 
    {Cs,lists:reverse(Xs),Bs}.

%% 
%% Generate carry look-ahead
%% then feed them into half address also using Gs
%% G(i) = Y(i)Z(i)
%% P(i) = Y(i)+Z(i)
%% C(0) = FALSE | TRUE
%% C(1) = G(0) + P(0)C(0)
%% C(2) = G(1) + P(1)G(0) + P(1)P(0)C(0)
%% C(3) = G(2) + P(2)G(1) + P(2)P(1)G(0) + P(2)P(1)P(0)C(0)
%% C(4) = G(3) + P(3)G(2) + P(3)P(2)G(1) + P(3)P(2)P(1)G(0) + P(2)P(1)P(0)C(0)
%% C(i+1) = G(i) + (P(i)*(Ci))
%% S(0) = Y(0) xor Z(0)
%% S(1) = Y(1) xor Z(1) xor C(1)
%% S(i) = Y(i) xor Z(i) xor C(i)
%%
vadd_fast(Ys,Zs,C0,Bs) ->
    %% io:format("vadd_fast: ~w, ~w\n", [Ys,Zs]),
    {Gs,Bs1} = map_op('and',Ys,Zs,Bs),
    {Ps,Bs2} = map_op('or',Ys,Zs,Bs1),
    {Cs,Bs3} = carry_lookahead(Gs,Ps,{bool,C0},Bs2),
    vadd_fast_sum(Ys,Zs,Cs,Bs3).

vadd_fast_sum(Ys,Zs,Cs,Bs) ->
    vadd_fast_sum_(Ys,Zs,Cs,[],[],Bs).

vadd_fast_sum_([Yi|Ys],[Zi|Zs],[Ci|Cs],Sum,Ca,Bs) ->
    {X1,Bs1} = operation('xor',{bool,Yi},{bool,Zi},Bs),
    {{bool,X2},Bs2} = operation('xor',X1,Ci,Bs1),
    vadd_fast_sum_(Ys,Zs,Cs,[X2|Sum],[Ci|Ca],Bs2);
vadd_fast_sum_([],[],[Co],Sum,Ca,Bs) ->
    {[Co|Ca],lists:reverse(Sum),Bs}.

carry_lookahead(Gs,Ps,C0,Bs) ->
    carry_lookahead_(Gs,Ps,1,length(Gs)+1,[C0],C0,Bs).

carry_lookahead_(_Gs,_Ps,I,I,Cs,_C0,Bs) ->
    {lists:reverse(Cs),Bs};
carry_lookahead_(Gs,Ps,I,N,Cs,C0,Bs) ->
    G = lists:sublist(Gs,I),      %% [G(0),G(1),..G(i)]
    P = lists:sublist(Ps,I),      %% [P(0),P(1),..P(i)]
    {X0,Bs1} = all([C0|P],Bs),
    {Ci,Bs1} = carry_ci(G,tl(P),[X0],Bs),
    carry_lookahead_(Gs,Ps,I+1,N,[Ci|Cs],C0,Bs1).

carry_ci([Gn],[],Xs,Bs) ->
    any([Gn|Xs], Bs);
carry_ci([Gi|Gs],P,Xs,Bs) ->
    {Xi,Bs1} = all([Gi|P],Bs),
    carry_ci(Gs,tl(P),[Xi|Xs],Bs1).

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
ite({bool,?T},T,_E, Bs) ->
    {T,Bs};
ite({bool,?F},_T,E, Bs) -> 
    {E,Bs};
ite(_I,X,X, Bs) ->
    {X,Bs};
%% (I & false) | (~I & E) == ~I & E
ite(I,{bool,?F},E, Bs) ->
    operation('and',negate(I),E,Bs);
%% (I & T) | (~I & false) == I & T
ite(I,T,{bool,?F}, Bs) ->
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
    {lists:reverse(Xs),Bs}.

%% conditional vector Ys or variable value Z
-ifdef(__UNUSED__).
vitex(I,Ys,Z,Bs) when is_list(Ys), is_integer(Z) ->
    vitex_(I,Ys,Z,[],Bs).
    
vitex_(I,[Y|Ys],Z,Xs,Bs) ->
    {{bool,X}, Bs1} = ite(I,{bool,Y},{bool,Z},Bs),
    vitex_(I,Ys,Z,[X|Xs],Bs1);
vitex_(_I,[],_Z,Xs,Bs) ->
    {lists:reverse(Xs),Bs}.
-endif.

%% 
%% shift_left 2 [X0,X1,X2,X3,X4,X5,X6,X7]  ==
%%              [FALSE,FALSE,X0,X1,X2,X3,X4,X5,X6,X7]

vshift_left(K,Xs) when K >= 0 ->
    lists:duplicate(K,?F) ++ Xs.

%% shift_left 2 [X0,X1,X2,X3,X4,X5,X6,X7]  ==
%%              [FALSE,FALSE,X0,X1,X2,X3,X4,X5]
vshift_left(K,N,Xs) when K >= 0 ->
    K1 = erlang:min(K,N),
    lists:duplicate(K1,?F) ++ lists:sublist(Xs,1,N-K1).

%% unsigned shift right (ignoring sign bit) 
%% shift_right 2 [X0,X1,X2,X3,X4,X5,X6,X7]  ==
%%               [X2,X3,X4,X5,X6,X7,FALSE,FALSE]

%% vushift_right(K,Xs) when K >= 0 ->
%%     vushift_right(K,length(Xs),Xs).

vushift_right(K,N,Xs) when K >= 0 ->
    K1 = erlang:min(K,N),
    lists:sublist(Xs, K1+1, N) ++ lists:duplicate(K1,?F).

%% signed shift right (shifing in sign bit)
%% shift_right 2 [X0,X1,X2,X3,X4,X5,X6,X7]  ==
%%               [X2,X3,X4,X5,X6,X7,X7,X7]

%% vshift_right(K,Xs) when K >= 0 ->
%%     vshift_right(K,length(Xs),Xs).

vshift_right(K,N,Xs) when K >= 0 ->
    K1 = erlang:min(K,N),
    SignBit = lists:nth(N, Xs),
    lists:sublist(Xs, K1+1, N) ++ lists:duplicate(K1,SignBit).

%% Compare equal
veq(Ys, Zs, Bs) ->
    {Xs,Bs1} = vmap_op('equ',Ys,Zs,Bs),
    vfold_op(Bs1,'and',{bool,?T},Xs).
    
%% Compare less
vless([Y],[Z],Bs) ->
    operation('lt',{bool,Y},{bool,Z},Bs);
vless([Y|Ys],[Z|Zs],Bs) ->
    {Lv,Ev,Bs1} = vlteq(Ys,Zs,Bs),
    {L1,Bs2} = operation('lt',{bool,Y},{bool,Z},Bs1),
    {L2,Bs3} = operation('and',Ev,L1,Bs2),
    operation('or',L2,Lv,Bs3).

vlteq([Y],[Z],Bs) ->
    {Lt,Bs1} = operation('lt', {bool,Y},{bool,Z},Bs),
    {Eq,Bs2} = operation('equ',{bool,Y},{bool,Z},Bs1),
    {Lt,Eq,Bs2};
vlteq([Y|Ys],[Z|Zs],Bs) ->
    {Lv,Ev,Bs1} = vlteq(Ys,Zs,Bs),
    {L1,Bs2} = operation('lt',{bool,Y},{bool,Z},Bs1),
    {E1,Bs3} = operation('equ',{bool,Y},{bool,Z},Bs2),
    {L2,Bs4} = operation('and',Ev,L1,Bs3),
    {Lv2,Bs5} = operation('or',L2,Lv,Bs4),
    {Ev2,Bs6} = operation('and',Ev,E1,Bs5),
    {Lv2,Ev2,Bs6}.

%% same as vmap_op but over list of bool instead of integer vars
map_op(Op,Ys,Zs,Bs) ->
    map_op(Op,Ys,Zs,[],Bs).

map_op(Op,[Y|Ys],[Z|Zs],Xs,Bs) ->
    {X,Bs1} = operation(Op,{bool,Y},{bool,Z},Bs),
    map_op(Op,Ys,Zs,[X|Xs],Bs1);
map_op(_Op,[],[],Xs,Bs) ->
    {lists:reverse(Xs),Bs}.

%% Apply same operator on two vectors
vmap_op(Op,Ys,Zs,Bs) ->
    vmap_op(Op,Ys,Zs,[],Bs).

vmap_op(Op,[Y|Ys],[Z|Zs],Xs,Bs) ->
    {{bool,X},Bs1} = operation(Op,{bool,Y},{bool,Z},Bs),
    vmap_op(Op,Ys,Zs,[X|Xs],Bs1);
vmap_op(_Op,[],[],Xs,Bs) ->
    {lists:reverse(Xs),Bs}.

%% Apply same operator on one vector and one variable
vmap_opx(Op,Ys,Z,Bs) ->
    vmap_opx(Op,Ys,Z,[],Bs).

vmap_opx(Op,[Y|Ys],Z,Xs,Bs) ->
    {{bool,X},Bs1} = operation(Op,{bool,Y},{bool,Z},Bs),
    vmap_opx(Op,Ys,Z,[X|Xs],Bs1);
vmap_opx(_Op,[],_Z,Xs,Bs) ->
    {lists:reverse(Xs),Bs}.


%% circuit for Ys < Zs
%% vless([Y|Ys],[Z|Zs],Xs,Bs) ->

sort(Xs,0,Bs) -> 
    {Xs,Bs};
sort(Xs,I,Bs) ->
    {[X|Xs1],Bs1} = minmax(Xs,Bs),
    {Xs2,Bs2} = sort(lists:reverse(Xs1),I-1,Bs1),
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

each_unbound(Bs, Fun) ->
    each_unbound_(Bs, Fun, next_unbound(Bs)).

each_unbound_(_Bs, _Fun, false) ->
    ok;
each_unbound_(Bs, Fun, Xi) ->
    Fun(Xi),
    each_unbound_(Bs, Fun, next_unbound(Bs,Xi)).

fold_unbound(Bs, Fun, Acc) ->
    fold_unbound_(Bs, Fun, Acc, next_unbound(Bs)).

fold_unbound_(_Bs, _Fun, Acc, false) ->
    Acc;
fold_unbound_(Bs, Fun, Acc, Xi) ->
    Acc1 = Fun(Xi, Acc),
    fold_unbound_(Bs, Fun, Acc1, next_unbound(Bs, Xi)).

each_variable(Bs, Fun) ->
    each_variable_(Bs, Fun, 1, varp_nif:info(Bs#bs.vp, number_of_variables)+1).

each_variable_(_Bs, _Fun, Max, Max) ->
    ok;
each_variable_(Bs, Fun, X, N) ->
    Fun(X),
    each_variable_(Bs, Fun, X+1, N).

clear_user_count(Bs) ->
    Vp = Bs#bs.vp,
    each_variable(Bs,
		 fun(X) ->
			 varp_nif:set_user_count(Vp, X, 0),
			 varp_nif:set_user_count(Vp, -X, 0)
		 end).
%%
%% collect the model
%% Boolean: {x,true} | {y,false}]
%% Integer: {a,{uint,{$1,$1,$1,$1}}} |  (a = 15)
%%          {b,{int,{$1,$0,$0,$1}}}  |  (b = -7)
%%          {c,{int,{$0,$0,$0}}}     |  (c = 0)
%% 
%% Partial numbers look like {x,{int,{$*,$1,$0,..,$*,$1}}}
%%
model(Bs) ->
    model(Bs#bs.vp, Bs#bs.vs).
    
model(Vp, Vs) ->
    lists:keysort(1, collect_model(Vp,Vs)).

collect_model(Vp,Vs) ->
    case maps:size(Vs) of
	0 -> %% fixme mixed model! CNF with is declarations
	    N = varp:get_number_of_variables(Vp),
	    lists:foldr(
	      fun(I,Acc) ->
		      case varp_nif:value(Vp,I) of
			  ?T -> [{{p,'x',[I]}, true}|Acc];
			  ?F -> [{{p,'x',[I]},false}|Acc];
			  _ -> Acc
		      end
	      end, [], lists:seq(1, N));
	_ ->
	    maps:fold(
	      fun (?T,_,Ms) -> Ms;
		  (?F,_,Ms) -> Ms;
		  (Y,Xs,Ms) when is_integer(Y) ->
		      model_vars(Vp,Vs,Xs,Y,Ms);
		  (_, _, Ms) -> Ms
	      end, [], Vs)
    end.

model_vars(Vp,Vs,[{Type,X,N,I}|Xs],Y,Ms) ->
    V = case varp_nif:value(Vp, Y) of
	    ?T -> $1;
	    ?F -> $0;
	    _  -> $*
	end,
    model_vars(Vp,Vs,Xs,Y,model_setvec(Type,X,N,I,V,Ms));
model_vars(Vp,Vs,[X|Xs],Y,Ms) ->
    case varp_nif:value(Vp, Y) of
	?T ->
	    model_vars(Vp,Vs,Xs,Y,[{X,true}|Ms]);
	?F ->
	    model_vars(Vp,Vs,Xs,Y,[{X,false}|Ms]);
	_ ->
	    model_vars(Vp,Vs,Xs,Y,Ms)
    end;
model_vars(_Vp,_Vs,[],_Y,Ms) ->
    Ms.

%% int/uint/bit is represented as ascii vector {Type,{$0|$1|$*,...}}
%% where the bit tuple is MSB (high to low) 
model_setvec(Type,X,N,I,V,Ms) ->
    case lists:keytake(X, 1, Ms) of
	{value,{X,{Type,Bits}},Ms1} ->
	    Bits1 = setelement(N-I,Bits,V),
	    [{X,{Type,Bits1}} | Ms1];
	false ->
	    [{X,{Type,erlang:make_tuple(N,$*,[{N-I,V}])}} | Ms]
    end.

print_model(true,I,_Partial,Bindings) ->
    Bindings1 = filter_bindings(Bindings),
    io:format("~w: ~s\n",
	      [I,lists:join(",",[format_binding(Bound) || Bound <- Bindings1 ])]);
print_model(literal,I,_Partial,Bindings) ->
    Bindings1 = filter_bindings(Bindings),
    io:format("~w: ~s\n",
	      [I,lists:join(",",[format_binding(Bound) || Bound <- Bindings1 ])]);
print_model(model,I,false,Bindings) ->
    Bindings1 = filter_bindings(Bindings),
    io:format("~w: ~s\n",
	      [I,lists:join(",",
			    [ format_binding(Bound) || 
				Bound <- Bindings1,
				element(2,Bound) =/= false ])]);
print_model(model,I,true,Bindings) ->
    Bindings1 = filter_bindings(Bindings),
    io:format("~w: ~s\n",
	      [I,lists:join(",",[format_binding(Bound) || Bound <- Bindings1 ])]);
%% print_model(umodel,I,_Partial,Bindings) ->
%%    io:format("~w: ~s\n",
%%	      [I,lists:join(",",[ format_binding(Bound) || 
%%				    Bound <- Bindings,
%%				    element(2,Bound) =/= false ])]);
print_model(erlang,_I,_Partial,Bindings) ->
    Bindings1 = filter_bindings(Bindings),
    io:format("~w.\n", [Bindings1]);
print_model(dimacs,_I,_Partial,Bindings) ->
    print_dimacs_rows(Bindings, 78);
print_model(false,_I,_PArtial,_Bindings) ->
    ok.

%% output model in DIMACS format
%% "v" L(1) ... L(i) "\n"
%% "v" L(i+1)...L(j) "\n"
%% "v" L(j+1).. 0\n"
%%
print_dimacs_rows(Bindings, LineLength) ->
    print_dimacs_rows_(Bindings, LineLength, LineLength, []).

print_dimacs_rows_([{{p,x,[J]},Value}|Bs], Remain, N, Acc) when is_integer(J) ->
    K  = if Value -> J; true -> -J end,
    Xi = [$\s | erlang:integer_to_list(K)],
    Len = length(Xi),
    Remain1 = Remain - Len,
    if Remain1 < 0 ->
	    io:format("v~s\n", [Acc]),
	    print_dimacs_rows_(Bs, N-Len, N, [Xi]);
       true ->
	    print_dimacs_rows_(Bs, Remain1, N, [Xi|Acc])
    end;
print_dimacs_rows_([B|Bs], Remain, N, Acc) ->
    Xi = [$\s | lists:flatten(format_binding(B))],
    Len = length(Xi),
    Remain1 = Remain - Len,
    if Remain1 < 0 ->
	    io:format("v~s\n", [Acc]),
	    print_dimacs_rows_(Bs, N-Len, N, [Xi]);
       true ->
	    print_dimacs_rows_(Bs, Remain1, N, [Xi|Acc])
    end;
print_dimacs_rows_([], _I, _N, []) ->
    ok;
print_dimacs_rows_([], _I, _N, Acc) ->
    io:format("v~s 0\n", [Acc]).

%% remove bindings on form _Var (hidden)
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
    case Value of
	true -> VarFmt;
	false -> [$!|VarFmt];
	{uint,Vec} -> [VarFmt,"=",format_uint(Vec)];
	{int,Vec} -> [VarFmt,"=",format_int(Vec)];
	{bit,Vec} -> [VarFmt,"=",format_bit(Vec)]
    end.

format_uint(Tuple) when is_tuple(Tuple) ->
    List = tuple_to_list(Tuple),
    try list_to_integer(List, 2) of
	UInt -> integer_to_list(UInt)
    catch
	error:_ ->
	    "0b"++List
    end.

format_int(Tuple) when is_tuple(Tuple) ->
    List = tuple_to_list(Tuple),
    try list_to_integer(List, 2) of
	UInt ->
	    if element(1,Tuple) =:= $1 -> %% signed
		    Abs=(((bnot UInt) band ((1 bsl tuple_size(Tuple))-1))+1),
		    [$-|integer_to_list(Abs)];
	       true ->
		    integer_to_list(UInt)
	    end
    catch
	error:_ ->
	    "0b"++List
    end.

format_bit(Tuple) when is_tuple(Tuple) ->
    "{"++tuple_to_list(Tuple)++"}".


log_clause(Bs, Clause) ->
    io:format("~s\n", [format_clause(Bs,Clause)]).

proof_output(Bs, $c, Text) ->  %% non-standard
    case want_proof_output(Bs) of
	false -> ok;
	binary -> ignore;
	user ->
	    io:put_chars(user, ["c ",Text,"\n"]);
	_ ->
	    file:write(Bs#bs.proof_fd,  ["c ",Text,"\n"])
    end;
proof_output(Bs, Prefix, Clause) ->
    case want_proof_output(Bs) of
	false -> ok;
	binary ->
	    Clause1 = lookup_clause(Bs, Clause),
	    %% fixme: lookup literals!
	    Bin = varp_nif:compress_clause(Bs#bs.vp, Clause1),
	    file:write(Bs#bs.proof_fd, <<Prefix, Bin/binary, 0>>);
	user ->
	    Clause1 = lookup_clause(Bs, Clause),
	    proof_output_text(user, Bs, Prefix, Clause1);
	_ ->
	    Clause1 = lookup_clause(Bs, Clause),
	    proof_output_text(Bs#bs.proof_fd, Bs, Prefix, Clause1)
    end.

lookup_clause(Bs, ClauseIndex) when is_integer(ClauseIndex) ->
    varp_nif:get_clause(Bs#bs.vp, ClauseIndex, undefined, true);
lookup_clause(_Bs, Clause) when is_list(Clause) ->
    Clause.

proof_output_text(Fd, Bs, Prefix, Clause) ->
    P = if Prefix =:= $a -> ""; true -> [Prefix,$\s] end,
    Chars = [P,[[proof_literal(Bs,Li),$\s] || Li <- Clause], "0\n"],
    if is_atom(Fd) ->
	    io:put_chars(Fd, Chars);
       true ->
	    file:write(Fd, Chars)
    end.

empty_vs(Bs) ->    
    (Bs#bs.vs =:= undefined) orelse  (maps:size(Bs#bs.vs) =:= 0).

proof_literal(Bs,Li) ->
    EmptyVs = empty_vs(Bs),
    if EmptyVs -> integer_to_list(Li);	    
       Li < 0 ->
	    case maps:find(-Li, Bs#bs.vs) of
		error -> integer_to_list(Li);
		{ok,[{p,x,[I]}]} -> integer_to_list(-I);
		{ok,[P|_]} -> [$!|format_symbol(P)]
	    end;
       Li > 0 ->
	    case maps:find(Li, Bs#bs.vs) of
		error -> integer_to_list(Li);
		{ok,[{p,x,[I]}]} -> integer_to_list(I);
		{ok,[P|_]} -> format_symbol(P)
	    end
    end.

-ifdef(not_used).
lookup_literal(Bs,Li) when is_integer(Li) ->
    EmptyVs = empty_vs(Bs),
    if EmptyVs -> Li;
       Li < 0 ->
	    case maps:find(-Li, Bs#bs.vs) of
		error -> Li;
		{ok,[{p,x,[I]}]} -> -I
	    end;
       Li > 0 ->
	    case maps:find(Li, Bs#bs.vs) of
		error -> Li;
		{ok,[{p,x,[I]}]} -> I
	    end
    end.
-endif.

format_p({p,T,As}) when is_integer(T) ->
    [$T,integer_to_list(As)|format_params(As)];
format_p({p,V,As}) when is_atom(V) ->
    [atom_to_list(V)|format_params(As)];
format_p({p,Name,As}) when is_list(Name); is_binary(Name) ->
    [Name|format_params(As)];
format_p({bitindex,Var,Index}) ->
    [format_p(Var),"[",integer_to_list(Index), "]"];
format_p({index,Var,Index}) ->
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
    lists:join(",",[format_lit(Bs,L,Bound)||L<-Ls]).

format_lit(Bs,X) when is_integer(X) ->
    format_lit(Bs,X,false).

format_lit(_Bs,?F,_Bound) -> "0";
format_lit(_Bs,?T,_Bound)  -> "1";
format_lit(Bs,X,Bound) when is_integer(X), X<0 ->
    ["!",format_var(Bs,-X,Bound)];
format_lit(Bs,X,Bound) when is_integer(X) ->
    format_var(Bs,X,Bound).

format_var(Bs,X) ->
    format_var(Bs,X,false).

format_var(_Bs,?T,_Bound) -> "1";
format_var(_Bs,?F,_Bound) -> "0";
format_var(Bs,X,Bound) ->
    case find_var(X,Bs) of
	error ->
	    format_bnd(Bs, X, X, Bound);
	{ok,[Var]} ->
	    format_bnd(Bs, X, Var, Bound)
    end.

format_bnd(_Bs, _X, Var, false) ->
    format_symbol(Var);
format_bnd(Bs, X, Var, true) ->
    Value = case value(Bs, X) of
		true -> "/1";
		false -> "/0";
		_ -> ""
	    end,
    format_symbol(Var) ++ Value;
format_bnd(Bs, X, Var, level) ->
    L = varp_nif:implication_level(Bs#bs.vp, X), 
    Value = case value(Bs, X) of
		true -> "=1@"++integer_to_list(L);
		false -> "=0@"++integer_to_list(L);
		_ -> ""
	    end,
    format_symbol(Var) ++ Value.

format_symbol(?T) -> "t";
format_symbol(?F) -> "f";
format_symbol(V) when is_atom(V) -> atom_to_list(V);
format_symbol(I) when is_integer(I),I>0 -> [$$|integer_to_list(I)];
format_symbol({bit,V,_N,I}) ->
    format_symbol(V)++"["++integer_to_list(I)++"]";
format_symbol({index,V,I}) ->
    format_symbol(V)++"["++integer_to_list(I)++"]";
format_symbol({uint,V,_N,I}) ->
    format_symbol(V)++"["++integer_to_list(I)++"]";
format_symbol({int,V,_N,I}) ->
    format_symbol(V)++"["++integer_to_list(I)++"]";
format_symbol({bitindex,V,I}) ->
    format_symbol(V)++"["++integer_to_list(I)++"]";
format_symbol(Var={p,_,_}) ->
    format_p(Var).

fmt_bind(Bs,X,Y,D) ->
    io_lib:format("~s/~s(~w)", [fmt_v(Bs,X),fmt_v(Bs,Y),D]).

fmt_bind(Bs,X,Y) ->
    io_lib:format("~s/~s", [fmt_v(Bs,X),fmt_v(Bs,Y)]).

fmt_bind_list(Bs,Xs) ->
    lists:join(",", [fmt_bind(Bs,X,Y) || {X,Y} <- Xs]).
    
