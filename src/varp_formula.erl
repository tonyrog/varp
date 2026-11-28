%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2012, Tony Rogvall
%%% @doc
%%%    Building formulas
%%% @end
%%% Created :  2 Sep 2012 by Tony Rogvall <tony@rogvall.se>

-module(varp_formula).

%% -define(DEBUG, true).
%% -compile(export_all).
-export([build/1, build/2]).
-export([build_assignment_defs/2]).
-export([new/0, new/1]).
-export([add_variable/1, add_atom/1]).
-export([variable/2]).
%% -export([alias/3]).
%% -export([set_var/3, add_var/4]).
-export([print_model/4]).
-export([uint64/2, uint32/2, uint16/2, uint8/2]).
-export([filter_bindings/1]).

-export([log_clause/2]).
-export([proof_output/3]).
-export([want_proof_output/1]).

-export([all/2, any/2, all/3, any/3, one/2, one/3, none/2, none/3]).
-export([eqk/4, gtk/4]).
-export([subst/3]).

-export([order_first/2]).
-export([order_last/2]).
-export([model/1, model/2]).
-export([intersect_bindings/3]).
-export([install_bindings/3]).
-export([each_unbound/2]).
-export([decl_type/2, decl_type/3, decl_width/3, float_spec/1, nif_type/1]).   %% fixed point and float declarations
-export([each_variable/2]).
-export([fold_unbound/3]).
-export([eval_meta/2]).
-export([del_clause/2]).
-export([del_unused_clauses/1]).
-export([clean_clauses/1, clean_clauses/2]).

-export([const_vector/2, const_vector/3]).
-export([const_vector/4]).

-export([vconst/1]).

%% interna circuit lookup from scanner
-export([init_circuit_def/0]).
-export([add_circuit_def/1]).
-export([is_circuit_def/2]).
-export([find_circuit_def/3]).
%% internal (test)
-export([operation1/3, operation1/4]).
-export([operation2/4, operation2/5]).

-include("varp.hrl").

-define(is_int_type(T),   (((T)=:=int) orelse ((T)=:=uint))).
%% operators that take booleans and give a boolean, everything else
%% applied to booleans is arithmetic and widens them to 1 bit vectors
%% wrap(E) and cast(E) take their type from the destination
-define(is_typed_by_target(F), ((F) =:= <<"wrap">> orelse (F) =:= <<"cast">>)).

-define(is_bool_op(Op),
	((Op) =:= 'and' orelse (Op) =:= 'or' orelse (Op) =:= 'xor' orelse
	 (Op) =:= 'imp' orelse (Op) =:= 'equ' orelse
	 (Op) =:= 'nimp' orelse (Op) =:= 'nand' orelse (Op) =:= 'nor' orelse
	 (Op) =:= 'band' orelse (Op) =:= 'bor' orelse (Op) =:= 'bxor' orelse
	 (Op) =:= 'lt' orelse (Op) =:= 'gt' orelse
	 (Op) =:= 'lte' orelse (Op) =:= 'gte' orelse
	 (Op) =:= 'eq' orelse (Op) =:= 'neq')).
%% the functions of eval_meta({call,...}); a name that is not declared
%% or defined and is one of these is evaluated, not made a variable
-define(is_meta_function(P),
	(P =:= <<"len">> orelse P =:= <<"byte">> orelse P =:= <<"factorial">> orelse
	 P =:= <<"binom">> orelse P =:= <<"sqrt">> orelse P =:= <<"isqrt">> orelse
	 P =:= <<"sqr">> orelse P =:= <<"nroot">> orelse P =:= <<"ln">> orelse
	 P =:= <<"log">> orelse P =:= <<"log2">> orelse P =:= <<"log10">> orelse
	 P =:= <<"ilog2">> orelse P =:= <<"isize">> orelse P =:= <<"usize">> orelse
	 P =:= <<"pow">> orelse P =:= <<"sin">> orelse P =:= <<"cos">> orelse
	 P =:= <<"trunc">> orelse P =:= <<"round">>)).
%% a fixed point vector is tagged {fix,F}, F fraction bits; its bits are
%% a two's complement integer scaled by 2^F (see the fixpoint section)
-define(is_fix(T), (is_tuple(T) andalso tuple_size(T) =:= 2
		    andalso element(1,(T)) =:= fix)).
%% an IEEE 754 vector is tagged {float,E,M}: a sign bit, E exponent bits
%% and M fraction bits (see the float754 section)
-define(is_float(T), (is_tuple(T) andalso tuple_size(T) =:= 3
		      andalso element(1,(T)) =:= float)).
%% X/float before --float has said which of the two it is
-define(is_meta_float(T), ((T) =:= {float,default})).
-define(is_vec_type(T), (((T)=:=int) orelse ((T)=:=uint) orelse ((T)=:=bit)
			 orelse ?is_fix(T) orelse ?is_float(T)
			 orelse ?is_meta_float(T))).
-define(is_compare_op(Op),
	((Op) =:= 'lt' orelse (Op) =:= 'lte' orelse (Op) =:= 'gt' orelse
	 (Op) =:= 'gte' orelse (Op) =:= 'eq' orelse (Op) =:= 'neq' orelse
	 (Op) =:= '=')).


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
		 seed       => maps:get(seed,OptMap),
		 decay      => float(maps:get(bump_decay,OptMap,0.95)),
		 icase      => maps:get(icase,OptMap),
		 %% the status options the encoders read back with
		 %% getopt (set_status): without these the command line
		 %% --divz, --carry ... never reached the instance
		 carry      => maps:get(carry,OptMap,ignore),
		 borrow     => maps:get(borrow,OptMap,ignore),
		 overflow   => maps:get(overflow,OptMap,ignore),
		 divz       => maps:get(divz,OptMap,false)
	       },
    Vp  = varp_nif:new(NewOpts),
    %% transfer some options to vp:setopt(Vp, ...)
    Proof_Output = maps:get(proof_output, OptMap),
    Proof_Filename = maps:get(proof_file, OptMap),
    Proof_Dirname  = maps:get(outdir, OptMap),

    varp_nif:setopt(Vp, assoc, maps:get(assoc,OptMap), user),
    varp_nif:setopt(Vp, proof_output, maps:get(proof_output,OptMap), user),
    varp_nif:setopt(Vp, adder, maps:get(adder,OptMap), user),
    varp_nif:setopt(Vp, method, maps:get(method,OptMap), user),
    varp_nif:setopt(Vp, print, maps:get(print,OptMap), user),
    varp_nif:setopt(Vp, partial, maps:get(partial,OptMap), user),
    varp_nif:setopt(Vp, starexec, maps:get(starexec,OptMap), user),
    varp_nif:setopt(Vp, proof_output, Proof_Output, user),
    varp_nif:setopt(Vp, proof_file, Proof_Filename, user),
    varp_nif:setopt(Vp, outdir, Proof_Dirname, user),

%%    Symbols  = maps:get(syms,OptMap),
    Counters = counters:new(?NUM_COUNTERS, []),
    Delta1   = counters:new(1024, []),
    Delta2   = counters:new(1024, []),
    CLen     = counters:new(1024, []),

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
%%       vs = Symbols,
       meta     = maps:get(meta,OptMap),
       defs     = maps:get(defs,OptMap),
       decls    = maps:get(decls,OptMap),
       circuits = make_circuit_map(maps:get(circuits,OptMap)),
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

make_circuit_map(Circuits) when is_map(Circuits) ->
    Circuits;
make_circuit_map(Circuits) when is_list(Circuits) ->
    maps:from_list([{Name,C} || C={circuit,Name,_Params,_Defs} <- Circuits]).


%% Check if proof output is active
want_proof_output(Bs) ->
    case varp_nif:getopt(Bs#bs.vp, proof_output) of
	none -> false;
	Type -> Type
    end.

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
    ?dbg0("del_clause: ~w/~s\n", [I,varp_nif:clause_info(V,I,set)]),
    del_clauses(V, varp_nif:clauseset_next(V, I)).

del_proof_clauses(_Bs, _V, false) ->
    ok;
del_proof_clauses(Bs, V, I) ->
    proof_output(Bs, $d, I),
    ?dbg0("proof del_clause: ~w/~s\n", [I,varp_nif:clause_info(V,I,set)]),
    varp_nif:del_clause(V, I),

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


%% is_temporary({p,<<$$,_/binary>>,_}) -> true;
%% is_temporary(_) -> false.

%% add symbol name to literal 
-spec add_symbol(Bs::#bs{}, 
		 Sym::{Name::iolist(),Index::[term()]},
		 L::integer(), Type::atom()) ->
	  ok.
add_symbol(Bs, Sym, L, Type) ->
    varp_nif:add_symbol(Bs#bs.vp, Sym, L, Type).

add_variable(Bs) ->
    varp_nif:add_variable(Bs#bs.vp).

add_atom(Bs) ->
    varp_nif:add_variable(Bs#bs.vp, _IsAtom=true).

find_var({p,Name,Args}, Bs) ->
    case find_sym({Name,Args}, Bs) of
	false ->
	    error;
	Val -> 
	    {ok,Val}
    end;
find_var({Type,Name,Args}, Bs) ->
    case find_sym({Name,Args}, Bs) of
	false ->
	    error;
	Val -> 
	    {ok,{Type,length(Val),Val}}
    end.

%% A local of a circuit instance (its name carries the instance prefix,
%% "op_add#3.C") is kept in #bs.locals and never enters the symbol
%% table, so a model does not list it and a formula with many
%% instances does not fill the table; --locals keeps them visible.
%% The map goes away with the instance (build_circuit restores the
%% caller's), nothing outside the body can name a local anyway.
find_sym(Sym, Bs) ->
    case maps:find(Sym, Bs#bs.locals) of
	{ok,Val} -> Val;
	error -> varp_nif:find_symbol(Bs#bs.vp, Sym)
    end.

hidden_name(Name, Bs) when is_binary(Name) ->
    binary:match(Name, <<"#">>) =/= nomatch andalso
	not maps:get(locals, Bs#bs.option, false) andalso
	not maps:is_key(Name, Bs#bs.visible);
hidden_name(_Name, _Bs) ->
    false.

new_symbol(Sym={Name,_Args}, Ls, Type, Bs) ->
    case hidden_name(Name, Bs) of
	true ->
	    %% what varp_nif:find_symbol would have answered
	    Bs#bs { locals = maps:put(Sym, {Type,Ls}, Bs#bs.locals) };
	false ->
	    add_symbol(Bs, Sym, Ls, Type),
	    Bs
    end.

make_variable({p,Name,Args}, Bs) ->
    L = add_atom(Bs),
    Bs1 = new_symbol({Name,Args}, L, bool, Bs),
    {{bool,L}, Bs1}.

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
variable_list_(Bs, [{p,Name,[]}|Vs], Acc) when is_binary(Name) ->
    %% the bare name of a predicate with arguments, "order
    %% --first=Move" for Move(p,q,time): every instance that exists,
    %% earliest step (last argument) first
    case predicate_instances(Bs, Name) of
	[] -> variable_list_1(Bs, {p,Name,[]}, Vs, Acc);
	Insts -> variable_list_(Bs, Insts ++ Vs, Acc)
    end;
variable_list_(Bs, [V|Vs], Acc) ->
    variable_list_1(Bs, V, Vs, Acc);
variable_list_(Bs, [], Acc) ->
    {Acc,Bs}.

variable_list_1(Bs, V, Vs, Acc) ->
    case bld(V, Bs) of
	{{bool,X}, Bs1} ->
	    ?dbg0("~w = ~w\n", [V, X]),
	    variable_list_(Bs1, Vs, [X|Acc]);
	{{T,_N,Xs}, Bs1} when ?is_vec_type(T) ->
	    variable_list_(Bs1, Vs, cat(Xs,Acc))
    end.

predicate_instances(Bs, Name) ->
    case maps:find(Name, maps:get(decls, Bs#bs.option, #{})) of
	{ok, {_Type, Arity, _}} when Arity > 0 ->
	    Vp = Bs#bs.vp,
	    Args = instances_(Vp, Name, varp_nif:first_symbol(Vp), []),
	    [{p,Name,A} || {_,A} <- lists:sort([{lists:reverse(A),A} || A <- Args])];
	_ ->
	    []
    end.

instances_(_Vp, _Name, false, Acc) ->
    Acc;
instances_(Vp, Name, Sym={Name,Args}, Acc) when Args =/= [] ->
    instances_(Vp, Name, varp_nif:next_symbol(Vp, Sym), [Args|Acc]);
instances_(Vp, Name, Sym, Acc) ->
    instances_(Vp, Name, varp_nif:next_symbol(Vp, Sym), Acc).

cat([X|Xs], Ys) -> cat(Xs, [X|Ys]);
cat([], Ys) -> Ys.

subst(Bs, X, Y) ->
    varp_nif:subst(Bs#bs.vp,X,Y).

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

    
variable(V, Bs) ->
    W = expand_meta(V, Bs),
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
			    Meta = maps:merge(Bs#bs.meta,maps:from_list(Bnd2)),
			    ?dbg0("meta bind: ~p\n", [Meta]),
			    {R,Bs1} = bld(Def, Bs#bs { meta=Meta}),
			    ?dbg0("R = ~p\n", [R]),
			    %% Meta1 = lists:nthtail(length(Bnd2),Bs1#bs.meta),
			    {R,Bs1#bs { meta=Bs#bs.meta}}
		    end;
		_ ->
		    make_variable(W, Bs)
	    end;
%%	{ok,N} when is_integer(N) ->
%%	    {{bool,N},Bs};
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
    Found = find_subst(P, Bs#bs.subst),
    case Found of
	false -> {p,P,Rs1};
	{{p,Q,[]},{p,_P,_Us}} -> {p,Q,[]};
	{{p,Q,Qs},{p,P,Ps}} when P =/= Q, length(Qs) > 0 ->
	    Bnd2 = lists:zip(Ps,Rs1),
	    Meta = Bnd2 ++ Bs#bs.meta,
	    expand_meta({p,Q,Qs}, Bs#bs { meta=Meta})
    end;
expand_meta(ID,_Bs) when is_binary(ID) ->
    {p,ID,[]};
expand_meta(V,_Bs) ->
    V.

%% definitions are keyed by {Name,Arity}, see varp:split_sections/3
match_def(P, As, Defs) ->
    List = maps:get({P,length(As)}, Defs, []),
    match_def_list(List,As).

match_def_list([{Fs,Def}|Ds],As) ->
    case match_def_args(Fs, As) of
	false -> match_def_list(Ds, As);
	Bnd -> {Bnd,Def}
    end;
match_def_list([], _As) -> false.

match_def_args(Fs, As) ->
    match_def_args(Fs, As, []).
    
match_def_args([F|Fs], [A|As], Acc) ->
    case {match_eval(F), match_eval(A)} of
	{Fi,Ai} when is_binary(Fi), is_integer(Ai) ->
	    match_def_args(Fs,As,[{Fi,Ai}|Acc]);
	{Fi,Fi} when is_integer(Fi) ->
	    match_def_args(Fs,As,Acc);
	{_,{term,T}} ->
	    %% "define F(x) ..." called as F(X(i)): a define takes
	    %% integers, a formula argument needs a circuit
	    error({define_argument, T});
	{_,Ai} when is_binary(Ai) ->
	    %% an unbound name, F(a) with a a variable
	    error({define_argument, {p,Ai,[]}});
	_ ->
	    false
    end;
match_def_args([],[],Acc) ->
    lists:reverse(Acc);
match_def_args(_, _, _Acc) ->
    false.

%% sub eval for match
match_eval({const,V}) -> V;
match_eval(Name) when is_binary(Name) -> Name;
match_eval(T) when is_tuple(T), element(1,T) =:= f;
		   is_tuple(T), element(1,T) =:= p -> {term, T};
match_eval(X) when is_integer(X) -> X;
match_eval(X) when is_atom(X) -> X.

%% find propositional variable defintion P() or P
find_prop_def(P, Defs) ->
    case maps:get({P,0}, Defs, []) of
	[{[],Def}] -> Def;
	_ -> false
    end.

%% element I of the array define P, 0 based
array_element(_P, Elems, I) when is_integer(I), I >= 0, I < length(Elems) ->
    lists:nth(I+1, Elems);
array_element(P, Elems, I) ->
    error({array_index, P, I, length(Elems)}).

find_subst(P, [E={_Qy,{p,P,_}}|_]) -> E;
find_subst(P, [_|Bnd]) -> find_subst(P, Bnd);
find_subst(_P ,[]) -> false.

bind_meta([V|Vs], Bs, Acc, Bnd) when is_binary(V) ->
    W = eval_meta(V,Bs),
    bind_meta(Vs, Bs, [W|Acc], [{V,W}|Bnd]);
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


%% keep defined circuits to allow parser to know what
%% symbols are predicates and what symbols are circuits
init_circuit_def() ->
    put(circuit_defs, varp_lib:pending_names()).

add_circuit_def(C={circuit,Name,_Params,_Defs}) ->
    %% undefined when a library circuit is the first token of a file:
    %% the grammar has not initialised yet (it does so on the first
    %% reduction, after that token), init_circuit_def/0 keeps the name
    CDef = case get(circuit_defs) of
	       undefined -> #{};
	       M -> M
	   end,
    put(circuit_defs, CDef#{ Name => true }),
    C.

%% lookup a circuit definition in the #bs.circuits map
find_circuit_def(Name, Defs, _ICase=false) when is_map(Defs) ->
    maps:find(Name, Defs);
find_circuit_def(Name, Defs, _ICase=true) when is_map(Defs) ->
    UName = string:uppercase(Name),
    find_circuit_def_(UName, maps:values(Defs));
find_circuit_def(Name, Defs, ICase) when is_list(Defs) ->
    find_circuit_def(Name, make_circuit_map(Defs), ICase).

find_circuit_def_(UName, [C={circuit,Name,_Params,_Defs}|Defs]) ->
    case string:uppercase(Name) of
	UName -> {ok,C};
	_ -> find_circuit_def_(UName, Defs)
    end;
find_circuit_def_(_UName, []) -> error.


%% installed in dictionary, called from scanner!
is_circuit_def(Name, ICase) ->
    case get(circuit_defs) of
	undefined -> false;
	CDef ->
	    case ICase of
		false ->
		    maps:get(Name, CDef, false);
		true ->
		    I = maps:iterator(CDef),
		    UName = string:uppercase(Name),
		    is_circuit_def_(UName, I)
	    end
    end.

is_circuit_def_(UName, I) ->
    case maps:next(I) of
	none -> false;
	{Name,true,I1} ->
	    case string:uppercase(Name) of
		UName -> true;
		_ -> is_circuit_def_(UName, I1)
	    end
    end.

set(undefined, Y, Bs) -> {Y, Bs};
set(X={{float,_,_},_,_}, Y, Bs) ->
    float_set(X, Y, Bs);
set(X={{fix,F},N,_}, Y={{float,_,_},_,_}, Bs) ->
    %% a float into a fixed point variable: truncated toward zero
    {Fx, Bs1} = float_to_fix(Y, F, false, N, Bs),
    fix_set(X, Fx, Bs1);
set(X, {{float,_,_},_,_}, _Bs) when is_tuple(X) ->
    error({float754_to_integer, operand_kind(X),
	   "use floor, ceil, round or trunc"});
set(X, Y, Bs) ->
    case fix_set(X, Y, Bs) of
	false -> operation1('=',X,Y,Bs);
	Result -> Result
    end.

%% is Name defined by a 'define', for any arity
is_definition(Name, Bs) ->
    lists:any(fun({N,_A}) -> N =:= Name;
		 (_) -> false
	      end, maps:keys(Bs#bs.defs)).

%% A symbol used as a propositional variable without a declaration.
%% That is normal in varp, P(1,2) is meant to spring into existence, so
%% plain "undeclared" is a weak signal.  The modes are
%%
%%   none  off
%%   typo  a symbol that occurs once in the source AND looks like a
%%         misspelling of another symbol.  a1/a2/a3 style families are
%%         not reported, they differ only in their digits
%%   once  every symbol that occurs once
%%   all   every undeclared symbol
%%
%% Note that an occurrence count is lexical: A(i) under a quantifier
%% occurs once but makes many variables, which is why 'once' is not the
%% default.
warn_undeclared(P, Arity, Bs) ->
    case maps:get(undeclared, Bs#bs.option, none) of
	none ->
	    ok;
	Mode ->
	    %% a name with a definition or a declared literal is not a
	    %% variable, and a name that is not in the source at all was
	    %% generated by varp itself (circuit locals, dimacs x(N))
	    case maps:is_key({P,Arity}, Bs#bs.defs) orelse
		maps:is_key(P, Bs#bs.literals) of
		true -> ok;
		false -> warn_undeclared_(P, Arity, Mode, Bs)
	    end
    end.

warn_undeclared_(P, Arity, Mode, Bs) ->
    Syms = maps:get(syms, Bs#bs.option, #{}),
    case maps:find(P, Syms) of
	error ->
	    ok;   %% generated by varp itself, not from the source
	{ok,{N,Line}} ->
	    case report_undeclared(Mode, P, N, Syms) of
		false -> ok;
		Why -> undeclared_warning(P, Arity, Line, Why, Bs)
	    end
    end.

report_undeclared(strict, _P, _N, _Syms) -> not_declared;
report_undeclared(all, _P, _N, _Syms) -> not_declared;
report_undeclared(once, _P, 1, _Syms) -> occurs_once;
report_undeclared(typo, P, 1, Syms) ->
    case near_miss(P, Syms) of
	false -> false;
	Q -> {looks_like, Q}
    end;
report_undeclared(_Mode, _P, _N, _Syms) -> false.

undeclared_warning(P, Arity, Line, Why, Bs) ->
    Where = maps:get(file, Bs#bs.option, "*internal*"),
    Name = if Arity =:= 0 -> [P];
	      true -> [P,"/",integer_to_list(Arity)]
	   end,
    case maps:get(undeclared, Bs#bs.option, none) of
	strict ->
	    %% a declared name is an established spelling however
	    %% seldom it occurs, so it can be the "did you mean"
	    Syms0 = maps:get(syms, Bs#bs.option, #{}),
	    Syms = maps:map(fun(Q, {N,L}) ->
				    case maps:is_key(Q, Bs#bs.decls) of
					true -> {max(N,2),L};
					false -> {N,L}
				    end
			    end, Syms0),
	    error({undeclared, Where, Line, lists:flatten(Name), near_miss(P, Syms)});
	_ -> ok
    end,
    case Why of
	{looks_like,Q} ->
	    ?warn("~s:~w: warning: '~s' occurs once, did you mean '~s'?\n",
		  [Where, Line, Name, Q]);
	occurs_once ->
	    ?warn("~s:~w: warning: '~s' occurs once and is not declared\n",
		  [Where, Line, Name]);
	not_declared ->
	    ?warn("~s:~w: warning: '~s' is not declared\n",
		  [Where, Line, Name])
    end.

%% Another symbol one edit away that is the established spelling, ie
%% one that occurs more than once.  Two guards keep the families apart
%% from the typos:
%%   - a1 and a2 differ only in their digits, that is a family
%%   - single letters are all one edit from each other, so require a
%%     name of at least ?TYPO_MIN_LEN characters
-define(TYPO_MIN_LEN, 3).

near_miss(P, _Syms) when byte_size(P) < ?TYPO_MIN_LEN ->
    false;
near_miss(P, Syms) ->
    near_miss_(P, undigit(P), maps:next(maps:iterator(Syms))).

near_miss_(_P, _Bare, none) -> false;
near_miss_(P, Bare, {P,_,I}) -> near_miss_(P, Bare, maps:next(I));
near_miss_(P, Bare, {Q,{N,_},I}) ->
    case (N > 1) andalso (byte_size(Q) >= ?TYPO_MIN_LEN) andalso
	(undigit(Q) =/= Bare) andalso edit_distance_1(P, Q) of
	true -> Q;
	false -> near_miss_(P, Bare, maps:next(I))
    end.

undigit(Name) ->
    << <<C>> || <<C>> <= Name, C < $0 orelse C > $9 >>.

%% true when A can be turned into B with one insert, delete or
%% substitution
edit_distance_1(A, B) ->
    Na = byte_size(A),
    Nb = byte_size(B),
    if Na =:= Nb -> subst_1(A, B);
       Na+1 =:= Nb -> insert_1(A, B);
       Nb+1 =:= Na -> insert_1(B, A);
       true -> false
    end.

subst_1(<<C,A/binary>>, <<C,B/binary>>) -> subst_1(A, B);
subst_1(<<_,A/binary>>, <<_,B/binary>>) -> A =:= B;
subst_1(<<>>, <<>>) -> false.   %% identical, not an edit

%% B is A with one extra character
insert_1(<<C,A/binary>>, <<C,B/binary>>) -> insert_1(A, B);
insert_1(A, <<_,B/binary>>) -> A =:= B;
insert_1(<<>>, <<>>) -> false.

icase(Bs) ->    
    maps:get(icase, Bs#bs.option, false).
    
%%
%% Generate the variable rules from a formula
%%
build(F) ->
    build(F,varp:default_options()).

build(F,Opts) when is_list(Opts) ->
    bld1(F, new(Opts));
build(F,Opts) when is_map(Opts) ->
    bld1(F, new(Opts));
build(F,Bs) when is_record(Bs, bs) ->
    bld1(F, Bs).

bld1(F, Bs) ->
    try bld(F, Bs) of
      	Value ->
	    Value
    catch
      	throw:contradiction -> 
     	    {{bool,?F},Bs}
	%% every other error is left for the caller, varp:varp_run/4
	%% reports it through varp:format_error/1.  Catching it here
	%% used to return the result of io:format/2, which then showed
	%% up as a second, bogus, {case_clause,ok} crash.
    end.

bld(Y, Bs) ->
    bld(undefined,Y,Bs).

bld(_X,undefined, Bs) -> {undefined, Bs};
bld(X,true,Bs) ->  set(X,{bool,?T},Bs);
bld(X,false,Bs) -> set(X,{bool,?F},Bs);
bld(X,{literal,Y}, Bs) when is_integer(Y) -> set(X,{bool,Y},Bs); %% FIXME???
%% The clauses below produce a value of their own and ignore the
%% assignment target, build_assign/3 ties the two together.
%% a function argument is parsed as a meta expression: an operator or
%% a call in one builds like the formula form, fma(X, Y, -Z)
bld(X,{op,Op,A,B}, Bs) when is_atom(Op), Op =/= ',' ->
    bld(X,{lop,Op,A,B}, Bs);
bld(X,{op,Op,A}, Bs) when is_atom(Op) ->
    bld(X,{lop,Op,A}, Bs);
bld(X,{call,F,As}, Bs) when is_binary(F) ->
    bld(X,{p,F,As}, Bs);
bld(_X,V,Bs) when is_binary(V) -> %% variable (and meta)
    Arity = 0,
    case varp:find_decl(V,Bs#bs.decls,icase(Bs)) of
	error ->
	    W = eval_meta(V,Bs),
	    if W >=0 ->
		    N = varp_math:unsigned_size(W),
		    const_vector(uint,W,N,Bs);
	       W < 0 ->
		    N = varp_math:signed_size(W),
		    const_vector(int,W,N,Bs)
	    end;
	{ok,{bool,Arity1,1}} when Arity =/= Arity1 ->
	    error({arity_mismatch,V});
	{ok,{bool,Arity,1}} ->
	    variable(V, Bs);
	{ok,{PType,_Arity,Size}} ->
	    var_vector(PType,V,Size,Bs)
    end;
bld(_X,W,Bs) when is_integer(W) ->
    if W < 0 ->
	    N = varp_math:signed_size(W),
	    const_vector(int,W,N,Bs);
       true ->
	    N = varp_math:unsigned_size(W),
	    const_vector(uint,W,N,Bs)
    end;
%% a float meta variable, limit=4.0 on the command line
bld(_X,W,Bs) when is_float(W) ->
    {{flo,W},Bs};
bld(_X,{const,W}, Bs) when is_integer(W) ->
    if W < 0 ->
	    N = varp_math:signed_size(W),
	    const_vector(int,W,N,Bs);
       true ->
	    N = varp_math:unsigned_size(W),
	    const_vector(uint,W,N,Bs)
    end;
%% a float literal is a fixed point constant whose fraction width is
%% not known until it meets an operand, see fix_op2/4
bld(_X,{const,W}, Bs) when is_float(W) ->
    {{flo,W},Bs};
%% float754 classification: a boolean, false for anything but a float
bld(X,{p,F,[A]}, Bs) when F =:= <<"isnan">>; F =:= <<"isinf">> ->
    {Y,Bs1} = bld(A, Bs),
    {V,Bs2} = case Y of
		  {T,_,_} when ?is_float(T) ->
		      {{Z,I,N}, Bs1a} = fclass(Y, Bs1),
		      _ = Z,
		      case F of
			  <<"isnan">> -> {N, Bs1a};
			  <<"isinf">> -> {I, Bs1a}
		      end;
		  _ -> {{bool,?F}, Bs1}
	      end,
    set(X, V, Bs2);
%% sqrt(X): the meta function when the argument is a meta expression
%% (sqrt(2) is a literal), else the float754 or fixed point root
bld(X,{p,<<"sqrt">>,[A]}, Bs) ->
    try eval_meta(A, Bs) of
	V when is_number(V), V >= 0 -> bld(X, {const,math:sqrt(V)}, Bs);
	V when is_number(V) -> error({sqrt_negative, V});
	V -> error({sqrt_argument, V})
    catch
	error:{unbound,_} ->   %% a variable: the circuit
	    {Y,Bs1} = bld(A, Bs),
	    {V1,Bs2} = sqrt_op(Y, Bs1),
	    set(X, V1, Bs2)
    end;
%% fma(A, B, C): a*b + c in float754 with one rounding
bld(X,{p,<<"fma">>,[A,B,C]}, Bs) ->
    {Ya,Bs1} = bld(A, Bs),
    {Yb,Bs2} = bld(B, Bs1),
    {Yc,Bs3} = bld(C, Bs2),
    T = case [V || V={{float,_,_},_,_} <- [Ya,Yb,Yc]] of
	    [] -> error({fma_float754_only, [Ya,Yb,Yc]});
	    [V1|_] -> float_type(V1, V1)
	end,
    {Af,Bs4} = to_float(Ya, T, Bs3),
    {Bf,Bs5} = to_float(Yb, T, Bs4),
    {Cf,Bs6} = to_float(Yc, T, Bs5),
    {V,Bs7} = float_fma(Af, Bf, Cf, T, Bs6),
    set(X, V, Bs7);
%% fixed point to integer
%% wrap(E, T): the low bits of E read as T, two's complement, as a C
%% cast or a store into a T sized memory cell.  wrap(E) takes the type
%% of its destination: X = wrap(E), or the other side of == (see the
%% 'eq' clause of lop).  fits(E, T): the exact value of E is
%% representable in T, the overflow that wrap would hide.
bld(X,{p,<<"wrap">>,[A,T]}, Bs) ->
    Type = type_arg(T, Bs),
    {Y,Bs1} = bld(A, Bs),
    {V,Bs2} = wrap_to(Type, Y, Bs1),
    set(X, V, Bs2);
bld(X,{p,<<"wrap">>,[A]}, Bs) when is_tuple(X) ->
    bld(X,{p,<<"wrap">>,[A,{type_of,X}]}, Bs);
bld(_X,{p,<<"wrap">>,[_A]}, _Bs) ->
    error({wrap_type_unknown,
	   "wrap(E) needs a typed destination, X = wrap(E) or "
	   "X == wrap(E); say the type otherwise, wrap(E, 32/unsigned)"});
bld(X,{p,<<"fits">>,[A,T]}, Bs) ->
    Type = type_arg(T, Bs),
    {Y,Bs1} = bld(A, Bs),
    {V,Bs2} = fits_in(Type, Y, Bs1),
    set(X, V, Bs2);
%% cast(E, T): the same bits read as T, no logic at all, what memory
%% does; E/unsigned, E/signed and E/float are cast(E, T) at the same
%% width.  cast(E) takes the type of its destination like wrap(E).
bld(X,{p,<<"cast">>,[A,T]}, Bs) ->
    Type = type_arg(T, Bs),
    {Y,Bs1} = bld(A, Bs),
    {V,Bs2} = cast_to(Type, Y, Bs1),
    set(X, V, Bs2);
%% E/unsigned inside a function argument parses as a type whose size
%% is E: as a value it is the cast
bld(X,{type,PType,E}, Bs) ->
    bld(X,{p,<<"cast">>,[E,{type,PType,same}]}, Bs);
bld(X,{p,<<"cast">>,[A]}, Bs) when is_tuple(X) ->
    bld(X,{p,<<"cast">>,[A,{type_of,X}]}, Bs);
bld(_X,{p,<<"cast">>,[_A]}, _Bs) ->
    error({cast_type_unknown,
	   "cast(E) needs a typed destination, X = cast(E) or "
	   "X == cast(E); say the type otherwise, cast(E, 32/float754)"});
bld(X,{p,F,[A]}, Bs) when F =:= <<"floor">>; F =:= <<"ceil">>;
			  F =:= <<"round">>; F =:= <<"trunc">> ->
    {Y,Bs1} = bld(A, Bs),
    {V,Bs2} = fix_to_int(binary_to_atom(F, latin1), Y, Bs1),
    set(X, V, Bs2);
%% built in integer functions (fixme)
bld(X,{p,<<"abs">>,[A]}, Bs) ->
    {Y,Bs1} = bld(A, Bs),
    operation1('abs',X,Y,Bs1);
bld(X,{p,<<"min">>,[A,B]}, Bs) ->
    {A1,Bs1} = bld(A, Bs),
    {B1,Bs2} = bld(B, Bs1),
    operation2('min',X,A1,B1,Bs2);
bld(X,{p,<<"max">>,[A,B]}, Bs) ->
    {A1,Bs1} = bld(A, Bs),
    {B1,Bs2} = bld(B, Bs1),
    operation2('max',X,A1,B1,Bs2);
bld(_X, V={p,P,Args}, Bs) ->
    Arity = length(Args),
    case varp:find_decl(P,Bs#bs.decls,icase(Bs)) of
	error when P =:= <<"inf">>, Args =:= [] ->
	    %% the float754 infinity, unless the user has an inf of their own
	    case is_definition(P, Bs) of
		true -> variable(V, Bs);
		false -> {{flo,inf}, Bs}
	    end;
	error ->
	    %% a name with a definition is a macro, not a variable.
	    %% declaring it as a boolean here would fix its arity and
	    %% stop the same name being defined for several arities.
	    case is_definition(P, Bs) of
		true ->
		    variable(V, Bs);
		false when Arity > 0, ?is_meta_function(P) ->
		    %% a built in meta function in formula position,
		    %% byte(msg, i) == 98: its value as a constant
		    bld(eval_meta({call,P,Args}, Bs), Bs);
		false when Arity =:= 0, is_map_key(P, Bs#bs.meta) ->
		    %% a bound meta variable used as a value, "A*B == n":
		    %% the scanner makes no difference between P and n,
		    %% so this is where a small letter name becomes its
		    %% number (a declared symbol of the same name wins)
		    bld(maps:get(P, Bs#bs.meta), Bs);
		false ->
		    warn_undeclared(P, Arity, Bs),
		    Decls1 = maps:put(P,{bool,Arity,1},Bs#bs.decls),
		    variable(V, Bs#bs { decls = Decls1 })
	    end;
	{ok,{bool,Arity1,1}} when Arity =/= Arity1 ->
	    error({arity_mismatch,P});
	{ok,{bool,Arity,1}} ->
	    variable({p,P,Args}, Bs);
	{ok,{PType,_Arity,Size}} ->
	    var_vector(PType,V,Size,Bs)
    end;
bld(_X,{PType0,SExpr0,PExpr},Bs) when ?is_vec_type(PType0) ->
    SExpr = decl_width(PType0, SExpr0, Bs),
    PType = decl_type(PType0, SExpr, Bs),
    if is_atom(PExpr) ->
	    Vn = atom_to_list(PExpr),
	    case maps:find(Vn,Bs#bs.meta) of
		error ->
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
%% an already built value, injected when a circuit body is instantiated
bld(X,{value,V}, Bs) ->
    set(X, V, Bs);
bld(_X,{expr,Expr}, Bs) ->
    W = eval_meta(Expr,Bs),
    if W >=0 ->
	    N = varp_math:unsigned_size(W),
	    const_vector(uint,W,N,Bs);
       W < 0 ->
	    N = varp_math:signed_size(W),
	    const_vector(int,W,N,Bs)
    end;
bld(X,{array,Fs}, Bs) ->
    %% an array used as a value is its elements as a vector
    bld(X,{vec,Fs}, Bs);
bld(_X,{vec,Fs}, Bs) ->
    {Ys,Bs1} = bld_list(Fs, Bs),
    Ys1 = join_vector(Ys),
    {{bit,length(Ys1),[bit(Y)||Y <- Ys1]},Bs1};

bld(X,{bitindex,A,I},Bs) ->
    I1 = eval_meta(I,Bs),
    case A of
	{p,P,[]} when not is_map_key(P, Bs#bs.decls) ->
	    %% "define K [..]; K[i]": the element, built as a formula
	    case find_prop_def(P, Bs#bs.defs) of
		{array,Elems} ->
		    bld(X, array_element(P, Elems, I1), Bs);
		_ ->
		    variable({index,A,I1}, Bs)
	    end;
	{p,P,_Ps} ->  %% check if declared
	    case varp:find_decl(P, Bs#bs.decls, icase(Bs)) of
		error ->
		    variable({index,A,I1}, Bs);
		{ok,{PType,_,PSize}} ->
		    case var_vector(PType,A,PSize,Bs) of
			{{uint,N,Ys},Bs1} -> {select_bool(I1,N,Ys), Bs1};
			{{int,N,Ys},Bs1}  -> {select_bool(I1,N,Ys), Bs1};
			{{bit,N,Ys},Bs1}  -> {select_bool(I1,N,Ys), Bs1};
			{{bool,Y},Bs1}    -> {{bool,Y},Bs1}
		    end
	    end;
	_ ->
	    case bld(A, Bs) of
		{{uint,N,Ys},Bs1} -> {select_bool(I1,N,Ys), Bs1};
		{{int,N,Ys},Bs1}  -> {select_bool(I1,N,Ys), Bs1};
		{{bit,N,Ys},Bs1}  -> {select_bool(I1,N,Ys), Bs1};
		{{bool,Y},Bs1}    -> {{bool,Y},Bs1}
                %% Y -> {select_bool(I1,1,[Y]),Bs}
	    end
    end;

bld(_X,{bitrange,A,I,J,S},Bs) ->
    I1 = eval_meta(I,Bs),
    J1 = eval_meta(J,Bs),
    S1 = eval_meta(S,Bs),
    case bld(A, Bs) of
	{{uint,N,Ys}, Bs1} -> {select_range(I1,J1,S1,N,Ys), Bs1};
	{{int,N,Ys}, Bs1}  -> {select_range(I1,J1,S1,N,Ys), Bs1};
	{{bit,N,Ys}, Bs1}  -> {select_range(I1,J1,S1,N,Ys), Bs1};
	{{bool,Y}, Bs1}    -> {select_range(I1,J1,S1,1,[Y]), Bs1}
    end;

%% Fixme: implement shift for variable argument
bld(X,{'shl',A,K},Bs) ->
    {Y,Bs1} = bld(A,Bs),
    {Z,Bs2} = bld(K,Bs1),
    operation2('shl',X,Y,Z,Bs2);
bld(X,{'rol',A,K},Bs) ->
    {Y,Bs1} = bld(A,Bs),
    {Z,Bs2} = bld(K,Bs1),
    operation2('rol',X,Y,Z,Bs2);
bld(X,{'shr',A,K},Bs) ->
    {Y,Bs1} = bld(A,Bs),
    {Z,Bs2} = bld(K,Bs1),
    operation2('shr',X,Y,Z,Bs2);
bld(X,{'ror',A,K},Bs) ->
    {Y,Bs1} = bld(A,Bs),
    {Z,Bs2} = bld(K,Bs1),
    operation2('ror',X,Y,Z,Bs2);

bld(_X,{cnf,{[],[],_Sections}},Bs) ->
    bld(false, Bs);
bld(_X,{cnf,{Vars,_Clauses,_Sections,Cs}},Bs) 
  when is_list(Cs) ->
    Bs1 = build_cnf(Cs,Vars,Bs),
    {{bool,?T}, Bs1};

bld(_X,{snf,{[],[],_Sections}},Bs) ->
    bld(false, Bs);
bld(_X,{snf,{_Vars,_Clauses,_Sections,Cs}},Bs) 
  when is_list(Cs) ->
    Bs1 = build_snf(Cs, Bs),
    {{bool,?T}, Bs1};

bld(X,{subst,Rx,Py,F},Bs) ->
    Bs1 = Bs#bs { subst = [{Rx,Py}|Bs#bs.subst]},
    bld(X,F,Bs1);
bld(X,{subst,SList,F},Bs) ->
    Bs1 = Bs#bs { subst = SList++Bs#bs.subst},
    bld(X,F,Bs1);

bld(_X,{lop,':=',L,R}, Bs) ->
    {Y,Bs1} = bld(R, Bs),
    operation1(':=',L,Y,Bs1);
bld(_X,{lop,'=',L,R={p,F,[_]}}, Bs) when ?is_typed_by_target(F) ->
    %% X = wrap(E), X = cast(E): the destination gives the type
    {Lv,Bs1} = bld(L, Bs),
    bld(Lv, R, Bs1);
bld(_X,{lop,'=',L,R}, Bs) ->
    {Y,Bs1} = bld(R, Bs),
    operation1('=',L,Y,Bs1);
bld(X,{lop,Op,A}, Bs) ->
    {Y,Bs1} = bld(A, Bs),
    operation1(Op, X, Y, Bs1);
bld(X,{lop,Op,A,{p,F,[E]}}, Bs) when (Op =:= 'eq' orelse Op =:= 'neq'),
				     ?is_typed_by_target(F) ->
    %% A == wrap(E), A == cast(E): the other side gives the type
    case A of
	{p,G,[_]} when ?is_typed_by_target(G) ->
	    error({wrap_type_unknown, "wrap(E) or cast(E) on both sides"});
	_ ->
	    {Y,Bs1} = bld(A, Bs),
	    {Z,Bs2} = bld({p,F,[E,{type_of,Y}]}, Bs1),
	    operation2(Op,X,Y,Z,Bs2)
    end;
bld(X,{lop,Op,A={p,F,[_]},B}, Bs) when (Op =:= 'eq' orelse Op =:= 'neq'),
				      ?is_typed_by_target(F) ->
    bld(X,{lop,Op,B,A}, Bs);
bld(X,_Bld={lop,Op,A,B}, Bs) ->
    ?dbg1("op = ~p\n", [_Bld]),
    {Y,Bs1} = bld(A, Bs),
    {Z,Bs2} = bld(B, Bs1),
    operation2(Op,X,Y,Z,Bs2);
bld(X,_Bld={lop,ite,C,T,E}, Bs) ->
    ?dbg1("op = ~p\n", [_Bld]),
    %% a condition known when building picks its branch and the other
    %% is never built: that is what ends a recursive circuit,
    %% "(n == 1) ? a[0] : u2b(..) + u2b(..)"
    case bld(C, Bs) of
	{{bool,?T},Bs1} -> bld(X, T, Bs1);
	{{bool,?F},Bs1} -> bld(X, E, Bs1);
	{Cf,Bs1} ->
	    {Tf,Bs2} = bld(T, Bs1),
	    {Ef,Bs3} = bld(E, Bs2),
	    ite(X,Cf,Tf,Ef,Bs3)
    end;

bld(X,{'ALL',Ys}, Bs) ->
    {Ys1,Bs1} = bld_args(Ys,Bs),
    all(X,Ys1,Bs1);
bld(X,{'ANY',Ys}, Bs) ->
    {Ys1,Bs1} = bld_args(Ys,Bs),
    any(X,Ys1,Bs1);
bld(X,{'NONE',Ys}, Bs) ->
    {Ys1,Bs1} = bld_args(Ys,Bs),
    none(X,Ys1,Bs1);
bld(X,{'ONE',Ys}, Bs) ->
    {Ys1,Bs1} = bld_args(Ys,Bs),
    one(X,Ys1,Bs1);
bld(X,{'SUM',Ys}, Bs) ->
    {Ys1,Bs1} = bld_args(Ys,Bs),
    sum(X,Ys1,Bs1);
bld(X,{'PROD',Ys}, Bs) ->
    {Ys1,Bs1} = bld_args(Ys,Bs),
    prod(X,Ys1,Bs1);
bld(X,{'PARITY',Ys}, Bs) ->
    {Ys1,Bs1} = bld_args(Ys,Bs),
    Y = varp_circuit:parity(Bs1#bs.vp,X,circuit_args(Ys1)),
    {{bool,Y},Bs1};
bld(X,{'ODD',Ys}, Bs) ->
    {Ys1,Bs1} = bld_args(Ys,Bs),
    Y = varp_circuit:parity(Bs1#bs.vp,X,circuit_args(Ys1)),
    {{bool,Y},Bs1};
bld(X,{'EVEN',Ys}, Bs) ->
    {Ys1,Bs1} = bld_args(Ys,Bs),
    Y = varp_circuit:parity(Bs1#bs.vp,X,circuit_args(Ys1)),
    {{bool,lnot(Y)},Bs1};
%% Quatifer version
bld(X,{{'ALL',Qs}, F}, Bs) ->
    {Ys,Bs1} = build_quant(F,Qs,Bs),
    all(X,Ys,Bs1);
bld(X,{{'ANY',Qs},F}, Bs) ->
    {Ys,Bs1} = build_quant(F,Qs,Bs),
    any(X,Ys,Bs1);
bld(X,{{'NONE',Qs},F}, Bs) ->
    {Ys,Bs1} = build_quant(F,Qs,Bs),
    none(X,Ys,Bs1);
bld(X,{{'ONE',Qs},F}, Bs) ->
    {Ys,Bs1} = build_quant(F,Qs,Bs),
    eqk(1,X,Ys,Bs1);

bld(X,{{'EQ',[X1|Qs]},F}, Bs) ->
    K = eval_meta(X1,Bs),
    {Ys,Bs1} = build_quant(F,Qs,Bs),
    if is_integer(K),K >= 0 ->
	    eqk(K,X,Ys, Bs1)
    end;
bld(X,{{'NEQ',[X1|Qs]},F}, Bs) ->
    K = eval_meta(X1,Bs),
    {Ys,Bs1} = build_quant(F,Qs,Bs),
    if is_integer(K),K >= 0 ->
	    neqk(K,X,Ys, Bs1)
    end;
bld(X,{{'GT',[X1|Qs]},F}, Bs) ->
    K = eval_meta(X1,Bs),
    {Ys,Bs1} = build_quant(F,Qs,Bs),
    if is_integer(K),K >= 0 ->
	    gtk(K,X,Ys,Bs1)
    end;
bld(X,{{'GTE',[X1|Qs]},F}, Bs) ->
    K = eval_meta(X1,Bs),
    {Ys,Bs1} = build_quant(F,Qs,Bs),
    if K =< 0 ->            %% at least none is always true
	    set(X,{bool,?T},Bs1);
       is_integer(K) ->
	    gtk(K-1,X,Ys,Bs1)
    end;
bld(X,{{'LT',[X1|Qs]},F}, Bs) ->
    K = eval_meta(X1,Bs),
    {Ys,Bs1} = build_quant(F,Qs,Bs),
    N = length(Ys),
    if K =< 0 ->            %% less than none is never true
	    set(X,{bool,?F},Bs1);
       K =:= 1 ->
	    none(X,Ys,Bs1);
       K > N ->             %% less than more than all is always true
	    set(X,{bool,?T},Bs1);
       is_integer(K) ->
	    gtk(N-K,X,lists:map(fun(Y) -> negate(Y) end, Ys), Bs1)
    end;
bld(X,{{'LTE',[X1|Qs]},F}, Bs) ->
    K = eval_meta(X1,Bs),
    {Ys,Bs1} = build_quant(F,Qs,Bs),
    N = length(Ys),
    if K < 0 ->
	    set(X,{bool,?F},Bs1);
       K =:= 0 ->
	    none(X,Ys,Bs1);
       K >= N ->            %% at most all is always true
	    set(X,{bool,?T},Bs1);
       is_integer(K) ->
	    gtk(N-K-1,X,lists:map(fun(Y) -> negate(Y) end, Ys), Bs1)
    end;
bld(X,{{'SUM',Qs}, F}, Bs) ->
    {Xs,Bs1} = build_iquant(F,Qs,Bs),
    sum(X,Xs,Bs1);
bld(X,{{'PROD',Qs}, F}, Bs) ->
    {Xs,Bs1} = build_iquant(F,Qs,Bs),
    prod(X,Xs,Bs1);
bld(X,{{'PARITY',Qs}, F}, Bs) ->
    {Xs,Bs1} = build_quant(F,Qs,Bs),
    Y = varp_circuit:parity(Bs1#bs.vp,X,circuit_args(Xs)),
    {{bool,Y},Bs1};
bld(X,{{'ODD',Qs}, F}, Bs) ->
    {Xs,Bs1} = build_quant(F,Qs,Bs),
    Y = varp_circuit:odd(Bs1#bs.vp,X,circuit_args(Xs)),
    {{bool,Y},Bs1};
bld(X,{{'EVEN',Qs}, F}, Bs) ->
    {Xs,Bs1} = build_quant(F,Qs,Bs),
    Y = varp_circuit:even(Bs1#bs.vp,X,circuit_args(Xs)),
    {{bool,Y},Bs1};
bld(X,{cop, Name, Args}, Bs) ->
    {Value,Bs1} = call_circuit(Name, Args, Bs),
    set(X, Value, Bs1).

%% a circuit of the file, or of the library (imported now when the
%% scanner never saw the name, as with --ops lib)
call_circuit(Name, Args, Bs) ->
    case find_circuit_def(Name, Bs#bs.circuits, icase(Bs)) of
	{ok, Circuit} ->
	    build_circuit(Circuit, Args, Bs);
	error ->
	    case varp_lib:circuit(Name) of
		{ok, Circuit} -> build_circuit(Circuit, Args, Bs);
		error -> error({circuit_undefined, Name})
	    end
    end.

%% build one or more arguments: a list of them, a vector whose bits
%% are the arguments, or a single boolean ("[ANY](A)", the grammar
%% gives one lexpr without a list around it)
bld_args(Fs,Bs) when is_list(Fs) ->
    bld_list(Fs, Bs);
bld_args(F,Bs) ->
    case bld(F, Bs) of
	{{bool,X}, Bs1} -> {[{bool,X}],Bs1};
	{{T,_N,Xs}, Bs1} when ?is_vec_type(T) -> {[{bool,X}||X<-Xs],Bs1}
    end.

bld_list(Fs, Bs) ->
    bld_list_(Fs, [], Bs).
    
bld_list_([F|Fs],Acc,Bs) ->
    {X,Bs1} = bld(F,Bs),
    bld_list_(Fs,[X|Acc],Bs1);
bld_list_([],Acc,Bs) ->
    {lists:reverse(Acc),Bs}.


%%
%% Build (instantiate) a circuit
%%
%%   circuit Name(in y,z; in ci; return x; out co) { ... }
%%
%% A circuit is a closed module.  Every name that occurs in the body is
%% local to the instance and is given the unique symbol prefix
%% "<Name>#<Seq>." so that locals show up in models as e.g. adder#3.s1
%% The only names that are NOT localised are
%%
%%   - the formal parameters,  they are replaced by the value of the
%%     corresponding argument at the call site
%%   - names that match a 'define' macro
%%   - (nested) circuit names
%%
%% Arguments bind to the 'in' and 'out' parameters, in declaration order.
%% Positional arguments fill the parameters from the left, named arguments
%% (name = expr) bind by parameter name, and a parameter with a default
%% (in a3 = false) may be left out.  Since an argument is built once and
%% then substituted as a value, assigning to an 'out' parameter inside the
%% body constrains the caller's variable, which is the point of 'out'.
%%
%% The value of the call is the value of the 'return' parameter, or
%% true when the circuit has no return parameter.
%%
build_circuit({circuit,Name,Params,Defs}, Args, Bs0) ->
    {Ins0,Outs0,Return0} = circuit_params(Name, Params),
    %% a:32/fixpoint parameters: the fraction width settled now
    Fx = fun(undefined) -> undefined;
	    (F=#{type := T}) ->
		 F#{ type => decl_type(T, maps:get(size, F, undefined), Bs0) }
	 end,
    {Ins,Outs,Return} = {[Fx(F) || F <- Ins0], [Fx(F) || F <- Outs0], Fx(Return0)},
    %% the size variables of the parameters (a:n) are local to this
    %% instance: unbound on entry, bound by the arguments, and the
    %% caller's bindings come back afterwards, so that a circuit can
    %% call another with sizes of its own (mul calling add)
    Sizes = [Sz || #{ size := Sz } <- Ins ++ Outs ++ [R || R <- [Return],
							   R =/= undefined],
		   is_binary(Sz)],
    Meta0 = Bs0#bs.meta,
    Bs0_1 = Bs0#bs { meta = maps:without(Sizes, Meta0) },
    {Bnd,Bs1} = circuit_bind(Name, Ins++Outs, Args, Bs0_1, Meta0),
    {Prefix,Bs2} = circuit_prefix(Name, Bs1),
    {RetName,Bs3} = circuit_return(Return, Prefix, Bs2),
    %% a local of the body (declare, define) or a parameter shadows a
    %% meta variable of the same name, like a declared symbol does at
    %% the top level: "[A s=1..n] ... X + Y" must not turn the s of
    %% op_add(...; return s) into the caller's step number
    Formals = [N || #{name := N} <- Ins ++ Outs ++ [R || R <- [Return],
							 R =/= undefined]],
    Meta = maps:without(circuit_locals(Defs) ++ Formals, Bs3#bs.meta),
    Body = circuit_rename(Defs, maps:from_list(Bnd), Prefix, Bs3#bs.defs,
                          Meta),
    Bs4 = build_circuit_body(Body, Bs3),
    {Value,Bs5} = circuit_value(RetName, Bs4),
    %% locals and nested circuit definitions do not leak into the caller,
    %% but declarations made for the arguments (in Bs1) do.
    {Value, Bs5#bs { decls = Bs1#bs.decls, circuits = Bs1#bs.circuits,
		     locals = Bs1#bs.locals, meta = Meta0 }}.

%% the names a circuit body declares or defines
circuit_locals(Defs) ->
    lists:append(
      [case D of
	   {declare,Ds} -> [P || Decl <- Ds, P <- [local_name(Decl)], P =/= undefined];
	   {define,{p,P,_},_} -> [P];
	   _ -> []
       end || D <- Defs]).

local_name({visible,D}) -> local_name(D);
local_name({'=',D,_Default}) -> local_name(D);
local_name({{p,P,_},_Type,_Size}) -> P;
local_name({p,P,_}) -> P;
local_name(_) -> undefined.

%% split the parameter list into {In, Out, Return}
circuit_params(Name, Params) ->
    circuit_params(Name, Params, [], [], undefined).

circuit_params(Name, [{in,Ds}|Ps], In, Out, Ret) ->
    circuit_params(Name, Ps, In++[circuit_formal(Name,D) || D <- Ds], Out, Ret);
circuit_params(Name, [{out,Ds}|Ps], In, Out, Ret) ->
    circuit_params(Name, Ps, In, Out++[circuit_formal(Name,D) || D <- Ds], Ret);
circuit_params(Name, [{meta,Ds}|Ps], In, Out, Ret) ->
    Ms = [(circuit_formal(Name,D))#{ type => meta } || D <- Ds],
    circuit_params(Name, Ps, In++Ms, Out, Ret);
circuit_params(Name, [{return,D}|Ps], In, Out, undefined) ->
    circuit_params(Name, Ps, In, Out, circuit_formal(Name,D));
circuit_params(Name, [{return,_}|_], _In, _Out, _Ret) ->
    error({circuit_multiple_return, Name});
circuit_params(_Name, [], In, Out, Ret) ->
    {In, Out, Ret}.

%% #{ name, type, size, default }
circuit_formal(Name, {'=',D,Default}) ->
    F = circuit_formal(Name, D),
    F#{ default => Default };
circuit_formal(_Name, {{p,P,[]},Type,Size}) ->
    #{ name => P, type => Type, size => Size, default => undefined };
circuit_formal(_Name, {p,P,[]}) ->
    #{ name => P, type => bool, size => 1, default => undefined };
circuit_formal(Name, D) ->
    error({circuit_parameter, Name, D}).

%% bind the call arguments to the formal parameters
%% The argument expressions belong to the caller and are built with
%% the caller's meta bindings (CallerMeta): a circuit calling itself,
%% "u2b(a >> (n/2))", means the caller's n, not the fresh one of the
%% instance being bound.
circuit_bind(Name, Formals, Args, Bs, CallerMeta) ->
    {Named,Pos} =
	lists:partition(fun({'=',N,_}) -> is_binary(N);
			   (_) -> false
			end, Args),
    NamedMap = maps:from_list([{N,E} || {'=',N,E} <- Named]),
    if length(Pos) > length(Formals) ->
	    error({circuit_arity, Name, length(Args), length(Formals)});
       true ->
	    ok
    end,
    case maps:keys(NamedMap) -- [N || #{name := N} <- Formals] of
	[] -> ok;
	Unknown -> error({circuit_unknown_argument, Name, Unknown})
    end,
    circuit_bind_(Name, Formals, 1, length(Pos), Pos, NamedMap, [], Bs, CallerMeta).

circuit_bind_(Name, [F=#{name := N}|Fs], I, NPos, Pos, Named, Acc, Bs, CallerMeta) ->
    Expr =
	if I =< NPos ->
		case maps:is_key(N, Named) of
		    true -> error({circuit_duplicate_argument, Name, N});
		    false -> lists:nth(I, Pos)
		end;
	   true ->
		case maps:find(N, Named) of
		    {ok,E} -> E;
		    error ->
			case maps:get(default, F) of
			    undefined ->
				error({circuit_missing_argument, Name, N});
			    D -> D
			end
		end
	end,
    {V,Bs1} = case F of
		  #{ type := meta } ->
		      %% an integer at build time, bound as a meta
		      %% variable for the body (build_circuit restores
		      %% the caller's bindings afterwards)
		      Int = try eval_meta(Expr, Bs#bs{ meta = CallerMeta })
			    catch error:{unbound, Var} -> {variable, Var}
			    end,
		      is_integer(Int) orelse error({circuit_meta_argument, Name, N, Int}),
		      {{meta,Int}, Bs#bs{ meta = maps:put(N, Int, Bs#bs.meta) }};
		  _ ->
		      circuit_arg(F, Expr, Bs, CallerMeta)
	      end,
    circuit_bind_(Name, Fs, I+1, NPos, Pos, Named, [{N,V}|Acc], Bs1, CallerMeta);
circuit_bind_(_Name, [], _I, _NPos, _Pos, _Named, Acc, Bs, _CallerMeta) ->
    {lists:reverse(Acc), Bs}.

%% Build one argument.  When the parameter is typed and the argument is a
%% plain, not yet declared, symbol then the parameter type/size is used to
%% declare it in the caller scope.  A size that is a bare meta variable
%% (a:n) is unified with the width of the argument, whatever the argument
%% is: a declared vector, an expression or a constant.  The first use
%% binds it, later uses must agree.
circuit_arg(#{type := Type, size := Size}, Expr={p,P,As}, Bs, CallerMeta)
  when Type =/= bool ->
    Bs1 = case varp:find_decl(P, Bs#bs.decls, icase(Bs)) of
	      error ->
		  %% a macro ("define seed 0xffff;") is expanded by
		  %% variable/2, anything else is an undeclared vector
		  %% of the parameter's width
		  case maps:is_key({P,length(As)}, Bs#bs.defs) of
		      false ->
			  N = eval_meta(Size, Bs),
			  Decls = maps:put(P, {Type,length(As),N}, Bs#bs.decls),
			  Bs#bs { decls = Decls };
		      true ->
			  Bs
		  end;
	      {ok,_Decl} ->
		  Bs
	  end,
    {V, Bs2} = bld_arg(Expr, Bs1, CallerMeta),
    {V, unify_size(Size, V, Bs2)};
circuit_arg(#{type := Type, size := Size}, Expr, Bs, CallerMeta) when Type =/= bool ->
    {V, Bs1} = bld_arg(Expr, Bs, CallerMeta),
    {V, unify_size(Size, V, Bs1)};
circuit_arg(_F, Expr, Bs, CallerMeta) ->
    bld_arg(Expr, Bs, CallerMeta).

%% an argument built in the caller's meta scope, the instance's kept
bld_arg(Expr, Bs, CallerMeta) ->
    {V, Bs1} = bld(Expr, Bs#bs{ meta = CallerMeta }),
    {V, Bs1#bs{ meta = Bs#bs.meta }}.

%% a:n against a value of width N
unify_size(Name, {T,N,_}, Bs) when is_binary(Name), ?is_vec_type(T) ->
    unify_meta(Name, N, Bs);
unify_size(Name, {bool,_}, Bs) when is_binary(Name) ->
    unify_meta(Name, 1, Bs);
unify_size(_Size, _V, Bs) ->
    Bs.

unify_meta(Name, N, Bs) ->
    case maps:find(Name, Bs#bs.meta) of
	error -> Bs#bs { meta = maps:put(Name, N, Bs#bs.meta) };
	{ok,N} -> Bs;
	{ok,Other} -> error({unable_to_unify, Name, Other, N})
    end.

%% unique symbol prefix for the locals of this instance
circuit_prefix(Name, Bs) ->
    Seq = Bs#bs.cseq + 1,
    Prefix = iolist_to_binary([Name,"#",integer_to_list(Seq),"."]),
    {Prefix, Bs#bs { cseq = Seq }}.

%% the return parameter is a fresh local
circuit_return(undefined, _Prefix, Bs) ->
    {undefined, Bs};
circuit_return(#{name := N, type := bool}, Prefix, Bs) ->
    {<<Prefix/binary,N/binary>>, Bs};
circuit_return(#{name := N, type := Type, size := Size}, Prefix, Bs) ->
    RName = <<Prefix/binary,N/binary>>,
    Sz = eval_meta(Size, Bs),
    {RName, Bs#bs { decls = maps:put(RName,{Type,0,Sz},Bs#bs.decls) }}.

circuit_value(undefined, Bs) ->
    {{bool,?T}, Bs};
circuit_value(RName, Bs) ->
    bld({p,RName,[]}, Bs).

%% Rewrite the body: formal parameters become values, every other
%% predicate/variable name is prefixed, macros and circuit names are kept.
%% a quantifier binds names for its body: they are integers, not
%% locals, and are not renamed
circuit_rename({{Q,Binds},Body}, Env, Prefix, Defs, Meta) when is_atom(Q),
							  is_list(Binds) ->
    Bound = [V || {op,'=',V,_} <- Binds, is_binary(V)],
    Env1 = maps:merge(Env, maps:from_list([{V,bound} || V <- Bound])),
    {{Q,circuit_rename(Binds, Env, Prefix, Defs, Meta)},
     circuit_rename(Body, Env1, Prefix, Defs, Meta)};
circuit_rename({p,P,As}, Env, Prefix, Defs, Meta) ->
    As1 = circuit_rename(As, Env, Prefix, Defs, Meta),
    case maps:find(P, Env) of
	{ok,bound} ->
	    {p,P,As1};
	{ok,{meta,I}} when As1 =:= [] ->
	    {const,I};
	{ok,V} when As1 =:= [] ->
	    {value,V};
	{ok,_} ->
	    error({circuit_parameter_arity, P});
	error ->
	    case maps:is_key({P,length(As1)}, Defs) orelse
		builtin_function(P, length(As1)) of
		true  -> {p,P,As1};
		false ->
		    %% a size parameter of this instance (a:n) or a meta
		    %% variable of the caller used as a value, "x = n;"
		    %% or "(i < n) ? ..": its number, as at the top level
		    case maps:find(P, Meta) of
			{ok,I} when As1 =:= [], is_integer(I) -> {const,I};
			_ -> {p,<<Prefix/binary,P/binary>>,As1}
		    end
	    end
    end;
%% a nested circuit definition keeps its own scope, it is renamed when
%% it is instantiated
circuit_rename(C={circuit,_Name,_Params,_Body}, _Env, _Prefix, _Defs, _Meta) ->
    C;
circuit_rename({cop,Name,As}, Env, Prefix, Defs, Meta) ->
    {cop,Name,circuit_rename(As, Env, Prefix, Defs, Meta)};
circuit_rename(T, Env, Prefix, Defs, Meta) when is_tuple(T) ->
    list_to_tuple(circuit_rename(tuple_to_list(T), Env, Prefix, Defs, Meta));
circuit_rename([H|T], Env, Prefix, Defs, Meta) ->
    [circuit_rename(H, Env, Prefix, Defs, Meta) |
     circuit_rename(T, Env, Prefix, Defs, Meta)];
circuit_rename(X, _Env, _Prefix, _Defs, _Meta) ->
    X.

%% the arithmetic functions bld/3 knows: not locals of a circuit body
builtin_function(<<"abs">>, 1) -> true;
builtin_function(<<"sqrt">>, 1) -> true;
builtin_function(<<"fma">>, 3) -> true;
builtin_function(<<"min">>, 2) -> true;
builtin_function(<<"max">>, 2) -> true;
builtin_function(<<"floor">>, 1) -> true;
builtin_function(<<"ceil">>, 1) -> true;
builtin_function(<<"round">>, 1) -> true;
builtin_function(<<"trunc">>, 1) -> true;
builtin_function(<<"isnan">>, 1) -> true;
builtin_function(<<"isinf">>, 1) -> true;
builtin_function(<<"wrap">>, 1) -> true;
builtin_function(<<"wrap">>, 2) -> true;
builtin_function(<<"fits">>, 2) -> true;
builtin_function(<<"cast">>, 1) -> true;
builtin_function(<<"cast">>, 2) -> true;
builtin_function(_, _) -> false.

build_circuit_body([{define,{p,Name,Ps},Def}|Body], Bs) ->
    %% a macro of the instance; its body was renamed with the rest
    Formals = [P || P <- Ps],
    Defs = maps:update_with({Name,length(Formals)},
			    fun(L) -> L ++ [{Formals,Def}] end,
			    [{Formals,Def}], Bs#bs.defs),
    build_circuit_body(Body, Bs#bs{ defs = Defs });
build_circuit_body([{declare,Ds}|Body], Bs) ->
    %% "declare t:4 /visible;": the (prefixed) name is excepted from
    %% hiding and ends up in the symbol table like a top level name
    Vis = [local_name(D) || {visible,D} <- Ds],
    Ds1 = [case D of {visible,D1} -> D1; _ -> D end || D <- Ds],
    Visible = maps:merge(Bs#bs.visible, maps:from_list([{N,true} || N <- Vis])),
    case varp:add_decls(Ds1, Bs#bs.decls, Bs) of
	{ok,Decls} ->
	    build_circuit_body(Body, Bs#bs { decls = Decls, visible = Visible });
	{error,Reason} -> error(Reason)
    end;
build_circuit_body([C={circuit,Name,_Params,_Defs}|Body], Bs) ->
    Circuits = maps:put(Name, C, Bs#bs.circuits),
    build_circuit_body(Body, Bs#bs { circuits = Circuits });
build_circuit_body([{lop,'=',OExpr,LExpr}|Body], Bs0) ->
    {_X,Bs1} = build_assign(OExpr, LExpr, Bs0),
    build_circuit_body(Body, Bs1);
build_circuit_body([{constraint,F}|Body], Bs0) ->
    build_circuit_body(Body, assert_formula(F, Bs0));
build_circuit_body([F|Body], Bs0) ->
    build_circuit_body(Body, assert_formula(F, Bs0));
build_circuit_body([], Bs) ->
    Bs.

%% a bare formula in a circuit body must hold
assert_formula(F, Bs0) ->
    case bld(F, Bs0) of
	{{bool,?T},Bs1} -> Bs1;
	{{bool,?F},_Bs1} -> throw(contradiction);
	{{bool,L},Bs1} ->
	    varp_circuit:clause(Bs1#bs.vp, [L]),
	    Bs1;
	{{_Type,_N,Ls},Bs1} ->
	    %% a vector is true when it is non zero
	    varp_circuit:clause(Bs1#bs.vp, Ls),
	    Bs1;
	{_,Bs1} ->
	    Bs1
    end.


%% build  [ oexpr = lexpr ';' ]
%% here we could/should generate Oexpr then pass the 
%% output to the left expression to be used as gate/circuit output?
build_assignment_defs([F={cop,_Name,_Args}|Assignments], Bs0) ->
    {_,Bs1} = bld(F, Bs0),
    build_assignment_defs(Assignments, Bs1);
build_assignment_defs([{constraint,F}|Assignments], Bs0) ->
    %% a quantified assignment at the file level
    build_assignment_defs(Assignments, assert_formula(F, Bs0));
build_assignment_defs([{lop,'=',OExpr,LExpr}|Assignments], Bs0) ->
    {_X,Bs1} = build_assign(OExpr, LExpr, Bs0),
    build_assignment_defs(Assignments, Bs1);
build_assignment_defs([], Bs) ->
    Bs.

%% OExpr = LExpr
%%
%% The left hand side is built first and then handed to bld/3 as the
%% target, so that a gate can be generated directly into it.  Not every
%% expression can do that (a plain variable reference, a constant, a bit
%% selection, ...) - those return a value of their own and are tied to
%% the target here instead.
build_assign(OExpr, LExpr, Bs0) ->
    {X,Bs1} = bld(OExpr, Bs0),
    case bld(X, LExpr, Bs1) of
	{X, Bs2} ->             %% built into the target
	    {X, Bs2};
	{Y, Bs2} ->             %% target was ignored, constrain it now
	    set(X, Y, Bs2)
    end.

%%
%% Special build of cnf/snf
%% in the cnf case assume that the clause are the
%% literal integers
%% in the snf case the literals are symbols
%%
build_cnf(Cs,Vars,Bs) ->
    %% CNF only works as first formula! variables
    %% must be numerated 1..Vars
    {1,Vars} = varp_nif:add_variables(Bs#bs.vp, Vars, true), %% yes, so match!
    build_cnf_(Cs, Vars, Bs).

build_cnf_([CL|CLs], Vars, Bs) ->
    use_clause(Bs#bs.vp, CL),
    try varp_circuit:clause(Bs#bs.vp, CL) of
	_IndexOrTrue ->
	    build_cnf_(CLs, Vars, Bs)
    catch
	thrown:_ ->
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
    end;
build_cnf_([],_Vars,Bs) ->
    Bs.



build_snf([CL|CLs], Bs) ->
    {Xs,Bs1} = bld_args(CL,Bs),
    Ls = [L || {bool,L} <- Xs],
    varp_circuit:clause(Bs1#bs.vp,Ls),
    build_snf(CLs, Bs1);
build_snf([], Bs) ->
    Bs.

use_clause(Vp, CL) ->
    lists:foreach(fun(Li) -> varp_nif:isused(Vp, abs(Li), true) end, CL).

%% boolean version
build_quant(Fs, Qs, Bs) when is_list(Fs), is_list(Qs) ->
    build_quant_list(Fs, Qs, Bs);
build_quant(F, Qs, Bs) when is_list(Qs) ->
    build_quant_(F, Qs, Bs).

build_quant_(F,[{op,'=',V,D}|Qs], Bs) ->
    Ds = eval_domain(D, Bs),
    build_quant_domain(F, V, Ds, Qs, Bs);
%% predicate expansion
build_quant_(_F, [{call,_Def,_Args}|_Qs], Bs) ->
    %% lookup Def
    {[], Bs};

build_quant_(F, [Expr|Qs], Bs) ->
    case eval_meta(Expr, Bs) of
	false -> {[],Bs};
	true -> build_quant_(F, Qs, Bs)
    end;
build_quant_(F, [], Bs) ->
    case bld(F, Bs) of
	{{T,_N,Xs}, Bs1} when ?is_vec_type(T) -> {[{bool,X}||X<-Xs],Bs1};
	{X,Bs1} -> {[X],Bs1}
    end.

build_quant_domain(F, Vn, [Y|Ys], Xs, Bs) when is_binary(Vn) ->
    Bs1 = push_meta(Vn, Y, Bs),
    {Zs1,Bs2} = build_quant_(F, Xs, Bs1),
    Bs3 = pop_meta(Bs2, Bs#bs.meta),
    {Zs2,Bs4} = build_quant_domain(F, Vn, Ys, Xs, Bs3),
    {Zs1++Zs2,Bs4};
%% fixme handle arbitrary vector!
build_quant_domain(F, V={vec,[Vn1,Vn2]},
		   [{vec,[Y1,Y2]}|Ys], Xs, Bs) when is_binary(Vn1),
						    is_binary(Vn2) ->
    ?dbg("Bind ~s=~w, ~s=~w\n", [Vn1,Y1,Vn2,Y2]),
    Bs1 = push_meta(Vn1, Y1, Bs),
    Bs2 = push_meta(Vn2, Y2, Bs1),
    {Zs1,Bs3} = build_quant_(F, Xs, Bs2),
    Bs4 = pop_meta(Bs3, Bs#bs.meta),
    {Zs2,Bs5} = build_quant_domain(F, V, Ys, Xs, Bs4),
    {Zs1++Zs2,Bs5};
%% fixme handle arbitrary vector! handle set/seqeuences properly
build_quant_domain(F, V={vec,[Vn1,Vn2]},
		   [[Y1,Y2]|Ys], Xs, Bs) when is_binary(Vn1), is_binary(Vn2) ->
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

build_iquant_(F,[{op,'=',V,D}|Qs], Bs) ->
    Ds = eval_domain(D, Bs),
    build_iquant_domain(F, V, Ds, Qs, Bs);
build_iquant_(F, [Expr|Qs], Bs) ->
    case eval_meta(Expr, Bs) of
	false -> {[],Bs};
	true -> build_iquant_(F, Qs, Bs)
    end;
build_iquant_(F, [], Bs) ->
    case bld(F, Bs) of
	{{bool,X},Bs1} -> {[{uint,1,[X]}], Bs1};
	{X,Bs1} -> {[X],Bs1}
    end.

build_iquant_domain(F, Vn, [Y|Ys], Xs, Bs) ->
    Bs1 = push_meta(Vn, Y, Bs),
    {Zs1,Bs2} = build_iquant_(F, Xs, Bs1),
    Bs3 = pop_meta(Bs2, Bs#bs.meta),
    {Zs2,Bs4} = build_iquant_domain(F, Vn, Ys, Xs, Bs3),
    {Zs1++Zs2,Bs4};
build_iquant_domain(_F, _Vn, [], _Xs, Bs) ->
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
       true -> [] %% lists:reverse(lists:seq(B1,A1))
    end;
eval_domain({call,<<"union">>,[A,B]}, Bs) ->
    A1 = eval_domain(A,Bs),
    B1 = eval_domain(B,Bs),
    ordsets:union(A1,B1);
eval_domain({call,<<"subtract">>,[A,B]}, Bs) ->
    A1 = eval_domain(A,Bs),
    B1 = eval_domain(B,Bs),
    ordsets:subtract(A1,B1);
eval_domain({call,<<"intersect">>,[A,B]}, Bs) ->
    A1 = eval_domain(A,Bs),
    B1 = eval_domain(B,Bs),
    ordsets:intersection(A1,B1);
eval_domain({call,<<"product">>,[A,B]}, Bs) ->
    A1 = eval_domain(A,Bs),
    B1 = eval_domain(B,Bs),
    [ [Ai,Bi] || Ai <- A1, Bi <- B1 ];
eval_domain({call,<<"subsets">>,[A]}, Bs) ->
    A1 = eval_domain(A,Bs),
    subsets(A1);
eval_domain({call,<<"subsets">>,[K,A]}, Bs) ->
    K1 = eval_meta(K,Bs),
    A1 = eval_domain(A,Bs),
    subsets(K1,A1);
eval_domain({call,<<"permutations">>,[A]}, Bs) ->
    A1 = eval_domain(A,Bs),
    permute(A1);
eval_domain({call,<<"zip">>,[A,B]}, Bs) ->
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

eval_meta(I, _Bs) when is_number(I) -> I;
eval_meta({const,V}, _Bs) -> V;
eval_meta({uint,_N,V}, _Bs) when is_integer(V) -> V;   %% a literal in a formula
eval_meta({int,_N,V}, _Bs) when is_integer(V) -> V;
eval_meta({range,A,B}, Bs) ->
    A1 = eval_meta(A,Bs),
    B1 = eval_meta(B,Bs),
    if A1 =< B1 -> lists:seq(A1, B1);
       true -> []
       %% true -> lists:reverse(lists:seq(B1,A1))
    end;
eval_meta(<<"true">>, _Bs)  -> true;
eval_meta(<<"false">>, _Bs) -> false;
eval_meta({p,ID,[]}, Bs) when is_binary(ID) -> eval_id(ID, Bs);
%% an argument expression of a circuit call in a meta position,
%% "op_rol(n - (m % n), X)": the formula operators as meta operators
eval_meta({lop,Op,A,B}, Bs) when is_atom(Op) -> eval_meta({op,Op,A,B}, Bs);
eval_meta({lop,Op,A}, Bs) when is_atom(Op) -> eval_meta({op,Op,A}, Bs);
eval_meta({p,F,As}, Bs) when is_binary(F) -> eval_meta({call,F,As}, Bs);  %% len(msg) in a define
eval_meta(ID, Bs) when is_binary(ID) -> eval_id(ID, Bs);
eval_meta({type,_,_}, _Bs) ->
    error({type_argument, "a type is an argument of wrap and fits only"});
eval_meta({call,F,As},Bs) ->
    case {F,eval_meta_list(As,Bs)} of
	{<<"factorial">>,[N]} -> varp_math:factorial(N);
	{<<"binom">>,[A,B]} -> varp_math:binom(A,B);
	{<<"sqrt">>,[A]}    -> math:sqrt(A);
	{<<"isqrt">>,[A]}   -> varp_math:isqrt(A);
	{<<"sqr">>,[A]}     -> A*A;
	{<<"nroot">>,[A,N]} -> varp_math:nroot(A,N);
	{<<"ln">>,[A]}      -> math:log(A);
	{<<"log">>,[A,N]}   -> math:log(A)/math:log(N);
	{<<"log2">>,[A]}    -> math:log(A)/math:log(2);
	{<<"log10">>,[A]}   -> math:log10(A);
	{<<"ilog2">>,[A]}   -> varp_math:ilog2(A);
	{<<"isize">>,[A]}   -> varp_math:signed_size(A);
	{<<"usize">>,[A]}   -> varp_math:unsigned_size(A);
	{<<"pi">>,[]}       -> math:pi();
	{<<"e">>,[]}        -> math:exp(1);
	{<<"pow">>,[A,B]}   -> 
	    if is_integer(A), is_integer(B) ->
		    varp_math:pow(A,B);
	       true ->
		    math:pow(A,B)
	    end;
	{<<"sin">>,[A]}     -> math:sin(A);
	{<<"cos">>,[A]}     -> math:cos(A);
	{<<"trunc">>,[A]}   -> trunc(A);
	{<<"round">>,[A]}   -> round(A);
	{<<"abs">>,[A]}     -> abs(A);
	{<<"max">>,[A,B]}   -> max(A,B);
	{<<"min">>,[A,B]}   -> min(A,B);
	{<<"sum">>,As}      ->
	    lists:foldl(fun(Ai,Sum) -> eval_meta(Ai,Bs)+Sum end, 0, As);
	%% strings, from a binding such as msg="hello world"
	{<<"len">>,[S]} when is_list(S) -> length(S);
	{<<"byte">>,[S,I]} when is_list(S), is_integer(I) ->
	    %% byte I of the string, 0 past the end
	    if I >= 0, I < length(S) -> lists:nth(I+1, S);
	       true -> 0
	    end;
	%% ordsets
	{<<"union">>,[A,B]}   -> ordsets:union(A,B);
	{<<"subtract">>,[A,B]}   -> ordsets:subtract(A,B);
	{<<"intersect">>,[A,B]}   -> ordsets:intersection(A,B);
	{<<"product">>,[A,B]}   -> [ [Ai,Bi] || Ai <- A, Bi <- B ];
	%% function symbol
	{Func,As1} when is_binary(Func) -> {f,Func,As1}
    end;

eval_meta({op,Op,A,B},Bs) ->
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
eval_meta(Ls, Bs) when is_list(Ls) -> %% FIXME!?
    eval_meta_list(Ls, Bs);
eval_meta({vec,Ls}, Bs) -> %% literal vector
    eval_meta_list(Ls, Bs);
eval_meta({array,Ls}, Bs) ->
    eval_meta_list(Ls, Bs);
eval_meta({bitindex,{p,P,[]},I}, Bs) ->
    case find_prop_def(P, Bs#bs.defs) of
	{array,Elems} -> eval_meta(array_element(P, Elems, eval_meta(I,Bs)), Bs);
	_ -> error({not_an_array, P})
    end;
eval_meta({op,'ite',C,A,B},Bs) ->
    case eval_meta(C,Bs) of
	true -> eval_meta(A,Bs);
	false -> eval_meta(B,Bs)
    end;
eval_meta({op,Op,A},Bs) ->
    case {Op,eval_meta(A,Bs)} of
	{'neg',A1} -> -A1;
	{'pos',A1} -> +A1;
	{'bnot',A1} ->  bnot A1;
	{'not',A1} -> not A1
    end.

eval_id(Vn, Bs) when is_binary(Vn) ->
    case maps:find(Vn,Bs#bs.meta) of
	error ->
	    case maps:find(Vn, Bs#bs.literals) of
		{ok,true} ->
		    Vn;
		error ->
		    case find_prop_def(Vn, Bs#bs.defs) of
			false ->
			    error({unbound, Vn});
			Def ->
			    eval_meta(Def, Bs)
		    end
	    end;
	{ok,W} -> 
	    W
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
    

lookup_or_add_decl({p,P,Ps},PType0,Size,Bs) ->
    PType = decl_type(PType0, Size, Bs),
    Arity = length(Ps),
    case varp:find_decl(P,Bs#bs.decls,icase(Bs)) of
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
	    Decls1 = maps:put(P, Type, Bs#bs.decls),
	    {ok, Type, Bs#bs { decls = Decls1 }}
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
    V = const_vector_(N-1,Type,N,[],Value),
    %% io:format("const vector : ~p\n", [V]),
    {V,Bs}.

const_vector(Type,Value,N) when is_integer(Value), is_integer(N) ->
    const_vector_(N-1,Type,N,[],Value).

const_vector(Type,Value) when is_integer(Value) ->
    N = case Type of
	    uint -> varp_math:unsigned_size(Value);
	    bit  -> varp_math:unsigned_size(Value);
	    int -> varp_math:signed_size(Value);
	    {fix,_} -> varp_math:signed_size(Value);
	    {float,E,M} -> 1+E+M
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
-ifdef(not_used).
alias_vector(Bs,T,V,Size,Xs) ->
    N = eval_meta(Size,Bs),
    alias_vector_(Bs,0,T,N,Xs,V).

alias_vector_(Bs,I,T,N,[X|Xs],V) ->
    Bs1 = alias({T,V,N,I},X,Bs),
    alias_vector_(Bs1,I+1,T,N,Xs,V);
alias_vector_(Bs,_I,_T,_N,[],_V) ->
    Bs.
-endif.
    
%% generate a variable vector, bits 
%% X[n-1] X[2] X[1] X[0]  return as little endian [X[0],X[1],X[2],X[n-1]]
var_vector(Type,V,N,Bs) ->
    {p,Name,Args} = expand_meta(V,Bs),
    N1 = eval_meta(N,Bs),
    Sym = {Name,Args},
    NT = nif_type(Type),   %% the symbol table has an atom, fix16 for {fix,16}
    case find_sym(Sym, Bs) of
	{NT,Ls} ->
	    {{Type,length(Ls),Ls},Bs};
	false ->
	    {V1,Vn} = varp_nif:add_variables(Bs#bs.vp, N1, true),
	    Ls = lists:seq(V1,Vn),
	    Bs1 = new_symbol(Sym, Ls, NT, Bs),
	    {{Type,N1,Ls},Bs1}
    end.

%% the type atom the symbol table and the model see
nif_type({fix,F}) -> list_to_atom("fix" ++ integer_to_list(F));
nif_type({float,E,M}) -> varp_float:type_atom(E, M);
nif_type(T) -> T.

%% A declared type as the parser left it.  The fraction width of a
%% bare /fixpoint is --fixpoint, that of /fixpoint(f) a meta expression;
%% a bare /float754 is the standard format of the size, /float754(e)
%% takes e exponent bits of the size, /float754(e,m) is explicit.
decl_type(T, Bs) ->
    decl_type(T, undefined, Bs).

decl_type({fix,default}, _Size, Bs) -> {fix, fix_frac(Bs)};
decl_type({fix,F}, _Size, Bs) -> {fix, meta_int(F, Bs)};
decl_type({float,default,default}, Size, Bs) ->
    {E,M} = varp_float:standard(decl_size(Size, Bs)),
    {float,E,M};
decl_type({float,default,M0}, Size, Bs) ->
    M = meta_int(M0, Bs),
    {float,decl_size(Size, Bs)-1-M,M};
decl_type({float,E0,M0}, _Size, Bs) ->
    {float, meta_int(E0, Bs), meta_int(M0, Bs)};
%% X/float, X:32/float: the format --float names
decl_type({float,default}, Size, Bs) ->
    {Spec, SpecSize} = float_option(Bs),
    decl_type(Spec, float_width(Size, SpecSize, Bs), Bs);
decl_type(T, _Size, _Bs) -> T.

meta_int(I, _Bs) when is_integer(I) -> I;
meta_int(E, Bs) -> eval_meta(E, Bs).

decl_size(undefined, _Bs) -> error(float754_size_unknown);
decl_size(S, Bs) -> meta_int(S, Bs).

%% the width of a declaration: its size expression, or for a bare
%% X/float the width --float gives
decl_width({float,default}, default, Bs) ->
    case float_option(Bs) of
	{_, undefined} -> error({float_size_unknown, float_option_string(Bs)});
	{_, Size} -> Size
    end;
decl_width(_PType, SExpr, Bs) ->
    eval_meta(SExpr, Bs).

float_width(undefined, SpecSize, _Bs) -> SpecSize;
float_width(default, SpecSize, _Bs) -> SpecSize;
float_width(Size0, SpecSize, Bs) ->
    Size = meta_int(Size0, Bs),
    if SpecSize =:= undefined; SpecSize =:= Size -> Size;
       true -> error({float_size_mismatch, Size, float_option_string(Bs)})
    end.

float_option_string(Bs) ->
    maps:get(float, Bs#bs.option, "float754").

%% --float as a declaration type and a width (undefined when the option
%% leaves the width to the declaration)
float_option(Bs) ->
    Str = float_option_string(Bs),
    case float_spec(Str) of
	error -> error({float_option, Str});
	Spec -> Spec
    end.

%% "float754", "32/float754", "32/float754(23)", "float754(8,23)",
%% "fixpoint", "32/fixpoint(8)", "fixpoint(16,16)": what follows the
%% slash of a declaration, with the size in front when it has one
float_spec(Str) ->
    RE = "^(?:([0-9]+)/)?(float754|fixpoint)(?:\\(([0-9]+)(?:,([0-9]+))?\\))?$",
    case re:run(string:trim(Str), RE, [{capture,all_but_first,list}]) of
	{match, Gs0} ->
	    [W,Name,A,B] = Gs0 ++ lists:duplicate(4-length(Gs0), ""),
	    float_spec_(Name, spec_int(W), spec_int(A), spec_int(B));
	nomatch ->
	    error
    end.

spec_int("") -> undefined;
spec_int(S) -> list_to_integer(S).

float_spec_("float754", W, undefined, undefined) -> {{float,default,default}, W};
float_spec_("float754", W, M, undefined) -> {{float,default,M}, W};
float_spec_("float754", undefined, E, M) -> {{float,E,M}, 1+E+M};
float_spec_("fixpoint", W, undefined, undefined) -> {{fix,default}, W};
float_spec_("fixpoint", W, F, undefined) -> {{fix,F}, W};
float_spec_("fixpoint", undefined, I, F) -> {{fix,F}, I+F};
float_spec_(_, _, _, _) -> error.

%%
%%var_vector_(Size,Size,Type,Xs,_V,Bs) -> 
%%    {{Type,Size,lists:reverse(Xs)},Bs};
%%var_vector_(I,Size,Type,Xs,V,Bs) ->
%%    {{bool,Xi},Bs1} = variable({Type,V,Size,I},Bs),
%%    var_vector_(I+1,Size,Type,[Xi|Xs],V,Bs1).

all(A,Bs) -> all(undefined,A,Bs).
%% the target of a gate: build_assign/3 hands over the built target,
%% {bool,L}; the circuit functions take the literal or undefined
qtarget({bool,L}) when is_integer(L) -> L;
qtarget(_) -> undefined.

all(X,As,Bs) ->
    X1 = varp_circuit:all(Bs#bs.vp,qtarget(X),circuit_args(As)),
    {{bool,X1},Bs}.

any(A,Bs) -> any(undefined,A,Bs).
any(X,As,Bs) ->
    X1 = varp_circuit:any(Bs#bs.vp,qtarget(X),circuit_args(As)),
    {{bool,X1},Bs}.    

none(A,Bs) -> none(undefined,A,Bs).
none(X,As,Bs) ->
    X1 = varp_circuit:none(Bs#bs.vp,qtarget(X),circuit_args(As)),
    {{bool,X1},Bs}.

one(A,Bs) -> one(undefined,A,Bs).
one(X,As, Bs) -> eqk(1,X,As,Bs).

sum(As, Bs) ->
    sum(undefined,As,Bs).

sum(X,[],Bs) -> {V, Bs1} = const_vector(uint,0,1,Bs), set(X,V,Bs1);
sum(X, [A], Bs) -> set(X,A,Bs);
sum(X, [A|As], Bs) ->
    {X1,Bs1} = sum_(As,Bs),
    operation2('add', X, A, X1, Bs1).

sum_([Y], Bs) -> {Y, Bs};
sum_([Y|Ys], Bs) ->
    {Yn,Bs1} = sum(Ys,Bs),
    operation2('add', Y, Yn, Bs1).


prod(As, Bs) ->
    prod(undefined,As,Bs).

prod(X,[],Bs) -> {V, Bs1} = const_vector(uint,1,1,Bs), set(X,V,Bs1);
prod(X, [A], Bs) -> set(X,A,Bs);
prod(X, [A|As], Bs) ->
    {X1,Bs1} = prod_(As,Bs),
    operation2('mul', X, A, X1, Bs1).

prod_([Y], Bs) -> {Y, Bs};
prod_([Y|Ys], Bs) ->
    {Yn,Bs1} = prod(Ys,Bs),
    operation2('mul', Y, Yn, Bs1).

eqk(K,X,Ys,Bs) ->
    X1 = varp_circuit:eqk(Bs#bs.vp,K,qtarget(X),circuit_args(Ys)),
    {{bool,X1},Bs}.

neqk(K,X,Ys,Bs) ->
    X1 = varp_circuit:neqk(Bs#bs.vp,K,qtarget(X),circuit_args(Ys)),
    {{bool,X1},Bs}.

gtk(K,X,Ys,Bs) ->
    X1 = varp_circuit:gtk(Bs#bs.vp,K,qtarget(X),circuit_args(Ys)),
    {{bool,X1},Bs}.

negate({bool,X}) -> {bool,lnot(X)}.

lnot(?T) -> ?F;
lnot(?F) -> ?T;
lnot(X) -> -X.
     
vconst({uint,_,Xs}) -> vunsigned(Xs);
vconst({int,_,Xs}) -> vsigned(Xs);
vconst({bit,_,Xs}) -> vunsigned(Xs);
vconst({{fix,_},_,Xs}) -> vsigned(Xs);   %% the raw, scaled integer
vconst({{float,_,_},_,Xs}) -> vunsigned(Xs);   %% the raw bits
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


circuit_args(Xs) ->
    [X || {bool,X} <- Xs].

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
	{T,_N,Ys} when ?is_vec_type(T) -> [{bool,Y}||Y<-Ys] ++ join_vector(Xs)
    end;
join_vector([]) ->
    [].

%%
%% Unary operator
%%
operation1(Op, A, Bs) ->
    case special_op1(Op, A, Bs) of
	false ->
	    case lib_op1(Op, A, Bs) of
		builtin -> builtin1(Op, A, Bs);
		Result -> Result
	    end;
	Result -> Result
    end.

%% the float and fixed point layers, before the integer encoders
special_op1(Op, A, Bs) ->
    case float_op1(Op, A, Bs) of
	false -> fix_op1(Op, A, Bs);
	Result -> Result
    end.

special_op2(Op, A, B, Bs) ->
    case float_op2(Op, A, B, Bs) of
	false -> fix_op2(Op, A, B, Bs);
	Result -> Result
    end.

builtin1(Op, {bool,A}, Bs) when Op =:= 'not'; Op =:= 'bnot' ->
    B = varp_circuit:gate(Bs#bs.vp,'not',A),
    {{bool,B}, Bs};
builtin1(Op, A, Bs) ->
    X = case Op of
	    'bnot' ->
		varp_arith:bitwise_not(Bs#bs.vp,A);
	    'not' ->
		B = varp_arith:neq(Bs#bs.vp,A,{uint,1,[false]}),
		{bool,B};
	    'neg' ->
		case vconst(A) of
		    false ->
			varp_arith:negate(Bs#bs.vp,A);
		    Av ->
			Av1 = -Av,
			An1 = varp_math:signed_size(Av1),
			const_vector_(An1-1,int,An1,[],Av1)
		end;
	    'abs' ->
		varp_arith:abs(Bs#bs.vp,A)
	end,
    {X, Bs}.

%% Operation with assignment to X
operation1(Op, undefined, A, Bs) ->
    operation1(Op, A, Bs);
operation1(Op, X, A, Bs) ->
    case special_op1(Op, A, Bs) of
	false ->
	    case lib_op1(Op, A, Bs) of
		builtin -> builtin1(Op, X, A, Bs);
		{V, Bs1} -> set(X, V, Bs1)
	    end;
	{V, Bs1} -> set(X, V, Bs1)
    end.

builtin1(Op, {bool,X}, {bool,A}, Bs) when
      Op =:= 'not'; Op =:= 'bnot'; Op =:= '=' ->
    X1 = case Op of
	     '=' ->
		 varp_circuit:set(Bs#bs.vp, X, A);
	     _ ->
		 varp_circuit:gate(Bs#bs.vp,'not',X,A)
	 end,
    {{bool,X1}, Bs};
%% operation1(':=',X,Y={T,Size,Ys},Bs) when ?is_vec_type(T) ->
%%     {Y, alias_vector(Bs,T,X,Size,Ys)};
builtin1(Op, X, A, Bs) ->
    X1 = case Op of
	    '=' ->
		varp_arith:set(Bs#bs.vp,X,A);
	    'bnot' ->
		varp_arith:bitwise_not(Bs#bs.vp,X,A);
	    'not' ->
		 Xb = varp_arith:neq(Bs#bs.vp,X,A,{uint,1,[false]}),
		 {bool,Xb};
	    'neg' ->
		 case vconst(A) of
		     false ->
			 varp_arith:negate(Bs#bs.vp,X,A);
		     Av ->
			 Av1 = -Av,
			 An1 = varp_math:signed_size(Av1),
			 const_vector_(An1-1,int,An1,[],Av1)
			 %% assign to X!!!
		 end;
	    'abs' ->
		 varp_arith:abs(Bs#bs.vp,X,A)
	end,
    {X1, Bs}.

%%
%% Binary operator
%%
operation2(Op,A,B,Bs) ->
    case special_op2(Op, A, B, Bs) of
	false ->
	    case fold2(Op, A, B, Bs) of
		false ->
		    case lib_op2(Op, A, B, Bs) of
			builtin -> builtin2(Op, A, B, Bs);
			Result -> Result
		    end;
		Folded -> Folded
	    end;
	Result -> Result
    end.

%% Two constant operands give a constant, no gates: "n / 2" in a body
%% where n is a size, "(n == 1) ? .. : .." as the end of a recursion.
%% Division by zero is left to the encoder and its --divz.
fold2(Op, A, B, Bs) when is_tuple(A), is_tuple(B),
			 (?is_vec_type(element(1,A)) orelse
			  ?is_vec_type(element(1,B))) ->
    case {vconst(A), vconst(B)} of
	{Av, Bv} when is_integer(Av), is_integer(Bv) ->
	    case fold2_(Op, Av, Bv) of
		none -> false;
		true -> {{bool,?T}, Bs};
		false -> {{bool,?F}, Bs};
		R when is_integer(R), R >= 0 ->
		    const_vector(uint, R, varp_math:unsigned_size(R), Bs);
		R when is_integer(R) ->
		    const_vector(int, R, varp_math:signed_size(R), Bs)
	    end;
	_ -> false
    end;
fold2(_Op, _A, _B, _Bs) ->
    false.

fold2_('add', A, B) -> A + B;
fold2_('sub', A, B) -> A - B;
fold2_('mul', A, B) -> A * B;
fold2_('div', A, B) when B =/= 0 -> A div B;
fold2_('rem', A, B) when B =/= 0 -> A rem B;
fold2_('min', A, B) -> erlang:min(A, B);
fold2_('max', A, B) -> erlang:max(A, B);
fold2_('shl', A, B) -> A bsl B;
fold2_('shr', A, B) -> A bsr B;
fold2_('lt', A, B) -> A < B;
fold2_('lte', A, B) -> A =< B;
fold2_('gt', A, B) -> A > B;
fold2_('gte', A, B) -> A >= B;
fold2_('eq', A, B) -> A == B;
fold2_('neq', A, B) -> A =/= B;
fold2_(_Op, _A, _B) -> none.

builtin2(Op,{bool,Y},{bool,Z}, Bs) when ?is_bool_op(Op) ->
    X = case Op of
	    'and' -> varp_circuit:and_gate(Bs#bs.vp, Y, Z);
	    'band' -> varp_circuit:and_gate(Bs#bs.vp, Y, Z);
	    'bor' -> varp_circuit:or_gate(Bs#bs.vp, Y, Z);
	    'bxor' -> varp_circuit:xor_gate(Bs#bs.vp, Y, Z);
	    'or' ->  varp_circuit:or_gate(Bs#bs.vp, Y, Z);
	    'imp' -> varp_circuit:imp_gate(Bs#bs.vp, Y, Z);
	    'equ' -> varp_circuit:equ_gate(Bs#bs.vp, Y, Z);
	    'xor' -> varp_circuit:xor_gate(Bs#bs.vp, Y, Z);
	    'nimp' -> varp_circuit:nimp_gate(Bs#bs.vp, Y, Z);
	    'nand' -> varp_circuit:nand_gate(Bs#bs.vp, Y, Z);
	    'nor' -> varp_circuit:nor_gate(Bs#bs.vp, Y, Z);
	    'lt' -> varp_circuit:lt_gate(Bs#bs.vp, Y, Z);
	    'gt' -> varp_circuit:gt_gate(Bs#bs.vp, Y, Z);
	    'lte' -> varp_circuit:lte_gate(Bs#bs.vp, Y, Z);
	    'gte' -> varp_circuit:gte_gate(Bs#bs.vp, Y, Z);
	    'eq' -> varp_circuit:equ_gate(Bs#bs.vp, Y, Z);
	    'neq' -> varp_circuit:xor_gate(Bs#bs.vp, Y, Z)
	end,
    {{bool,X},Bs};
%% operation2(':=',V,X={T,Size,Xs},Bs) when ?is_vec_type(T) ->
%%     {X, alias_vector(Bs,T,V,Size,Xs)};
%% operation2(':=',V,X={bool,Xb},Bs) ->
%%     {X, alias(V,Xb,Bs)};
builtin2(Op,A,B,Bs) ->
    C = case Op of 
	    'band' -> varp_arith:bitwise_and(Bs#bs.vp,A,B);
	    'bor' -> varp_arith:bitwise_or(Bs#bs.vp,A,B);
	    'bxor' -> varp_arith:bitwise_xor(Bs#bs.vp,A,B);
	    'imp' -> An = varp_arith:bitwise_not(Bs#bs.vp,A),
		     varp_arith:bitwise_or(Bs#bs.vp,An,B);
	    'equ' -> varp_arith:bitwise_equ(Bs#bs.vp,A,B);
	    'lt' -> X = varp_arith:lt(Bs#bs.vp,A,B),{bool,X};
	    'lte' -> X = varp_arith:lte(Bs#bs.vp,A,B),{bool,X};
	    'gt' -> X = varp_arith:gt(Bs#bs.vp,A,B),{bool,X};
	    'gte' -> X = varp_arith:gte(Bs#bs.vp,A,B),{bool,X};
	    'eq' -> X = varp_arith:eq(Bs#bs.vp,A,B),{bool,X};
	    'neq' -> X = varp_arith:neq(Bs#bs.vp,A,B),{bool,X};
	    'shl' -> varp_arith:shl(Bs#bs.vp,A,B);
	    'shr' -> varp_arith:shr(Bs#bs.vp,A,B);
	    'rol' -> varp_arith:rol(Bs#bs.vp,A,B);
	    'ror' -> varp_arith:ror(Bs#bs.vp,A,B);
	    'add' -> varp_arith:add(Bs#bs.vp,A,B);
	    'sub' -> varp_arith:subtract(Bs#bs.vp,A,B);
	    'mul' -> varp_arith:multiply(Bs#bs.vp,A,B);
	    'div' -> varp_arith:divide(Bs#bs.vp,A,B);
	    'rem' -> varp_arith:reminder(Bs#bs.vp,A,B);
	    'min' -> varp_arith:min(Bs#bs.vp,A,B);
	    'max' -> varp_arith:max(Bs#bs.vp,A,B);
	    %% operator '=' is kind of assignment but really a 
	    %% equality test and check of overflow bits
	    %% FIXME: same as '==' but check overflow / truncate 
	    '=' -> X = varp_arith:set(Bs#bs.vp,A,B),{bool,X};
	    %% `and', `or', `xor', `nand', `nor' and `nimp' are absent from this
	    %% clause on purpose: they need BOOLEAN operands, and here at least
	    %% one side is a vector. A vector is a value, not a condition --
	    %% there is no implicit truthiness -- so the formula has to compare
	    %% it. Until this clause existed the miss fell out of the case as
	    %% {case_clause,'and'}, which told the user nothing at all.
	    _ ->
		erlang:error({not_a_condition, Op, operand_kind(A),
			      operand_kind(B)})
	end,
    {C, Bs}.

%% Describe an operand for the error above. A width and a type is as much as is
%% known here -- the name the user wrote is long gone by the time a value is
%% built, so the message names the OPERATOR and leaves finding the side to them.
operand_kind({bool,_})            -> boolean;
operand_kind({T,N,_}) when is_integer(N) -> {T,N};
operand_kind({T,N}) when is_integer(N)   -> {T,N};
operand_kind(Other)               -> Other.

%% like operation2 but result is predetermined in X
operation2(Op,undefined,Y,Z,Bs) ->
    operation2(Op,Y,Z,Bs);
operation2(Op,X,Y,Z,Bs) ->
    case special_op2(Op, Y, Z, Bs) of
	false ->
	    case lib_op2(Op, Y, Z, Bs) of
		builtin -> builtin2(Op, X, Y, Z, Bs);
		{V, Bs1} -> set(X, V, Bs1)
	    end;
	{V, Bs1} -> set(X, V, Bs1)
    end.

builtin2(Op,{bool,X},{bool,Y},{bool,Z}, Bs) when ?is_bool_op(Op) ->
    %% X1 is "normally" equal to X
    X1 = case Op of
	    'and' -> varp_circuit:and_gate(Bs#bs.vp, X, Y, Z);
	    'band' -> varp_circuit:and_gate(Bs#bs.vp, X, Y, Z);
	    'bor' -> varp_circuit:or_gate(Bs#bs.vp, X, Y, Z);
	    'bxor' -> varp_circuit:xor_gate(Bs#bs.vp, X, Y, Z);
	    'or' ->  varp_circuit:or_gate(Bs#bs.vp, X, Y, Z);
	    'imp' -> varp_circuit:imp_gate(Bs#bs.vp, X, Y, Z);
	    'equ' -> varp_circuit:equ_gate(Bs#bs.vp, X, Y, Z);
	    'xor' -> varp_circuit:xor_gate(Bs#bs.vp, X, Y, Z);
	    'nimp' -> varp_circuit:nimp_gate(Bs#bs.vp, X, Y, Z);
	    'nand' -> varp_circuit:nand_gate(Bs#bs.vp, X, Y, Z);
	    'nor' -> varp_circuit:nor_gate(Bs#bs.vp, X, Y, Z);
	    'lt' -> varp_circuit:lt_gate(Bs#bs.vp, X, Y, Z);
	    'gt' -> varp_circuit:gt_gate(Bs#bs.vp, X, Y, Z);
	    'lte' -> varp_circuit:lte_gate(Bs#bs.vp, X, Y, Z);
	    'gte' -> varp_circuit:gte_gate(Bs#bs.vp, X, Y, Z);
	    'eq' -> varp_circuit:equ_gate(Bs#bs.vp, X, Y, Z);
	    'neq' -> varp_circuit:xor_gate(Bs#bs.vp, X, Y, Z)
	end,
    {{bool,X1},Bs};
%% operation2(':=',X,Y={bool,Yb},Bs) ->
%%     {Y, alias(X,Yb,Bs)};
%% a comparison into a boolean target is built into its literal; any
%% other target (a vector, "declare x:2; x = (A == B);") gets the value
builtin2(Op,X,Y,Z,Bs) when ?is_compare_op(Op) ->
    case X of
	{bool,Xl} ->
	    Xb = case Op of
		     'lt' -> varp_arith:lt(Bs#bs.vp,Xl,Y,Z);
		     'lte' -> varp_arith:lte(Bs#bs.vp,Xl,Y,Z);
		     'gt' -> varp_arith:gt(Bs#bs.vp,Xl,Y,Z);
		     'gte' -> varp_arith:gte(Bs#bs.vp,Xl,Y,Z);
		     'eq' -> varp_arith:eq(Bs#bs.vp,Xl,Y,Z);
		     'neq' -> varp_arith:neq(Bs#bs.vp,Xl,Y,Z);
		     %% operator '=' is kind of assignment but really a
		     %% equality test and check of overflow bits
		     %% FIXME: same as '==' but check overflow / truncate
		     '=' -> varp_arith:eq(Bs#bs.vp,Xl,Y,Z)
		 end,
	    {{bool,Xb}, Bs};
	_ ->
	    {C,Bs1} = builtin2(Op,Y,Z,Bs),
	    set(X,C,Bs1)
    end;
builtin2(Op,X,Y,Z,Bs) ->
    X1 = case Op of 
	     'band' -> varp_arith:bitwise_and(Bs#bs.vp,X,Y,Z);
	     'bor' -> varp_arith:bitwise_or(Bs#bs.vp,X,Y,Z);
	     'bxor' -> varp_arith:bitwise_xor(Bs#bs.vp,X,Y,Z);
	     'imp' -> Yn = varp_arith:bitwise_not(Bs#bs.vp,Y),
		     varp_arith:bitwise_or(Bs#bs.vp,X,Yn,Z);
	     'equ' -> varp_arith:bitwise_equ(Bs#bs.vp,X,Y,Z);
	     'shl' -> varp_arith:shl(Bs#bs.vp,X,Y,Z);
	     'shr' -> varp_arith:shr(Bs#bs.vp,X,Y,Z);
	     'rol' -> varp_arith:rol(Bs#bs.vp,X,Y,Z);
	     'ror' -> varp_arith:ror(Bs#bs.vp,X,Y,Z);
	     'add' -> varp_arith:add(Bs#bs.vp,X,Y,Z);
	     'sub' -> varp_arith:subtract(Bs#bs.vp,X,Y,Z);
	     'mul' -> varp_arith:multiply(Bs#bs.vp,X,Y,Z);
	     'div' -> varp_arith:divide(Bs#bs.vp,X,Y,Z);
	     'rem' -> varp_arith:reminder(Bs#bs.vp,X,Y,Z);
	     'min' -> varp_arith:min(Bs#bs.vp,X,Y,Z);
	     'max' -> varp_arith:max(Bs#bs.vp,X,Y,Z)
	 end,
    {X1, Bs}.

%%
%% --ops lib: the operators built from the library circuits instead of
%% the encoders in varp_arith, which stay as the reference.  Returns
%% builtin when the built in encoder is to be used: the option is off,
%% both operands are booleans (a gate, not arithmetic), or the library
%% has no circuit for the case (rotation, bitwise on signed, the '='
%% test).  A signed operand selects the op_s* circuit and the other
%% operand is made signed first, like the encoders do; subtraction and
%% negation are signed always, as the encoders give a signed result.
%% Division by zero gets the --divz status the encoders set.
%%
lib_ops(Bs) ->
    maps:get(ops, Bs#bs.option, builtin) =:= lib.

lib_op1(Op, A, Bs) ->
    case is_tuple(A) andalso lib_ops(Bs) andalso element(1, A) =/= bool of
	false -> builtin;
	true ->
	    case Op of
		'neg' ->
		    lib_call(<<"op_sneg">>, [{value,varp_arith:iarg(A)}], Bs);
		'bnot' when element(1, A) =/= int ->
		    lib_call(<<"op_bnot">>, [{value,A}], Bs);
		_ -> builtin
	    end
    end.

lib_op2(Op, A, B, Bs) when is_tuple(A), is_tuple(B) ->
    case lib_ops(Bs) andalso
	not (element(1, A) =:= bool andalso element(1, B) =:= bool) of
	false -> builtin;
	true -> lib_op2_(Op, lib_type(A, B), A, B, Bs)
    end;
lib_op2(_Op, _A, _B, _Bs) ->
    builtin.

lib_type(A, B) ->
    case varp_arith:mix_type(A, B) of
	int -> int;
	_ -> uint
    end.

lib_args(int, A, B) -> [{value,varp_arith:iarg(A)}, {value,varp_arith:iarg(B)}];
lib_args(uint, A, B) -> [{value,varp_arith:varg(A)}, {value,varp_arith:varg(B)}].

lib_name(uint, Base) -> <<"op_", Base/binary>>;
lib_name(int, Base) -> <<"op_s", Base/binary>>.

lib_op2_(Op, T, A, B, Bs) when Op =:= 'add'; Op =:= 'mul';
			       Op =:= 'min'; Op =:= 'max';
			       Op =:= 'lt'; Op =:= 'lte';
			       Op =:= 'gt'; Op =:= 'gte';
			       Op =:= 'eq'; Op =:= 'neq' ->
    lib_call(lib_name(T, atom_to_binary(Op)), lib_args(T, A, B), Bs);
lib_op2_('sub', _T, A, B, Bs) ->
    lib_call(<<"op_ssub">>, lib_args(int, A, B), Bs);
lib_op2_('rem', T, A, B, Bs) ->
    Bs1 = lib_divz(B, Bs),
    lib_call(lib_name(T, <<"rem">>), lib_args(T, A, B), Bs1);
lib_op2_('div', T, A, B, Bs) ->
    Bs1 = lib_divz(B, Bs),
    Name = lib_name(T, <<"div">>),
    %% the remainder is an out parameter: a fresh symbol of the caller
    {Prefix, Bs2} = circuit_prefix(Name, Bs1),
    lib_call(Name, lib_args(T, A, B) ++ [{p,<<Prefix/binary,"r">>,[]}], Bs2);
lib_op2_(Op, uint, A, B, Bs) when Op =:= 'band'; Op =:= 'bor'; Op =:= 'bxor' ->
    lib_call(lib_name(uint, atom_to_binary(Op)), lib_args(uint, A, B), Bs);
lib_op2_(Op, T, A, K, Bs) when Op =:= 'shl'; Op =:= 'shr' ->
    case varp_arith:vconst(K) of
	false -> builtin;
	N when Op =:= 'shl', N >= 0; Op =:= 'shr', N < 0 ->
	    [Arg|_] = lib_args(T, A, A),
	    {V, Bs1} = lib_call(<<"op_shl">>, [{const,abs(N)}, Arg], Bs),
	    {lib_retag(T, V), Bs1};
	N ->
	    [Arg|_] = lib_args(T, A, A),
	    case T of
		int -> lib_call(<<"op_sar">>, [{const,abs(N)}, Arg], Bs);
		uint -> lib_call(<<"op_shr">>, [{const,abs(N)}, Arg], Bs)
	    end
    end;
lib_op2_(Op, T, A, K, Bs) when Op =:= 'rol'; Op =:= 'ror' ->
    case varp_arith:vconst(K) of
	N when is_integer(N), N >= 0 ->
	    [Arg|_] = lib_args(T, A, A),
	    Name = <<"op_", (atom_to_binary(Op))/binary>>,
	    {V, Bs1} = lib_call(Name, [{const,N}, Arg], Bs),
	    {lib_retag(T, V), Bs1};
	_ -> builtin
    end;
lib_op2_(_Op, _T, _A, _B, _Bs) ->
    builtin.

%% op_shl is wiring, the same for both signs: the result keeps the type
lib_retag(int, {uint,N,Bits}) -> {int,N,Bits};
lib_retag(_T, V) -> V.

%% B == 0 gets the --divz status (false by default: no model)
lib_divz(B, Bs) ->
    Vp = Bs#bs.vp,
    Zero = varp_arith:eq(Vp, varp_arith:varg(B), {uint,1,[false]}),
    varp_arith:set_status(Vp, Zero, varp_nif:getopt(Vp, divz)),
    Bs.

lib_call(Name, Args, Bs) ->
    call_circuit(Name, Args, Bs).

%%
%% Fixed point, {fix,F}: a two's complement integer of N bits read as
%% value / 2^F.  Everything is done with the integer operators on the
%% raw bits, so --ops lib and --overflow apply as for integers:
%%
%%   + - min max % < <= ...  the raw integers, after the operands are
%%                           brought to a common F (an integer is
%%                           shifted up F bits, a float literal is
%%                           round(V * 2^F))
%%   *                       the raw product has 2F fraction bits, the
%%                           low F are dropped (floor)
%%   /                       (a << F) / b, truncating toward zero like
%%                           the signed integer division
%%   & | ^ << >>             on the raw bits, no scaling
%%   floor ceil round trunc  to an integer; round is half up
%%
%% A float literal with no fixed point operand gets --fixpoint fraction
%% bits, so "X * 1.0 / Y" divides two integers in Q16.16.  Assigning a
%% fixed point value to an integer is an error: say which rounding.
%%
fix_frac(Bs) ->
    maps:get(fixpoint, Bs#bs.option, 16).

lit(true) -> ?T;
lit(false) -> ?F.

is_fixish({flo,_}) -> true;
is_fixish({T,_,_}) -> ?is_fix(T);
is_fixish(_) -> false.

%% the common fraction width of two operands
fix_common(A, B, Bs) ->
    case [F || {{fix,F},_,_} <- [A,B]] of
	[] -> fix_frac(Bs);
	Fs -> lists:max(Fs)
    end.

%% an operand as the raw integer of a {fix,F} value
to_raw({{fix,F},N,Xs}, F, Bs) ->
    {{int,N,Xs}, Bs};
to_raw({{fix,F0},N,Xs}, F, Bs) when F0 < F ->
    {shift_up({int,N,Xs}, F-F0), Bs};
to_raw({{fix,F0},N,Xs}, F, Bs) ->   %% F0 > F: precision goes
    {shift_down({int,N,Xs}, F0-F), Bs};
to_raw({flo,V}, _F, _Bs) when is_atom(V) ->   %% inf, '-inf'
    error({fixpoint_infinity, V});
to_raw({flo,V}, F, Bs) ->
    R = round(V * (1 bsl F)),
    {const_vector(int, R, varp_math:signed_size(R)), Bs};
to_raw(V={{float,_,_},_,_}, F, Bs) ->
    {{_,N,Xs}, Bs1} = float_to_fix(V, F, false, 64, Bs),
    {{int,N,Xs}, Bs1};
to_raw({bool,X}, F, Bs) ->
    to_raw({uint,1,[X]}, F, Bs);
to_raw(V, F, Bs) ->
    {shift_up(varp_arith:iarg(V), F), Bs}.

%% the raw bits of a fixed point operand, other operands as they are
to_bits({{fix,_},N,Xs}) -> {int,N,Xs};
to_bits({flo,_}) -> error(fixpoint_bitwise_literal);
to_bits(V) -> V.

%% wiring only: multiply or divide the raw integer by 2^K.  A folded
%% constant comes as an unsigned vector, iarg gives it its sign bit.
shift_up(V, K) ->
    {int,N,Xs} = varp_arith:iarg(V),
    {int,N+K,lists:duplicate(K,false) ++ Xs}.

shift_down(V, K) ->
    case varp_arith:iarg(V) of
	{int,N,Xs} when N > K ->
	    {int,N-K,lists:nthtail(K,Xs)};
	{int,_N,Xs} ->
	    {int,1,[lists:last(Xs)]}   %% nothing but the sign is left
    end.

%% an integer result as a fixed point value; a folded constant comes
%% back unsigned, so it gets its zero sign bit first
fix_result(F, R) ->
    {int,N,Xs} = varp_arith:iarg(R),
    {{fix,F},N,Xs}.

fix_op1(Op, {flo,inf}, Bs) ->
    case Op of
	'neg' -> {{flo,'-inf'}, Bs};
	'abs' -> {{flo,inf}, Bs};
	_ -> error({fixpoint_infinity, inf})
    end;
fix_op1(Op, {flo,'-inf'}, Bs) ->
    case Op of
	'neg' -> {{flo,inf}, Bs};
	'abs' -> {{flo,inf}, Bs};
	_ -> error({fixpoint_infinity, '-inf'})
    end;
fix_op1(Op, {flo,V}, Bs) ->
    case Op of
	'neg' -> {{flo,-V}, Bs};
	'abs' -> {{flo,erlang:abs(V)}, Bs};
	'not' -> {{bool,if V == 0 -> ?T; true -> ?F end}, Bs};
	_ -> error({fixpoint_operator, Op, float_literal})
    end;
fix_op1(Op, {{fix,F},N,Xs}, Bs) ->
    {R, Bs1} = operation1(Op, {int,N,Xs}, Bs),
    case Op of
	'not' -> {R, Bs1};                %% X != 0, a boolean
	_ -> {fix_result(F, R), Bs1}       %% neg abs bnot
    end;
fix_op1(_Op, _A, _Bs) ->
    false.

fix_op2(Op, {flo,X}, {flo,Y}, Bs) when is_number(X), is_number(Y) ->
    %% two literals stay a literal, the format is settled when it
    %% meets an operand: 3.0e38 * 10 is not a Q16.16 product
    case Op of
	'add' -> {{flo,X+Y}, Bs};
	'sub' -> {{flo,X-Y}, Bs};
	'mul' -> {{flo,X*Y}, Bs};
	'div' when Y == 0 -> error({float_literal_division_by_zero, X, Y});
	'div' -> {{flo,X/Y}, Bs};
	'min' -> {{flo,erlang:min(X,Y)}, Bs};
	'max' -> {{flo,erlang:max(X,Y)}, Bs};
	'lt' -> {{bool,lit(X < Y)}, Bs};
	'lte' -> {{bool,lit(X =< Y)}, Bs};
	'gt' -> {{bool,lit(X > Y)}, Bs};
	'gte' -> {{bool,lit(X >= Y)}, Bs};
	'eq' -> {{bool,lit(X == Y)}, Bs};
	'neq' -> {{bool,lit(X /= Y)}, Bs};
	_ -> fix_op2_(Op, {flo,X}, {flo,Y}, Bs)
    end;
fix_op2(Op, A, B, Bs) when is_tuple(A), is_tuple(B) ->
    case is_fixish(A) orelse is_fixish(B) of
	true -> fix_op2_(Op, A, B, Bs);
	false -> false
    end;
fix_op2(_Op, _A, _B, _Bs) ->
    false.

fix_op2_(Op, A, B, Bs) when Op =:= 'shl'; Op =:= 'shr';
			   Op =:= 'rol'; Op =:= 'ror' ->
    %% the shift count is an integer, the bits move as they are
    case {A, is_fixish(B)} of
	{{{fix,F},N,Xs}, false} ->
	    {R, Bs1} = operation2(Op, {int,N,Xs}, B, Bs),
	    {fix_result(F, R), Bs1};
	_ ->
	    error({fixpoint_operand, Op})
    end;
fix_op2_(Op, A, B, Bs) when Op =:= 'band'; Op =:= 'bor';
			   Op =:= 'bxor'; Op =:= 'equ' ->
    %% bit by bit on the raw bits, no scaling (the mux of ?: needs it)
    F = fix_common(A, B, Bs),
    {R, Bs1} = operation2(Op, to_bits(A), to_bits(B), Bs),
    {fix_result(F, R), Bs1};
fix_op2_(Op, A, B, Bs) when Op =:= 'lt'; Op =:= 'lte'; Op =:= 'gt';
			   Op =:= 'gte'; Op =:= 'eq'; Op =:= 'neq' ->
    F = fix_common(A, B, Bs),
    {Ar, Bs1} = to_raw(A, F, Bs),
    {Br, Bs2} = to_raw(B, F, Bs1),
    operation2(Op, Ar, Br, Bs2);
fix_op2_('mul', A, B, Bs) ->
    F = fix_common(A, B, Bs),
    {Ar, Bs1} = to_raw(A, F, Bs),
    {Br, Bs2} = to_raw(B, F, Bs1),
    case lib_ops(Bs2) andalso vconst(Ar) =:= false andalso vconst(Br) =:= false of
	true ->
	    {P, Bs3} = lib_call(<<"op_fixmul">>,
				[{const,F},{value,Ar},{value,Br}], Bs2),
	    {fix_result(F, P), Bs3};
	false ->
	    {P, Bs3} = operation2('mul', Ar, Br, Bs2),
	    {fix_result(F, shift_down(P, F)), Bs3}
    end;
fix_op2_('div', A, B, Bs) ->
    F = fix_common(A, B, Bs),
    {Ar, Bs1} = to_raw(A, F, Bs),
    {Br, Bs2} = to_raw(B, F, Bs1),
    case lib_ops(Bs2) andalso vconst(Ar) =:= false andalso vconst(Br) =:= false of
	true ->
	    Bs3 = lib_divz(Br, Bs2),
	    {Prefix, Bs4} = circuit_prefix(<<"op_fixdiv">>, Bs3),
	    {Q, Bs5} = lib_call(<<"op_fixdiv">>,
				[{const,F},{value,Ar},{value,Br},
				 {p,<<Prefix/binary,"r">>,[]}], Bs4),
	    {fix_result(F, Q), Bs5};
	false ->
	    {Q, Bs3} = operation2('div', shift_up(Ar, F), Br, Bs2),
	    {fix_result(F, Q), Bs3}
    end;
fix_op2_(Op, A, B, Bs) ->
    %% add sub rem min max, and the logical operators which the
    %% integer code rejects with not_a_condition
    F = fix_common(A, B, Bs),
    {Ar, Bs1} = to_raw(A, F, Bs),
    {Br, Bs2} = to_raw(B, F, Bs1),
    {R, Bs3} = operation2(Op, Ar, Br, Bs2),
    case R of
	{bool,_} -> {R, Bs3};
	_ -> {fix_result(F, R), Bs3}
    end.

%% the branches of ?: as two {fix,F} values when one of them is fixed
%% point or a float literal; false when there is nothing to do
fix_align(T, E, Bs) when is_tuple(T), is_tuple(E) ->
    case is_floatish(T) orelse is_floatish(E) of
	true ->
	    Ty = float_type(T, E),
	    case {T, E} of
		{{Ty,_,_},{Ty,_,_}} -> false;
		_ ->
		    {T1, Bs1} = to_float(T, Ty, Bs),
		    {E1, Bs2} = to_float(E, Ty, Bs1),
		    {T1, E1, Bs2}
	    end;
	false -> fix_align_(T, E, Bs)
    end;
fix_align(_T, _E, _Bs) ->
    false.

fix_align_(T, E, Bs) ->
    case is_fixish(T) orelse is_fixish(E) of
	false -> false;
	true ->
	    case {T, E} of
		{{Ft,_,_},{Ft,_,_}} when ?is_fix(Ft) -> false;
		_ ->
		    F = fix_common(T, E, Bs),
		    {Tr, Bs1} = to_raw(T, F, Bs),
		    {Er, Bs2} = to_raw(E, F, Bs1),
		    {fix_result(F, Tr), fix_result(F, Er), Bs2}
	    end
    end.

%% X = Y with a fixed point side
fix_set(X={{fix,F},N,Xs}, Y, Bs) ->
    {Yr, Bs1} = to_raw(Y, F, Bs),
    {_, Bs2} = operation1('=', {int,N,Xs}, Yr, Bs1),
    {X, Bs2};
fix_set(X, Y, _Bs) ->
    case is_fixish(Y) andalso is_tuple(X) of
	true ->
	    error({fixpoint_to_integer, operand_kind(X),
		   "use floor, ceil, round or trunc"});
	false ->
	    false
    end.

%% floor ceil round trunc of a fixed point value, an integer result
fix_to_int(Fun, {flo,V}, Bs) ->
    R = case Fun of
	    floor -> erlang:floor(V);
	    ceil -> erlang:ceil(V);
	    round -> erlang:floor(V + 0.5);
	    trunc -> erlang:trunc(V)
	end,
    bld({const,R}, Bs);
fix_to_int(Fun, V={{float,_,_},_,_}, Bs) ->
    %% through a fixed point value: none for trunc, two fraction bits
    %% with a sticky bit for the others (enough for floor, ceil and
    %% round half up to be exact)
    {F, Sticky} = case Fun of trunc -> {0,false}; _ -> {2,true} end,
    {Fx, Bs1} = float_to_fix(V, F, Sticky, 64, Bs),
    fix_to_int(Fun, Fx, Bs1);
fix_to_int(_Fun, {{fix,0},N,Xs}, Bs) ->
    {{int,N,Xs}, Bs};
fix_to_int(Fun, {{fix,F},N,Xs}, Bs) ->
    Raw = {int,N,Xs},
    case Fun of
	floor ->
	    {shift_down(Raw, F), Bs};
	ceil ->
	    {S, Bs1} = operation2('add', Raw, const_vector(uint, (1 bsl F)-1, F), Bs),
	    {shift_down(S, F), Bs1};
	round when F > 0 ->
	    {S, Bs1} = operation2('add', Raw, const_vector(uint, 1 bsl (F-1), F), Bs),
	    {shift_down(S, F), Bs1};
	round ->
	    {Raw, Bs};
	trunc ->
	    %% floor, plus one when negative with a fraction
	    Fl = shift_down(Raw, F),
	    K = min(F, N),
	    Low = {uint,K,lists:sublist(Xs, K)},
	    {NZ, Bs1} = operation2('neq', Low, {uint,1,[false]}, Bs),
	    {{bool,Adj}, Bs2} = operation2('and', {bool,lists:last(Xs)}, NZ, Bs1),
	    operation2('add', Fl, {uint,1,[Adj]}, Bs2)
    end;
fix_to_int(_Fun, V, Bs) ->
    {V, Bs}.   %% already an integer

%%
%% wrap(E, T) and fits(E, T).  The type argument is what a declaration
%% says after the name: 32/unsigned, 8/signed, 32/fixpoint,
%% 16/fixpoint(4), fixpoint(8,8), 32/float754, float754(8,23), 32/float;
%% the parser leaves the keyword forms as {type,_,_} and the others as
%% a division or a call.  {type_of,V} is the type of a built value, the
%% destination of wrap(E).  The result is {Type,Width}.
%%
type_arg({type_of,{bool,_}}, _Bs) -> {bool,1};
type_arg({type_of,{T,N,_}}, _Bs) -> {T,N};
type_arg({type,PType,same}, _Bs) ->
    {PType, same};        %% E/unsigned: the width of E, see cast_to/3
type_arg({type,PType,SExpr}, Bs) ->
    Size = decl_width(PType, SExpr, Bs),
    {decl_type(PType, Size, Bs), Size};
type_arg({op,'div',SExpr,Q}, Bs) when is_binary(Q) ->
    type_arg_(Q, [], SExpr, Bs);
type_arg({op,'div',SExpr,{call,Q,As}}, Bs) when is_binary(Q) ->
    type_arg_(Q, As, SExpr, Bs);
type_arg({op,'div',SExpr,{p,Q,As}}, Bs) when is_binary(Q) ->
    type_arg_(Q, As, SExpr, Bs);
type_arg({call,Q,[A,B]}, Bs) when is_binary(Q) ->
    type_arg_(Q, [A,B], undefined, Bs);
type_arg({p,Q,[A,B]}, Bs) when is_binary(Q) ->
    type_arg_(Q, [A,B], undefined, Bs);
type_arg(Other, _Bs) ->
    error({type_expected, Other,
	   "32/unsigned, 8/signed, 32/fixpoint, 16/fixpoint(4), "
	   "fixpoint(8,8), 32/float754, float754(8,23) or 32/float"}).

type_arg_(<<"fixpoint">>, [], SExpr, Bs) ->
    Size = eval_meta(SExpr, Bs),
    {decl_type({fix,default}, Size, Bs), Size};
type_arg_(<<"fixpoint">>, [F], SExpr, Bs) ->
    Size = eval_meta(SExpr, Bs),
    {decl_type({fix,F}, Size, Bs), Size};
type_arg_(<<"fixpoint">>, [I,F], undefined, Bs) ->
    Fv = eval_meta(F, Bs),
    {{fix,Fv}, eval_meta(I, Bs) + Fv};
type_arg_(<<"float754">>, [], SExpr, Bs) ->
    Size = eval_meta(SExpr, Bs),
    {decl_type({float,default,default}, Size, Bs), Size};
type_arg_(<<"float754">>, [M], SExpr, Bs) ->
    Size = eval_meta(SExpr, Bs),
    {decl_type({float,default,M}, Size, Bs), Size};
type_arg_(<<"float754">>, [E,M], undefined, Bs) ->
    Ev = eval_meta(E, Bs), Mv = eval_meta(M, Bs),
    {{float,Ev,Mv}, 1+Ev+Mv};
type_arg_(Q, As, SExpr, _Bs) ->
    error({type_expected, {Q, length(As), SExpr}}).

%% the low N bits of a value as {T,N}: sign extended when the value is
%% signed and shorter, cut at the top otherwise.  A fixed point target
%% takes the raw bits at its fraction width, so an integer is scaled
%% first and a float literal is a constant; a fixed point or float754
%% value into an integer needs a rounding, as an assignment does.
wrap_to({{float,_,_},_N}, _V, _Bs) ->
    error({wrap_float754,
	   "wrap to float754 has no meaning (the bits of an integer are "
	   "no float), convert the value instead"});
wrap_to({{fix,F},N}, V, Bs) ->
    {Raw,Bs1} = to_raw(V, F, Bs),
    {int,K,Xs} = varp_arith:iarg(Raw),
    {{{fix,F},N,low_bits(Xs, K, N, int)}, Bs1};
wrap_to({T,N}, V, _Bs) when is_tuple(V), element(1,V) =:= flo;
			    is_tuple(V), ?is_fix(element(1,V)) ->
    error({fixpoint_to_integer, {T,N}, "use floor, ceil, round or trunc"});
wrap_to({T,N}, {{float,_,_},_,_}, _Bs) ->
    error({float754_to_integer, {T,N}, "use floor, ceil, round or trunc"});
wrap_to({bool,1}, V, Bs) ->
    {_Vt,_K,Xs} = varp_arith:varg(V),
    {{bool,hd(Xs)}, Bs};
wrap_to({T,N}, V, Bs) ->
    {Vt,K,Xs} = varp_arith:varg(V),
    {{T,N,low_bits(Xs, K, N, Vt)}, Bs}.

low_bits(Xs, K, N, _Vt) when K >= N ->
    lists:sublist(Xs, N);
low_bits(Xs, K, N, Vt) ->
    Ext = case Vt of int -> lists:last(Xs); _ -> false end,
    Xs ++ lists:duplicate(N-K, Ext).

%% does the exact value fit in {T,N}: a boolean.  Signed: the bits above
%% the target all equal its sign bit.  Unsigned: the bits above the
%% target, and the sign of a signed value, are all zero.
fits_in({{float,_,_},_N}, _V, _Bs) ->
    error({fits_float754, "use isinf and isnan for float754"});
fits_in({{fix,F},N}, V, Bs) ->
    {Raw,Bs1} = to_raw(V, F, Bs),
    fits_int(N, varp_arith:iarg(Raw), Bs1);
fits_in({T,N}, V, _Bs) when is_tuple(V), element(1,V) =:= flo;
			    is_tuple(V), ?is_fix(element(1,V)) ->
    error({fixpoint_to_integer, {T,N}, "use floor, ceil, round or trunc"});
fits_in({T,N}, {{float,_,_},_,_}, _Bs) ->
    error({float754_to_integer, {T,N}, "use floor, ceil, round or trunc"});
fits_in({int,N}, V, Bs) ->
    fits_int(N, varp_arith:iarg(V), Bs);
fits_in({bool,1}, V, Bs) ->
    fits_in({uint,1}, V, Bs);
fits_in({_T,N}, V, Bs) ->
    {Vt,K,Xs} = varp_arith:varg(V),
    Above = case Vt of
		int -> lists:nthtail(min(N, K-1), Xs);  %% the sign too
		_ when K > N -> lists:nthtail(N, Xs);
		_ -> []
	    end,
    Vp = Bs#bs.vp,
    {{bool,varp_circuit:all(Vp, [varp_circuit:inv(B) || B <- Above])}, Bs}.

fits_int(N, {int,K,_Xs}, Bs) when K =< N ->
    {{bool,?T}, Bs};
fits_int(N, {int,_K,Xs}, Bs) ->
    Vp = Bs#bs.vp,
    S = lists:nth(N, Xs),
    Same = [varp_circuit:equ_gate(Vp, B, S) || B <- lists:nthtail(N, Xs)],
    {{bool,varp_circuit:all(Vp, Same)}, Bs}.

%% the same bits as another type of the same width: integer <-> fixed
%% point <-> float754, a float from its bit pattern, a float's bits as
%% an integer.  A float literal has no bits until it has a format.
cast_to(_Type, {flo,V}, _Bs) ->
    error({cast_literal, V, "a float literal has no bits of its own, "
	   "give it a type first: cast(X, ..) with X == 1.5"});
cast_to({PType,same}, V, Bs) ->
    {K,_Xs} = bits_of(V),
    cast_to({decl_type(PType, K, Bs), K}, V, Bs);
cast_to({T,N}, V, Bs) ->
    {K,Xs0} = bits_of(V),
    %% a constant has only the bits its value needs: cast(0x3FC00000,
    %% 32/float754) is the 32 bit pattern
    Xs = case V of
	     {Vt,_,_} when is_atom(Vt), K < N ->
		 case varp_arith:vconst(V) of
		     C when is_integer(C) -> low_bits(Xs0, K, N, Vt);
		     false -> Xs0
		 end;
	     _ -> Xs0
	 end,
    case length(Xs) of
	N when T =:= bool -> {{bool,hd(Xs)}, Bs};
	N -> {{T,N,Xs}, Bs};
	_ ->
	    error({cast_width, {operand_kind(V), K}, {T,N},
		   "cast keeps the bits, so the widths must agree; "
		   "wrap(E, T) cuts or extends"})
    end.

bits_of({bool,X}) -> {1,[X]};
bits_of({_T,N,Xs}) -> {N,Xs}.

%%
%% IEEE 754 light, {float,E,M}: a sign bit, E exponent bits and M
%% fraction bits, the bits in the order fraction, exponent, sign (LSB
%% first like every vector).  Normal numbers and zero only: no NaN, no
%% infinity, nothing subnormal (such a result is flushed to zero, an
%% exponent overflow is not caught).  The pure part, encoding a number
%% with round to nearest even and printing, is varp_float.
%%
%% There is the type, the literals, comparison, negation, abs, min
%% and max, the conversions (an integer or fixed point operand that
%% meets a float becomes a float, round to nearest even; a float
%% assigned to a fixed point variable is truncated toward zero;
%% floor/ceil/round/trunc give an integer) and + - * /.  inf and NaN
%% are read and produced as IEEE says (inf - inf, 0 * inf, 0/0 and
%% inf/inf are NaN, a NaN operand gives NaN, NaN compares unordered),
%% only subnormal results are flushed to zero.  --inf and --nan say
%% whether such a result may, may not or must arise, --fdivz is the
%% --divz of the float division, the name inf is the literal ("X !=
%% inf") and isnan(X), isinf(X) test a value.
%%
is_floatish({T,_,_}) -> ?is_float(T);
is_floatish(_) -> false.

%% the format two operands share
float_type(A, B) ->
    case lists:usort([T || {T,_,_} <- [A,B], ?is_float(T)]) of
	[T] -> T;
	Ts -> error({float754_mixed, Ts})
    end.

fsplit({{float,E,M},_N,Xs}) ->
    {Man,Rest} = lists:split(M, Xs),
    {Exp,[S]} = lists:split(E, Rest),
    {S, {uint,E,Exp}, {uint,M,Man}}.

%% exponent and fraction as one unsigned: the order of the magnitudes
fmag({{float,E,M},_N,Xs}) -> {uint,E+M,lists:sublist(Xs, E+M)}.
fsign({{float,_,_},_N,Xs}) -> lists:last(Xs).
fbits({{float,_,_},N,Xs}) -> {uint,N,Xs};
fbits(V) -> V.

fmake(T={float,E,M}, {_,_,MagXs}, S) ->
    {T,1+E+M, vfit(MagXs, E+M) ++ [S]}.

%% cut or zero extend a bit list to K bits
vfit(Xs, K) when length(Xs) >= K -> lists:sublist(Xs, K);
vfit(Xs, K) -> Xs ++ lists:duplicate(K - length(Xs), false).

zeros(K) -> lists:duplicate(K, false).

const_int(C) when C < 0 -> const_vector(int, C, varp_math:signed_size(C));
const_int(C) -> const_vector(uint, C, varp_math:unsigned_size(C)).

%% a literal: a tiny inexact one counts as an underflow too
float_const(V, T, Bs) when is_integer(V) ->
    float_scaled(V, 0, T, Bs);
float_const(V, T={float,E,M}, Bs) when is_float(V) ->
    <<S:1,Eb:11,Mb:52>> = <<V:64/float>>,
    if Eb =:= 0, Mb =:= 0 ->
	    {const_vector(T, S bsl (E+M), 1+E+M), Bs};
       Eb =:= 2047 ->
	    error({float754_not_a_number, V});
       true ->
	    {I, Sh} = if Eb =:= 0 -> {Mb, -1074};
			 true -> {(1 bsl 52) bor Mb, Eb - 1075}
		      end,
	    float_scaled(if S =:= 1 -> -I; true -> I end, Sh, T, Bs)
    end.

%% I * 2^Shift as a constant of the format, under --underflow
float_scaled(I, Shift, T={float,E,M}, Bs) ->
    case varp_float:encode_status(I, Shift, E, M, float_mode(Bs)) of
	{ok,Bits,Underflow} ->
	    {const_vector(T, Bits, 1+E+M), underflow_folded(Underflow, Bs)};
	{error,Reason} ->
	    error(Reason)
    end.

%% an operand as a float of format T
to_float(V={{float,E,M},_,_}, {float,E,M}, Bs) ->
    {V, Bs};
to_float({T0,_,_}, T, _Bs) when ?is_float(T0) ->
    error({float754_mixed, [T0,T]});
to_float({flo,inf}, T={float,E,M}, Bs) ->
    {const_vector(T, varp_float:inf_bits(0, E, M), 1+E+M), Bs};
to_float({flo,'-inf'}, T={float,E,M}, Bs) ->
    {const_vector(T, varp_float:inf_bits(1, E, M), 1+E+M), Bs};
to_float({flo,X}, T, Bs) ->
    float_const(X, T, Bs);
to_float({bool,X}, T, Bs) ->
    to_float({uint,1,[X]}, T, Bs);
to_float(V, T, Bs) ->
    {F, Raw} = case V of
		   {{fix,F0},N,Xs} -> {F0, {int,N,Xs}};
		   _ -> {0, varp_arith:iarg(V)}
	       end,
    case vconst(Raw) of
	R when is_integer(R) ->
	    float_scaled(R, -F, T, Bs);
	false ->
	    int_to_float(Raw, F, T, Bs)
    end.

%% a two's complement integer (scaled by 2^F) to a float: magnitude,
%% normalise with a leading zero count, round to nearest even
int_to_float(Raw={int,_W,Xs}, F, T={float,E,_M}, Bs) ->
    S = lists:last(Xs),
    {A0, Bs1} = operation1('abs', Raw, Bs),
    A = {uint,Wa,_} = varp_arith:varg(A0),
    {{uint,Wa,NXs}, LZ, Bs2} = lz_norm(A, Bs1),
    K0 = Wa - 1 + varp_float:bias(E) - F,
    {ExpI, Bs3} = operation2('sub', const_int(K0), LZ, Bs2),
    {Z1, Bs4} = operation2('eq', A, {uint,1,[false]}, Bs3),
    {Rounded, Zero, Over, Bs5} =
	fpack({uint,Wa,NXs}, {bool,?F}, ExpI, Z1, {bool,?F}, T, Bs4),
    Bs6 = inf_status(Over, Bs5),
    special_result({bool,?F}, Over, Zero, Rounded, {bool,S}, T, Bs6).

%% the finite result of an operation or a conversion.  NXs holds the
%% normalised magnitude, its leading one at the top (bit W-1), below
%% it the fraction, the guard bit and sticky bits (ExtraSticky ors
%% in); Ex is the biased exponent of the leading one as a signed
%% vector.  Below the normal range (Ex <= 0) the significand is
%% shifted right into a subnormal, 1-Ex steps with a sticky bit, or
%% under --ftz left alone and flushed to zero.  Round to nearest even:
%% the carry of the rounding runs into the exponent field, which
%% turns an all ones subnormal fraction into the smallest normal and
%% lifts an exponent of zero.  Exact0 says the exact result is zero
%% (NXs and Ex mean nothing then), Masked that an operand is special
%% (inf, NaN, a zero) and the finite path is noise.  --underflow is a
%% tiny and inexact result (tininess before rounding), in ftz any
%% tiny nonzero one.  Returns {Mag, Zero, Over, Bs}: the E+M bit
%% magnitude, the zero flag for special_result (exact, or flushed)
%% and the overflow (for inf_status, already masked).
fpack({uint,W,NXs0}, ExtraSticky, Ex, Exact0, Masked, {float,E,M}, Bs) ->
    Zv = {uint,1,[false]},
    Wm = M+3,
    {Wn, NXs} = if W < Wm -> {Wm, zeros(Wm-W) ++ NXs0};
		   true -> {W, NXs0}
		end,
    Top = lists:nthtail(Wn-(M+1), NXs),             %% fraction and lead
    Guard0 = lists:nth(Wn-(M+1), NXs),
    {St0, Bs1} = any_bits(lists:sublist(NXs, Wn-(M+2)), Bs),
    {{bool,StL}, Bs2} = operation2('or', St0, ExtraSticky, Bs1),
    Sig = {uint,Wm,[StL, Guard0 | Top]},
    {Tiny={bool,TinyL}, Bs3} = operation2('lte', Ex, Zv, Bs2),
    Ftz = maps:get(ftz, Bs#bs.option, false),
    {{uint,Wm,[StF, GuardF | TopF]}, Bs4} =
	case Ftz of
	    true ->
		{Sig, Bs3};
	    false ->
		%% the shift 1-Ex when tiny, at most M+2 (everything
		%% into the sticky bit), nothing otherwise
		NB = varp_math:unsigned_size(M+2),
		{D0, B1} = operation2('sub', const_int(1), Ex, Bs3),
		{{bool,BigL}, B2} = operation2('gte', D0, const_int(M+2), B1),
		D0u = {uint,NB,vfit(element(3, varp_arith:varg(D0)), NB)},
		{D1, B3} = operation2('bor', D0u, {uint,NB,lists:duplicate(NB, BigL)}, B2),
		{D2, B4} = operation2('band', D1, {uint,NB,lists:duplicate(NB, TinyL)}, B3),
		Amt = {uint,NB,vfit(element(3, varp_arith:varg(D2)), NB)},
		{{uint,Wm,ShXs}, StSh, B5} = barrel_right(Sig, Amt, M+2, B4),
		{{bool,StL2}, B6} = operation2('or', {bool,hd(ShXs)}, StSh, B5),
		{{uint,Wm,[StL2|tl(ShXs)]}, B6}
	end,
    ManXs = lists:sublist(TopF, M),
    Lsb = hd(TopF),
    {{bool,Up}, Bs5} = round_up(GuardF, {bool,StF}, Lsb, Bs4),
    ExXs = vfit(element(3, Ex), E),
    {ExField, Bs6} =
	case Ftz of
	    true -> {{uint,E,ExXs}, Bs5};
	    false -> ite(undefined, Tiny, {uint,E,zeros(E)}, {uint,E,ExXs}, Bs5)
	end,
    {uint,E,ExFXs} = ExField,
    {R0, Bs7} = operation2('add', {uint,E+M,ManXs ++ ExFXs}, {uint,1,[Up]}, Bs6),
    RXs = vfit(element(3, varp_arith:varg(R0)), E+M),
    Rounded = {uint,E+M,RXs},
    {Inexact, Bs8} = operation2('or', {bool,GuardF}, {bool,StF}, Bs7),
    {Real, Bs9} = operation2('and', negate(Exact0), negate(Masked), Bs8),
    %% tiny after rounding (ftz): a carry out of an all ones fraction
    %% lifts an exponent of zero to one
    {Neg, Bs10} = operation2('lt', Ex, Zv, Bs9),
    {Ex0, Bs11} = operation2('eq', Ex, Zv, Bs10),
    {AllOnes, Bs12} = operation2('eq', {uint,M,ManXs}, {uint,M,ones(M)}, Bs11),
    {Carry, Bs13} = operation2('and', {bool,Up}, AllOnes, Bs12),
    {Tiny0, Bs14} = operation2('and', Ex0, negate(Carry), Bs13),
    {TinyR, Bs15} = operation2('or', Neg, Tiny0, Bs14),
    {Zero, Under, Bs16} =
	case Ftz of
	    true ->
		{Flushed, B7} = operation2('and', TinyR, Real, Bs15),
		{Z, B8} = operation2('or', Exact0, Flushed, B7),
		{Z, Flushed, B8};
	    false ->
		{U0, B7} = operation2('and', Tiny, Inexact, Bs15),
		{U, B8} = operation2('and', U0, Real, B7),
		{Exact0, U, B8}
	end,
    Bs17 = underflow_status(Under, Bs16),
    %% above the range: the exponent at the top, or the rounding
    %% carrying it there
    {Over0, Bs18} = operation2('gte', Ex, const_int((1 bsl E)-1), Bs17),
    {Over1, Bs19} = operation2('eq', {uint,E,lists:nthtail(M, RXs)}, {uint,E,ones(E)}, Bs18),
    {Over2, Bs20} = operation2('or', Over0, Over1, Bs19),
    {Over3, Bs21} = operation2('and', Over2, negate(Zero), Bs20),
    {Over, Bs22} = operation2('and', Over3, Real, Bs21),
    {Rounded, Zero, Over, Bs22}.

any_bits([], Bs) -> {{bool,?F}, Bs};
any_bits(Xs, Bs) -> operation2('neq', {uint,length(Xs),Xs}, {uint,1,[false]}, Bs).

%% round to nearest even: up when the guard bit is set and either a
%% lower bit is set or the result would be odd
round_up(Guard, Sticky, Lsb, Bs) ->
    {T1, Bs1} = operation2('or', Sticky, {bool,Lsb}, Bs),
    operation2('and', {bool,Guard}, T1, Bs1).

%% shift the leading one of an unsigned vector to the top, and count
%% the steps: a conditional shift by every power of two, top down
lz_norm(A={uint,1,_}, Bs) ->
    {A, {uint,1,[false]}, Bs};
lz_norm(A={uint,W,_}, Bs) ->
    Ks = [1 bsl K || K <- lists:seq(varp_math:ilog2(W-1), 0, -1)],
    {Cur, Zs, Bs1} =
	lists:foldl(
	  fun(K, {C={uint,W1,CXs}, Acc, B}) ->
		  Top = {uint,K,lists:nthtail(W1-K, CXs)},
		  {Z, B1} = operation2('eq', Top, {uint,1,[false]}, B),
		  Shifted = {uint,W1,zeros(K) ++ lists:sublist(CXs, W1-K)},
		  {C1, B2} = ite(undefined, Z, Shifted, C, B1),
		  {{uint,W1,vfit(element(3, varp_arith:varg(C1)), W1)},
		   [{K,Z}|Acc], B2}
	  end, {A,[],Bs}, Ks),
    LZ = {uint,length(Ks),[L || {_K,{bool,L}} <- lists:keysort(1, Zs)]},
    {Cur, LZ, Bs1}.

%% a float as a fixed point value with F fraction bits, the magnitude
%% truncated; Sticky ors the lost bits into the lowest bit (for the
%% rounding functions); Width bounds the shift to the left
float_to_fix(V={{float,E,M},_,_}, F, Sticky, Width, Bs) ->
    {S, Exp0, {uint,M,ManXs}} = fsplit(V),
    {{bool,H}, Bs0} = operation2('neq', Exp0, {uint,1,[false]}, Bs),
    Sig = {uint,M+1,ManXs ++ [H]},             %% the hidden one
    %% a subnormal pattern (no hidden one) has the exponent 1
    {Exp, Bs1} = operation2('bor', Exp0, {uint,1,[neg_lit(H)]}, Bs0),
    C = varp_float:bias(E) + M - F,             %% shift left by Exp - C
    MaxL = max(0, min((1 bsl E) - 1 - C, Width)),
    MaxR = M + 2,                               %% beyond: all sticky
    {Dl, Bs2} = operation2('sub', Exp, const_int(C), Bs1),
    {Left, Bs3} = barrel_left(Sig, Dl, MaxL, Bs2),
    {Dr, Bs4} = operation2('sub', const_int(C), Exp, Bs3),
    {Right0, StR0, Bs5} = barrel_right(Sig, Dr, MaxR, Bs4),
    {Big, Bs6} = operation2('gte', Dr, const_int(MaxR), Bs5),
    {NZ, Bs7} = operation2('neq', Sig, {uint,1,[false]}, Bs6),
    {Right1, Bs8} = ite(undefined, Big, {uint,M+1,zeros(M+1)}, Right0, Bs7),
    {StBig, Bs9} = operation2('and', Big, NZ, Bs8),
    {StR, Bs10} = operation2('or', StBig, StR0, Bs9),
    {Ge, Bs11} = operation2('gte', Exp, const_int(C), Bs10),
    Wm = M+1+MaxL,
    LeftW = {uint,Wm,vfit(element(3, varp_arith:varg(Left)), Wm)},
    RightW = {uint,Wm,vfit(element(3, varp_arith:varg(Right1)), Wm)},
    {Mag0, Bs12} = ite(undefined, Ge, LeftW, RightW, Bs11),
    {Mag, Bs13} =
	case Sticky of
	    true ->
		{St, Bs12a} = operation2('and', negate(Ge), StR, Bs12),
		{bool,StL} = St,
		operation2('bor', Mag0, {uint,1,[StL]}, Bs12a);
	    false ->
		{Mag0, Bs12}
	end,
    Int = varp_arith:iarg(varp_arith:varg(Mag)),
    {Neg, Bs14} = operation1('neg', Int, Bs13),
    {Raw, Bs15} = ite(undefined, {bool,S}, Neg, Int, Bs14),
    {fix_result(F, Raw), Bs15}.

%% V << Amount, the amount up to Max (an integer vector, its low bits
%% count), W+Max bits out
barrel_left(V={uint,_W,_}, _Amount, 0, Bs) ->
    {V, Bs};
barrel_left({uint,W,Xs}, Amount, Max, Bs) ->
    Wout = W + Max,
    NB = varp_math:unsigned_size(Max),
    AmtXs = vfit(element(3, Amount), NB),
    lists:foldl(
      fun(K, {C={uint,_,CXs}, B}) ->
	      Sh = 1 bsl K,
	      Shifted = {uint,Wout,zeros(Sh) ++ lists:sublist(CXs, Wout-Sh)},
	      {C1, B1} = ite(undefined, {bool,lists:nth(K+1, AmtXs)}, Shifted, C, B),
	      {{uint,Wout,vfit(element(3, varp_arith:varg(C1)), Wout)}, B1}
      end, {{uint,Wout,Xs ++ zeros(Max)}, Bs}, lists:seq(0, NB-1)).

%% V >> Amount, zeros in, and a sticky bit: were any ones shifted out
barrel_right({uint,W,Xs}, Amount, Max, Bs) ->
    NB = varp_math:unsigned_size(Max),
    AmtXs = vfit(element(3, Amount), NB),
    lists:foldl(
      fun(K, {C={uint,_,CXs}, St, B}) ->
	      Sh = min(1 bsl K, W),
	      Bit = {bool,lists:nth(K+1, AmtXs)},
	      Shifted = {uint,W,lists:nthtail(Sh, CXs) ++ zeros(Sh)},
	      {AnyLow, B1} = any_bits(lists:sublist(CXs, Sh), B),
	      {StK, B2} = operation2('and', Bit, AnyLow, B1),
	      {St1, B3} = operation2('or', St, StK, B2),
	      {C1, B4} = ite(undefined, Bit, Shifted, C, B3),
	      {{uint,W,vfit(element(3, varp_arith:varg(C1)), W)}, St1, B4}
      end, {{uint,W,Xs}, {bool,?F}, Bs}, lists:seq(0, NB-1)).

float_op1(Op, V={{float,E,M},N,Xs}, Bs) ->
    case Op of
	'neg' -> {{{float,E,M},N,lists:droplast(Xs) ++ [neg_lit(fsign(V))]}, Bs};
	'abs' -> {{{float,E,M},N,lists:droplast(Xs) ++ [?F]}, Bs};
	'not' -> operation2('neq', fmag(V), {uint,1,[false]}, Bs);
	_ -> error({float754_operator, Op})
    end;
float_op1(_Op, _V, _Bs) ->
    false.

float_op2(Op, A, B, Bs) when is_tuple(A), is_tuple(B) ->
    case is_floatish(A) orelse is_floatish(B) of
	true -> float_op2_(Op, A, B, Bs);
	false -> false
    end;
float_op2(_Op, _A, _B, _Bs) ->
    false.

float_op2_(Op, A, B, Bs) when Op =:= 'band'; Op =:= 'bor';
			     Op =:= 'bxor'; Op =:= 'equ' ->
    %% bit by bit on the raw bits (the mux of ?:)
    T = float_type(A, B),
    {R, Bs1} = operation2(Op, fbits(A), fbits(B), Bs),
    {{_,N,Xs}, _} = {varp_arith:varg(R), ok},
    {{T,N,Xs}, Bs1};
float_op2_(Op, A, B, Bs) when Op =:= 'lt'; Op =:= 'lte'; Op =:= 'gt';
			     Op =:= 'gte'; Op =:= 'eq'; Op =:= 'neq' ->
    T = float_type(A, B),
    {Af, Bs1} = to_float(A, T, Bs),
    {Bf, Bs2} = to_float(B, T, Bs1),
    float_compare(Op, Af, Bf, Bs2);
float_op2_(Op, A, B, Bs) when Op =:= 'min'; Op =:= 'max' ->
    %% minNum/maxNum of IEEE 754-2008: a NaN loses to a number
    T = float_type(A, B),
    {Af, Bs1} = to_float(A, T, Bs),
    {Bf, Bs2} = to_float(B, T, Bs1),
    {Lt, Bs3} = float_compare('lt', Af, Bf, Bs2),
    {R0, Bs4} = case Op of
		    'min' -> ite(undefined, Lt, Af, Bf, Bs3);
		    'max' -> ite(undefined, Lt, Bf, Af, Bs3)
		end,
    {{_,_,Na}, Bs5} = fclass(Af, Bs4),
    {{_,_,Nb}, Bs6} = fclass(Bf, Bs5),
    {R1, Bs7} = ite(undefined, Nb, Af, retag(T, R0), Bs6),
    {R2, Bs8} = ite(undefined, Na, Bf, retag(T, R1), Bs7),
    {retag(T, R2), Bs8};
float_op2_('mul', A, B, Bs) ->
    T = float_type(A, B),
    {Af, Bs1} = to_float(A, T, Bs),
    {Bf, Bs2} = to_float(B, T, Bs1),
    float_mul(Af, Bf, T, Bs2);
float_op2_(Op, A, B, Bs) when Op =:= 'add'; Op =:= 'sub' ->
    T = float_type(A, B),
    {Af, Bs1} = to_float(A, T, Bs),
    {Bf0, Bs2} = to_float(B, T, Bs1),
    %% a - b is a + (-b)
    Bf = case Op of 'sub' -> fneg(Bf0); 'add' -> Bf0 end,
    float_add(Af, Bf, T, Bs2);
float_op2_('div', A, B, Bs) ->
    T = float_type(A, B),
    {Af, Bs1} = to_float(A, T, Bs),
    {Bf, Bs2} = to_float(B, T, Bs1),
    float_div(Af, Bf, T, Bs2);
float_op2_(Op, _A, _B, _Bs) ->
    error({float754_operator, Op}).

%% --inf: an overflowing result is allowed, forbidden or required
inf_status({bool,Over}, Bs) ->
    varp_arith:set_status(Bs#bs.vp, Over, maps:get(inf, Bs#bs.option, ignore)),
    Bs.

%% --underflow: a tiny and inexact result is allowed, forbidden or
%% required (in ftz every tiny nonzero result, it is lost)
underflow_status({bool,U}, Bs) ->
    varp_arith:set_status(Bs#bs.vp, U, maps:get(underflow, Bs#bs.option, ignore)),
    Bs.

%% --ops lib: the whole operation is the library circuit op_fmul,
%% op_fadd or op_fdiv (over op_fnorm, op_fpack, op_fresult and
%% op_fclass), with e, m and the --ftz flag as meta parameters and the
%% flags for --inf, --underflow, --nan (and --fdivz) as out parameters,
%% fresh symbols of the caller
lib_float_op(Name, Af, Bf, T={float,E,M}, Bs) ->
    Z = case float_mode(Bs) of ftz -> 1; ieee -> 0 end,
    {Prefix, Bs1} = circuit_prefix(Name, Bs),
    Flag = fun(F) -> {p,<<Prefix/binary,F/binary>>,[]} end,
    Outs = [Flag(<<"over">>), Flag(<<"under">>), Flag(<<"nan">>)] ++
	case Name of
	    <<"op_fdiv">> -> [Flag(<<"divz">>)];
	    _ -> []
	end,
    {R, Bs2} = lib_call(Name, [{const,E},{const,M},{const,Z},
			       {value,fbits(Af)},{value,fbits(Bf)}] ++ Outs, Bs1),
    {[Over,Under,NaN|Rest], Bs3} =
	lists:mapfoldl(fun(P, B) -> bld(P, B) end, Bs2, Outs),
    Bs4 = inf_status(Over, Bs3),
    Bs5 = underflow_status(Under, Bs4),
    Bs6 = nan_status(NaN, Bs5),
    Bs7 = case Rest of
	      [{bool,DivZ}] ->
		  varp_arith:set_status(Bs6#bs.vp, DivZ, maps:get(fdivz, Bs6#bs.option, false)),
		  Bs6;
	      [] -> Bs6
	  end,
    {retag(T, R), Bs7}.

%% --ftz: ieee (gradual underflow, subnormal results) or ftz (light,
%% flush to zero)
float_mode(Bs) ->
    case maps:get(ftz, Bs#bs.option, false) of
	true -> ftz;
	false -> ieee
    end.

%% a folded operation: the bits and its underflow flag
fold_status({Bits, Underflow}, T={float,E,M}, Bs) ->
    Bs1 = inf_folded(Bits, T, Bs),
    {const_vector(T, Bits, 1+E+M), underflow_folded(Underflow, Bs1)}.

%% a folded value or a literal that underflowed (like inf_folded, a
%% constant that did not says nothing, so --underflow true can hold)
underflow_folded(true, Bs) -> underflow_status({bool,true}, Bs);
underflow_folded(false, Bs) -> Bs.

%% a folded constant that overflowed or is NaN, under --inf and --nan
inf_folded(Bits, {float,E,M}, Bs) ->
    case varp_float:fields(Bits, E, M) of
	{_, Eb, 0} when Eb =:= (1 bsl E) - 1 -> inf_status({bool,true}, Bs);
	{_, Eb, _} when Eb =:= (1 bsl E) - 1 -> nan_status({bool,true}, Bs);
	_ -> Bs
    end.

%% --nan: a NaN result is allowed, forbidden or required
nan_status({bool,N}, Bs) ->
    varp_arith:set_status(Bs#bs.vp, N, maps:get(nan, Bs#bs.option, ignore)),
    Bs.

%% zero, inf and NaN of a float: {{bool,Z},{bool,I},{bool,N}}
fclass(V={{float,E,_M},_,_}, Bs) ->
    {_, Exp, Man} = fsplit(V),
    {ExpAll, Bs1} = operation2('eq', Exp, {uint,E,ones(E)}, Bs),
    {ManZ, Bs2} = operation2('eq', Man, {uint,1,[false]}, Bs1),
    {Z, Bs3} = operation2('eq', fmag(V), {uint,1,[false]}, Bs2),
    {I, Bs4} = operation2('and', ExpAll, ManZ, Bs3),
    {N, Bs5} = operation2('and', ExpAll, negate(ManZ), Bs4),
    {{Z,I,N}, Bs5}.

nan_pattern(E, M) -> {uint,E+M,zeros(M-1) ++ [true] ++ ones(E)}.

%% the special operands of a two operand operation: the result is NaN
%% (NaNc), the result is inf with the sign S (InfC), or the result is
%% zero (ZeroC); Finite is the ordinary magnitude.  The sign of a NaN is
%% zero.
special_result(NaNc, InfC, ZeroC, Finite, S, T={float,E,M}, Bs) ->
    Bs1 = nan_status(NaNc, Bs),
    Inf = {uint,E+M,zeros(M) ++ ones(E)},
    {M1, Bs2} = ite(undefined, ZeroC, {uint,E+M,zeros(E+M)}, Finite, Bs1),
    {M2, Bs3} = ite(undefined, InfC, Inf, M1, Bs2),
    {M3, Bs4} = ite(undefined, NaNc, nan_pattern(E, M), M2, Bs3),
    {{bool,S1}, Bs5} = operation2('and', S, negate(NaNc), Bs4),
    {fmake(T, varp_arith:varg(M3), S1), Bs5}.

%% a / b: both significands normalised (a subnormal pattern has leading
%% zeros), the quotient of a << (M+2) by b has M+3 bits with the
%% leading one at the top or one below, a nonzero remainder is the
%% sticky bit.  Division by zero is --fdivz and gives inf.
float_div(Af, Bf, T={float,E,M}, Bs) ->
    Const = case {vconst(Af), vconst(Bf)} of
		{Ab, Bb} when is_integer(Ab), is_integer(Bb) ->
		    %% a zero divisor is left to the circuit and --fdivz
		    element(1, varp_float:light_value(Bb, E, M)) =/= zero;
		_ -> false
	    end,
    case Const of
	true ->
	    fold_status(varp_float:div_fold(vconst(Af), vconst(Bf), E, M, float_mode(Bs)), T, Bs);
	false ->
	  case lib_ops(Bs) of
	    true -> lib_float_op(<<"op_fdiv">>, Af, Bf, T, Bs);
	    false ->
	    Zv = {uint,1,[false]},
	    {Sa, Ea0, {uint,M,MaXs}} = fsplit(Af),
	    {Sb, Eb0, {uint,M,MbXs}} = fsplit(Bf),
	    {{bool,S}, Bs1} = operation2('xor', {bool,Sa}, {bool,Sb}, Bs),
	    {{bool,Ha}, Bs2} = operation2('neq', Ea0, Zv, Bs1),
	    {{bool,Hb}, Bs3} = operation2('neq', Eb0, Zv, Bs2),
	    {Ea, Bs4} = operation2('bor', Ea0, {uint,1,[neg_lit(Ha)]}, Bs3),
	    {Eb, Bs5} = operation2('bor', Eb0, {uint,1,[neg_lit(Hb)]}, Bs4),
	    SigA = {uint,M+1,MaXs ++ [Ha]},
	    SigB = {uint,M+1,MbXs ++ [Hb]},
	    {SigAn, LZa, Bs6} = lz_norm(SigA, Bs5),
	    {SigBn, LZb, Bs7} = lz_norm(SigB, Bs6),
	    {Azero, Bs8} = operation2('eq', SigA, Zv, Bs7),
	    {Bzero={bool,BzL}, Bs8a} = operation2('eq', SigB, Zv, Bs8),
	    %% x/0 is --fdivz; 0/0 is not a number, that is --nan
	    {{bool,DivZ}, Bs9} = operation2('and', Bzero, negate(Azero), Bs8a),
	    varp_arith:set_status(Bs9#bs.vp, DivZ, maps:get(fdivz, Bs9#bs.option, false)),
	    {uint,_,AnXs} = SigAn,
	    Num = {uint,2*M+3,zeros(M+2) ++ AnXs},
	    %% the integer divider's own --divz status fires on the same
	    %% condition: keep it out of the way with a one in the divisor
	    {Den, Bs10} = operation2('bor', SigBn, {uint,1,[BzL]}, Bs9),
	    {Q0, Rnz, Bs11} =
		case lib_ops(Bs10) of
		    true ->
			{Q1, B1} = operation2('div', Num, Den, Bs10),
			{P1, B2} = operation2('mul', Q1, Den, B1),
			{R1, B3} = operation2('neq', P1, Num, B2),
			{Q1, R1, B3};
		    false ->
			{Q1, R1} = varp_arith:divrem(Bs10#bs.vp, Num, Den),
			{R2, B1} = operation2('neq', R1, Zv, Bs10),
			{Q1, R2, B1}
		end,
	    W = M+3,
	    Qw = {uint,W,vfit(element(3, varp_arith:varg(Q0)), W)},
	    {Qn, LZ, Bs12} = lz_norm(Qw, Bs11),
	    %% Ea - Eb + (LZb - LZa) + bias - LZ
	    {E1, Bs15} = operation2('sub', Ea, Eb, Bs12),
	    {E2, Bs16} = operation2('add', E1, LZb, Bs15),
	    {E3, Bs17} = operation2('sub', E2, LZa, Bs16),
	    {E4, Bs18} = operation2('add', E3, const_int(varp_float:bias(E)), Bs17),
	    {Ex, Bs19} = operation2('sub', E4, LZ, Bs18),
	    {{_,Ia,Na}, Bs26a} = fclass(Af, Bs19),
	    {{_,Ib,Nb}, Bs26b} = fclass(Bf, Bs26a),
	    %% 0/0, inf/inf and a NaN operand: NaN; inf/x: inf; x/inf: 0
	    {N1, Bs26c} = operation2('or', Na, Nb, Bs26b),
	    {N2, Bs26d} = operation2('and', Azero, Bzero, Bs26c),
	    {N3, Bs26e} = operation2('and', Ia, Ib, Bs26d),
	    {N4, Bs26f} = operation2('or', N1, N2, Bs26e),
	    {NaNc, Bs26g} = operation2('or', N4, N3, Bs26f),
	    {M1, Bs26h} = operation2('or', NaNc, Bzero, Bs26g),
	    {M2, Bs26i} = operation2('or', M1, Ia, Bs26h),
	    {Masked, Bs26j} = operation2('or', M2, Ib, Bs26i),
	    {Rounded, Zero0, Over, Bs27} = fpack(Qn, Rnz, Ex, Azero, Masked, T, Bs26j),
	    {Zero, Bs27a} = operation2('or', Zero0, Ib, Bs27),
	    Bs31 = inf_status(Over, Bs27a),
	    {InfC0, Bs32} = operation2('or', Over, Bzero, Bs31),
	    {InfC, Bs33} = operation2('or', InfC0, Ia, Bs32),
	    special_result(NaNc, InfC, Zero, Rounded, {bool,S}, T, Bs33)
	  end
    end.

fneg(V={T,N,Xs}) -> {T,N,lists:droplast(Xs) ++ [neg_lit(fsign(V))]}.

%% sqrt of a float, a fixed point value, an integer (fixed point with
%% --fixpoint fraction bits, like a float literal that meets one) or a
%% literal
sqrt_op({flo,V}, Bs) when is_number(V), V >= 0 ->
    {{flo,math:sqrt(V)}, Bs};
sqrt_op({flo,inf}, Bs) ->
    {{flo,inf}, Bs};
sqrt_op({flo,V}, _Bs) ->
    error({sqrt_negative, V});
sqrt_op(V={{float,_,_},_,_}, Bs) ->
    float_sqrt(V, float_type(V, V), Bs);
sqrt_op(V, Bs) when is_tuple(V) ->
    F = case V of
	    {{fix,F0},_,_} -> F0;
	    _ -> fix_frac(Bs)
	end,
    {Raw, Bs1} = to_raw(V, F, Bs),
    fix_sqrt(Raw, F, Bs1).

%% floor(sqrt(v)) in fixed point: isqrt(raw << F) has F fraction bits
%% again.  A negative operand has no model (a constant is an error).
fix_sqrt(Raw, F, Bs) ->
    case vconst(Raw) of
	R when is_integer(R), R < 0 ->
	    error({sqrt_negative, R / (1 bsl F)});
	R when is_integer(R) ->
	    {fix_result(F, const_int(varp_math:isqrt(R bsl F))), Bs};
	false ->
	    {int,N,Xs} = varp_arith:iarg(Raw),
	    varp_arith:set_status(Bs#bs.vp, lists:last(Xs), false),
	    Mag = {uint,N-1+F,zeros(F) ++ lists:droplast(Xs)},
	    {Q, Bs1} = isqrt(Mag, Bs),
	    {fix_result(F, Q), Bs1}
    end.

%% floor(sqrt(a)) of an unsigned vector, and whether a remainder is
%% left; --ops lib takes op_isqrt
isqrt(A={uint,W0,Xs0}, Bs) ->
    {Q, _Rnz, Bs1} = isqrt_rem(A, Bs),
    _ = {W0, Xs0},
    {Q, Bs1}.

isqrt_rem({uint,W0,Xs0}, Bs) ->
    {W, Xs} = if W0 rem 2 =:= 1 -> {W0+1, Xs0 ++ [false]};
		 true -> {W0, Xs0}
	      end,
    K = W div 2,
    case lib_ops(Bs) of
	true ->
	    {Prefix, Bs1} = circuit_prefix(<<"op_isqrt">>, Bs),
	    Rp = {p,<<Prefix/binary,"r">>,[]},
	    {Q, Bs2} = lib_call(<<"op_isqrt">>, [{const,K},{value,{uint,W,Xs}},Rp], Bs1),
	    {R, Bs3} = bld(Rp, Bs2),
	    {Rnz, Bs4} = operation2('neq', R, {uint,1,[false]}, Bs3),
	    {{uint,K,vfit(element(3, varp_arith:varg(Q)), K)}, Rnz, Bs4};
	false ->
	    isqrt_circuit(K, Xs, Bs)
    end.

%% restoring square root, two bits of a per step from the top: the
%% partial remainder shifted with the next pair, the root bit says
%% whether 4q+1 fits, the remainder follows
isqrt_circuit(K, Xs, Bs) ->
    Wr = K+3,
    Pairs = [{lists:nth(2*I+1, Xs), lists:nth(2*I+2, Xs)} || I <- lists:seq(K-1, 0, -1)],
    {R, Q, Bs1} =
	lists:foldl(
	  fun({B0,B1}, {{uint,_,RXs}, {uint,_,QXs}, B}) ->
		  R1 = {uint,Wr,vfit([B0,B1|RXs], Wr)},
		  Tv = {uint,Wr,vfit([true,false|QXs], Wr)},
		  {Ge={bool,GeL}, Ba} = operation2('gte', R1, Tv, B),
		  {D, Bb} = operation2('sub', R1, Tv, Ba),
		  Dv = {uint,Wr,vfit(element(3, varp_arith:varg(D)), Wr)},
		  {R2, Bc} = ite(undefined, Ge, Dv, R1, Bb),
		  {{uint,Wr,vfit(element(3, varp_arith:varg(R2)), Wr)},
		   {uint,K,vfit([GeL|QXs], K)}, Bc}
	  end, {{uint,Wr,zeros(Wr)}, {uint,K,zeros(K)}, Bs}, Pairs),
    {Rnz, Bs2} = operation2('neq', R, {uint,1,[false]}, Bs1),
    {Q, Rnz, Bs2}.

%% sqrt(a) in float754: the significand normalised (a subnormal has
%% leading zeros), the unbiased exponent made even by doubling the
%% significand, halved for the result; the integer root of the
%% significand scaled by 2^(M+2) has M+2 bits (lead, fraction, guard),
%% a nonzero remainder is the sticky bit (a root is never a tie).  The
%% result is never tiny or above the range.  -0 is -0, a negative
%% number, -inf and NaN give NaN (--nan), +inf gives inf.
float_sqrt(Af, T={float,E,M}, Bs) ->
    case vconst(Af) of
	Ab when is_integer(Ab) ->
	    Bits = varp_float:sqrt_bits(Ab, E, M),
	    {const_vector(T, Bits, 1+E+M), inf_folded(Bits, T, Bs)};
	false ->
	    case lib_ops(Bs) of
		true -> lib_float_sqrt(Af, T, Bs);
		false -> float_sqrt_(Af, T, Bs)
	    end
    end.

float_sqrt_(Af, T={float,E,M}, Bs) ->
    Zv = {uint,1,[false]},
    {S, Ex0, {uint,M,MaXs}} = fsplit(Af),
    {{bool,H}, Bs1} = operation2('neq', Ex0, Zv, Bs),
    Sig = {uint,M+1,MaXs ++ [H]},
    {{uint,_,SnXs}, LZ, Bs2} = lz_norm(Sig, Bs1),
    {E1, Bs3} = operation2('bor', Ex0, {uint,1,[neg_lit(H)]}, Bs2),
    %% the unbiased exponent of the leading one, made even
    {Eu0, Bs4} = operation2('sub', E1, LZ, Bs3),
    {Eu, Bs5} = operation2('sub', Eu0, const_int(varp_float:bias(E)), Bs4),
    {int,_,EuXs} = varp_arith:iarg(Eu),
    Odd = hd(EuXs),
    {Eh0, Bs6} = operation2('sub', Eu, {uint,1,[Odd]}, Bs5),
    {int,We,EhXs} = varp_arith:iarg(Eh0),
    Eh = {int,We,tl(EhXs) ++ [lists:last(EhXs)]},        %% exact, it is even
    {Eb, Bs7} = operation2('add', Eh, const_int(varp_float:bias(E)), Bs6),
    %% the significand, doubled for an odd exponent, scaled by 2^(M+2)
    {N2, Bs8} = ite(undefined, {bool,Odd}, {uint,M+2,[false|SnXs]},
		    {uint,M+2,SnXs ++ [false]}, Bs7),
    N2Xs = vfit(element(3, varp_arith:varg(N2)), M+2),
    {{uint,_,QXs}, Rnz, Bs9} = isqrt_circuit(M+2, zeros(M+2) ++ N2Xs, Bs8),
    Guard = hd(QXs),
    ManXs = lists:sublist(QXs, 2, M),
    {{bool,Up}, Bs10} = round_up(Guard, Rnz, lists:nth(2, QXs), Bs9),
    EbXs = vfit(element(3, varp_arith:varg(Eb)), E),
    {R0, Bs11} = operation2('add', {uint,E+M,ManXs ++ EbXs}, {uint,1,[Up]}, Bs10),
    Rounded = {uint,E+M,vfit(element(3, varp_arith:varg(R0)), E+M)},
    {{Z,I,Nn}, Bs12} = fclass(Af, Bs11),
    {Neg0, Bs13} = operation2('and', {bool,S}, negate(Z), Bs12),
    {NaNc, Bs14} = operation2('or', Nn, Neg0, Bs13),
    special_result(NaNc, I, Z, Rounded, {bool,S}, T, Bs14).

%% a * b + c with one rounding.  The exact product (2M+2 bits) sits
%% in a window of W = 3M+8 bits at bit 3; the addend's significand
%% starts at the top of the window (its lsb at 2M+7, two bits clear of
%% the product, which is then only sticky) and is shifted right by
%% r = M+4 + Ea + Eb - Ec - bias with what falls off as a sticky bit in
%% bit 0; r < 0 leaves it at the top and raises the window's base by
%% -r instead.  Signs equal: add; else the smaller magnitude is taken
%% from the larger and the sign follows the larger (an exact zero
%% difference is +0).  Normalise, then fpack as the other operations.
float_fma(Af, Bf, Cf, T={float,E,M}, Bs) ->
    case {vconst(Af), vconst(Bf), vconst(Cf)} of
	{Ab, Bb, Cb} when is_integer(Ab), is_integer(Bb), is_integer(Cb) ->
	    fold_status(varp_float:fma_fold(Ab, Bb, Cb, E, M, float_mode(Bs)), T, Bs);
	_ ->
	    case lib_ops(Bs) of
		true -> lib_float_fma(Af, Bf, Cf, T, Bs);
		false -> float_fma_(Af, Bf, Cf, T, Bs)
	    end
    end.

float_fma_(Af, Bf, Cf, T={float,E,M}, Bs) ->
    Zv = {uint,1,[false]},
    W = 3*M+8,
    {Sa, Ea0, {uint,M,MaXs}} = fsplit(Af),
    {Sb, Eb0, {uint,M,MbXs}} = fsplit(Bf),
    {Sc, Ec0, {uint,M,McXs}} = fsplit(Cf),
    {{bool,Ha}, Bs1} = operation2('neq', Ea0, Zv, Bs),
    {{bool,Hb}, Bs2} = operation2('neq', Eb0, Zv, Bs1),
    {{bool,Hc}, Bs3} = operation2('neq', Ec0, Zv, Bs2),
    {Ea1, Bs4} = operation2('bor', Ea0, {uint,1,[neg_lit(Ha)]}, Bs3),
    {Eb1, Bs5} = operation2('bor', Eb0, {uint,1,[neg_lit(Hb)]}, Bs4),
    {Ec1, Bs6} = operation2('bor', Ec0, {uint,1,[neg_lit(Hc)]}, Bs5),
    {{bool,Sp}, Bs7} = operation2('xor', {bool,Sa}, {bool,Sb}, Bs6),
    {P0, Bs8} = operation2('mul', {uint,M+1,MaXs ++ [Ha]}, {uint,M+1,MbXs ++ [Hb]}, Bs7),
    PXs = vfit(element(3, varp_arith:varg(P0)), 2*M+2),
    Pw = {uint,W,zeros(3) ++ PXs ++ zeros(W-3-(2*M+2))},
    %% the addend: r = M+4 + Ea + Eb - Ec - bias, clamped to [0, W]
    {R1, Bs9} = operation2('add', Ea1, Eb1, Bs8),
    {R2, Bs10} = operation2('sub', R1, Ec1, Bs9),
    {Rr, Bs11} = operation2('add', R2, const_int(M+4-varp_float:bias(E)), Bs10),
    {{bool,RNeg}, Bs12} = operation2('lt', Rr, Zv, Bs11),
    {{bool,RBig}, Bs13} = operation2('gte', Rr, const_int(W), Bs12),
    NB = varp_math:unsigned_size(W),
    Ru = {uint,NB,vfit(element(3, varp_arith:varg(Rr)), NB)},
    {A1, Bs14} = operation2('bor', Ru, {uint,NB,lists:duplicate(NB, RBig)}, Bs13),
    {A2, Bs15} = operation2('band', A1, {uint,NB,lists:duplicate(NB, neg_lit(RNeg))}, Bs14),
    Amt = {uint,NB,vfit(element(3, varp_arith:varg(A2)), NB)},
    Ctop = {uint,W,zeros(2*M+7) ++ McXs ++ [Hc]},
    {{uint,W,CsXs}, StC, Bs16} = barrel_right(Ctop, Amt, W, Bs15),
    {{bool,C0}, Bs17} = operation2('or', {bool,hd(CsXs)}, StC, Bs16),
    Cw = {uint,W,[C0|tl(CsXs)]},
    %% add, or subtract the smaller from the larger
    {Sub={bool,SubL}, Bs18} = operation2('xor', {bool,Sp}, {bool,Sc}, Bs17),
    {Sum, Bs19} = operation2('add', Pw, Cw, Bs18),
    {PgeC, Bs20} = operation2('gte', Pw, Cw, Bs19),
    {D1, Bs21} = operation2('sub', Pw, Cw, Bs20),
    {D2, Bs22} = operation2('sub', Cw, Pw, Bs21),
    D1w = {uint,W,vfit(element(3, varp_arith:varg(D1)), W)},
    D2w = {uint,W,vfit(element(3, varp_arith:varg(D2)), W)},
    {Dif, Bs23} = ite(undefined, PgeC, D1w, D2w, Bs22),
    DifW1 = {uint,W+1,vfit(element(3, varp_arith:varg(Dif)), W+1)},
    SumW1 = {uint,W+1,vfit(element(3, varp_arith:varg(Sum)), W+1)},
    {R, Bs24} = ite(undefined, Sub, DifW1, SumW1, Bs23),
    RW = {uint,W+1,vfit(element(3, varp_arith:varg(R)), W+1)},
    {Z1, Bs25} = operation2('eq', RW, Zv, Bs24),
    {Rn, LZ, Bs26} = lz_norm(RW, Bs25),
    %% the biased exponent of the lead: Ea + Eb - bias + M + 5 + max(0,-r) - LZ
    {NegR, Bs27} = operation2('sub', Zv, Rr, Bs26),
    {int,Wn,NegRXs} = varp_arith:iarg(NegR),
    {Extra, Bs28} = ite(undefined, {bool,RNeg}, {int,Wn,NegRXs}, {int,Wn,zeros(Wn)}, Bs27),
    {X1, Bs29} = operation2('add', R1, const_int(M+5-varp_float:bias(E)), Bs28),
    {X2, Bs30} = operation2('add', X1, Extra, Bs29),
    {Ex, Bs31} = operation2('sub', X2, LZ, Bs30),
    %% the sign: the leading operand's, +0 for an exact difference
    {S0, Bs32} = ite(undefined, PgeC, {bool,Sp}, {bool,Sc}, Bs31),
    {S1, Bs33} = ite(undefined, Sub, S0, {bool,Sp}, Bs32),
    {ZeroSub, Bs34} = operation2('and', Z1, Sub, Bs33),
    {S2, Bs35} = operation2('and', S1, negate(ZeroSub), Bs34),
    %% the special operands
    {{Za,Ia,Na}, Bs36} = fclass(Af, Bs35),
    {{Zb,Ib,Nb}, Bs37} = fclass(Bf, Bs36),
    {{_Zc,Ic,Nc}, Bs38} = fclass(Cf, Bs37),
    {Ip, Bs39} = operation2('or', Ia, Ib, Bs38),
    {N1, Bs40} = operation2('or', Na, Nb, Bs39),
    {N2, Bs41} = operation2('or', N1, Nc, Bs40),
    {N3, Bs42} = operation2('and', Ia, Zb, Bs41),
    {N4, Bs43} = operation2('and', Ib, Za, Bs42),
    {N5, Bs44} = operation2('and', Ip, Ic, Bs43),
    {N6, Bs45} = operation2('and', N5, {bool,SubL}, Bs44),
    {N7, Bs46} = operation2('or', N2, N3, Bs45),
    {N8, Bs47} = operation2('or', N7, N4, Bs46),
    {NaNc, Bs48} = operation2('or', N8, N6, Bs47),
    {InfC0, Bs49} = operation2('or', Ip, Ic, Bs48),
    {Masked, Bs50} = operation2('or', NaNc, InfC0, Bs49),
    {SInf, Bs51} = ite(undefined, Ip, {bool,Sp}, {bool,Sc}, Bs50),
    {S, Bs52} = ite(undefined, InfC0, SInf, S2, Bs51),
    {Rounded, Zero, Over, Bs53} = fpack(Rn, {bool,?F}, Ex, Z1, Masked, T, Bs52),
    Bs54 = inf_status(Over, Bs53),
    {InfC, Bs55} = operation2('or', Over, InfC0, Bs54),
    special_result(NaNc, InfC, Zero, Rounded, S, T, Bs55).

lib_float_fma(Af, Bf, Cf, T={float,E,M}, Bs) ->
    Z = case float_mode(Bs) of ftz -> 1; ieee -> 0 end,
    {Prefix, Bs1} = circuit_prefix(<<"op_ffma">>, Bs),
    Flag = fun(F) -> {p,<<Prefix/binary,F/binary>>,[]} end,
    Outs = [Flag(<<"over">>), Flag(<<"under">>), Flag(<<"nan">>)],
    {R, Bs2} = lib_call(<<"op_ffma">>, [{const,E},{const,M},{const,Z},
				{value,fbits(Af)},{value,fbits(Bf)},{value,fbits(Cf)}] ++ Outs, Bs1),
    {[Over,Under,NaN], Bs3} = lists:mapfoldl(fun(P, B) -> bld(P, B) end, Bs2, Outs),
    Bs4 = inf_status(Over, Bs3),
    Bs5 = underflow_status(Under, Bs4),
    {retag(T, R), nan_status(NaN, Bs5)}.

lib_float_sqrt(Af, T={float,E,M}, Bs) ->
    {Prefix, Bs1} = circuit_prefix(<<"op_fsqrt">>, Bs),
    NaNp = {p,<<Prefix/binary,"nan">>,[]},
    {R, Bs2} = lib_call(<<"op_fsqrt">>, [{const,E},{const,M},{value,fbits(Af)},NaNp], Bs1),
    {NaN, Bs3} = bld(NaNp, Bs2),
    {retag(T, R), nan_status(NaN, Bs3)}.

%% any vector's bits as a float of format T
retag(T={float,E,M}, {_,_,Xs}) -> {T,1+E+M,vfit(Xs, 1+E+M)}.

%% a + b: the operand with the larger magnitude leads; the other one's
%% significand is shifted right by the exponent difference, with three
%% extra bits below (guard, round and a sticky bit that collects what
%% falls off), and is added to or subtracted from the leading one as
%% the signs agree or not.  The result is normalised (a carry moves it
%% one up, a cancellation can move it far down), rounded to nearest
%% even, a subnormal below the normal range (zero under --ftz) and inf
%% above it.
%% The sign is the leading operand's; a difference that cancels is +0.
float_add(Af, Bf, T={float,E,M}, Bs) ->
    case {vconst(Af), vconst(Bf)} of
	{Ab, Bb} when is_integer(Ab), is_integer(Bb) ->
	    fold_status(varp_float:add_fold(Ab, Bb, E, M, float_mode(Bs)), T, Bs);
	_ ->
	  case lib_ops(Bs) of
	    true -> lib_float_op(<<"op_fadd">>, Af, Bf, T, Bs);
	    false ->
	    Zv = {uint,1,[false]},
	    {Lt, Bs1} = operation2('lt', fmag(Af), fmag(Bf), Bs),
	    {Big0, Bs2} = ite(undefined, Lt, fbits(Bf), fbits(Af), Bs1),
	    {Small0, Bs3} = ite(undefined, Lt, fbits(Af), fbits(Bf), Bs2),
	    Big = retag(T, Big0),
	    Small = retag(T, Small0),
	    {Sb, Eb0, {uint,M,MbXs}} = fsplit(Big),
	    {Ss, Es0, {uint,M,MsXs}} = fsplit(Small),
	    {{bool,Hb}, Bs4} = operation2('neq', Eb0, Zv, Bs3),
	    {{bool,Hs}, Bs5} = operation2('neq', Es0, Zv, Bs4),
	    {Eb, Bs6} = operation2('bor', Eb0, {uint,1,[neg_lit(Hb)]}, Bs5),
	    {Es, Bs7} = operation2('bor', Es0, {uint,1,[neg_lit(Hs)]}, Bs6),
	    G = 3,
	    Wd = M+1+G,
	    SigB = {uint,Wd,zeros(G) ++ MbXs ++ [Hb]},
	    SigS = {uint,Wd,zeros(G) ++ MsXs ++ [Hs]},
	    %% align the small one
	    {D, Bs8} = operation2('sub', Eb, Es, Bs7),
	    {Sh0, St0, Bs9} = barrel_right(SigS, D, Wd, Bs8),
	    {Far, Bs10} = operation2('gte', D, const_int(Wd), Bs9),
	    {NZs, Bs11} = operation2('neq', SigS, Zv, Bs10),
	    {Sh1, Bs12} = ite(undefined, Far, {uint,Wd,zeros(Wd)}, Sh0, Bs11),
	    {StFar, Bs13} = operation2('and', Far, NZs, Bs12),
	    {{bool,StL}, Bs14} = operation2('or', StFar, St0, Bs13),
	    {Aligned, Bs15} = operation2('bor', Sh1, {uint,1,[StL]}, Bs14),
	    %% add or subtract the magnitudes
	    {Sub, Bs16} = operation2('xor', {bool,Sb}, {bool,Ss}, Bs15),
	    {Sum, Bs17} = operation2('add', SigB, Aligned, Bs16),
	    {Dif, Bs18} = operation2('sub', SigB, Aligned, Bs17),
	    W = Wd+1,
	    SumW = {uint,W,vfit(element(3, varp_arith:varg(Sum)), W)},
	    DifW = {uint,W,vfit(element(3, varp_arith:varg(Dif)), W)},
	    {R, Bs19} = ite(undefined, Sub, DifW, SumW, Bs18),
	    RW = {uint,W,vfit(element(3, varp_arith:varg(R)), W)},
	    %% normalise: the leading one to bit W-1, the exponent Eb+1
	    {Rn, LZ, Bs20} = lz_norm(RW, Bs19),
	    {Ex0, Bs23} = operation2('add', Eb, {uint,1,[true]}, Bs20),
	    {Ex, Bs24} = operation2('sub', Ex0, LZ, Bs23),
	    {Z1, Bs26} = operation2('eq', RW, Zv, Bs24),
	    {{_,Ia,Na}, Bs33a} = fclass(Af, Bs26),
	    {{_,Ib,Nb}, Bs33b} = fclass(Bf, Bs33a),
	    %% inf - inf and a NaN operand: NaN; inf + x: inf
	    {N1, Bs33c} = operation2('or', Na, Nb, Bs33b),
	    {BothInf, Bs33d} = operation2('and', Ia, Ib, Bs33c),
	    {N2, Bs33e} = operation2('and', BothInf, Sub, Bs33d),
	    {NaNc, Bs33f} = operation2('or', N1, N2, Bs33e),
	    {AnyInf, Bs33g} = operation2('or', Ia, Ib, Bs33f),
	    {Masked, Bs33h} = operation2('or', NaNc, AnyInf, Bs33g),
	    {Rounded, Zero, Over, Bs34} = fpack(Rn, {bool,?F}, Ex, Z1, Masked, T, Bs33h),
	    Bs34c = inf_status(Over, Bs34),
	    {InfC, Bs35} = operation2('or', Over, AnyInf, Bs34c),
	    %% the sign: the leading operand's, +0 when a difference cancels
	    %% exactly (a flushed difference keeps its sign)
	    {ZeroSub, Bs36} = operation2('and', Z1, Sub, Bs35),
	    {S, Bs37} = operation2('and', {bool,Sb}, negate(ZeroSub), Bs36),
	    special_result(NaNc, InfC, Zero, Rounded, S, T, Bs37)
	  end
    end.

ones(K) -> lists:duplicate(K, true).

%% a * b: the product of the significands is normalised (its leading
%% one goes to bit 2M+1; for two normal numbers that is at most one
%% step, a subnormal factor needs more), the M bits below the leading
%% one are the fraction, the next is the guard bit and the rest the
%% sticky bit.  The exponent is Ea + Eb - bias + 1 - LZ, a subnormal
%% factor counting as exponent 1.  Zero when a factor is zero or the
%% exponent falls to zero or below (flush to zero), inf when it
%% reaches the top.
float_mul(Af, Bf, T={float,E,M}, Bs) ->
    case {vconst(Af), vconst(Bf)} of
	{Ab, Bb} when is_integer(Ab), is_integer(Bb) ->
	    fold_status(varp_float:mul_fold(Ab, Bb, E, M, float_mode(Bs)), T, Bs);
	_ ->
	  case lib_ops(Bs) of
	    true -> lib_float_op(<<"op_fmul">>, Af, Bf, T, Bs);
	    false ->
	    Zv = {uint,1,[false]},
	    {Sa, Ea, {uint,M,MaXs}} = fsplit(Af),
	    {Sb, Eb, {uint,M,MbXs}} = fsplit(Bf),
	    {{bool,S}, Bs1} = operation2('xor', {bool,Sa}, {bool,Sb}, Bs),
	    {{bool,HaL}, Bs2} = operation2('neq', Ea, Zv, Bs1),
	    {{bool,HbL}, Bs3} = operation2('neq', Eb, Zv, Bs2),
	    SigA = {uint,M+1,MaXs ++ [HaL]},
	    SigB = {uint,M+1,MbXs ++ [HbL]},
	    %% a subnormal factor has the exponent 1
	    {Ea1, Bs3a} = operation2('bor', Ea, {uint,1,[neg_lit(HaL)]}, Bs3),
	    {Eb1, Bs3b} = operation2('bor', Eb, {uint,1,[neg_lit(HbL)]}, Bs3a),
	    {P0, Bs4} = operation2('mul', SigA, SigB, Bs3b),
	    W = 2*M+2,
	    P = {uint,W,vfit(element(3, varp_arith:varg(P0)), W)},
	    {Pn, LZ, Bs5} = lz_norm(P, Bs4),
	    {Es, Bs8} = operation2('add', Ea1, Eb1, Bs5),
	    {Es1, Bs9} = operation2('sub', Es, LZ, Bs8),
	    {Ex, Bs10} = operation2('sub', Es1, const_int(varp_float:bias(E) - 1), Bs9),
	    {Z1, Bs12} = operation2('eq', P, Zv, Bs10),
	    {{Za,Ia,Na}, Bs14a} = fclass(Af, Bs12),
	    {{Zb,Ib,Nb}, Bs14b} = fclass(Bf, Bs14a),
	    %% inf * 0 and a NaN operand: NaN; inf * x: inf
	    {N1, Bs14c} = operation2('or', Na, Nb, Bs14b),
	    {N2, Bs14d} = operation2('and', Ia, Zb, Bs14c),
	    {N3, Bs14e} = operation2('and', Ib, Za, Bs14d),
	    {N4, Bs14f} = operation2('or', N1, N2, Bs14e),
	    {NaNc, Bs14g} = operation2('or', N4, N3, Bs14f),
	    {AnyInf, Bs14h} = operation2('or', Ia, Ib, Bs14g),
	    {Masked, Bs14i} = operation2('or', NaNc, AnyInf, Bs14h),
	    {Rounded, Zero, Over, Bs15b} = fpack(Pn, {bool,?F}, Ex, Z1, Masked, T, Bs14i),
	    Bs15c = inf_status(Over, Bs15b),
	    {InfC, Bs15d} = operation2('or', Over, AnyInf, Bs15c),
	    special_result(NaNc, InfC, Zero, Rounded, {bool,S}, T, Bs15d)
	  end
    end.

%% sign and magnitude (the IEEE order): two zeros are equal, otherwise
%% equal magnitudes with the same sign are; a negative is below a
%% positive unless both are zero, two negatives compare the other way
%% round
float_compare(Op, Af, Bf, Bs) ->
    Sa = {bool,fsign(Af)}, Sb = {bool,fsign(Bf)},
    Ma = fmag(Af), Mb = fmag(Bf),
    Zv = {uint,1,[false]},
    {Eqm, Bs1} = operation2('eq', Ma, Mb, Bs),
    {Za, Bs2} = operation2('eq', Ma, Zv, Bs1),
    {Zb, Bs3} = operation2('eq', Mb, Zv, Bs2),
    {Both0, Bs4} = operation2('and', Za, Zb, Bs3),
    {SameS, Bs5} = operation2('equ', Sa, Sb, Bs4),
    {EqN, Bs6} = operation2('and', Eqm, SameS, Bs5),
    {Eq, Bs7} = operation2('or', EqN, Both0, Bs6),
    %% a NaN on either side is unordered: everything false but !=
    {{_,_,Na}, Bs7a} = fclass(Af, Bs7),
    {{_,_,Nb}, Bs7b} = fclass(Bf, Bs7a),
    {Unord, Bs7c} = operation2('or', Na, Nb, Bs7b),
    Ordered = fun(R, B) -> operation2('and', R, negate(Unord), B) end,
    case Op of
	'eq' -> Ordered(Eq, Bs7c);
	'neq' -> operation2('or', negate(Eq), Unord, Bs7c);
	'lt' ->
	    {Lt, Bs8} = float_lt(Sa, Sb, Ma, Mb, Both0, Bs7c),
	    Ordered(Lt, Bs8);
	'gt' ->
	    {Gt, Bs8} = float_lt(Sb, Sa, Mb, Ma, Both0, Bs7c),
	    Ordered(Gt, Bs8);
	'lte' ->
	    {Lt, Bs8} = float_lt(Sa, Sb, Ma, Mb, Both0, Bs7c),
	    {R, Bs9} = operation2('or', Lt, Eq, Bs8),
	    Ordered(R, Bs9);
	'gte' ->
	    {Gt, Bs8} = float_lt(Sb, Sa, Mb, Ma, Both0, Bs7c),
	    {R, Bs9} = operation2('or', Gt, Eq, Bs8),
	    Ordered(R, Bs9)
    end.

float_lt(Sa, Sb, Ma, Mb, Both0, Bs) ->
    {Ltm, Bs1} = operation2('lt', Ma, Mb, Bs),
    {Gtm, Bs2} = operation2('lt', Mb, Ma, Bs1),
    {NegPos, Bs3} = operation2('and', Sa, negate(Sb), Bs2),        %% a < 0 <= b
    {BothPos, Bs4} = operation2('and', negate(Sa), negate(Sb), Bs3),
    {PP, Bs5} = operation2('and', BothPos, Ltm, Bs4),
    {BothNeg, Bs6} = operation2('and', Sa, Sb, Bs5),
    {NN, Bs7} = operation2('and', BothNeg, Gtm, Bs6),
    {Or1, Bs8} = operation2('or', NegPos, PP, Bs7),
    {Or2, Bs9} = operation2('or', Or1, NN, Bs8),
    operation2('and', negate(Both0), Or2, Bs9).

%% X = Y with a float target
float_set(X={T,N,Xs}, Y, Bs) ->
    {Yf, Bs1} = to_float(Y, T, Bs),
    {_, Bs2} = operation1('=', {uint,N,Xs}, fbits(Yf), Bs1),
    {X, Bs2}.

%%
%% if-then-else circuit
%%  (I & T) | (~I & E)
%%
%% fixed point branches first, "heat ? 0.5 : -0.25": both branches
%% become {fix,F} values so that the mux below moves raw bits
ite(X,Cond,T,E, Bs) ->
    case fix_align(T, E, Bs) of
	false -> ite_(X,Cond,T,E,Bs);
	{T1,E1,Bs1} -> ite_(X,Cond,T1,E1,Bs1)
    end.

ite_(X,{bool,?T},T,_E, Bs) -> set(X,T,Bs);
ite_(X,{bool,?F},_T,E, Bs) -> set(X,E,Bs);
ite_(X,_Cond,Y,Y, Bs) -> set(X,Y,Bs);
%% a vector branch: a bitwise mux with the condition spread over the
%% width, X = (C & T) | (~C & E) bit by bit
ite_(X,Cond,T,E, Bs) when ?is_vec_type(element(1,T));
			  ?is_vec_type(element(1,E)) ->
    C = cond_lit(Cond),
    N = max(vec_width(T), vec_width(E)),
    Cv = {uint,N,lists:duplicate(N,C)},
    Cnv = {uint,N,lists:duplicate(N,neg_lit(C))},
    {A1,Bs1} = operation2('band',Cv,T,Bs),
    {A2,Bs2} = operation2('band',Cnv,E,Bs1),
    operation2('bor',X,A1,A2,Bs2);
%% (Cond & false) | (~Cond & E) == ~Cond & E
ite_(X,Cond,{bool,?F},E, Bs) -> operation2('and',X,negate(Cond),E,Bs);
%% (Cond & T) | (~Cond & false) == Cond & T
ite_(X,Cond,T,{bool,?F}, Bs) -> operation2('and',X,Cond,T,Bs);
ite_(X,Cond,T,E, Bs) ->
    {A1,Bs1} = operation2('and',Cond,T,Bs),
    {A2,Bs2} = operation2('and',negate(Cond),E,Bs1),
    operation2('or',X,A1,A2,Bs2).

cond_lit({bool,C}) -> C;
cond_lit({_T,1,[C]}) -> C;
cond_lit(V) -> error({condition_not_boolean, V}).

neg_lit(?T) -> ?F;
neg_lit(?F) -> ?T;
neg_lit(C) when is_integer(C) -> -C.

vec_width({bool,_}) -> 1;
vec_width({_T,N,_}) -> N.

each_unbound(Bs, Fun) ->
    each_unbound_(Bs, Fun, varp_nif:next_unbound(Bs#bs.vp)).

each_unbound_(_Bs, _Fun, false) ->
    ok;
each_unbound_(Bs, Fun, Xi) ->
    Fun(Xi),
    each_unbound_(Bs, Fun, varp_nif:next_unbound(Bs#bs.vp,Xi)).

fold_unbound(Bs, Fun, Acc) ->
    fold_unbound_(Bs, Fun, Acc, varp_nif:next_unbound(Bs#bs.vp)).

fold_unbound_(_Bs, _Fun, Acc, false) ->
    Acc;
fold_unbound_(Bs, Fun, Acc, Xi) ->
    Acc1 = Fun(Xi, Acc),
    fold_unbound_(Bs, Fun, Acc1, varp_nif:next_unbound(Bs#bs.vp, Xi)).

each_variable(Bs, Fun) ->
    each_variable_(Bs, Fun, 1, varp_nif:getstat(Bs#bs.vp, number_of_variables)+1).

each_variable_(_Bs, _Fun, Max, Max) ->
    ok;
each_variable_(Bs, Fun, X, N) ->
    Fun(X),
    each_variable_(Bs, Fun, X+1, N).

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
    model(Bs, #{}).

%% subst => true: a substituted boolean whose representative has no
%% value is {Var, {equ, Rep}} or {Var, {nequ, Rep}}, where Rep is the
%% representative {p,Name,Args}, a bit {bit,{p,..},Pos} of a vector,
%% or an internal variable {var, I}
model(Bs, Opts) ->
    model_(Bs#bs.vp, maps:get(subst, Opts, false)).

model_(Vp, Subst) ->
    lists:keysort(1, collect_model(Vp, Subst)).

collect_model(Vp, Subst) ->
    case varp_nif:first_symbol(Vp) of
	false -> %% fixme mixed model! CNF with is declarations
	    N = varp:get_number_of_variables(Vp),
	    lists:foldr(
	      fun(I,Acc) ->
		      case varp_nif:value(Vp,I) of
			  ?T -> [{{p,<<"x">>,[I]}, true}|Acc];
			  ?F -> [{{p,<<"x">>,[I]},false}|Acc];
			  _ -> Acc
		      end
	      end, [], lists:seq(1, N));
	_ ->
	    N = varp:get_number_of_variables(Vp),
	    lists:foldr(
	      fun(I,Acc) ->
		      case varp_nif:get_symbol(Vp,I) of
			  [] -> Acc;
			  [{{Name,Args},bool,1,0}] ->
			      Value = case varp_nif:value(Vp,I) of
					  undefined when Subst ->
					      representative(Vp, I);
					  V0 -> V0
				      end,
			      [{{p,Name,Args},Value}|Acc];
			  [{{Name,Args},Type,Len,Pos}] ->
			      Value = varp_nif:value(Vp,I),
			      V = case Value of
				      ?T -> $1;
				      ?F -> $0;
				      _  -> $*
				  end,
			      model_setvec(Type,{p,Name,Args},Len,Pos,V,Acc)
		      end
	      end, [], lists:seq(1, N))
    end.

-if(not_used).

model_vars(Vp,[{Type,X,N,I}|Xs],Y,Ms) ->
    V = case varp_nif:value(Vp, Y) of
	    ?T -> $1;
	    ?F -> $0;
	    _  -> $*
	end,
    model_vars(Vp,Xs,Y,model_setvec(Type,X,N,I,V,Ms));
model_vars(Vp,[X|Xs],Y,Ms) ->
    case varp_nif:value(Vp, Y) of
	?T ->
	    model_vars(Vp,Xs,Y,[{X,true}|Ms]);
	?F ->
	    model_vars(Vp,Xs,Y,[{X,false}|Ms]);
	_ ->
	    model_vars(Vp,Xs,Y,Ms)
    end;
model_vars(_Vp,[],_Y,Ms) ->
    Ms.
-endif.

%% the representative of a substituted variable, undefined when the
%% variable is not substituted
representative(Vp, I) ->
    case varp_nif:bound(Vp, I) of
	L when is_integer(L) ->
	    Rep = case varp_nif:get_symbol(Vp, abs(L)) of
		      [{{Name,Args},bool,1,0}] -> {p,Name,Args};
		      [{{Name,Args},_Type,_Len,Pos}] -> {bit,{p,Name,Args},Pos};
		      [] -> {var, abs(L)}
		  end,
	    if L > 0 -> {equ, Rep};
	       true -> {nequ, Rep}
	    end;
	_ ->
	    undefined
    end.

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
	      [I,lists:join(",",[varp_format:format_binding(Bound) || Bound <- Bindings1 ])]);
print_model(literal,I,_Partial,Bindings) ->
    Bindings1 = filter_bindings(Bindings),
    io:format("~w: ~s\n",
	      [I,lists:join(",",[varp_format:format_binding(Bound) || Bound <- Bindings1 ])]);
print_model(model,I,false,Bindings) ->
    Bindings1 = filter_bindings(Bindings),
    io:format("~w: ~s\n",
	      [I,lists:join(",",
			    [ varp_format:format_binding(Bound) || 
				Bound <- Bindings1,
				element(2,Bound) =/= false ])]);
print_model(model,I,true,Bindings) ->
    Bindings1 = filter_bindings(Bindings),
    io:format("~w: ~s\n",
	      [I,lists:join(",",[varp_format:format_binding(Bound) || Bound <- Bindings1 ])]);
%% print_model(umodel,I,_Partial,Bindings) ->
%%    io:format("~w: ~s\n",
%%	      [I,lists:join(",",[ varp_format:format_binding(Bound) || 
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

print_dimacs_rows_([{{p,<<"x">>,[J]},Value}|Bs], Remain, N, Acc) when is_integer(J) ->
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
    Xi = [$\s | lists:flatten(varp_format:format_binding(B))],
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
filter_bindings([{{p,_V,_},undefined}|Bs]) ->
    filter_bindings(Bs);
filter_bindings([B={{p,V,_},_}|Bs]) when is_binary(V) ->
    case V of
	<<$_,_/binary>> ->
	    filter_bindings(Bs);
	_  -> [B|filter_bindings(Bs)]
    end;
filter_bindings([B|Bs]) ->
    [B|filter_bindings(Bs)];
filter_bindings([]) ->
    [].

log_clause(Bs, Clause) ->
    io:format("~s\n", [varp_format:format_clause(Bs,Clause)]).

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

proof_literal(Bs,Li) ->
    case varp_nif:get_symbol(Bs#bs.vp,abs(Li)) of
	%% x(I) is a dimacs numbered variable, print it as a number
	[{{<<"x">>,[I]},bool,1,0}] when Li < 0 -> integer_to_list(-I);
	[{{<<"x">>,[I]},bool,1,0}] -> integer_to_list(I);
	[{P,bool,1,0}] when Li < 0 -> [$!|varp_format:format_internal_symbol(P)];
	[{P,bool,1,0}] -> varp_format:format_internal_symbol(P);
	%% internal or vector variable, no boolean symbol of its own
	_ -> integer_to_list(Li)
    end.
