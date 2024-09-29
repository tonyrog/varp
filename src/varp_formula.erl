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
-export([add_variable/1, add_variable/2]).
-export([variable/2, alias/3]).
-export([print_model/4]).
-export([find_var/2, get_var/2]).
-export([uint64/2, uint32/2, uint16/2, uint8/2]).
-export([filter_bindings/1]).

-export([log_clause/2]).
-export([proof_output/3]).
-export([want_proof_output/1]).

%% building with operations
-export([operation/4, operation/3]).
-export([all/2, any/2]).
-export([eqk/3, gtk/3]).
-export([subst/3]).

%% varp_nif wrappers
-export([getopt/2]).
-export([order_first/2]).
-export([order_last/2]).
-export([model/1, model/2]).
-export([intersect_bindings/3]).
-export([install_bindings/3]).
-export([model_variables/2]).
-export([each_unbound/2]).
-export([each_variable/2]).
-export([fold_unbound/3]).
-export([eval_meta/2]).
-export([add_clause/2, add_clause/3]).
-export([del_clause/2]).
-export([del_unused_clauses/1]).
-export([clean_clauses/1, clean_clauses/2]).
-export([set_var/3, add_var/4]).
-export([const_vector/2, const_vector/3]).
-export([const_vector/4]).

-export([vconst/1]).

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

    Symbols  = maps:get(syms,OptMap),
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
       vs = Symbols,
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

add_variable(Bs) ->
    varp_nif:add_variable(Bs#bs.vp, false, true).

%% Create a variable and mark all atoms as used
add_variable(Bs, IsAtom) ->
    varp_nif:add_variable(Bs#bs.vp, IsAtom, true).

%% add symbol name to literal 
-spec add_symbol(Bs::#bs{}, L::integer(), Sym::term()|iolist()) ->
		       ok.
add_symbol(Bs, L, Sym) ->
    %% io:format("add_symbol: ~p ~p\n", [L, Sym]),
    varp_nif:add_symbol(Bs#bs.vp, L, Sym).

%% build an OR gate with Y as output and Xs as input
%% Y = X1 xor X2 .. xor Xn
xor_gate(Bs,Y,Xs) ->
    %% gate(Bs, 'xor', Y, Xs).
    varp_circuit:parity(Bs#bs.vp, Y, Xs).

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


is_temporary({p,<<$$,_/binary>>,_}) -> true;
is_temporary(_) -> false.

make_variable(V, Bs) ->
    case is_temporary(V) of
	true ->
	    N = add_variable(Bs, false),
	    add_symbol(Bs, N, varp_format:format_symbol(V)),
	    {{bool,N}, alias(V,N,Bs)};
	false ->
	    N = add_variable(Bs, true),
	    add_symbol(Bs, N, varp_format:format_symbol(V)),
	    {{bool,N}, alias(V,N,Bs)}
    end.

getopt(Bs, Item) ->
    maps:get(Bs#bs.option, Item).

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

match_def(P, As, Defs) ->
    PSym = {P,length(As)},
    List = maps:get(PSym, Defs, []),
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

-spec alias(V::var(),N::integer(),Bs::#bs{}) -> #bs{}.

alias(V,N,Bs) ->
    case find_var(N,Bs) of
	error ->
	    set_var(V,N,Bs);
	{ok,Alias} ->
	    add_var(V,N,Alias,Bs)
    end.

find_var(V, Bs) ->
    Val = find_var_(V, Bs),
    ?dbg0("find_var ~p = ~p\n", [V,Val]),
    Val.

find_var_(V, Bs) ->
    case maps:get(icase, Bs#bs.option, false) of
	false ->
	    maps:find(V, Bs#bs.vs);
	true ->
	    case V of
		{p,P,Ps} ->
		    UP = string:uppercase(P),
		    maps:find({p,UP,Ps}, Bs#bs.vs);
		_ ->
		    maps:find(V, Bs#bs.vs)
	    end
    end.

get_var(V, Bs) ->
    case maps:get(icase, Bs#bs.option, false) of
	false ->
	    maps:get(V, Bs#bs.vs);
	true ->
	    case V of
		{p,P,Ps} ->
		    UP = string:uppercase(P),
		    maps:get({p,UP,Ps}, Bs#bs.vs)
	    end
    end.

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
     	    {{bool,?F},Bs};
	?EXCEPTION(error,Error,Stack) ->
	    io:format("error: ~w\n~p\n", [Error,?GET_STACK(Stack)])
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

build_(V, Bs) when is_binary(V) -> %% variable (and meta)
    Arity = 0,
    case maps:find(V,Bs#bs.decls) of
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
build_(W, Bs) when is_integer(W) ->
    if W < 0 ->
	    N = varp_math:signed_size(W),
	    const_vector(int,W,N,Bs);
       true ->
	    N = varp_math:unsigned_size(W),
	    const_vector(uint,W,N,Bs)
    end;
build_({const,W}, Bs) when is_integer(W) ->
    if W < 0 ->
	    N = varp_math:signed_size(W),
	    const_vector(int,W,N,Bs);
       true ->
	    N = varp_math:unsigned_size(W),
	    const_vector(uint,W,N,Bs)
    end;
%% built in integer functions (fixme)
build_({p,<<"abs">>,[A]}, Bs) ->
    {Y,Bs1} = build__(A, Bs),
    operation_('abs', Y, Bs1);
build_({p,<<"min">>,[A,B]}, Bs) ->
    {A1,Bs1} = build__(A, Bs),
    {B1,Bs2} = build__(B, Bs1),
    operation_('min', A1, B1, Bs2);
build_({p,<<"max">>,[A,B]}, Bs) ->
    {A1,Bs1} = build__(A, Bs),
    {B1,Bs2} = build__(B, Bs1),
    operation_('max', A1, B1, Bs2);
build_(V={p,P,Ps}, Bs) ->
    PSym = case maps:get(icase, Bs#bs.option, false) of
	       false -> varp:make_psym(P, Ps);
	       true -> varp:make_psym(string:uppercase(P), Ps)
	   end,
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
    {{bool,?T}, Bs};

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

build_({lop,':=', L, R}, Bs) ->
    {Y,Bs1} = build__(R, Bs),
    operation_(':=', L, Y, Bs1);
build_({lop,'=', L, R}, Bs) ->
    {Y,Bs1} = build__(R, Bs),
    operation_('=', L, Y, Bs1);
build_({lop,Op,A}, Bs) ->
    {Y,Bs1} = build__(A, Bs),
    operation_(Op, Y, Bs1);    
build_({lop,Op,A,B}, Bs) ->
    {Y,Bs1} = build__(A, Bs),
    {Z,Bs2} = build__(B, Bs1),
    operation_(Op,Y,Z,Bs2);
build_({lop,ite,C,T,E}, Bs) ->
    {Cf,Bs1} = build__(C, Bs),
    {Tf,Bs2} = build__(T, Bs1),
    {Ef,Bs3} = build__(E, Bs2),
    ite(Cf, Tf, Ef, Bs3);

build_({'ALL',Fs}, Bs) ->
    {Xs,Bs1} = build_args(Fs,Bs),
    all(Xs, Bs1);
build_({'ANY',Fs}, Bs) ->
    {Xs,Bs1} = build_args(Fs,Bs),
    any(Xs, Bs1);
build_({'NONE',Fs}, Bs) ->
    {Xs,Bs1} = build_args(Fs,Bs),
    none(Xs, Bs1);
build_({'ONE',Fs}, Bs) ->
    {Xs,Bs1} = build_args(Fs,Bs),
    one(Xs, Bs1);
build_({'SUM',Ys}, Bs) ->
    {Xs,Bs1} = build_args(Ys,Bs),
    sum(Xs, Bs1);
build_({'PROD',Ys}, Bs) ->
    {Xs,Bs1} = build_args(Ys,Bs),
    prod(Xs, Bs1);
build_({'PARITY',Ys}, Bs) ->
    {Xs,Bs1} = build_args(Ys,Bs),
    parity(Xs, Bs1);
build_({'ODD',Ys}, Bs) ->
    {Xs,Bs1} = build_args(Ys,Bs),
    parity(Xs, Bs1);
build_({'EVEN',Ys}, Bs) ->
    {Xs,Bs1} = build_args(Ys,Bs),
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
    eqk(1, Ys, Bs1);

build_({{'EQ',[X1|Qs]},F}, Bs) ->
    K = eval_meta(X1,Bs),
    {Ys,Bs1} = build_quant(F,Qs,Bs),
    if is_integer(K),K >= 0 ->
	    eqk(K, Ys, Bs1)
    end;
build_({{'NEQ',[X1|Qs]},F}, Bs) ->
    K = eval_meta(X1,Bs),
    {Ys,Bs1} = build_quant(F,Qs,Bs),
    if is_integer(K),K >= 0 ->
	    {X,Bs2} = eqk(K, Ys, Bs1),
	    {negate(X),Bs2}
    end;
build_({{'GT',[X1|Qs]},F}, Bs) ->
    K = eval_meta(X1,Bs),
    {Ys,Bs1} = build_quant(F,Qs,Bs),
    if is_integer(K),K >= 0 ->
	    gtk(K,Ys,Bs1)
    end;
build_({{'GTE',[X1|Qs]},F}, Bs) ->
    K = eval_meta(X1,Bs),
    {Ys,Bs1} = build_quant(F,Qs,Bs),
    if K =:= 0 ->
	    any(Ys,Bs1);
       is_integer(K),K >= 0 ->
	    gtk(K-1,Ys,Bs1)
    end;
build_({{'LT',[X1|Qs]},F}, Bs) ->
    K = eval_meta(X1,Bs),
    {Ys,Bs1} = build_quant(F,Qs,Bs),
    if K =:= 1 ->
	    none(Ys,Bs1);
       is_integer(K),K > 1 ->
	    N = length(Ys),
	    gtk(N-K, lists:map(fun(Y) -> negate(Y) end, Ys), Bs1)
    end;
build_({{'LTE',[X1|Qs]},F}, Bs) ->
    K = eval_meta(X1,Bs),
    {Ys,Bs1} = build_quant(F,Qs,Bs),
    if K =:= 0 ->
	    none(Ys,Bs1);
       is_integer(K),K > 0 ->
	    N = length(Ys),
	    gtk(N-K-1, lists:map(fun(Y) -> negate(Y) end, Ys), Bs1)
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
    {negate(Y),Bs2};
build_({cop, Name, Args}, Bs) ->
    %% locate circuit definition
    case maps:find(Name, Bs#bs.circuits) of
	{ok, Circuit} ->
	    build_circuit(Circuit, Args, Bs);
	error ->
	    io:format("circuit ~p not defined\n", [Name]),
	    error({circuit_undefined, Name})
    end;
build_(Form, _Bs) ->
    io:format("NOT IMPLEMENTED: ~p\n", [Form]),
    throw(not_implemented).

%%
%% Build circuit
%% create a symbol prefix for each nesting level
%% C = C1....Ci
%%   input variables are bound to parameter variables (p1=x && y, p2=z)
%%   int a, b, c = false
%%       C.a = p1 (add_symbol)
%%       C.b = p2 (add_symbol)
%%       C.c = false
%%   out o;
%%   return r;
%%       C.f = C.a xor C.b xor C.c;
%%       C.o = C.f
%%       C.r = C.f and C.b
%%
%%  Return variable C.d
%%  Return true if there is no return parameter
%%   
build_circuit(Circuit, Args, Bs) ->
    io:format("build circuit = ~p ~p\n",
	      [Circuit, Args]),
    {{bool,?T}, Bs}.


%% build  [ oexpr := lexpr ';' ]
%% here we could/should generate Oexpr then pass the 
%% output to the left expression to be used as gate/circuit output?
build_assignment_defs([{lop,'=',OExpr,LExpr}|Assignments], Bs0) ->
    {Y,Bs1} = build(LExpr,Bs0),
    {X,Bs2} = build(OExpr,Bs1),
    {{bool,Z},Bs3} = operation('eq',X,Y,Bs2),
    xor_gate(Bs3,?F,[Z,?T]),
    build_assignment_defs(Assignments, Bs3);
build_assignment_defs([], Bs) ->
    Bs.

%%
%% Special build of cnf/snf
%% in the cnf case assume that the clause are the
%% literal integers
%% in the snf case the literals are symbols
%%
build_snf([CL|CLs], Bs) ->
    {Xs,Bs1} = build_args(CL,Bs),
    Ls = [L || {bool,L} <- Xs],
    try add_clause(Bs1,Ls) of
	{false,_I} ->
	    throw(contradiction);
	false ->
	    throw(contradiction);
	_ ->
	    build_snf(CLs, Bs1)
    catch
	?EXCEPTION(error,Reason,Stack) ->
	    io:format("snf error: ~w\n~p\n", [Reason,?GET_STACK(Stack)]),
	    error(Reason)
    end;
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
    case build__(F, Bs) of
	{{uint,_N,Xs}, Bs1} -> {[{bool,X}||X<-Xs],Bs1};
	{{int,_N,Xs}, Bs1}  -> {[{bool,X}||X<-Xs],Bs1};
	{{bit,_N,Xs}, Bs1}  -> {[{bool,X}||X<-Xs],Bs1};
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

build_iquant_(F,[{'=',V,D}|Qs], Bs) ->
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

eval_meta(I, _Bs) when is_integer(I) -> I;
eval_meta({const,V}, _Bs) -> V;
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
eval_meta(ID, Bs) when is_binary(ID) -> eval_id(ID, Bs);
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
			    io:format("'~s' is not bound\n", [Vn]),
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

all(As, Bs) ->
    X = varp_circuit:all(Bs#bs.vp, circuit_args(As)),
    {{bool,X},Bs}.

any(As, Bs) ->
    X = varp_circuit:any(Bs#bs.vp, circuit_args(As)),
    {{bool,X},Bs}.    

none(As,Bs) ->
    X = varp_circuit:none(Bs#bs.vp, circuit_args(As)),
    {{bool,X},Bs}.

one(Xs, Bs) ->
    eqk(1,Xs,Bs).

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

eqk(K,Xs,Bs) ->
    X = varp_circuit:eqk(Bs#bs.vp, K, circuit_args(Xs)),
    {{bool,X},Bs}.

gtk(K,Xs,Bs) ->
    X = varp_circuit:gtk(Bs#bs.vp, K, circuit_args(Xs)),
    {{bool,X},Bs}.

negate({bool,X}) -> {bool,lnot(X)}.

lnot(?T) -> ?F;
lnot(?F) -> ?T;
lnot(X) -> -X.
     
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

build_args(Fs,Bs) when is_list(Fs) ->
    build_list(Fs, Bs);
build_args(F,Bs) ->
    case build__(F, Bs) of
	{{uint,_N,Xs}, Bs1} -> {[{bool,X}||X<-Xs],Bs1};
	{{int,_N,Xs}, Bs1}  -> {[{bool,X}||X<-Xs],Bs1};
	{{bit,_N,Xs}, Bs1}  -> {[{bool,X}||X<-Xs],Bs1}
    end.

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


operation_(Op, A, Bs) ->
    %% io:format("operation: ~w ~w\n", [Op,[A]]),
    operation(Op,A,Bs).

operation_(Op, A,B, Bs) ->
    %% io:format("operation: ~w ~w\n", [Op,[A,B]]),
    operation(Op,A,B,Bs).

%%
%% Unary operator
%%
operation('bnot', A, Bs) ->
    B = varp_arith:bitwise_not(Bs#bs.vp,A),
    {B, Bs};
operation('not', {bool,A}, Bs) ->
    {lnot(A), Bs};
operation('not', A, Bs) ->
    B = varp_arith:neq(Bs#bs.vp,A,{uint,1,[false]}),
    {{bool,B}, Bs};

operation('neg', A, Bs) ->
    case vconst(A) of
	false ->
	    B = varp_arith:negate(Bs#bs.vp,A),
	    {B, Bs};
	Av ->
	    Av1 = -Av,
	    An1 = varp_math:signed_size(Av1),
	    {const_vector_(An1-1,int,An1,[],Av1),Bs}
    end;
operation('abs', A, Bs) ->
    B = varp_arith:abs(Bs#bs.vp,A),
    {B, Bs}.

%%
%% Binary operator
%%
operation('and',{bool,?F},{bool,_Z}, Bs) ->    {{bool,?F},Bs};
operation('and',{bool,_Y},{bool,?F}, Bs) ->    {{bool,?F},Bs};
operation('and',{bool,?T},{bool,Z}, Bs) ->    {{bool,Z},Bs};
operation('and',{bool,Y},{bool,?T}, Bs) ->    {{bool,Y},Bs};
operation('and',{bool,Y},{bool,Z}, Bs) ->
    X = varp_circuit:and_gate(Bs#bs.vp, Y, Z),
    {{bool,X},Bs};

operation('band',A,B,Bs) ->
    C = varp_arith:bitwise_and(Bs#bs.vp,A,B),
    {C, Bs};

operation('or',{bool,?F},{bool,?F}, Bs) -> {{bool,?F},Bs};
operation('or',{bool,?T},{bool,_Z}, Bs) -> {{bool,?T},Bs};
operation('or',{bool,_Y},{bool,?T}, Bs) -> {{bool,?T},Bs};
operation('or',{bool,?F},{bool,Z}, Bs) -> {{bool,Z},Bs};
operation('or',{bool,Y},{bool,?F}, Bs) -> {{bool,Y},Bs};
operation('or',{bool,Y},{bool,Z}, Bs) ->
    X = varp_circuit:or_gate(Bs#bs.vp, Y, Z),
    {{bool,X},Bs};
    
operation('bor',A,B,Bs) ->
    C = varp_arith:bitwise_or(Bs#bs.vp,A,B),
    {C, Bs};

operation('imp',{bool,?F},{bool,?T}, Bs) ->  {{bool,?T},Bs};
operation('imp',{bool,?F},{bool,?F}, Bs) -> {{bool,?T},Bs};
operation('imp',{bool,?T},{bool,?T}, Bs) ->   {{bool,?T},Bs};
operation('imp',{bool,?T},{bool,?F}, Bs) ->  {{bool,?F},Bs};
operation('imp',{bool,Y},{bool,Z}, Bs) ->
    X = varp_circuit:imp_gate(Bs#bs.vp, Y, Z),
    {{bool,X},Bs};
operation('imp',A,B,Bs) ->
    {An,Bs1} = operation_('~',A,Bs),
    operation_('|',An,B,Bs1);

operation('equ',{bool,?F},{bool,Z},Bs) -> {{bool,lnot(Z)},Bs};
operation('equ',{bool,?T},{bool,Z},Bs) -> {{bool,Z},Bs};
operation('equ',{bool,Y},{bool,?T},Bs) -> {{bool,Y},Bs};
operation('equ',{bool,Y},{bool,?F},Bs) -> {{bool,lnot(Y)},Bs};
operation('equ',{bool,Y},{bool,Z},Bs) ->
    %% X = add_variable(Bs),
    %% {{bool,X},xor_gate(Bs,X,[lnot(Y),Z])};
    X = varp_circuit:xor_gate(Bs#bs.vp, lnot(Y), Z),
    {{bool,X},Bs};

operation('equ',A,B,Bs) ->
    C = varp_arith:bitwise_equ(Bs#bs.vp,A,B),
    {C,Bs};

operation('xor',{bool,?F},{bool,Z}, Bs) -> {{bool,Z},Bs};
operation('xor',{bool,?T},{bool,Z}, Bs) -> {{bool,lnot(Z)},Bs};
operation('xor',{bool,Z},{bool,?F}, Bs) -> {{bool,Z},Bs};
operation('xor',{bool,Z},{bool,?T}, Bs) -> {{bool,lnot(Z)},Bs};
operation('xor',{bool,Y},{bool,Z}, Bs) ->
    X = varp_circuit:xor_gate(Bs#bs.vp, Y, Z),
    {{bool,X},Bs};

operation('bxor',A,B,Bs) ->
    C = varp_arith:bitwise_xor(Bs#bs.vp,A,B),
    {C, Bs};

operation('lt',A,B,Bs) ->
    C = varp_arith:lt(Bs#bs.vp,A,B),
    {{bool,C},Bs};
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

operation('eq',A,B,Bs) ->
    Eq = varp_arith:eq(Bs#bs.vp,A,B),
    {{bool,Eq},Bs};

%%
%% Alias operation
%%
operation(':=',V,X={T,Size,Xs},Bs) when ?is_vec_type(T) ->
    {X, alias_vector(Bs,T,V,Size,Xs)};
operation(':=',V,X={bool,Xb},Bs) ->
    {X, alias(V,Xb,Bs)};

%% operator '=' is kind of assignment but really a 
%% equality test and check of overflow bits
operation('=',R,L,Bs) ->
    %% FIXME: same as '==' but check overflow / truncate 
    operation('equ',R,L,Bs);

operation('shl',A,B,Bs) ->
    C = varp_arith:shl(Bs#bs.vp, A, B),
    {C, Bs};

operation('shr',A,B,Bs) ->
    C = varp_arith:shr(Bs#bs.vp, A, B),
    {C, Bs};
	    
%% rotate left
operation('rol',A,B,Bs) ->
    C = varp_arith:rol(Bs#bs.vp, A, B),
    {C, Bs};

%% rotate right
operation('ror',A,B,Bs) ->
    C = varp_arith:ror(Bs#bs.vp, A, B),
    {C, Bs};

operation('add',A,B,Bs) ->
    C = varp_arith:add(Bs#bs.vp, A, B),
    {C, Bs};

operation('sub',A,B,Bs) ->
    C = varp_arith:subtract(Bs#bs.vp, A, B),
    {C, Bs};

operation('mul',A,B,Bs) ->
    C = varp_arith:multiply(Bs#bs.vp, A, B),
    {C, Bs};

%% DivZero  could be used to generate a Exception output
%% Signed?
operation('div',Y,Z,Bs) ->
    Q = varp_arith:divide(Bs#bs.vp, Y, Z),
    {Q, Bs};

%% DivZero  could be used to generate a Exception output
%% Signed?
operation('rem',Y,Z,Bs) ->
    R = varp_arith:reminder(Bs#bs.vp,Y,Z),
    {R, Bs};

operation('min',A,B,Bs) ->
    C = varp_arith:min(Bs#bs.vp, A, B),
    {C, Bs};

operation('max',A,B,Bs) ->
    C = varp_arith:max(Bs#bs.vp, A, B),
    {C, Bs}.

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
    each_unbound_(Bs, Fun, varp:next_unbound(Bs#bs.vp)).

each_unbound_(_Bs, _Fun, false) ->
    ok;
each_unbound_(Bs, Fun, Xi) ->
    Fun(Xi),
    each_unbound_(Bs, Fun, varp:next_unbound(Bs#bs.vp,Xi)).

fold_unbound(Bs, Fun, Acc) ->
    fold_unbound_(Bs, Fun, Acc, varp:next_unbound(Bs#bs.vp)).

fold_unbound_(_Bs, _Fun, Acc, false) ->
    Acc;
fold_unbound_(Bs, Fun, Acc, Xi) ->
    Acc1 = Fun(Xi, Acc),
    fold_unbound_(Bs, Fun, Acc1, varp:next_unbound(Bs#bs.vp, Xi)).

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
			  ?T -> [{{p,<<"x">>,[I]}, true}|Acc];
			  ?F -> [{{p,<<"x">>,[I]},false}|Acc];
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

empty_vs(Bs) ->    
    (Bs#bs.vs =:= undefined) orelse  (maps:size(Bs#bs.vs) =:= 0).

proof_literal(Bs,Li) ->
    EmptyVs = empty_vs(Bs),
    if EmptyVs -> integer_to_list(Li);	    
       Li < 0 ->
	    case maps:find(-Li, Bs#bs.vs) of
		error -> integer_to_list(Li);
		{ok,[{p,<<"x">>,[I]}]} -> integer_to_list(-I);
		{ok,[P|_]} -> [$!|varp_format:format_symbol(P)]
	    end;
       Li > 0 ->
	    case maps:find(Li, Bs#bs.vs) of
		error -> integer_to_list(Li);
		{ok,[{p,<<"x">>,[I]}]} -> integer_to_list(I);
		{ok,[P|_]} -> varp_format:format_symbol(P)
	    end
    end.
