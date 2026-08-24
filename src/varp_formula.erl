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
-export([model/1]).
-export([intersect_bindings/3]).
-export([install_bindings/3]).
-export([each_unbound/2]).
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
-define(is_bool_op(Op),
	((Op) =:= 'and' orelse (Op) =:= 'or' orelse (Op) =:= 'xor' orelse
	 (Op) =:= 'imp' orelse (Op) =:= 'equ' orelse
	 (Op) =:= 'nimp' orelse (Op) =:= 'nand' orelse (Op) =:= 'nor' orelse
	 (Op) =:= 'band' orelse (Op) =:= 'bor' orelse (Op) =:= 'bxor' orelse
	 (Op) =:= 'lt' orelse (Op) =:= 'gt' orelse
	 (Op) =:= 'lte' orelse (Op) =:= 'gte' orelse
	 (Op) =:= 'eq' orelse (Op) =:= 'neq')).
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
		 seed       => maps:get(seed,OptMap),
		 icase      => maps:get(icase,OptMap),
		 bcp2       => maps:get(bcp2,OptMap)
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
    Sym = {Name,Args},
    case varp_nif:find_symbol(Bs#bs.vp, Sym) of
	false ->
	    error;
	Val -> 
	    {ok,Val}
    end;
find_var({Type,Name,Args}, Bs) ->
    Sym = {Name,Args},
    case varp_nif:find_symbol(Bs#bs.vp, Sym) of
	false ->
	    error;
	Val -> 
	    {ok,{Type,length(Val),Val}}
    end.
    

make_variable({p,Name,Args}, Bs) ->
    L = add_atom(Bs),
    Var = {Name,Args},
    add_symbol(Bs, Var, L, bool),
    {{bool,L}, Bs}.

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
    case bld(V, Bs) of
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


%% keep defined circuits to allow parser to know what
%% symbols are predicates and what symbols are circuits
init_circuit_def() ->
    put(circuit_defs, #{}).

add_circuit_def(C={circuit,Name,_Params,_Defs}) ->
    CDef = get(circuit_defs),
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
set(X, Y, Bs) -> operation1('=',X,Y,Bs).

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
bld(_X,{const,W}, Bs) when is_integer(W) ->
    if W < 0 ->
	    N = varp_math:signed_size(W),
	    const_vector(int,W,N,Bs);
       true ->
	    N = varp_math:unsigned_size(W),
	    const_vector(uint,W,N,Bs)
    end;
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
	error ->
	    %% a name with a definition is a macro, not a variable.
	    %% declaring it as a boolean here would fix its arity and
	    %% stop the same name being defined for several arities.
	    case is_definition(P, Bs) of
		true ->
		    variable(V, Bs);
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
bld(_X,{PType,SExpr,PExpr},Bs) when
      PType =:= uint; PType =:= int; PType =:= bit ->
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
bld(_X,{vec,Fs}, Bs) ->
    {Ys,Bs1} = bld_list(Fs, Bs),
    Ys1 = join_vector(Ys),
    {{bit,length(Ys1),[bit(Y)||Y <- Ys1]},Bs1};

bld(_X,{bitindex,A,I},Bs) ->
    I1 = eval_meta(I,Bs),
    case A of
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
bld(_X,{lop,'=',L,R}, Bs) ->
    {Y,Bs1} = bld(R, Bs),
    operation1('=',L,Y,Bs1);
bld(X,{lop,Op,A}, Bs) ->
    {Y,Bs1} = bld(A, Bs),
    operation1(Op, X, Y, Bs1);
bld(X,{lop,Op,A,B}, Bs) ->
    {Y,Bs1} = bld(A, Bs),
    {Z,Bs2} = bld(B, Bs1),
    operation2(Op,X,Y,Z,Bs2);
bld(X,{lop,ite,C,T,E}, Bs) ->
    {Cf,Bs1} = bld(C, Bs),
    {Tf,Bs2} = bld(T, Bs1),
    {Ef,Bs3} = bld(E, Bs2),
    ite(X,Cf,Tf,Ef,Bs3);

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
    case find_circuit_def(Name, Bs#bs.circuits, icase(Bs)) of
	{ok, Circuit} ->
	    {Value,Bs1} = build_circuit(Circuit, Args, Bs),
	    set(X, Value, Bs1);
	error ->
	    error({circuit_undefined, Name})
    end.

%% build one or more arguments
bld_args(Fs,Bs) when is_list(Fs) ->
    bld_list(Fs, Bs);
bld_args(F,Bs) ->
    case bld(F, Bs) of
	{{uint,_N,Xs}, Bs1} -> {[{bool,X}||X<-Xs],Bs1};
	{{int,_N,Xs}, Bs1}  -> {[{bool,X}||X<-Xs],Bs1};
	{{bit,_N,Xs}, Bs1}  -> {[{bool,X}||X<-Xs],Bs1}
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
    {Ins,Outs,Return} = circuit_params(Name, Params),
    {Bnd,Bs1} = circuit_bind(Name, Ins++Outs, Args, Bs0),
    {Prefix,Bs2} = circuit_prefix(Name, Bs1),
    {RetName,Bs3} = circuit_return(Return, Prefix, Bs2),
    Body = circuit_rename(Defs, maps:from_list(Bnd), Prefix, Bs3#bs.defs),
    Bs4 = build_circuit_body(Body, Bs3),
    {Value,Bs5} = circuit_value(RetName, Bs4),
    %% locals and nested circuit definitions do not leak into the caller,
    %% but declarations made for the arguments (in Bs1) do.
    {Value, Bs5#bs { decls = Bs1#bs.decls, circuits = Bs1#bs.circuits }}.

%% split the parameter list into {In, Out, Return}
circuit_params(Name, Params) ->
    circuit_params(Name, Params, [], [], undefined).

circuit_params(Name, [{in,Ds}|Ps], In, Out, Ret) ->
    circuit_params(Name, Ps, In++[circuit_formal(Name,D) || D <- Ds], Out, Ret);
circuit_params(Name, [{out,Ds}|Ps], In, Out, Ret) ->
    circuit_params(Name, Ps, In, Out++[circuit_formal(Name,D) || D <- Ds], Ret);
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
circuit_bind(Name, Formals, Args, Bs) ->
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
    circuit_bind_(Name, Formals, 1, length(Pos), Pos, NamedMap, [], Bs).

circuit_bind_(Name, [F=#{name := N}|Fs], I, NPos, Pos, Named, Acc, Bs) ->
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
    {V,Bs1} = circuit_arg(F, Expr, Bs),
    circuit_bind_(Name, Fs, I+1, NPos, Pos, Named, [{N,V}|Acc], Bs1);
circuit_bind_(_Name, [], _I, _NPos, _Pos, _Named, Acc, Bs) ->
    {lists:reverse(Acc), Bs}.

%% build one argument.  When the parameter is typed and the argument is a
%% plain, not yet declared, symbol then the parameter type/size is used to
%% declare it in the caller scope.
circuit_arg(#{type := Type, size := Size}, Expr={p,P,As}, Bs)
  when Type =/= bool ->
    Bs1 = case varp:find_decl(P, Bs#bs.decls, icase(Bs)) of
	      error ->
		  N = eval_meta(Size, Bs),
		  Decls = maps:put(P, {Type,length(As),N}, Bs#bs.decls),
		  Bs#bs { decls = Decls };
	      _ ->
		  Bs
	  end,
    bld(Expr, Bs1);
circuit_arg(_F, Expr, Bs) ->
    bld(Expr, Bs).

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
circuit_rename({p,P,As}, Env, Prefix, Defs) ->
    As1 = circuit_rename(As, Env, Prefix, Defs),
    case maps:find(P, Env) of
	{ok,V} when As1 =:= [] ->
	    {value,V};
	{ok,_} ->
	    error({circuit_parameter_arity, P});
	error ->
	    case maps:is_key({P,length(As1)}, Defs) of
		true  -> {p,P,As1};
		false -> {p,<<Prefix/binary,P/binary>>,As1}
	    end
    end;
%% a nested circuit definition keeps its own scope, it is renamed when
%% it is instantiated
circuit_rename(C={circuit,_Name,_Params,_Body}, _Env, _Prefix, _Defs) ->
    C;
circuit_rename({cop,Name,As}, Env, Prefix, Defs) ->
    {cop,Name,circuit_rename(As, Env, Prefix, Defs)};
circuit_rename(T, Env, Prefix, Defs) when is_tuple(T) ->
    list_to_tuple(circuit_rename(tuple_to_list(T), Env, Prefix, Defs));
circuit_rename([H|T], Env, Prefix, Defs) ->
    [circuit_rename(H, Env, Prefix, Defs) |
     circuit_rename(T, Env, Prefix, Defs)];
circuit_rename(X, _Env, _Prefix, _Defs) ->
    X.

build_circuit_body([{declare,Ds}|Body], Bs) ->
    case varp:add_decls(Ds, Bs#bs.decls, Bs) of
	{ok,Decls} -> build_circuit_body(Body, Bs#bs { decls = Decls });
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
    case varp_nif:find_symbol(Bs#bs.vp, Sym) of
	{Type,Ls} ->
	    %% io:format("var_vector (~w) ~p = ~p\n", [N1,Sym,{Type,Ls}]),
	    {{Type,length(Ls),Ls},Bs};
	false ->
	    {V1,Vn} = varp_nif:add_variables(Bs#bs.vp, N1, true),
	    Ls = lists:seq(V1,Vn),
	    Var = {Name,Args},
	    add_symbol(Bs, Var, Ls, Type),
	    %% io:format("add var_vector (~w) ~p = ~p\n", [N1,Sym,{Type,Ls}]),
	    {{Type,N1,Ls},Bs}
    end.

%%
%%var_vector_(Size,Size,Type,Xs,_V,Bs) -> 
%%    {{Type,Size,lists:reverse(Xs)},Bs};
%%var_vector_(I,Size,Type,Xs,V,Bs) ->
%%    {{bool,Xi},Bs1} = variable({Type,V,Size,I},Bs),
%%    var_vector_(I+1,Size,Type,[Xi|Xs],V,Bs1).

all(A,Bs) -> all(undefined,A,Bs).
all(X,As,Bs) ->
    X1 = varp_circuit:all(Bs#bs.vp,X,circuit_args(As)),
    {{bool,X1},Bs}.

any(A,Bs) -> any(undefined,A,Bs).
any(X,As,Bs) ->
    X1 = varp_circuit:any(Bs#bs.vp,X,circuit_args(As)),
    {{bool,X1},Bs}.    

none(A,Bs) -> none(undefined,A,Bs).
none(X,As,Bs) ->
    X1 = varp_circuit:none(Bs#bs.vp,X,circuit_args(As)),
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
    X1 = varp_circuit:eqk(Bs#bs.vp,K,X,circuit_args(Ys)),
    {{bool,X1},Bs}.

neqk(K,X,Ys,Bs) ->
    X1 = varp_circuit:neqk(Bs#bs.vp,K,X,circuit_args(Ys)),
    {{bool,X1},Bs}.

gtk(K,X,Ys,Bs) ->
    X1 = varp_circuit:gtk(Bs#bs.vp,K,X,circuit_args(Ys)),
    {{bool,X1},Bs}.

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

%%
%% Unary operator
%%
operation1(Op, {bool,A}, Bs) when Op =:= 'not'; Op =:= 'bnot' ->
    B = varp_circuit:gate(Bs#bs.vp,'not',A),
    {{bool,B}, Bs};
operation1(Op, A, Bs) ->
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
operation1(Op, {bool,X}, {bool,A}, Bs) when
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
operation1(Op, undefined, A, Bs) ->
    operation1(Op, A, Bs);
operation1(Op, X, A, Bs) ->
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
operation2(Op,{bool,Y},{bool,Z}, Bs) when ?is_bool_op(Op) ->
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
operation2(Op,A,B,Bs) ->
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
	    '=' -> X = varp_arith:set(Bs#bs.vp,A,B),{bool,X}
	end,
    {C, Bs}.

%% like operation2 but result is predetermined in X
operation2(Op,undefined,Y,Z,Bs) ->
    operation2(Op,Y,Z,Bs);
operation2(Op,{bool,X},{bool,Y},{bool,Z}, Bs) when ?is_bool_op(Op) ->
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
operation2(Op,X,Y,Z,Bs) ->
    X1 = case Op of 
	     'band' -> varp_arith:bitwise_and(Bs#bs.vp,X,Y,Z);
	     'bor' -> varp_arith:bitwise_or(Bs#bs.vp,X,Y,Z);
	     'bxor' -> varp_arith:bitwise_xor(Bs#bs.vp,X,Y,Z);
	     'imp' -> Yn = varp_arith:bitwise_not(Bs#bs.vp,Y),
		     varp_arith:bitwise_or(Bs#bs.vp,X,Yn,Z);
	     'equ' -> varp_arith:bitwise_equ(Bs#bs.vp,X,Y,Z);
	     'lt' -> Xb = varp_arith:lt(Bs#bs.vp,X,Y,Z), {bool,Xb};
	     'lte' -> Xb = varp_arith:lte(Bs#bs.vp,X,Y,Z), {bool,Xb};
	     'gt' -> Xb = varp_arith:gt(Bs#bs.vp,X,Y,Z), {bool,Xb};
	     'gte' -> Xb = varp_arith:gte(Bs#bs.vp,X,Y,Z), {bool,Xb};
	     'eq' -> Xb = varp_arith:eq(Bs#bs.vp,X,Y,Z), {bool,Xb};
	     'neq' -> Xb = varp_arith:neq(Bs#bs.vp,X,Y,Z),{bool,Xb};
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
	     'max' -> varp_arith:max(Bs#bs.vp,X,Y,Z);
	     %% operator '=' is kind of assignment but really a 
	     %% equality test and check of overflow bits
	     %% FIXME: same as '==' but check overflow / truncate 
	     '=' -> Xb = varp_arith:eq(Bs#bs.vp,X,Y,Z), {bool,Xb}
	 end,
    {X1, Bs}.

%%
%% if-then-else circuit
%%  (I & T) | (~I & E)
%%
ite(X,{bool,?T},T,_E, Bs) -> set(X,T,Bs);
ite(X,{bool,?F},_T,E, Bs) -> set(X,E,Bs);
ite(X,_Cond,Y,Y, Bs) -> set(X,Y,Bs);
%% (Cond & false) | (~Cond & E) == ~Cond & E
ite(X,Cond,{bool,?F},E, Bs) -> operation2('and',X,negate(Cond),E,Bs);
%% (Cond & T) | (~Cond & false) == Cond & T
ite(X,Cond,T,{bool,?F}, Bs) -> operation2('and',X,Cond,T,Bs);
ite(X,Cond,T,E, Bs) ->
    {A1,Bs1} = operation2('and',Cond,T,Bs),
    {A2,Bs2} = operation2('and',negate(Cond),E,Bs1),
    operation2('or',X,A1,A2,Bs2).

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
    model_(Bs#bs.vp).
    
model_(Vp) ->
    lists:keysort(1, collect_model(Vp)).

collect_model(Vp) ->
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
			      Value = varp_nif:value(Vp,I),
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
