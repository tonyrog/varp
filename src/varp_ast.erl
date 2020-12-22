%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2020, Tony Rogvall
%%% @doc
%%%    The new name for varp_formula
%%% @end
%%% Created :  3 Sep 2020 by Tony Rogvall <tony@rogvall.se>

-module(varp_ast).

-include("varp.hrl").

-export([build/1, build/2, build/3]).
-export([test/1]).

build(Tree) ->
    build(Tree, varp_nif:new(#{})).

build(Tree, Vp) ->
    build(Tree, Vp, #{}).

build(Tree, Vp, State) ->
    %% io:format("Build: ~p\n", [Tree]),
    case Tree of
	true -> true;
	false -> false;
	{'p', Sym, Args}   -> var(Sym, Args, Vp, State);
	{'not', A}         -> unary('not',A,Vp,State);
	{'and', A1, A2}    -> binary('and',A1,A2,Vp,State);
	{'or', A1, A2}     -> binary('or',A1,A2,Vp,State);
	{'imp', A1, A2}    -> binary('imp',A1,A2,Vp,State);
	{'xor', A1, A2}    -> binary('xor',A1,A2,Vp,State);
	{'equ', A1, A2}    -> binary('equ',A1,A2,Vp,State);
	{'ALL',As}         -> nary('all',As,Vp,State);
	{'ANY',As}         -> nary('any',As,Vp,State);
	{'NONE',As}        -> nary('none',As,Vp,State);
	{'ONE',As}         -> nary('one',As,Vp,State);
	{'ODD',As}         -> nary('odd',As,Vp,State);
	{'EVEN',As}        -> nary('even',As,Vp,State);
	{'PARITY',As}      -> nary('parity',As,Vp,State);
	{{'ALL',Gs},A}     -> quant('all',Gs,A,Vp,State);
	{{'ANY',Gs},A}     -> quant('any',Gs,A,Vp,State);
	{{'NONE',Gs},A}    -> quant('none',Gs,A,Vp,State);
	{{'ONE',Gs},A}     -> quant('one',Gs,A,Vp,State);
	{{'ODD',Gs},A}     -> quant('odd',Gs,A,Vp,State);
	{{'EVEN',Gs},A}    -> quant('even',Gs,A,Vp,State);
	{{'PARITY',Gs},A}  -> quant('parity',Gs,A,Vp,State);
	{{'EQ',[K|Gs]},A}  -> quant_k('eq',K,Gs,A,Vp,State);
	{{'NEQ',[K|Gs]},A} -> quant_k('neq',K,Gs,A,Vp,State);
	{{'LT',[K|Gs]},A}  -> quant_k('lt',K,Gs,A,Vp,State);
	{{'LTE',[K|Gs]},A} -> quant_k('lte',K,Gs,A,Vp,State);
	{{'GT',[K|Gs]},A}  -> quant_k('gt',K,Gs,A,Vp,State);
	{{'GTE',[K|Gs]},A} -> quant_k('gte',K,Gs,A,Vp,State);
	%% allowed conditionals in logic part (must expand to constant!)
	{'gt',  A1, A2}     -> cond_bin("gt",A1,A2,Vp,State);
	{'gte', A1, A2}     -> cond_bin("gte",A1,A2,Vp,State);
	{'lt', A1, A2}      -> cond_bin("lt",A1,A2,Vp,State);
	{'lte', A1, A2}     -> cond_bin("lte",A1,A2,Vp,State);
	{'eq', A1, A2}      -> cond_bin("eq",A1,A2,Vp,State);
	{'neq', A1, A2}     -> cond_bin("neq",A1,A2,Vp,State)
    end.

var(Sym, Args, Vp, State) ->
    {P, As} = var_term({p,Sym,Args}),
    As1 = [eval_term(Ai,State) || Ai <- As],
    Term1 = {P, As1},
    case varp_nif:find_symbol(Vp, Term1) of
	false ->
	    Var = varp_nif:add_variable(Vp, true),
	    varp_nif:isused(Vp, Var, true),  %% mark as in use!
	    varp_nif:add_symbol(Vp, Var, Term1),
	    Var;
	Var when is_integer(Var) ->
	    Var;
	Vec when is_list(Vec) ->
	    Vec
    end.

unary(Gate, A, Vp, State) ->
    Y = build(A, Vp, State),
    varp_circuit:gate(Vp, Gate, Y).
    
binary(Gate, A1, A2, Vp, State) ->
    Y = build(A1, Vp, State),
    Z = build(A2, Vp, State),
    varp_circuit:gate(Vp, Gate, Y, Z).

nary(Gate, As, Vp, State) ->
    Ys = [build(Ai, Vp, State) || Ai <- As],
    varp_circuit:gate(Vp, Gate, Ys).

quant_k(Gate,Gk,Gs,A,Vp,State) ->
    Kt = to_term(Gk),
    K = eval_term(Kt,State),
    L = qbuild(Gs,A,Vp,State),
    varp_circuit:gate(Vp, Gate, K, lists:flatten(L)).

quant(Gate,Gs,A,Vp,State) ->
    L = qbuild(Gs,A,Vp,State),
    varp_circuit:gate(Vp, Gate, lists:flatten(L)).

qbuild([G|Gs],A,Vp,State) ->
    case G of
	{assign,{id,X},R} ->
	    Rt = to_term(R),
	    case eval_term(Rt,State) of
		{range,From,To} ->
		    [ qbuild(Gs,A,Vp,State#{X=>I}) || I <- lists:seq(From,To)];
		I ->
		    qbuild(Gs,A,Vp,State#{X=>I})
	    end;
	_ ->
	    Gt = to_term(G),
	    case eval_term(Gt,State) of
		false -> [];
		true -> qbuild(Gs,A,Vp,State)
	    end
    end;
qbuild([],A,Vp,State) ->
    [build(A, Vp, State)].

cond_bin(Op, L, R, _Vp, State) ->
    L1 = to_term(L),
    R1 = to_term(R),
    Ret = eval_term({Op,[L1,R1]}, State),
    %% io:format("cond_bin: ~p = ~p, (state=~p)\n", [{Op,[L1,R1]},Ret,State]),
    Ret.

var_term({p,V,[]}) ->
    {atom_to_list(V), []};
var_term({p,V,Args}) ->
    {atom_to_list(V), [to_term(A) || A <- Args]}.

%% convert tree to term form

to_term({const,Value}) -> Value;
to_term({id,Name}) -> Name;
to_term({range,From,To}) -> {range,to_term(From),to_term(To)};
to_term({call,Func,Args}) ->
    { Func, [ to_term(A) || A <- Args]};
to_term({uint,_Len,Value}) -> Value;
to_term({int,_Len,Value}) -> Value;
to_term({Op,Arg1,Arg2}) when is_atom(Op) ->
    to_binary_term(Op,Arg1,Arg2);
to_term({Op,Arg}) when is_atom(Op) ->
    to_unary_term(Op,Arg).

to_binary_term(Op,Arg1,Arg2) when is_atom(Op) ->
    OpName = atom_to_list(Op),
    { OpName, [to_term(Arg1), to_term(Arg2)]}.

to_unary_term(Op,Arg) when is_atom(Op) ->
    OpName = atom_to_list(Op),
    { OpName, [to_term(Arg)]}.    

eval_term(Value,_Bs) when is_integer(Value) -> 
    Value;
eval_term({range,From,To},Bs) ->
    {range,eval_term(From,Bs),eval_term(To,Bs)};
eval_term(Var,Bs) when is_list(Var); is_atom(Var) ->
    case maps:get(Var, Bs, undefined) of
	undefined -> error({undefined_variable,Var});
	Value -> Value
    end;
eval_term({"add",[A,B]},Bs) -> eval(fun erlang:'+'/2, A,B, Bs);
eval_term({"sub",[A,B]},Bs) -> eval(fun erlang:'-'/2, A,B, Bs);
eval_term({"mul",[A,B]},Bs) -> eval(fun erlang:'*'/2, A,B, Bs);
eval_term({"div",[A,B]},Bs) -> eval(fun erlang:'div'/2, A,B, Bs);
eval_term({"rem",[A,B]},Bs) -> eval(fun erlang:'rem'/2, A,B, Bs);
eval_term({"band",[A,B]},Bs) -> eval(fun erlang:'band'/2, A,B, Bs);
eval_term({"bor",[A,B]},Bs) -> eval(fun erlang:'bor'/2, A,B, Bs);
eval_term({"bxor",[A,B]},Bs) -> eval(fun erlang:'bxor'/2, A,B, Bs);
eval_term({"gt",[A,B]},Bs) -> eval(fun erlang:'>'/2, A,B, Bs);
eval_term({"gte",[A,B]},Bs) -> eval(fun erlang:'>='/2, A,B, Bs);
eval_term({"lt",[A,B]},Bs) -> eval(fun erlang:'<'/2, A,B, Bs);
eval_term({"lte",[A,B]},Bs) -> eval(fun erlang:'=<'/2, A,B, Bs);
eval_term({"eq",[A,B]},Bs) -> eval(fun erlang:'=='/2, A,B, Bs);
eval_term({"neq",[A,B]},Bs) -> eval(fun erlang:'/='/2, A,B, Bs);
eval_term({"neg",[A]},Bs) -> eval(fun erlang:'-'/1, A, Bs);
eval_term({"pos",[A]},Bs) -> eval(fun erlang:'+'/1, A, Bs);
eval_term({"bnot",[A]},Bs) -> eval(fun erlang:'bnot'/1, A, Bs);
eval_term({Sym,As}, Bs) ->
    %% Note! The module varp_user must be preloaded!
    %% Fixme: declare function symbols that can stay abstract (for unification)
    try list_to_existing_atom(Sym) of
	Fun ->
	    Arity = length(As),
	    case erlang:function_exported(varp_user, Fun, Arity) of
		true ->
		    Args = [eval_term(Ai,Bs) || Ai <- As],
		    apply(varp_user, Fun, Args);
		false ->
		    error({undefined_function,Fun})
	    end
    catch 
	error:badarg ->
	    error({undefined_function,Sym})
    end.

eval(Fun, A, B, Bs) ->
    Av = eval_term(A, Bs),
    Bv = eval_term(B, Bs),
    Fun(Av,Bv).

eval(Fun, A, Bs) ->
    Av = eval_term(A, Bs),
    Fun(Av).

%% TEST function

test(Text) ->
    {ok,{_Def,Tree}} = varp:parse(Text),
    io:format("Tree = ~p\n", [Tree]),
    Vp = varp_nif:new(#{xref => true}),
    F = build(Tree, Vp, #{}),
    case varp_nif:bind(Vp, F) of
	false ->
	    io:format("0 models found\n", []),
	    0;
	true ->
	    varp_nif:push(Vp),
	    varp_circuit:bt_all(Vp)
    end.
