%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2020, Tony Rogvall
%%% @doc
%%%    The new name for varp_formula
%%% @end
%%% Created :  3 Sep 2020 by Tony Rogvall <tony@rogvall.se>

-module(varp_ast).

-include("varp.hrl").

-export([build/1, build/2, build/3]).

build(Tree) ->
    build(Tree, varc:new(#{})).

build(Tree, Vp) ->
    build(Tree, Vp, #{}).

build(Tree, Vp, State) ->
    io:format("Build: ~p\n", [Tree]),
    case Tree of
	{'p', Sym, Args}  -> var(Sym, Args, Vp, State);
	{'not', A}        -> unary('not',A,Vp,State);
	{'!', A}          -> unary('not',A,Vp,State);
	{'and', A1, A2}   -> binary('and',A1,A2,Vp,State);
	{'&&', A1, A2}    -> binary('and',A1,A2,Vp,State);
	{'or', A1, A2}    -> binary('or',A1,A2,Vp,State);
	{'||', A1, A2}    -> binary('or',A1,A2,Vp,State);
	{'imp', A1, A2}   -> binary('imp',A1,A2,Vp,State);
	{'->', A1, A2}    -> binary('imp',A1,A2,Vp,State);
	{'xor', A1, A2}   -> binary('xor',A1,A2,Vp,State);
	{'equ', A1, A2}   -> binary('equ',A1,A2,Vp,State);
	{'<->', A1, A2}   -> binary('equ',A1,A2,Vp,State);
	{'==', A1, A2}    -> binary('equ',A1,A2,Vp,State);
	{'ALL',As}        -> nary('all',As,Vp,State);
	{'ANY',As}        -> nary('any',As,Vp,State);
	{'NONE',As}       -> nary('none',As,Vp,State);
	{'ONE',As}        -> nary('one',As,Vp,State)
    end.

var(Sym, Args, Vp, State) ->
    {P, As} = var_term({p,Sym,Args}),
    As1 = [eval_term(Ai,State) || Ai <- As],
    Term1 = {P, As1},
    case varc:find_symbol(Vp, Term1) of
	false ->
	    Var = varc:add_variable(Vp, true),
	    varc:add_symbol(Vp, Var, Term1),
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

var_term({p,V,[]}) ->
    {atom_to_list(V), []};
var_term({p,V,Args}) ->
    {atom_to_list(V), [var_term_(A) || A <- Args]}.

var_term_(#cconst{base=Base,value=Value}) ->
    const_int(Base, Value);
var_term_(#cid{name=Name}) ->
    Name;
var_term_(#cbinary{op=Op,arg1=Arg1,arg2=Arg2}) ->
    Tab = #{ '+' => "add", '-' => "sub", '*' => "mul",
	     '/' => "div", '%' => "rem",
	     '&' => "band", '|' => "bor", "^" => "bxor" },
    { maps:get(Op, Tab), [var_term_(Arg1), var_term_(Arg2)]};
var_term_(#cunary{op=Op,arg=Arg}) ->
    Tab = #{ '-' => "neg", '+' => "pos", '~' => "bnot" },
    { maps:get(Op, Tab), [var_term_(Arg)]};
var_term_(#ccall{func=#cid{name=Func},args=Args}) ->
    { Func, [ var_term_(A) || A <- Args]}.


const_int(16,"0x"++Value) ->
    list_to_integer(Value, 16);
const_int(2,"0b"++Value) ->
    list_to_integer(Value, 2);
const_int(8,"0"++Value) ->
    list_to_integer(Value, 8);
const_int(Base,Value) ->
    list_to_integer(Value, Base).

eval_term(Value,_Bs) when is_integer(Value) -> 
    Value;
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

