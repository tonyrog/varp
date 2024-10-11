%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2024, Tony Rogvall
%%% @doc
%%%    Format module for varp
%%% @end
%%% Created : 29 Sep 2024 by Tony Rogvall <tony@rogvall.se>

-module(varp_format).

%% -define(DEBUG, true).
%% -compile(export_all).
-export([format_clause/2, format_clause/3]).
-export([format_literals/2, format_literals/3]).
-export([format_lit/2, format_lit/3]).
-export([format_var/2]).
-export([format_binding/1]).
-export([format_symbol/1]).
-export([format_meta/1]).
-export([format_internal_symbol/1]).

%% -export([fmt_v/2, fmt_q/2]).

-include("varp.hrl").

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
    case varp_formula:find_var(X,Bs) of
	error ->
	    format_bnd(Bs, X, X, Bound);
	{ok,[Var]} ->
	    format_bnd(Bs, X, Var, Bound)
    end.

format_bnd(_Bs, _X, Var, false) ->
    format_symbol(Var);
format_bnd(Bs, X, Var, true) ->
    Value = case varp_nif:value(Bs#bs.vp, X) of
		true -> "/1";
		false -> "/0";
		_ -> ""
	    end,
    format_symbol(Var) ++ Value;
format_bnd(Bs, X, Var, level) ->
    L = varp_nif:implication_level(Bs#bs.vp, X), 
    Value = case varp_nif:value(Bs#bs.vp, X) of
		true -> "=1@"++integer_to_list(L);
		false -> "=0@"++integer_to_list(L);
		_ -> ""
	    end,
    format_symbol(Var) ++ Value.

format_symbol(?T) -> "t";
format_symbol(?F) -> "f";
format_symbol(Name) when is_binary(Name) -> [Name];
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

format_p(Name) when is_binary(Name) -> Name;
format_p({p,V,[]}) when is_binary(V) -> [V];
format_p({p,T,As}) when is_integer(T) ->
    [$T,integer_to_list(As)|format_params(As)];
format_p({p,V,As}) when is_binary(V) ->
    [V|format_params(As)];
format_p({p,Name,As}) when is_list(Name); is_binary(Name) ->
    [Name|format_params(As)];
format_p({bitindex,Var,Index}) ->
    [format_p(Var),"[",integer_to_list(Index), "]"];
format_p({index,Var,Index}) ->
    [format_p(Var),"[",integer_to_list(Index), "]"].

%% format varp_nif symbol {Name,[param()]}  varp_nif:get_symbol
format_internal_symbol({SymName,Params}) when is_binary(SymName) ->
    [binary_to_list(SymName) | format_params(Params)];
format_internal_symbol({{SymName,Params},bool,1,0}) ->
    [binary_to_list(SymName) | format_params(Params)];
format_internal_symbol({{SymName,Params},_Type,_N,Pos}) ->
    [binary_to_list(SymName), format_params(Params) | ["[",integer_to_list(Pos),"]"]].


format_params([]) -> "";
format_params(As) when is_list(As) ->
    ["(",fmt_index_list(As),")"].

fmt_index_list([I]) ->
    [fmt_index(I)];
fmt_index_list([I|Is]) ->
    [fmt_index(I),","|fmt_index_list(Is)].


fmt_index(I) when is_integer(I) ->
    integer_to_list(I);
fmt_index({const,I}) ->
    integer_to_list(I);
fmt_index(A) when is_binary(A) ->
    [A];
fmt_index(Set) when is_list(Set) ->
    ["{",fmt_set(Set),"}"];
fmt_index({f,F,Is}) ->
    fmt_func(F,Is).

fmt_func(F,Is) when is_binary(F) ->
    [F|fmt_fargs(Is)];
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


format_meta(Expr) ->
    format_meta_(Expr, ?MAX_PRIO).

format_meta_(I,_P) when is_integer(I) -> integer_to_list(I);
format_meta_(Name,_P) when is_binary(Name) -> Name;
format_meta_({const,V},_P) -> integer_to_list(V);
format_meta_({range,A,B},_P) ->
    if A =:= B -> A;
       true -> [format_meta(A),"..",format_meta(B)]
    end;
format_meta_({call,F,As},_P) when is_binary(F)->
    [F,"(", format_meta_list(As), ")"];
format_meta_({op,Op,A,B},P) ->
    P1 = priority(Op),
    Fa = format_meta_(A,P1),
    Fb = format_meta_(B,P1),
    if P1 > P ->
	    ["(",Fa," ",format_op(Op)," ",Fb,")"];
       true ->
	    [Fa," ",format_op(Op)," ",Fb]
    end;
format_meta_({op,Op,A},P) ->
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

-ifdef(not_used).
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
fmt_index(A) when is_binary(A) ->
    [A];
fmt_index(Set) when is_list(Set) ->
    ["{",fmt_set(Set),"}"];
fmt_index({f,F,Is}) ->
    fmt_func(F,Is).

fmt_func(F,Is) when is_binary(F) ->
    [F|fmt_fargs(Is)];
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

-endif.
