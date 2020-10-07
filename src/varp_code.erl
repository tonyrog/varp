%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2020, Tony Rogvall
%%% @doc
%%%    Code to build clauses
%%% @end
%%% Created :  4 Oct 2020 by Tony Rogvall <tony@rogvall.se>

-module(varp_code).

-compile(export_all).

-define(dbg(F,A), io:format((F),(A))).
%% compile:
%% parse:
formula() ->
    "[A x=1..n][A y=x..n+1] (P(x) -> Q(y))".

parse(Formula) ->
    {ok,{_Opts,Tree}} = varp:parse(Formula),
    Tree.

%% This is the demo parse tree
tree() ->
    {{'ALL',[{assign,{id,"x"}, {range,{const,1},{id,"n"}}}]},
     {{'ALL',[{assign,{id,"y"},{range,{id,"x"},{add,{id,"n"},{const,1}}}}]},
      {imp,{p,'P',[{id,"x"}]},{p,'Q',[{id,"y"}]}}}}.


compile(Tree) ->
    erase(label_counter),
    lists:flatten(compile(Tree,[])).

compile(Tree,E) ->
    case Tree of
	true -> [{const,true}];
	false -> [{const,false}];
	{'p', Sym, Args} -> compile_var(Sym, Args,E);
	{'not', A}       -> compile_unary('cor',A, E);
	{'or', A1, A2}   -> compile_binary('cor',A1,A2,E);
	{'and', A1, A2}  -> compile_binary('cand',A1,A2,E);
	{'imp', A1, A2}  -> compile_binary('cimp',A1,A2,E);
	{'equ', A1, A2}  -> compile_binary('cequ',A1,A2,E);
	{'xor', A1, A2}  -> compile_binary('cxor',A1,A2,E);
	{{'ALL',Gs},A} -> compile_quant('call',Gs,A,E);
	{{'ANY',Gs},A} -> compile_quant('cany',Gs,A,E)
    end.

compile_unary(Op, A,E) ->
    [compile(A,E),Op].

compile_binary(Op,A1,A2,E) ->
    [compile(A1,E),compile(A2,E),Op].

compile_quant(Op,[G|Gs],A,E) ->
    case G of
	{assign,{id,X},R} ->
	    L1 = new_label(),
	    L2 = new_label(),
	    Range = compile_range(R, E),
	    [[Range,'do'],
	     {label,L1},
	     {leave,L2},
	     compile_quant(Op, Gs, A, [X|E]),
	     {loop,L1},
	     {label,L2},
	     Range,swap,'isub',{const,1},'iadd',
	     Op];
	_ ->
	    L1 = new_label(),
	    [compile_expr(G, E),
	     {jumpz,L1},
	     compile_quant(Op, Gs, A, E),
	     {label,L1}]
    end;
compile_quant(_Op,[],A,E) ->
    compile(A, E).

new_label() ->
    L = case get(label_counter) of
	    undefined -> 1;
	    C -> C+1
	end,
    put(label_counter, L),
    {l,L}.

compile_var(Sym,[],_E) ->
    [{args,0},{p,Sym}];
compile_var(Sym,Args,E) ->
    [compile_args(Args,E),{args,length(Args)},{p,Sym}].

compile_args([A|As],E) ->
    [compile_args(As,E),compile_arg(A,E)];
compile_args([A],E) ->
    compile_arg(A,E);
compile_args([],_E) ->
    [].

compile_arg(X,_E) when is_integer(X) ->
    {const,X};
compile_arg(Const={const,_},_E) ->
    Const;
compile_arg({id,V},E) ->
    case index(V, E) of
	false -> {var,V};
	I -> {lvar,I}
    end;
compile_arg({F,[A1,A2]},E) ->
    case F of
	"add" -> compile_binary_args(iadd,A1,A2,E);
	"sub" -> compile_binary_args(isub,A1,A2,E);
	"mul" -> compile_binary_args(imul,A1,A2,E);
	"div" -> compile_binary_args(idiv,A1,A2,E);
	"rem" -> compile_binary_args(irem,A1,A2,E);
	"band" -> compile_binary_args(iband,A1,A2,E);
	"bor" -> compile_binary_args(ibor,A1,A2,E);
	"bxor" -> compile_binary_args(ibxor,A1,A2,E);
	"or" -> compile_binary_args(ior,A1,A2,E);
	"and" -> compile_binary_args(iand,A1,A2,E);
	"shl" -> compile_binary_args(ishl,A1,A2,E);
	"shr" -> compile_binary_args(ishr,A1,A2,E);
	"gt" -> compile_binary_args(igt,A1,A2,E);
	"gte" -> compile_binary_args(igte,A1,A2,E);
	"lt" -> compile_binary_args(ilt,A1,A2,E);
	"lte" -> compile_binary_args(ilte,A1,A2,E);
	"eq" -> compile_binary_args(ieq,A1,A2,E);
	"neq" -> compile_binary_args(ineq,A1,A2,E)
    end;
compile_arg({F,[A1]},E) ->
    case F of
	"not" -> compile_unary_args(inot,A1,E);
	"neg" -> compile_unary_args(ineg,A1,E);
	"pos" -> compile_unary_args(ipos,A1,E);
	"bnot" -> compile_unary_args(ibnot,A1,E)
    end.
	    
compile_unary_args(Op,A,E) ->
    [compile_args(A,E),Op].

compile_binary_args(Op,A1,A2,E) ->
    [compile_args(A1,E),compile_args(A2,E),Op].

compile_range({range,From,To}, E) ->
    [compile_expr(From,E),compile_expr(To,E)];
compile_range(Value, E) ->
    [compile_expr(Value,E),dup].
    

compile_expr({const,X},_E) ->
    [{const,X}];
compile_expr({id,ID},E) ->
    case index(ID, E) of
	false -> [{var,ID}];
	I -> [{lvar,I}]
    end;
compile_expr({range,From,To},E) ->
    [compile_expr(From,E),compile_expr(To,E)];
compile_expr({F,A1,A2},E) when is_atom(F) ->
    case F of
	'add'-> compile_binary_expr(iadd,A1,A2,E);
	'sub' -> compile_binary_expr(isub,A1,A2,E);
	'mul' -> compile_binary_expr(imul,A1,A2,E);
	'div' -> compile_binary_expr(idiv,A1,A2,E);
	'rem' -> compile_binary_expr(irem,A1,A2,E);
	'band' -> compile_binary_expr(iband,A1,A2,E);
	'bor' -> compile_binary_expr(ibor,A1,A2,E);
	'bxor' -> compile_binary_expr(ibxor,A1,A2,E);
	'or' -> compile_binary_expr(ior,A1,A2,E);
	'and' -> compile_binary_expr(iand,A1,A2,E);
	'shl' -> compile_binary_expr(ishl,A1,A2,E);
	'shr' -> compile_binary_expr(ishr,A1,A2,E);
	'gt' -> compile_binary_expr(igt,A1,A2,E);
	'gte' -> compile_binary_expr(igte,A1,A2,E);
	'lt' -> compile_binary_expr(ilt,A1,A2,E);
	'lte' -> compile_binary_expr(ilte,A1,A2,E);
	'eq' -> compile_binary_expr(ieq,A1,A2,E);
	'neq' -> compile_binary_expr(ineq,A1,A2,E)
    end;
compile_expr({F,A}, E) when is_atom(F) ->
    case F of
	'neg' -> compile_unary_expr(inet, A, E);
	'pos' -> compile_unary_expr(ipos, A, E);
	'bnot' -> compile_unary_expr(ibnot, A, E)
    end.

compile_unary_expr(Op,A,E) ->
    [compile_expr(A,E),Op].

compile_binary_expr(Op,A1,A2,E) ->
    [compile_expr(A1,E),compile_expr(A2,E),Op].

index(A, As) ->
    index(A, As, 1).

index(A, [A|_As], I) -> I;
index(A, [_|As], I) -> index(A, As, I+1);
index(_A, [], _) ->  false.

%% compile:
%%
%%    {const,1},{global,"n"},do,
%% {label,l1},
%%      {leave,l3},  ## check loop condition
%%      {lvar,1},{var,"n"},{const,1},iadd,do,
%%   {label,l2},
%%      {leave,l4},  ## check loop condition
%%      %% P(x) -> Q(y)
%%      {lvar,2},{args,1},{p,'Q'},{lvar,1},{args,1},{p,'P'},imp,
%%      {loop,l2}
%%   {label,l4}
%%      {var,"n"},{lvar,1},isub,{const,2},iadd,all,
%%   {loop,l1}
%% {label,l3}
%% {var,"n"}, all,
%% ret,
%%
asm() ->
    [
     {const,1},        %% 1
     {var,"n"},        %% 2
     do,               %% 3
{label,l0},
     {leave,l1},       %% 4 leave L1
     {lvar,1},         %% 5 (x)
     {var,"n"},        %% 6
     {const,1},        %% 7
     iadd,             %% 8
     do,               %% 9
{label,l3},
     {leave,l2},       %% 10 leave L2
     %% P(x) -> Q(y)
     {lvar,2},         %% 14 (x)
     {args,1},         %% 15
     {p,'P'},          %% 16 P(x)
     {lvar,1},         %% 11 (y)
     {args,1},         %% 12
     {p,'Q'},          %% 13 Q(y)
     cimp,             %% 17
     {loop,l3},        %% 18
{label,l2},
     {var,"n"},        %% 19 n
     {lvar,1},         %% 20 x
     isub,             %% 21 n-x
     {const,2},        %% 22 1+1
     iadd,             %% 23 (n-x+1)+1
     call,             %% 24 circuit ALL
     {loop,l0},        %% 25
{label,l1},
     {var,"n"},        %% 26
     call,             %% 27 ALL
     ret               %% 28 (label l3)
    ].

test() ->
    Asm = asm(),
    Code = assemble(Asm),
    Vp = varc:new(#{}),
    case run(Vp, #{ "n" => 3 }, Code) of
	[Var] ->
	    {Var, Vp};
	[] ->
	    io:format("warning stack underflow\n", []),
	    {undefined, Vp};
	[Var|Stack] ->
	    io:format("warning stack not overflow: ~w\n", [Stack]),
	    {Var, Vp}
    end.

%% resolve all labels and replace with absolute position
assemble(Code) ->
    if is_tuple(Code) ->
	    assemble_(tuple_to_list(Code), [], 1, #{});
       is_list(Code) -> 
	    assemble_(Code, [], 1, #{})
    end.

assemble_([{label,L} | Code], Acc, Addr, Ls) ->
    assemble_(Code, Acc, Addr, Ls#{ L => Addr });
assemble_([C | Code], Acc, Addr, Ls) ->
    assemble_(Code, [C|Acc], Addr+1, Ls);
assemble_([], Acc, _Addr, Ls) ->
    resolve_(Acc, [], Ls).

%% resolve goto, leave and loop and reverse again
resolve_([{goto,L} | Code], Acc, Ls) ->
    J = get_addr(L, Ls),
    resolve_(Code, [{goto,J}|Acc], Ls);
resolve_([{leave,L} | Code], Acc, Ls) ->
    J = get_addr(L, Ls),
    resolve_(Code, [{leave,J}|Acc], Ls);
resolve_([{loop,L} | Code], Acc, Ls) ->
    J = get_addr(L, Ls),
    resolve_(Code, [{loop,J}|Acc], Ls);
resolve_([C | Code], Acc, Ls) ->
    resolve_(Code, [C | Acc], Ls);
resolve_([], Acc, _Ls) ->
    list_to_tuple(Acc).

get_addr(L, Ls) ->
    J = maps:get(L, Ls, 0),
    if J =:= 0 -> error({label,L,not_defined});
       true -> J
    end.
    

run(Vp, Code) ->
    run(Vp, #{}, Code).

run(Vp, Vs, Code) ->
    step(Vp, Vs, 1, Code, [], []).

step(_Vp, _Vs, I, Code, Stack, _Loop) when I > tuple_size(Code) ->
    Stack;
step(Vp, Vs, I, Code, Stack, Loop) ->
    Op = element(I,Code),
    io:format("~w: op=~w, stack=~w, loop=~w\n", [I,Op,Stack,Loop]),
    case Op of
	iadd -> step(Vp,Vs,I+1,Code,iadd(Stack),Loop);
	isub -> step(Vp,Vs,I+1,Code,isub(Stack),Loop);
	imul -> step(Vp,Vs,I+1,Code,imul(Stack),Loop);
	idiv -> step(Vp,Vs,I+1,Code,idiv(Stack),Loop);
	irem -> step(Vp,Vs,I+1,Code,irem(Stack),Loop);
	iband -> step(Vp,Vs,I+1,Code,iband(Stack),Loop);
	ibor -> step(Vp,Vs,I+1,Code,ibor(Stack),Loop);
	ibxor -> step(Vp,Vs,I+1,Code,ibxor(Stack),Loop);
	ior -> step(Vp,Vs,I+1,Code,ior(Stack),Loop);
	iand -> step(Vp,Vs,I+1,Code,iand(Stack),Loop);
	ishl -> step(Vp,Vs,I+1,Code,ishl(Stack),Loop);
	ishr -> step(Vp,Vs,I+1,Code,ishr(Stack),Loop);
	igt -> step(Vp,Vs,I+1,Code,igt(Stack),Loop);
	igte -> step(Vp,Vs,I+1,Code,igte(Stack),Loop);
	ilt -> step(Vp,Vs,I+1,Code,ilt(Stack),Loop);
	ilte -> step(Vp,Vs,I+1,Code,ilte(Stack),Loop);
	ieq -> step(Vp,Vs,I+1,Code,ieq(Stack),Loop);
	ineq -> step(Vp,Vs,I+1,Code,ineq(Stack),Loop);
	ineg -> step(Vp,Vs,I+1,Code,ineg(Stack),Loop);
	ipos -> step(Vp,Vs,I+1,Code,Stack,Loop);  %% noop
	ibnot -> step(Vp,Vs,I+1,Code,ibnot(Stack),Loop);
	inot -> step(Vp,Vs,I+1,Code,inot(Stack),Loop);
	{const,V} -> step(Vp,Vs,I+1,Code,[V | Stack],Loop);
	{goto,J} -> step(Vp,Vs,J,Code,Stack,Loop);
	{args,N} -> step(Vp,Vs,I+1,Code,args(Vp,N,Stack),Loop);
	{p,P} -> step(Vp,Vs,I+1,Code,p(Vp,P,Stack),Loop);
	cor -> step(Vp,Vs,I+1,Code,cor(Vp,Stack),Loop);
	cand -> step(Vp,Vs,I+1,Code,cand(Vp,Stack),Loop);
	cimp -> step(Vp,Vs,I+1,Code,cimp(Vp,Stack),Loop);
	cequ -> step(Vp,Vs,I+1,Code,cequ(Vp,Stack),Loop);
	call  -> step(Vp,Vs,I+1,Code,call(Vp,Stack),Loop);
	cany  -> step(Vp,Vs,I+1,Code,cany(Vp,Stack),Loop);
	clause -> step(Vp,Vs,I+1,Code,clause(Vp,Stack),Loop);
	{lvar,K} ->
	    {X,_} = lists:nth(K,Loop),
	    step(Vp,Vs,I+1,Code,[X|Stack],Loop);
	{var,Var} ->
	    X = maps:get(Var,Vs,0),
	    step(Vp,Vs,I+1,Code,[X|Stack],Loop);
	dup ->
	    [X|_] = Stack,
	    step(Vp,Vs,I+1,Code,[X|Stack],Loop);
	swap ->
	    [X,Y|Stack1] = Stack,
	    step(Vp,Vs,I+1,Code,[Y,X|Stack1],Loop);
	drop ->
	    [_|Stack1] = Stack,
	    step(Vp,Vs,I+1,Code,Stack1,Loop);
	print ->
	    io:format("~w\n", [hd(Stack)]),
	    step(Vp,Vs,I+1,Code,tl(Stack),Loop);
	do -> 
	    [Limit,Index|Stack1] = Stack,
	    io:format("DO from ~w to ~w\n", [Index, Limit]),
	    step(Vp,Vs,I+1,Code,Stack1,[{Index,Limit}|Loop]);
	{leave,J} ->
	    [{Index,Limit}|Loop0] = Loop,
	    if Index > Limit ->
		    step(Vp,Vs,J,Code,Stack,Loop0);
	       true ->
		    step(Vp,Vs,I+1,Code,Stack,Loop)
	    end;
	{loop,J} -> 
	    [{Index,Limit}|Loop1] = Loop,
	    step(Vp,Vs,J,Code,Stack,[{Index+1,Limit}|Loop1]);
	ret ->
	    Stack;
	ok -> ok
    end.

iadd([V1,V2|Vs]) -> [V2+V1|Vs].
isub([V1,V2|Vs]) -> [V2-V1|Vs].
imul([V1,V2|Vs]) -> [V2*V1|Vs].
idiv([V1,V2|Vs]) -> [V2 div V1|Vs].
irem([V1,V2|Vs]) -> [V2 rem V1|Vs].
iband([V1,V2|Vs]) -> [V2 band V1|Vs].
ibor([V1,V2|Vs]) -> [V2 bor V1|Vs].
ibxor([V1,V2|Vs]) -> [V2 bxor V1|Vs].
ior([V1,V2|Vs]) -> 
    if V1 =:= 0, V2 =:= 0 -> [0 | Vs];
       true -> [1|Vs]
    end.
iand([V1,V2|Vs]) -> 
    if V1 =/= 0, V2 =/= 0 -> [1 | Vs];
       true -> [0|Vs]
    end.
ishl([V1,V2|Vs]) -> [V2 bsl V1 | Vs].
ishr([V1,V2|Vs]) -> [V2 bsr V1 | Vs].
igt([V1,V2|Vs]) -> [if V2 > V1 -> 1; true -> 0 end | Vs].
igte([V1,V2|Vs]) -> [if V2 >= V1 -> 1; true -> 0 end | Vs].
ilt([V1,V2|Vs]) -> [if V2 < V1 -> 1; true -> 0 end | Vs].
ilte([V1,V2|Vs]) -> [if V2 =< V1 -> 1; true -> 0 end | Vs].
ieq([V1,V2|Vs]) -> [if V2 =:= V1 -> 1; true -> 0 end | Vs].
ineq([V1,V2|Vs]) -> [if V2 =/= V1 -> 1; true -> 0 end | Vs].
ineg([V1|Vs]) -> [-V1 | Vs].
ibnot([V1|Vs]) -> [bnot V1 | Vs].
inot([V1|Vs]) -> [if V1 =:= 0 -> 1; true -> 1 end | Vs].

p(Vp,P,[Args|Stack]) ->
    Term = {P,Args},
    case varc:find_symbol(Vp, Term) of
	false ->
	    Var = varc:add_variable(Vp, true),
	    io:format("new ~w = ~w\n", [Term, Var]),
	    varc:isused(Vp, Var, true),  %% mark as in use!
	    varc:add_symbol(Vp, Var, Term),
	    [Var|Stack];
	Var when is_integer(Var) ->
	    io:format("~w = ~w\n", [Term, Var]),
	    [Var|Stack]
    end.

sym(Vp,Lit) ->
    case varc:get_symbol(Vp, Lit) of
	[{Term,_}|_] -> Term;
	_ -> Lit
    end.
	    
args(_Vp,N,Stack) ->
    {Args,Stack1} = lists:split(N, Stack),
    [Args | Stack1].

cor(Vp, [X1,X2|Vs]) ->
    ?dbg("~w or ~w\n", [sym(Vp,X2),sym(Vp,X1)]),
    X = varp_circuit:or_gate(Vp, X2, X1),
    [X | Vs].

cand(Vp, [X1,X2|Vs]) ->
    ?dbg("~w and ~w\n", [sym(Vp,X2),sym(Vp,X1)]),
    X = varp_circuit:and_gate(Vp, X2, X1),
    [X | Vs].

cimp(Vp, [X1,X2|Vs]) ->
    ?dbg("~w -> ~w\n", [sym(Vp,X2),sym(Vp,X1)]),
    X = varp_circuit:imp_gate(Vp, X2, X1),
    [X | Vs].

cequ(Vp, [X1,X2|Vs]) ->
    ?dbg("~w <-> ~w\n", [sym(Vp,X2),sym(Vp,X1)]),
    X = varp_circuit:equ_gate(Vp, X2, X1),
    [X | Vs].

cinv(Vp, [X1 | Vs]) ->
    ?dbg("!~w\n", [sym(Vp,X1)]),
    X = varp_circuit:inv_pin(Vp, X1),
    [X | Vs].

clause(Vp, [N|Stack]) ->
    {Args,Stack1} = lists:split(N, Stack),
    varc:add_clause(Vp, Args),
    Stack1.

%% ciruit-all not call
call(Vp, [N|Stack]) ->
    {Args,Stack1} = lists:split(N, Stack),
    ?dbg("ALL ~w\n", [[sym(Vp,Xi) || Xi <- Args]]),
    X = varp_circuit:all(Vp, Args),
    [X | Stack1].

cany(Vp, [N|Stack]) ->
    {Args,Stack1} = lists:split(N, Stack),
    ?dbg("ANY ~w\n", [[sym(Vp,Xi) || Xi <- Args]]),
    X = varp_circuit:any(Vp, Args),
    [X | Stack1].
