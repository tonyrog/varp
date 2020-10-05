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

%% tree:
tree() ->
    {{'ALL',[{assign,{id,"x"}, {range,{const,1},{id,"n"}}}]},
     {{'ALL',[{assign,{id,"y"},{range,{id,"x"},{add,{id,"n"},{const,1}}}}]},
      {imp,{p,'P',[{id,"x"}]},{p,'Q',[{id,"y"}]}}}}.

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
code() ->
    {
     {const,1},        %% 1
     {var,"n"},        %% 2
     do,               %% 3
%% L0
     {leave,26},       %% 4 leave L1
     {lvar,1},         %% 5 (x)
     {var,"n"},        %% 6
     {const,1},        %% 7
     iadd,             %% 8
     do,               %% 9
%% L3	    
     {leave,19},       %% 10 leave L2
     %% P(x) -> Q(y)
     {lvar,1},         %% 14 (y)
     {args,1},         %% 15
     {p,'P'},          %% 16
     {lvar,2},         %% 11 (x)
     {args,1},         %% 12
     {p,'Q'},          %% 13
     cimp,             %% 17
     {loop,10},        %% 18 loop L3
%% L2
     {var,"n"},        %% 19 n
     {lvar,1},         %% 20 x
     isub,             %% 21 n-x
     {const,2},        %% 22 1+1
     iadd,             %% 23 (n-x+1)+1
     all,              %% 24 ALL
     {loop,4},         %% 25 loop L0
%% L1
     {var,"n"},        %% 26
     all,              %% 27
     ret               %% 28 (label l3)
    }.

test() ->
    Code = code(),
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
