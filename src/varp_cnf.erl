%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2010, Tony Rogvall
%%% @doc
%%%   Rewrite formulas into CNF format
%%% @end
%%% Created : 20 Aug 2010 by Tony Rogvall <tony@rogvall.se>

-module(varp_cnf).
-export([rewrite/1]).
-export([clauses/1]).
-export([normalize_clause/1,normalize_clause/2]).
-export([normalize_clauses/1,normalize_clauses/2]).
-export([format/1]).

-compile(export_all).

%%
%% Formula to CNF form
%% return {Clauses, Literals}
%%
clauses(A) ->
    %% io:format("A=~p\n", [A]),
    A1 = rewrite(A),
    %% io:format("A1=~p\n", [A1]),
    Cs1 = clause_form(A1),
    %% io:format("Cs1=~p\n", [Cs1]),
    {Cs2,Ls1} = normalize_clauses(Cs1),
    %% io:format("Cs2=~p, Ls1=~p\n", [Cs2,Ls1]),
    {Cs3,Ls2} = subsume_clauses(Cs2),
    %% io:format("Cs3=~p,Ls2=~p\n", [Cs3,Ls2]),
    {Cs3,Ls1++Ls2}.

%%
%% Normalize all clauses
%%
normalize_clauses(Cs) ->
    normalize_clauses(Cs,[]).

normalize_clauses(Cs,Ls) ->
    normalize_clauses_(Cs,Ls,[],[]).

normalize_clauses_([C|Cs],Ls,Acc,Ls1) ->
    case normalize_clause(C,Ls) of
	[] ->
	    normalize_clauses_(Cs,Ls,Acc,Ls1);
	[L] ->
	    normalize_clauses_(Cs,Ls,Acc,[L|Ls1]);
	D  -> 
	    normalize_clauses_(Cs,Ls,[D|Acc],Ls1)
    end;
normalize_clauses_([],Ls,Acc,[]) ->
    {Acc,Ls};
normalize_clauses_([],Ls,Acc,Ls1) -> %% one more round
    normalize_clauses_(Acc,Ls1++Ls,[],[]).

%% Normalize a clause.
%%  Rule (after usort, where multiple literals are removed)
%%      ~A ... A => []
%%      A true B => []
%%      A false B => A B
%%
normalize_clause(CL) ->
    normalize_clause(CL,[]).
normalize_clause(CL,Ls) ->
    normalize_clause_(lists:usort(CL),[],Ls).

%% fixme: handle true,false and removed literals !
normalize_clause_([false|As],CL,Ls) -> normalize_clause_(As,CL,Ls);
normalize_clause_([true|_],_CL,_Ls) -> [];
normalize_clause_([L={'not',A}|As],CL,Ls) ->
    case lists:member(A,Ls) of
	true -> 
	    normalize_clause_(As,CL,Ls);  %% !A=false
	false ->
	    case lists:member(L,Ls) of
		true -> [];  %% !A=true
		false -> 
		    normalize_clause_(As,[L|CL],Ls)
	    end
    end;
normalize_clause_([A|As],CL,Ls) ->
    case lists:member(A,Ls) of
	true ->
	    [];  %% A=true
	false ->
	    L = {'not',A},
	    case lists:member(L,Ls) of
		true -> normalize_clause_(As,CL,Ls);  %% !A=false
		false -> 
		    normalize_clause_(As,[A|CL],Ls)
	    end
    end;
normalize_clause_([],CL,_Ls) ->
    CL.

%%
%% Remove sub clauses, return clauses and a lists of
%% removed literals
%%
subsume_clauses(Cs) ->
    CsL = lists:map(fun(C) -> {length(C), C} end, Cs),
    CsL1 = lists:keysort(1, CsL),
    {DLs,Ls} = subsume_clauses_(CsL1,[],[]),
    {lists:map(fun({_,C}) -> C end, DLs), Ls}.
		  
subsume_clauses_([CL|CLs],DLs,Ls) ->
    CLs1 = subsume_clause_(CL,CLs),
    subsume_clauses_(CLs1,[CL|DLs],Ls);
subsume_clauses_([],DLs,Ls) ->
    {DLs,Ls}.

%% remove clauses DL that are subsumed by CL
subsume_clause_(CL={_N,C},[DL={_M,D}|CLs]) ->
    case C -- D of
	[] -> subsume_clause_(CL, CLs);
	_ -> [DL | subsume_clause_(CL, CLs)]
    end;
subsume_clause_(_CL, []) ->
    [].

clause_form({'and',A,B}) ->
    clause_form(A) ++ clause_form(B);
clause_form({'or',A,B}) ->
    As = clause_form(A),
    lists:flatmap(fun(Bd) ->
			  lists:map(fun(Ad) -> Ad++Bd end, As)
		  end, clause_form(B));
clause_form({'not',V}) ->
    [[{'not',V}]];
clause_form(V) ->
    [[V]].

%%
%% rewrite into and-or form, also move negation to the literals
%%
rewrite(true)  -> true;
rewrite(1)     -> true;
rewrite(false) -> false;
rewrite(0)     -> false;
rewrite(A={p,_P,_Vs}) -> A;
rewrite(A={'not',{p,_P,_Vs}}) -> A;
rewrite({'not', {'not', A}}) -> rewrite(A);
rewrite({'not', {'and', A, B}}) -> r('or',{'not',A},{'not',B});
rewrite({'not', {'or', A, B}})  -> r('and', {'not',A},{'not',B});
rewrite({'not', F}) -> rewrite(r('not',F));
rewrite({'!', F})  -> rewrite(r('not',F));
rewrite({'and', A, B}) -> r('and', A, B);
rewrite({'&&', A, B}) ->  r('and', A, B);
rewrite({'&', A, B}) ->  r('and', A, B);
rewrite({'or', A, B}) ->  r('or', A, B);
rewrite({'||', A, B}) ->  r('or', A, B);
rewrite({'|', A, B}) ->  r('or', A, B);
rewrite({'imp',A,B}) ->   r('or', {'not', A}, B);
rewrite({'->',A,B}) ->    r('or', {'not', A}, B);
rewrite({'<->',A,B}) ->   rewrite({'equ',A,B});
rewrite({'equ',A,B}) ->
    A1 = rewrite(A), B1 = rewrite(B),
    {'and',
     {'or', rewrite({'not', A1}), B1},
     {'or', rewrite({'not', B1}), A1}};
rewrite({'xor',A,B})    -> rewrite({'not',{'equ',A,B}});

rewrite({'all',Fs})  -> fold('and',true,[rewrite(F) || F <- Fs]);
rewrite({'any',Fs})  -> fold('or',false,[rewrite(F) || F <- Fs]);
rewrite({'none',Fs}) -> fold('and',true,[rewrite({'not',F}) || F <- Fs]);
rewrite({'one',[]})  -> false;
rewrite({'one',[F]}) -> rewrite(F);
rewrite({'one',Fs})  ->
    rewrite({'and', {all, [{'not',{'and',A,B}} || {A,B} <- pairs(Fs)]},
	     {any, Fs}}).

r(Op,A,B) -> {Op,rewrite(A),rewrite(B)}.
r(Op,A)   -> {Op,rewrite(A)}.


fold(_Op,Init,[]) -> Init;
fold(_Op,_Init,[A]) -> A;
fold(Op,Init,[A|As]) -> {Op,A,fold(Op,Init,As)}.

pairs([]) -> [];
pairs([_]) -> [];
pairs([A|As]) -> [{A,Ai} || Ai <- As] ++ pairs(As).

prod(N,File) ->
    {CLs,Ls,Decls} = prod(N),
    file:write_file(File, format(Decls,CLs ++ [[L]||L<-Ls])).

prod(N) when is_integer(N), N>1 ->
    put(next_var, 2), %% FIXME!
    Nv = integer_bits(N),
    L  = (length(Nv)+1) div 2,
    Is = lists:seq(0,L-1),
    X  = [{bit_index,{p,'X',[]},I}||I<-Is],
    Y  = [{bit_index,{p,'Y',[]},I}||I<-Is],
    Decls = [{{p,'X',[]},uint,L},{{p,'Y',[]},uint,L}],
    {Prod,Cs} = multiply(X, Y, []),
    %% Prod=Nv
    Cs1 = assign(Prod,Nv,Cs),
    %% X>1
    Cs2 = gt_1(X,Cs1),
    %% Y>1
    Cs3 = gt_1(Y,Cs2),
    {Cs3,[],Decls}.
    %%
    %% {Cs4,Ls1} = normalize_clauses(Cs3),
    %% {Cs4,Ls1}.
    %% {Cs5,Ls2} = subsume_clauses(Cs4),
    %% {Cs5,Ls1++Ls2,Decls}.

sum(N,File) ->
    {CLs,Ls,Decls} = sum(N),
    file:write_file(File, format(Decls,CLs ++ [[L]||L<-Ls])).

sum(N) when is_integer(N), N>1 ->
    put(next_var, 2), %% FIXME!
    Nv = integer_bits(N),
    L  = length(Nv),
    Is = lists:seq(0,L-1),
    X  = [{bit_index,{p,'X',[]},I}||I<-Is],
    Y  = [{bit_index,{p,'Y',[]},I}||I<-Is],
    Decls = [{{p,'X',[]},uint,L},{{p,'Y',[]},uint,L}],
    {Cout,Sum,Cs} = add(X, Y, []),
    %% Prod=Nv
    Cs1 = assign(Sum++[Cout],Nv,Cs),
    %% X>0
    Cs2 = gt_0(X,Cs1),
    %% Y>0
    Cs3 = gt_0(Y,Cs2),
    {Cs3,[],Decls}.
    %%
    %% {Cs4,Ls1} = normalize_clauses(Cs3),
    %% {Cs4,Ls1}.
    %% {Cs5,Ls2} = subsume_clauses(Cs4),
    %% {Cs5,Ls1++Ls2,Decls}.

integer_bits(N) ->
    [element((I-$0)+1,{false,true})||I<-lists:reverse(integer_to_list(N,2))].

assign([Z|Zs], [true|Vs], Cs) ->
    assign(Zs,Vs,[[Z]|Cs]);
assign([Z|Zs], [false|Vs], Cs) ->
    assign(Zs,Vs,[[{'not',Z}]|Cs]);
assign([Z|Zs],[],Cs) ->
    assign(Zs,[],[[{'not',Z}]|Cs]);
assign([],[],Cs) ->
    Cs.

gt_0(Xs,Cs) ->    
    [Xs|Cs].

gt_1([_|Xs],Cs) ->    
    [Xs | Cs].

multiply(X, Y, Cs) ->
    {X1,Y1} = extend(X,Y),
    multiply_(Y1,X1,lists:duplicate(length(X1),false),[],Cs).

multiply_([Yi|Ys],X,Prev,Out,Cs) ->
    {M, Cs1} = mult_by_bit(X,Yi,Cs),
    {Cout,[S1|Sum],Cs2} = add(M,Prev,Cs1),
    Prev1 = Sum++[Cout],
    Out1 = Out++[S1],
    multiply_(Ys,X,Prev1,Out1,Cs2);
multiply_([],_X,Prev,Out,Cs) ->
    {Out ++ Prev, Cs}.

mult_by_bit([A|X], B, Cs) ->
    {And,Cs1} = cand(A,B,Cs),
    {As,Cs2} = mult_by_bit(X, B, Cs1),
    {[And|As], Cs2};
mult_by_bit([], _B, Cs) ->
    {[false], Cs}.

%% simple sequential adder
add(X,Y,Cs) ->
    Cout = create_var(),
    add(X,Y,Cout,Cs).

add(X,Y,Cout,Cs) ->
    {X1,Y1} = extend(X,Y),
    add_(lists:zip(X1,Y1),false,Cout,[],Cs).

add_([{Ai,Bi}],Cin,Cout,Sum,Cs) ->
    S = create_var(),
    {Cout,lists:reverse([S|Sum]),full_adder(Ai,Bi,Cin,S,Cout,Cs)};
add_([{Ai,Bi}|Inputs],Cin,Cout,Sum,Cs) ->
    S = create_var(),
    Cout1 = create_var(),
    Cs1 = full_adder(Ai,Bi,Cin,S,Cout1,Cs),
    add_(Inputs,Cout1,Cout,[S|Sum],Cs1);
add_([],_Cin,Cout,Sum,Cs) ->
    {Cout,lists:reverse(Sum),Cs}.

cand(A,B,Cs) ->
    cand(A,B,create_var(),Cs).
cand(A,B,Out,Cs) ->
    {Out,[[neg(A),neg(B),Out],[A,neg(Out)],[B,neg(Out)] | Cs]}.

%% full adder in CNF form
%% input A, B, and carry in Cin
%% output S sum, and carry out Cout
%% Cs are list of clauses
%%
full_adder(A,B,Cin,S,Cout,Cs) ->
    [[neg(A), neg(B), neg(Cin), S],
     [neg(A), neg(B), Cout],
     [neg(A), neg(Cin), Cout],
     [neg(A), Cout, S],
     [A, B, Cin, neg(S)],
     [A, B, neg(Cout)],
     [A, Cin, neg(Cout)],
     [A, neg(Cout), neg(S)],
     [neg(B), neg(Cin), Cout],
     [neg(B), Cout, S],
     [B, Cin, neg(Cout)],
     [B, neg(Cout), neg(S)],
     [neg(Cin), Cout, S],
     [Cin, neg(Cout), neg(S)] | Cs].

create_var() ->
    case get(next_var) of
	undefined -> put(next_var,3), 2;
	V -> put(next_var,V+1), V
    end.

neg(true) -> false;
neg(false) -> true;
neg({'not',X}) -> X;
neg(X) -> {'not',X}.

%% make bool vector X and Y the same size
extend(X,Y) ->
    Lx = length(X),
    Ly = length(Y),
    if Lx < Ly -> {X++lists:duplicate(Ly-Lx,false),Y};
       Lx > Ly -> {X,Y++lists:duplicate(Lx-Ly,false)};
       true -> {X,Y}
    end.

format(CLs) ->
    format([],CLs).

format(Decls,CLs) ->
    NClauses = length(CLs),
    Vars = snf_vars(CLs),
    NVars = length(Vars),
    [["c auto generated from <file>\n"],
     ["p snf ", integer_to_list(NVars), " ", integer_to_list(NClauses), "\n"],
     [[format_decl(D)] || D <- Decls],
     [[format_clause(C)," .","\n"] || C <- CLs],
     ["%\n"],
     [".\n"]].

snf_vars(CLs) -> snf_vars(CLs,sets:new()).
snf_vars([C|CLs],VSet) ->
    VSet1 = lists:foldl(
	      fun({'not',V}, Si) -> add_var(V,Si);
		 (V,Si) -> add_var(V,Si)
	      end, VSet, C),
    snf_vars(CLs, VSet1);
snf_vars([],VSet) ->
    sets:to_list(VSet).

add_var(true,VSet) -> VSet;
add_var(false,VSet) -> VSet;
add_var(V,VSet) -> sets:add_element(V,VSet).

format_decl({Name,int,Sz}) ->
    ["c declare ", format_symbol(Name),":",integer_to_list(Sz),"/signed","\n"];
format_decl({Name,uint,Sz}) ->
    ["c declare ",format_symbol(Name),":",integer_to_list(Sz),"/unsigned","\n"];
format_decl(_) -> [].

format_clause(C) ->
    concat([format_literal(L) || L <- C], " ").

format_literal({'not',V}) -> ["!",format_symbol(V)];
format_literal(V) ->  format_symbol(V).

format_symbol(true) -> "true";
format_symbol(false) -> "false";
format_symbol(V) when is_atom(V) -> atom_to_list(V);
format_symbol(I) when is_integer(I) -> [$T|integer_to_list(I)];
format_symbol({bit_index,V,I}) ->
    atom_to_list(V)++"["++integer_to_list(I)++"]";
format_symbol({p,V,[]}) -> atom_to_list(V);
format_symbol({p,V,As}) ->
    [atom_to_list(V),"(", concat([io_lib:format("~w",[X])||X<-As], ","), ")"].

concat([], _) -> [];
concat([H],_) -> [H];
concat([H|T],S) -> [H,S | concat(T,S)].

