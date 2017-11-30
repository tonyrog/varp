%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2010, Tony Rogvall
%%% @doc
%%%   Rewrite formulas into CNF format
%%% @end
%%% Created : 20 Aug 2010 by Tony Rogvall <tony@rogvall.se>

-module(varp_cnf).
-export([rewrite/1]).
-export([clauses/1]).
-export([succ_dimacs/2, succ/2]).
-export([normalize_clause/1, normalize_clauses/1]).
-export([format/1]).

-compile(export_all).

-import(lists, [reverse/1, map/2, foldl/3, member/2]).

%%
%%
%%
satisfy(F0) ->
    F = varp_expand:formula(F0),
    Vs = lists:sort(varp_expand:variables(F)),
    {A, _Ls} = clauses(F),
    %% io:format("literals=~w\n",[_Ls]),
    Af = {all, map(fun(Cp) -> {any,Cp} end, A)},
    case varp:satisfy({'and',{none,Vs}, Af}) of
	false ->
	    {A1,_Ls1} = normalize_clauses(succ_clauses(A,Vs)),
	    %% io:format("literals1=~w\n",[_Ls1]),
	    Af1 = {all, map(fun(Cp) -> {any,Cp} end, A1)},
	    case varp:prove({'imp',Af,Af1}) of
		true -> false;
		{false,{N,Ms}} -> {true,{N,Ms}}
	    end;
	{true,{N1,Ms1}} -> {true,{N1,Ms1}}
    end.
	    
test_succ(C,Vs) ->
    Cs = {all, map(fun(Cp) -> {any,Cp} end, succ(C,Vs))},
    varp:prove({'imp', {any,C}, Cs}).

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
    Cs2 = normalize_clauses(Cs1),
    %% io:format("Cs2=~p\n", [Cs2]),
    Cs3 = subsume_clauses(Cs2),
    %% io:format("Cs3=~p\n", [Cs3]),
    Cs3.

%%
%% Normalize all clauses
%%
normalize_clauses(Cs) ->
    normalize_clauses_(Cs,[]).

normalize_clauses_([C|Cs],Acc) ->
    case normalize_clause(C) of
	[] -> normalize_clauses_(Cs,Acc);
	D  -> normalize_clauses_(Cs,[D|Acc])
    end;
normalize_clauses_([],Acc) ->
    Acc.

%% Normalize a clause.
%%  Rule (after usort, where multiple literals are removed)
%%      ~A ... A => []
%%      A true B => []
%%      A false B => A B
%%
normalize_clause(CL) ->
    normalize_clause_(lists:usort(CL),[]).

%% fixme: handle true,false and removed literals !
normalize_clause_([false|As],CL) ->   normalize_clause_(As,CL);
normalize_clause_([true|_],_CL)  ->   [];
normalize_clause_([L={'not',_}|As], CL) -> normalize_clause_(As, [L|CL]);
normalize_clause_([A|As], CL) ->
    NA = {'not',A},
    case lists:member(NA, As) orelse lists:member(NA,CL) of
	false -> normalize_clause_(As, [A|CL]);
	true -> []
    end;
normalize_clause_([], CL) -> %% only potive literals should remain
    CL.

%%
%% Remove sub clauses, return clauses and a lists of
%% removed literals
%%
subsume_clauses(Cs) ->
    CsL = map(fun(C) -> {length(C), C} end, Cs),
    CsL1 = lists:keysort(1, CsL),
    {DLs,Ls} = subsume_clauses_(CsL1,[],[]),
    {map(fun({_,C}) -> C end, DLs), Ls}.
		  

subsume_clauses_([CL|CLs],DLs,Ls) ->
    CLs1 = subsume_clause_(CL,CLs),
%%    case CL of
%%	{1,[L]} -> subsume_clauses_(CLs1,DLs,[L|Ls]);
%%	_ -> subsume_clauses_(CLs1,[CL|DLs],Ls)
%%    end;
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
			  map(fun(Ad) -> Ad++Bd end, As)
		  end, clause_form(B));
clause_form({'not',V}) ->
    [[{'not',V}]];
clause_form(V) ->
    [[V]].

%%
%% rewrite into and-or form, also move negation to the literals
%%
rewrite(true) -> true;
rewrite(1) -> true;
rewrite(false) -> false;
rewrite(0) -> false;
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

fold(_Op,Init,[]) -> Init;
fold(_Op,_Init,[A]) -> A;
fold(Op,Init,[A|As]) -> {Op,A,fold(Op,Init,As)}.

r(Op,A,B) -> {Op,rewrite(A),rewrite(B)}.
r(Op,A) -> {Op,rewrite(A)}.

pairs([]) -> [];
pairs([_]) -> [];
pairs([A|As]) -> [{A,Ai} || Ai <- As] ++ pairs(As).

%%
%% Fixme: should probably output in a kind of
%% dimacs format, but with symbols
%%

format(CLs) ->
    NClauses = length(CLs),
    NVars = length(lists:usort(lists:map(fun({'not',V}) -> V; (V) -> V end, lists:flatten(CLs)))),
    [["c auto generated from <file>\n"],
     ["p snf ", integer_to_list(NVars), " ", integer_to_list(NClauses), "\n"],
     [[format_clause(C)," .","\n"] || C <- CLs],
     ["%\n"],
     [".\n"]].

format_clause(C) ->
    concat([format_literal(L) || L <- C], " ").

format_literal({'not',V}) -> ["!",format_symbol(V)];
format_literal(V) ->  format_symbol(V).

format_symbol(true) -> "true";
format_symbol(false) -> "false";
format_symbol({p,V,[]}) -> atom_to_list(V);
format_symbol({p,V,As}) ->
    [atom_to_list(V),"(", concat([io_lib:format("~w",[X])||X<-As], ","), ")"].

concat([], _) -> [];
concat([H],_) -> [H];
concat([H|T],S) -> [H,S | concat(T,S)].

%%
%% triple to CNF clauses
%% X : Y -> Z
%%   [Z,~X,~Y]
%%   [X,~Z],
%%   [X,Y]
%%
triple(imp, X, Y, Z) ->
    [[Z,-X,-Y], [X,-Z], [X,Y]];
%%
%% X : Y <-> Z
%%   [X,~Y,~Z]
%%   [X,Y,Z]
%%   [Y,~X,~Z]
%%   [Z,~X,~Z]
%%
triple(equ, X, Y, Z) ->
    [[X,-Y,-Z],[X,Y,Z],[Y,-X,-Z],[Z,-X,-Z]].

%%
%% Generate clauses for some arithmetic operations
%%

%% generate integer as boolean variable vector
bits(X, N, V) ->
    map(fun(I) ->
		Vi = {var,{X,I}},
		if V band (1 bsl I) =:= 0 -> 
			{'not',Vi};
		   true -> 
			Vi
		end 
	end,
	lists:seq(0,N-1)).

%% multiplier 2*N  bit input M bit output
mult(N, M) ->
    {any,
     [{all,bits(x,M,Y*Z)++bits(y,N,Y)++bits(z,N,Z)} ||
	 Y <- lists:seq(0,(1 bsl N)-1),
	 Z <- lists:seq(0,(1 bsl N)-1)]}.

%%
%% Successor clauses generation
%% 

%% Vn is number of variables in the overall formula
%% C is on form [I, -I]   (I = 1..Vn)
%% DIMACS literals are translated into 2...N+1
%%
succ_dimacs(C, Vn) ->
    Cover = map(fun(I) when I < 0 -> {-I-1,1};
		   (I) -> {I-1,0}
		end, C),
    map(fun(Cp) ->
		map(fun({I,0}) -> I+1;
		       ({I,1}) -> -(I+1)
		    end, Cp)
	end, succ_(Cover,Vn)).

succ_clauses(Cs,Vs) ->
    succ_clauses(Cs,Vs,[]).

succ_clauses([C|Cs],Vs,As) ->
    As1 = succ(C,Vs,As),
    succ_clauses(Cs,Vs,As1);
succ_clauses([],_Vs,As1) ->
    As1.


%% Vs is the variable ordering table [P0,P1,P2,....]
%% C is on form [ v, {'not', w} ]
succ(C,Vs) ->
    succ(C,Vs,[]).

succ(C,Vs,As) ->
    Vn = length(Vs),
    Cover = map(fun({'not',V}) -> {index(V, Vs),1};
		   (V) -> {index(V,Vs),0}
		end, C),
    foldl(fun(Cp,As1) ->
		  [map(fun({I,0}) -> lists:nth(I+1,Vs);
		       ({I,1}) -> {'not',lists:nth(I+1,Vs)}
		       end, Cp) | As1]
	  end,As,succ_(Cover,Vn)).

succ_(Cover,Vn) ->
    case lists:keysort(1, Cover) of
	[{I,0}|Is] ->
	    %% least significant variable occur positive!
	    Prefix = map(fun(J) -> {J,0} end, lists:seq(0,I-1)),
	    Succ = Prefix ++ [{I,1}|Is],
	    [Succ];
	[{I,1}|Is] ->
	    Prefix = map(fun(J) -> {J,0} end, lists:seq(0,I)),
	    succ1_(I+1,Vn,Prefix,Is,[])
    end.

succ1_(I,Vn,Prefix,Is=[{J,_}|_],Cs) when I < J ->
    Prefix1 = Prefix ++ [{I,0}],
    Succ = Prefix++[{I,1}]++Is,
    succ1_(I+1,Vn,Prefix1,Is,[Succ | Cs]);
succ1_(I,Vn,Prefix,Is0=[{I,1}|Is],Cs) ->
    Prefix1 = Prefix ++ [{I,0}],
    Succ = Prefix++Is0,
    succ1_(I+1,Vn,Prefix1,Is,[Succ | Cs]);
succ1_(I,_Vn,Prefix,[{I,0}|Is],Cs) ->
    Succ = Prefix++[{I,1}]++Is,
    [Succ | Cs];
succ1_(I,Vn,Prefix,[],Cs) when I < Vn ->
    Prefix1 = Prefix ++ [{I,0}],
    Succ = Prefix++[{I,1}],
    succ1_(I+1,Vn,Prefix1,[],[Succ | Cs]);
succ1_(Vn,Vn,Prefix,[],Cs) ->
    Succ = Prefix,
    [Succ | Cs].

%% find index of variable V in Vs (0...N-1)
index(V, Vs) ->    
    index(V, 0, Vs).

index(V, I, [V|_]) -> I;
index(V, I, [_|Vs]) -> index(V,I+1,Vs).


    








