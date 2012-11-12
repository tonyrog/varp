%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2010, Tony Rogvall
%%% @doc
%%%   Rewrite formulas into CNF format
%%% @end
%%% Created : 20 Aug 2010 by Tony Rogvall <tony@rogvall.se>

-module(cnf).
-export([rewrite/1]).
-export([clauses/1]).
-export([succ_dimacs/2, succ/2]).
-export([normalize_clause/1, normalize_clauses/1]).
-export([vars/1]).

-compile(export_all).

-import(lists, [reverse/1, map/2, foldl/3, member/2]).

%%
%%
%%
satisfy(F) ->
    Vs = lists:sort(vars(F)),
    {A, Ls} = clauses(F),
    io:format("literals=~w\n",[Ls]),
    Af = {all, map(fun(Cp) -> {any,Cp} end, A)},
    case varp:satisfy({'and',{none,Vs}, Af}) of
	false ->
	    {A1,Ls1} = normalize_clauses(succ_clauses(A,Vs)),
	    io:format("literals1=~w\n",[Ls1]),
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
    A1 = rewrite(A),
    Cs1 = clause_form(A1),
    Cs2 = normalize_clauses(Cs1),
    normalize_sub_clauses(Cs2).

%%
%% Normalize all clauses
%%
normalize_clauses([C|Cs]) ->
    case normalize_clause(C) of
	[] -> normalize_clauses(Cs);
	D -> [D | normalize_clauses(Cs)]
    end;
normalize_clauses([]) ->
    [].

%%
%% Remove sub clauses
%%
normalize_sub_clauses(Cs) ->
    CsL = map(fun(C) -> {length(C), C} end, Cs),
    CsL1 = lists:keysort(1, CsL),
    {DLs,Ls} = normalize_sub_clauses_(CsL1,[],[]),
    {map(fun({_,C}) -> C end, DLs), Ls}.
		  

normalize_sub_clauses_([CL|CLs],DLs,Ls) ->
    CLs1 = normalize_sub_clause_(CL,CLs),
    case CL of
	{1,[L]} -> normalize_sub_clauses_(CLs1,DLs,[L|Ls]);
	_ -> normalize_sub_clauses_(CLs1,[CL|DLs],Ls)
    end;
normalize_sub_clauses_([],DLs,Ls) ->
    {DLs,Ls}.

normalize_sub_clause_(CL={N,_},[DL={N,_}|CLs]) ->
    [DL | normalize_sub_clause_(CL, CLs)];
normalize_sub_clause_(CL={_N,C},[DL={_M,D}|CLs]) ->
    case C -- D of
	[] -> normalize_sub_clause_(CL, CLs);
	_ -> [DL | normalize_sub_clause_(CL, CLs)]
    end;
normalize_sub_clause_(_CL, []) ->
    [].
    

%% Normalize a clause.
%%  Rule (after usort, where multiple literals are removed)
%%      ~A ... A => []
%%      A true B => A B
%%      A false B => []
%%
normalize_clause(C) ->
    normalize_clause_(lists:usort(C),[]).

normalize_clause_(As0=[A|As], C) when is_integer(A) ->
    if A < 0 ->
	    case lists:member(-A, As) of
		false -> normalize_clause_(As, [A|C]);
		true -> []
	    end;
       A > 0 ->
	    reverse(C) ++ As0
    end;
normalize_clause_([false|As],C) ->
    normalize_clause_(As,C);
normalize_clause_([true|_],_C) ->
    [];
normalize_clause_(As=[{'not',_}|_], C) ->
    reverse(C) ++ As;
normalize_clause_([A|As], C) ->
    case lists:member({'not',A}, As) of
	false -> normalize_clause_(As, [A|C]);
	true -> []
    end;
normalize_clause_([], C) ->
    reverse(C).


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


%% collect all variables in formula
vars(F) ->
    vars(F,[]).

vars(A,Vs) when is_atom(A) -> var_add(A,Vs);
vars({var,A},Vs) -> var_add({var,A},Vs);
vars({'not',F},Vs) -> vars(F,Vs);
vars({'and',A,B},Vs) -> vars(A,vars(B,Vs));
vars({'or',A,B},Vs) -> vars(A,vars(B,Vs));
vars({'imp',A,B},Vs) -> vars(A,vars(B,Vs));
vars({'equ',A,B},Vs) -> vars(A,vars(B,Vs));
vars({'xor',A,B},Vs) -> vars(A,vars(B,Vs));
vars({'all',Fs},Vs) -> foldl(fun(G,Ws) -> vars(G,Ws) end, Vs, Fs);
vars({'any',Fs},Vs) -> foldl(fun(G,Ws) -> vars(G,Ws) end, Vs, Fs);
vars({'none',Fs},Vs) -> foldl(fun(G,Ws) -> vars(G,Ws) end, Vs, Fs).

var_add(V, Vs) ->    
    case member(V, Vs) of
	true -> Vs;
	false -> [V|Vs]
    end.


rewrite(A) when is_atom(A) -> A;
rewrite({var,A}) -> {var,A};
rewrite({'not',A}) when is_atom(A) -> {'not',A};
rewrite({'not',{var,A}}) -> {'not',{var,A}};
rewrite({'not', {'not', A}}) -> rewrite(A);
rewrite({'not', {'and', A, B}}) ->
    {'or', rewrite({'not',A}), rewrite({'not',B})};
rewrite({'not', {'or', A, B}}) ->
    {'and', rewrite({'not',A}),rewrite({'not',B})};
rewrite({'not', F}) -> rewrite({'not',rewrite(F)});
rewrite({'and', A, B}) -> {'and', rewrite(A), rewrite(B)};
rewrite({'or', A, B}) ->  {'or', rewrite(A), rewrite(B)};
rewrite({'imp',A,B}) ->   {'or', rewrite({'not', A}), rewrite(B)};
rewrite({'equ',A,B}) ->
    {'and',
     {'or', rewrite({'not', A}), rewrite(B)},
     {'or', rewrite({'not', B}), rewrite(A)}};
rewrite({'xor',A,B})    -> rewrite({'not',{'equ',A,B}});
rewrite({'all',[]})     -> true;
rewrite({'all',[F]})    -> rewrite(F);
rewrite({'all',[F|Fs]}) -> {'and',rewrite(F),rewrite({'all',Fs})};
rewrite({'any',[]})     -> false;
rewrite({'any',[F]})    -> rewrite(F);
rewrite({'any',[F|Fs]}) -> {'or',rewrite(F),rewrite({'any',Fs})};
rewrite({'none',Fs})    -> rewrite({'not',{any,Fs}}).

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


    








