%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2013, Tony Rogvall
%%% @doc
%%%    Ideas around clauses
%%     DPLL algoritm
%%     
%%% @end
%%% Created :  7 Dec 2013 by Tony Rogvall <tony@rogvall.se>

-module(clause).

-compile(export_all).
-import(lists, [map/2, foldl/3, member/2]).

-define(DEFAULT_K,    3).
-define(DEFAULT_SIZE, 128).

load(File) ->
    case filename:extension(File) of
	".cnf" -> load_cnf(File);
	_ -> load_varp(File)
    end.

load_varp(File) ->
    load_varp(File,[]).
load_varp(File,Bs) ->
    case varp:file(File) of
	{ok,Formula} ->
	    F = varp_expandd:formula(Formula,Bs),
	    {Cs,_Ls} = varp_cnf:clauses(F),
	    Cs1 = varp_dimacs:from_cnf(Cs),
	    {ok,[new(CL) || CL <- Cs1]};
	Error ->
	    Error
    end.

load_cnf(File) ->
    case varp_dimacs:load(File) of
	{cnf,{_NVars,_NClauses,CLs}} ->
	    %% revert to normal dimacs format...
	    {ok, from_xi(CLs)};
	Error ->
	    Error
    end.

%% assume variables are on form x(I) translate into I
from_xi(CLs) ->
    [ new([case L of
	       {p,x,[I]} -> I;
	       {'not',{p,x,[I]}} -> -I;
	       (true) -> 1;
	       (false) -> -1
	   end || L <- CL ]) || CL <- CLs].

%% backtrack  idea:
%% given a set of clauses CLs
%% pick a clause CL = [A,B,C,D,E,F]
%% assuming [B,C,D,E,F]=0   => A=1 that is
%%    B=0,C=0,D=0,E=0,F=0 and A=1 then evaluate all clauses!
%%    no contradiction and no model go to next clause (recurse)
%%
%% assume   [B,C,D,E,F]=1   => A is not interesting thus
%%   reduce the initial clause by removing A
%%
%%

%%
%% Check a clause 
%% 1 = A1 V A2 V ... V An
%% 1 = A1 V 0  => A1 = 1
%% 1 = A1 V A1 => A1 = 1
%%
%% Subformula construct:
%%   want to assume something about X15 = A1 V A5 
%%   X15/1  => 1 = A1 V A5 like a new clause
%%   X15/0  => 0 = A1 V A5 => A1=0, A5=0
%%

%% map over clauses that contain X 
fold(Fun, Acc, X, CLs) when X > 1 ->
    XMask = hash_l(X),
    foldl(fun(CL={_Bind,Mask,Pos,Neg},Acc1) ->
		  if Mask band XMask =/= 0 ->
			  case member(X,Pos) orelse 
			      member(-X,Neg) of
			      true -> 
				  Fun(CL,Acc1);
			      false ->
				  io:format("false positive\n", []),
				  Acc1
			  end;
		     true ->
			  Acc1
		  end
	  end, Acc, CLs).


fold2(Fun, Acc, X, Y, CLs) when X > 1, Y > 1 ->
    XYMask = hash_l(X) bor hash_l(Y),
    foldl(fun(CL={_Bind,Mask,Pos,Neg},Acc1) ->
		  if Mask band XYMask =/= 0 ->
			  case (member(X,Pos) orelse member(-X,Neg)) andalso
			      (member(Y,Pos) orelse member(-Y,Neg)) of
			      true -> 
				  Fun(CL,Acc1);
			      false ->
				  io:format("false positive\n", []),
				  Acc1
			  end;
		     true ->
			  Acc1
		  end
	  end, Acc, CLs).

%% select clauses where X is present
select(X, CLs) ->
    fold(fun(CL,Acc) -> [CL|Acc] end, [], X, CLs).

%% select clauses where X and Y are present
select(X,Y,CLs) ->
    fold2(fun(CL,Acc) -> [CL|Acc] end, [], X,Y, CLs).

%%
%% A clause is {LastPos,Mask,PosLiterals,NegLiterals}
%% Pos|Neg-Literals = [Literal]
%% Literal = <n>  where n is an integer |n| > 1
%% 1 = true
%% -1 = false
new(Ls) ->
    case normalize(Ls) of
	{[],[]} -> 
	    %% contradiction
	    false;
	{[1|Pos],Neg} ->
	    %% dead clause! but must save literals for model
	    {0,0,Pos,Neg};
	{Pos,Neg} ->
	    {0,hash(Pos,hash(Neg)),Pos,Neg}
    end.

%% normalize by:
%% A A  B => A B
%% A -A B => [1]
%% -1   B => B
%%  1   B => 1 B  (special case, keep literals for model)
%%        => []   (contradiction)
%%
normalize(Ls) ->
    %% sort literals together
    Ls1 = lists:usort(fun(X,Y) -> 
			      Ax=abs(X),Ay=abs(Y),
			      if Ax =:= Ay -> X =< Y; 
				 true -> Ax =< Ay end end, 
		      Ls),
    %% [-1,1,2,-1,-2,3,4,3] => [-1,1,-2,2,3,4]
    unormalize_(Ls1,0,[],[]).

unormalize_([-1|Ls],T,Pos,Neg) -> unormalize_(Ls,T,Pos,Neg);
unormalize_([1|Ls],_T,Pos,Neg) -> unormalize_(Ls,1,Pos,Neg);
unormalize_([L1|Ls1=[L2|Ls]],T,Pos,Neg) ->
    if L1 =:= -L2 ->  unormalize_(Ls,1,[abs(L1)|Pos],Neg);
       L1 < 0 -> unormalize_(Ls1,T,Pos,[L1|Neg]);
       L1 > 0 -> unormalize_(Ls1,T,[L1|Pos],Neg)
    end;
unormalize_([L1],T,Pos,Neg) when L1 < 0 ->
    uclause(T,Pos,[L1|Neg]);
unormalize_([L1],T,Pos,Neg) when L1 > 0 ->
    uclause(T,[L1|Pos],Neg);
unormalize_([],T,Pos,Neg) ->
    uclause(T,Pos,Neg).
    
uclause(0,Pos,Neg) -> {Pos,Neg};
uclause(1,Pos,Neg) -> {[1|Pos],Neg}.

%% hash a clause
hash(Ls) -> hash(Ls, 0).
hash([L|Ls],Mask) ->
    hash(Ls, hash_l(L,Mask));
hash([],Mask) ->
    Mask.

%% hash a literal
member_l(X, Mask) when X < 0 ->
    test_l_(-X, 1, ?DEFAULT_K, Mask);
member_l(X, Mask) when X > 0 ->
    test_l_(X, 1, ?DEFAULT_K, Mask).


test_l_(_X, I, K, _Mask) when I > K -> true;
test_l_(X, I, K, Mask) ->
    Pos = erlang:phash2([X|I], (1 bsl 32)) rem ?DEFAULT_SIZE,
    case bit:test(Mask, Pos) of
	1 -> test_l_(X,I+1,K,Mask);
	0 -> false
    end.

hash_l(X) -> hash_l(X, 0).
hash_l(X,Mask) -> hash_l(X, ?DEFAULT_K, Mask).

hash_l(X, K, Mask) when X < 0 -> hash_l_(-X, 1, K, Mask);
hash_l(X, K, Mask) when X > 0 -> hash_l_(X, 1, K, Mask).

hash_l_(_X, I, K, Mask) when I > K -> Mask;
hash_l_(X, I, K, Mask) ->
    Pos = erlang:phash2([X|I], (1 bsl 32)) rem ?DEFAULT_SIZE,
    Mask1 = bit:set(Mask, Pos),
    hash_l_(X, I+1, K, Mask1).
