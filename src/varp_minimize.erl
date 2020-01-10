%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2020, Tony Rogvall
%%% @doc
%%%     VARP clause minimize
%%% @end
%%% Created : 10 Jan 2020 by Tony Rogvall <tony@rogvall.se>

-module(varp_minimize).
-export([clause/2]).

-include("varp.hrl").

clause(_Bs,[]) -> [];
clause(_Bs,Clause=[_]) -> Clause;
clause(Bs,Clause0) ->
    Clause = sort_abs_clause(Clause0),
    %% io:format("minimize: ~p\n", [Clause]),
    case clause_(Bs, Clause, Clause, [], 0, 0) of
	{0,_,_} -> 
	    %% io:format("  no change\n", []),
	    Clause;
	{NumRemoved,_InputClauseLength,Clause1} ->
	    counters:add(Bs#bs.counters, ?COUNTER_MINIMIZE_COUNT,
			 NumRemoved),
	    %% io:format("minimize: saved ~.2f%\n", [(NumRemoved / _InputClauseLength)*100]),
	    Clause1
    end.

clause_(Bs, [Li|Ls], Clause, NewClause, Removed, Length) ->
    case varc:implication_clause(Bs#bs.vp, -Li) of
	-1 ->
	    clause_(Bs, Ls, Clause, [Li|NewClause], Removed, Length+1);
	I ->
	    A = varc:get_clause(Bs#bs.vp,I),
	    %% io:format("implication clause of ~w = ~w, clause=~w\n", 
	    %%    [-Li, A, Clause]),
	    %% if A-{Li} is a subset of Clause then remove Li from clause
	    case is_subclause_abs(A, -Li, Clause) of
		true ->
		    clause_(Bs, Ls, Clause, NewClause, Removed+1, Length+1);
		false ->
		    clause_(Bs, Ls, Clause, [Li|NewClause], Removed, Length+1)
	    end
    end;
clause_(_Bs, [], _Clause, NewClause, Removed, Length) ->
    {Removed,Length,lists:reverse(NewClause)}.


sort_abs_clause(Clause) ->
    lists:sort(
      fun(A,A) -> false;
	 (A,B) -> 
	      case abs(A) - abs(B) of
		  0 -> A < 0;
		  R -> R > 0
	      end
      end, Clause).

%% assume clauses are abs sorted in reversed order
is_subclause_abs([Li|As],Li,Bs) ->
    is_subclause_abs(As,Li,Bs);
is_subclause_abs([X|As],Li,[X|Bs]) ->
    is_subclause_abs(As,Li,Bs);
is_subclause_abs(As=[A|_As0],Li,[B|Bs]) ->
    if abs(A) < abs(B) ->
	    is_subclause_abs(As,Li,Bs);
       true ->
	    false
    end;
is_subclause_abs([],_Li,_Bs) ->
    true;
is_subclause_abs(_As,_Li,[]) ->
    false.
