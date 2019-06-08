%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2018, Tony Rogvall
%%% @doc
%%%    Given a SNF/CNF generate 
%%%    a model reduction defintion 
%%% @end
%%% Created : 25 Apr 2018 by Tony Rogvall <tony@rogvall.se>

-module(varp_reduction).
-compile(export_all).

-include("varp.hrl").

reduction(Bs) ->
    N = varp_formula:number_of_unbound(Bs),
    varp_formula:config(Bs, permanent, 0),
    CMax = varp_formula:get_info(Bs, permanent),
    Type = varp_formula:getopt(Bs, reduction_type),
    case varp_formula:getopt(Bs, reduction) of
	0 ->
	    Bs;
	all ->
	    red(Bs,N,CMax,Type);
	M ->
	    red(Bs,min(N,M),CMax,Type)
    end.

red(Bs,N,CMax,Type) ->
    case varp_formula:first_unbound(Bs) of
	false -> Bs;
	{I,X} -> red(Bs,I,X,N,CMax,Type)
    end.

red(Bs,_I,_X,0,_CMax,_Type) -> Bs;
red(Bs, I, X,N,CMax,Type) ->
    Bs1 = add_var(Bs,X,CMax,Type),
    case varp_formula:next_unbound(Bs1,I) of
	false -> Bs1;
	{I1,X1} -> red(Bs1,I1,X1,N-1,CMax,Type)
    end.

add_var(Bs,V,CMax,Type) ->
    io:format("reduction=~s,cmax=~w\n",[varp_formula:format_lit(Bs,V),CMax]),
    case Type of
	pos ->
	    Is = get_clauses(Bs,V,CMax),
	    add_lit(Bs,V,Is);
	neg ->
	    Is = get_clauses(Bs,-V,CMax),
	    add_lit(Bs,-V,Is);
	both ->
	    Is1 = get_clauses(Bs,V,CMax),
	    Is2 = get_clauses(Bs,-V,CMax),
	    Bs1 = add_lit(Bs,V,Is1),
	    add_lit(Bs1,-V,Is2);
	min ->
	    Is1 = get_clauses(Bs,V,CMax),
	    Is2 = get_clauses(Bs,-V,CMax),
	    Is1L = length(Is1),
	    Is2L = length(Is2),
	    if Is2L =:= 0 ->
		    add_lit(Bs,V,Is1);
	       Is1L =:= 0 ->
		    add_lit(Bs,-V,Is2);
	       Is1L < Is2L ->
		    add_lit(Bs,V,Is1);
	       true ->
		    add_lit(Bs,-V,Is2)
	    end
    end.

add_lit(Bs,L,Is) ->
    {Cs,Bs1} = clauses(Bs,Is,L,[]),
    %% emit_def(Bs, L, Cs),
    lists:foreach(
      fun({Y,Xs}) ->
	      Xs1 = [-Xi||Xi<-Xs],
	      varp_formula:or_clause(Bs1,[Y|Xs1]),
	      lists:foreach(
		fun(X) ->
			varp_formula:or_clause(Bs1,[-Y,X])
		end, Xs)
      end, Cs),
    Ys = [Y || {Y,_} <- Cs],
    varp_formula:or_clause(Bs1,[-L|Ys]).
    
emit_def(Bs, L, Cs) ->
    io:format("~s == ", [varp_formula:format_lit(Bs,L)]),
    lists:foreach(
      fun({'ALL',[{literal,L1}]}) ->
	      io:format("{~s}|",[varp_formula:format_lit(Bs,L1)]);
	 ({'ALL',[{literal,L1}|Ls]}) ->
	      io:format("{~s",[varp_formula:format_lit(Bs,L1)]),
	      lists:foreach(
		fun({literal,Li}) ->
			io:format("&~s", [varp_formula:format_lit(Bs,Li)])
		end, Ls),
	      io:format("}|")
      end, Cs),
    io:format("\n").
    
%% return list on form [{Y,[Xi]}]
clauses(Bs,[I|Cs],L,Acc) ->
    Clause = lists:delete(I, get_clause(Bs,I)),
    {Y,Bs1} = varp_formula:fresh_var(Bs),
    clauses(Bs1,Cs,L,[{Y,Clause}|Acc]);
clauses(Bs, [], _L, Acc) ->
    {Acc,Bs}.

get_clause(Bs, I) ->
    {'or',[?TRUE|CL]} = varc:get_clause(Bs#bs.vp, I),
    CL.

get_clauses(Bs, L, CMax) ->
    CLs = varp_formula:get_clauses(Bs,L,literal),
    [I || I <- CLs, I < CMax].
