%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2014, Tony Rogvall
%%% @doc
%%%     topological sort of triples {X,Y,Z}
%%% @end
%%% Created : 23 Mar 2014 by Tony Rogvall <tony@rogvall.se>

-module(varp_topsort).

-compile(export_all).

%% return a list of variables found in the triple set
%% the list is return with leafs first 

triples(Ts) ->
    Ns = node_list(Ts),
    sort(Ns, Ts, [], dict:new()).

sort([N|Ns], Ts, L, D) ->
    case is_unmarked(N, D) of
	true ->
	    {L1,D1} = visit(N, Ts, L, D),
	    sort(Ns, Ts, L1, D1);
	false ->
	    sort(Ns, Ts, L, D)
    end;
sort([], _Ts, L, _D) ->
    L.

visit(N, Ts, L, D) ->
    case is_temporary(N, D) of
	true ->
	    {L, D};
	false ->
	    case is_unmarked(N, D) of
		true ->
		    D1 = mark(N, temporary, D),
		    visit_edges(N, Ts, Ts, L, D1);
		false ->
		    {L, D}
	    end
    end.

visit_edges(N, [{M,N1,_}|Ts], Ts0, L, D) when N =:= abs(N1) ->
    {L1,D1} = visit(abs(M), Ts0, L, D),
    visit_edges(N, Ts, Ts0, L1, D1);
visit_edges(N, [{M,_,N1}|Ts], Ts0, L, D) when N =:= abs(N1) ->
    {L1,D1} = visit(abs(M), Ts0, L, D),
    visit_edges(N, Ts, Ts0, L1, D1);
visit_edges(N, [_|Ts], Ts0, L, D) ->
    visit_edges(N, Ts, Ts0, L, D);
visit_edges(N, [], _Ts0, L, D) ->
    D1 = mark(N, permanent, D),
    {[N|L], D1}.

mark(N, Tag, D) ->
    dict:store(N, Tag, D).

is_unmarked(N, D) ->
    case dict:find(N, D) of
	error -> true;
	{ok,_} -> false
    end.

is_temporary(N, D) ->
    case dict:find(N, D) of
	{ok,temporary} -> true;
	_ -> false
    end.

%% return a list of nodes present in Ts (but remove 1, and sign)
node_list(Ts) ->
    Ns0 = lists:foldl(
	   fun({X,Y,Z},Si) ->
		   sets:union(Si, sets:from_list([abs(X),abs(Y),abs(Z)]))
	   end, sets:new(), Ts),
    sets:to_list(sets:del_element(1, Ns0)).
