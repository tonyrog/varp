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
    case varp_formula:getopt(Bs,reduction) of
	0 -> Bs;
	all -> red(Bs,N);
	M -> red(Bs,min(N,M))
    end.

red(Bs,N) ->
    case varp_formula:first_unbound(Bs) of
	false -> Bs;
	{I,X} -> red(Bs,I,X,N)
    end.

red(Bs,_I,_X,0) -> Bs;
red(Bs, I, X,N) ->
    Bs1 = add_var(Bs,X),
    case varp_formula:next_unbound(Bs1,I) of
	false -> Bs1;
	{I1,X1} -> red(Bs1,I1,X1,N-1)
    end.

add_var(Bs, V) ->
    io:format("reduction ~s\n", [varp_formula:format_lit(Bs,V)]),
    Bs1 = add_lit(Bs, V),
    add_lit(Bs1, -V).

add_lit(Bs, L) ->
    Is = varp_formula:get_clauses(Bs, L, literal),
    Cs = clauses(Bs, Is, L),
    %% emit_def(Bs, L, Cs),
    {{bool,V}, Bs1} = varp_formula:build({'ANY',Cs}, Bs),
    varp_formula:xor_gate(Bs1, ?TRUE, [L,-V]).

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
    

clauses(Bs, [I|Cs], L) ->
    [clause(get_clause(Bs, I), L, []) | clauses(Bs,Cs,L)];
clauses(_Bs, [], _L) ->
    [].

%% from [A,B,L,C,D] => [-A,-B,-C,-D]
clause([L|Ls], L, Acc) -> 
    clause(Ls, L, Acc);
clause([Li|Ls], L, Acc) -> 
    clause(Ls, L, [{literal,-Li}|Acc]);
clause([], _L, Acc) ->
    {'ALL',Acc}.

get_clause(Bs, I) ->
    {'or',[?TRUE|CL]} = varc:get_clause(Bs#bs.vp, I),
    CL.
