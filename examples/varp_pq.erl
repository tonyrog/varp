%%
%% Simple run varp over various products
%%

-module(varp_pq).

-export([start/0]).
-export([start/1]).
-export([formula/2]).

start() ->
    start(20).

start(N) ->
    Ps = primes:list(N),
    io:format("~3s ", [" "]),
    lists:foreach(fun(P) -> io:format("~3w ", [P]) end, Ps),
    io:format("\n"),
    lists:foldl(
      fun(P,Ci) ->
	      io:format("~3w ", [P]),
	      Ck = lists:foldl(
		     fun(Q,Cj) when P > Q ->
			     case pq(P,Q) of
				 true ->
				     io:format("~3s ", ["X"]),
				     Cj+1;
				 false ->
				     io:format("~3s ", ["-"]),
				     Cj
			     end;
			(_,Cj) ->
			     io:format("~3s ", [" "]),
			     Cj
		     end, 0, Ps),
	      io:format("\n"),
	      Ck + Ci
      end, 0, Ps).

pq(P, Q) ->
    F = formula(P, Q),
    Options = 
	[{max,1},
	 {print,false},
	 %% {log,info},
	 {clause,true},
	 {bcp, true},
	 {value,true},
	 {reduction,all},{reduction_type,both},
	 {saturate, 1},
	 {backtrack,false}
	],
    case varp_prover:run_formula(F,Options) of
	{1,[Model]} ->
	    {_,P} = lists:keyfind({p,'P',[]},1, Model),
	    {_,Q} = lists:keyfind({p,'Q',[]},1, Model),
	    true;
	_ ->
	    false
    end.

%% 
%%  formula (P*Q == N) && (P > Q) && (Q > 1)
%%
formula(P, Q) ->
    N = max(bit:size(P),bit:size(Q)),
    Pn = {uint,N,{p,'P',[]}},
    Qn = {uint,N,{p,'Q',[]}},
    {'ALL', [
	     {'==',{'*',Pn,Qn},{uint,N+N,P*Q}},
	     {'==',{'*',Qn,Pn},{uint,N+N,P*Q}},
	     {'>',Pn,Qn},
	     {'>',Qn,{uint,N,1}}
	    ]}.
