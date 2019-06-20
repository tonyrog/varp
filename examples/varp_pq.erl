%%
%% Simple run varp over various products
%%

-module(varp_pq).

-export([start/0, start/2, start/3]).

start() ->
    start(20, [commute,{red,min}]).

start(N, Opts) ->
    start(N,N,Opts).

start(N, Last, Opts) when Last =< N ->
    application:start(varp), %% plugin etc!
    Ps = primes:list(N),
    Ps1 = lists:sublist(Ps,N-Last+1,Last),
    io:format("~3s ", [" "]),
    lists:foreach(fun(P) -> io:format("~3w ", [P]) end, Ps),
    io:format("\n"),
    M=
	lists:foldl(
	  fun(P,Ci) ->
		  io:format("~3w ", [P]),
		  Ck = lists:foldl(
			 fun(Q,Cj) when P > Q ->
				 case pq(P,Q,Opts) of
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
	  end, 0, Ps1),
    {M, (N*(N-1)) div 2}.

pq(P, Q, Opts) ->
    Formula = formula(P, Q, Opts),
    Adder = proplists:get_value(adder, Opts, plain),
    Assoc = proplists:get_value(assoc, Opts, none),
    Options = [{print,false},{assoc,Assoc},{adder,Adder}],
    Do = [{satisfy,[]}] ++
	 case lists:keyfind(red,1,Opts) of
	     false -> [];
	     {red,Type} -> [{reduction,[{size,all},{type,Type}]}]
	 end ++
	[{saturate,[{level,1}]}],

    GOpts = varp:load_option_list(Options),
    GDo = varp:parse_do(Do),

    case varp:do_run(GDo,Formula,GOpts) of
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
formula(P, Q, Opts) ->
    N = max(bit:size(P),bit:size(Q)),
    Pn = {uint,N,{p,'P',[]}},
    Qn = {uint,N,{p,'Q',[]}},
    {'ALL',
     case lists:member(commute, Opts) of
	 true ->
	     [{'==',{'*',Qn,Pn},{uint,N+N,P*Q}}];
	 false ->
	     []
     end ++ 
     [
      {'==',{'*',Pn,Qn},{uint,N+N,P*Q}},
      {'>',Pn,Qn},
      {'>',Qn,{uint,N,1}}
     ]}.


    
