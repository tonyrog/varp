%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2012, Tony Rogvall
%%% @doc
%%%
%%% @end
%%% Created : 29 Aug 2012 by Tony Rogvall <tony@rogvall.se>

-module(example).

-compile(export_all).
-import(lists, [map/2]).

%% simple test (X <-> Y) & (Y <-> Z)

test3() ->
    {1,[_]} = prover:satisfy_formula({'and',a,b}),
    {3,[_,_,_]} = prover:satisfy_formula({'or',a,b}),
    {3,[_,_,_]} = prover:satisfy_formula({'imp', a, b}),
    {2,[_,_]} = prover:satisfy_formula({'equ',a,b}),
    {2,[_,_]} = prover:satisfy_formula({'xor',a,b}),
    ok.

ps(N) ->
    prover:satisfy(pigeon(N)).

%% N pigeons in N-1 pigeon holes
pigeon(N) ->
    %% All pigeons must be in a hole
    F1 = {forall,p,{1,N},
	  {exists,h,{1,N-1}, ph(p,h) }},
    %% Any two pigeons must be in different holes
    F2 = {forall,h,{1,N-1},
	  {forall,pi,{1,N},
	   {forall,pj,{1,N},
	    {suchthat,{'<',pi,pj},
	     {'not',{'and',ph(pi,h),ph(pj,h)}}}}}},
    {'and',F1,F2}.

ph(Pi,Hj) -> {var,{ph,Pi,Hj}}.    


%% 
%% AxEy ( (p[x,y] & r[x]) v (q[x,y] & ~r[x]) )
%% 
rsat(N) ->
    {forall,x,{1,N},
     {exists,y,{1,N},
      {'or',{'and',p(x,y),r(x)}, {'and',q(x,y),{'not',r(x)}}}}}.

%% 
%% AxEy ( (p[x,y] & r[y]) v (q[x,y] & ~r[y]) )
%% 
ysat(N) ->
    {forall,x,{1,N},
     {exists,y,{1,N},
      {'or',{'and',p(x,y),r(y)}, {'and',q(x,y),{'not',r(y)}}}}}.


%% 
%% ExAy ( (p[x,y] & r[x]) v (q[x,y] & ~r[x]) )
%% 
xsat(N) ->
    {exists,x,{1,N},
     {forall,y,{1,N},
      {'or',{'and',p(x,y),r(x)}, {'and',q(x,y),{'not',r(x)}}}}}.



p(X,Y) -> {var,{p,X,Y}}.
q(X,Y) -> {var,{q,X,Y}}.
r(X) -> {var,{r,X}}.
    
%%
%%  ExAy p(x,y) -> AyEx p(x,y)
%% 
ae(N) ->
    {imp,
     {exists,x,{1,N}, {forall,y,{1,N}, p(x,y)}},
     {forall,y,{1,N}, {exists,x,{1,N}, p(x,y)}}}.
     
%% AxEy p(x,y) & r(y)
xy(N) ->
    {forall,x,{1,N},
     {exists,y,{1,N},
      {'and', p(x,y), r(y)}}}.

%% AxEy p(x,y) & r(x)
xy2(N) ->
    {forall,x,{1,N},
     {exists,y,{1,N},
      {'and', p(x,y), r(x)}}}.
%%
%% AxEy p(x,y) & AxAyAz (p(x,y)&p(y,z) -> p(x,z)) -> Ex p(x,x)
%%
fe(N) ->
    {'imp',
     {'and', 
      {forall,x,{1,N},{exists,y,{1,N}, {var,p(x,y)}}},
      {forall,x,{1,N},
       {forall,y,{1,N},
	{forall,z,{1,N}, {'imp',{'and',p(x,y),p(y,z)}, p(x,z) }}}}},
     {exists,x,{1,N}, p(x,x) }}.


%% N = X*Y, X <= Y, X > 1
prime(N) ->
    K = imath:ilog2(N) + 1,
    %% is_prime == no model to the following formula
    X = {uint,K,x},
    Y = {uint,K,y},
    {'all', 
     [
      {'==', {uint,K,N}, {'*', X, Y}},
      {'<=', X, Y},             %% only solution where X <= Y
      {'>',  X, {uint,K,1}}     %% and X > 1  (implies Y > 1 of course)
     ]}.

%% Z = X*Y, X <= Y, X > 1
factorize(K) ->
    X = {uint,K,x},
    Y = {uint,K,y},
    Z = {uint,K,z},
    {'all', 
     [
      {'==', Z, {'*', X, Y}},
      {'<=', X, Y},             %% only solution where X <= Y
      {'>',  X, {uint,K,1}}     %% and X > 1  (implies Y > 1 of course)
     ]}.
%%
%% 1-saturated = 809   (pair=false)
%% 1-saturated = 1289  (pair=true)
%% 2-saturated = 2741...
%%
first_none_k_saturated_prime() ->
    first_none_k_saturated_prime([]).

first_none_k_saturated_prime(Opts) when is_list(Opts) ->
    first_none_k_saturated_prime(1, 2, Opts).    

first_none_k_saturated_prime(K,P,Opts) ->
    Opts1 = [{value,true}|Opts],
    case prover:saturate_formula(K, formulas:prime(P), Opts1) of
	false ->
	    io:format("~w: ~w ok\n", [K,P]),
	    first_none_k_saturated_prime(K,primes:next(P),Opts);
	_Bs ->
	    io:format("first none ~w-saturated prime: ~w\n", [K,P]),
	    first_none_k_saturated_prime(K+1,P,Opts)
    end.
    


count_models(F,N) ->
    F0 = apply(?MODULE, F, [N]),
    {Y,Ts,Bs} = prover:skolem(F0, true, [{r,I}||I <- lists:seq(1,N)]),
    %% K = (1 bsl (2*N*N)),
    %% count counter models
    case prover:eval_equal(Y,true,Ts,Bs) of
	{Ts1,Bs1} ->
	    prover:count_models(Ts1, Bs1);
	false ->
	    0
    end.

%% cantor1

cantor_2() ->
    N = 2,
    D = {0,N-1},
    %% Fxy = (x^2+2xy+y^2+3x+y)/2
    Fxy = {'/',{sum,[{'*',x,x},{'*',2,{'*',x,y}},{'*',y,y},
		     {'*',3,x}, y]}, 2},
    F = form:expand({forall,x,D,
		     {forall,y,D,
		      {exists,z,D,
		       {exists,u,D,
			{all,[{var,{r,x,z}},
			      {var,{r,z,u}},
			      {var,{r,u,y}}]}
		       }}}}),
    F1 = form:expand({subst,{r,x,y},{p,Fxy},F}),
    F2 = form:peval(F1),
    io:format("2:D=~w, F=~s\n\n", [D,form:fmt(F2)]).

cantor_3() ->
    N = 3,
    D = {0,N-1},
    %% Fxy = (x^2+2xy+y^2+3x+y)/2
    Fxy = {'/',{sum,[{'*',x,x},{'*',2,{'*',x,y}},{'*',y,y},
		     {'*',3,x}, y]}, 2},
    F = form:expand({forall,x,D,
		     {forall,y,D,
		      {exists,z,D,
		       {exists,u,D,
			{exists,w,D,
			 {all,[{var,{r,x,z}},
			       {var,{r,z,u}},
			       {var,{r,u,w}},
			       {var,{r,w,y}}]}
			}}}}}),
    F1 = form:expand({subst,{r,x,y},{p,Fxy},F}),
    F2 = form:peval(F1),
    io:format("~w:D=~w, F=~s\n\n", [N,D,form:fmt(F2)]).


cantor_4() ->
    N = 4,
    D = {0,N-1},
    %% Fxy = (x^2+2xy+y^2+3x+y)/2
    Fxy = {'/',{sum,[{'*',x,x},{'*',2,{'*',x,y}},{'*',y,y},
		     {'*',3,x}, y]}, 2},
    F = form:expand({forall,x,D,
		    {forall,y,D,
		     {exists,z,D,
		      {exists,u,D,
		       {exists,w,D,
			{exists,v,D,
			 {all,[{var,{r,x,z}},
			       {var,{r,z,u}},
			       {var,{r,u,v}},
			       {var,{r,v,w}},
			       {var,{r,w,y}}]}
			}}}}}}),
    F1 = form:expand({subst,{r,x,y},{p,Fxy},F}),
    F2 = form:peval(F1),
    io:format("~w:D=~w, F=~s\n\n", [N,D,form:fmt(F2)]).

