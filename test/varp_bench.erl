%%
%%  An example where speed matters
%%

-module(varp_bench).

-compile(export_all).

%%
%% Macbook pro: 2.53 GHz Intel Core 2 Duo, 4 GB 1067 MHe DDR3
%% Mac OS X 10.7.1
%% Results:  
%%    base line:  47730405 us
%%    +native:    40277954 us
%%    optim1:     29884303 us   (cons instead of append in equal/eq)
%%    optim2:     28684267 us   dotted pair
%%
%%    varc:       3610925 us    C implementaion of core
%%
%%
run() ->
    {Time, undefined} = timer:tc(?MODULE, prime_check, [2,65003]),
    {ok,Time}.

prime_check(T,V) ->
    N = imath:ilog2(V) + 1,
    %% is_prime == no model to the following formula
    X = {uint,N,{p,'X',[]}},
    Y = {uint,N,{p,'Y',[]}},
    F = 
	{'ALL', 
	 [
	  {'==', {uint,N,V}, {'*', X, Y}},
	  {'<=', X, Y},             %% only solution where X <= Y
	  {'>',  X, {uint,N,1}}     %% and X > 1  (implies Y > 1 of course)
	 ]},
    varp_prover:satisfy_formula(F, [{saturate,T},
				    {log,info},
				    {pair,false},
				    {backtrack,false},
				    {print,model},
				    {method,count}]).

