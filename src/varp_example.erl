%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2010, Tony Rogvall
%%% @doc
%%%    Example formulas
%%% @end
%%% Created : 30 Aug 2010 by Tony Rogvall <tony@rogvall.se>

-module(varp_example).

-compile(export_all).

%% check if V is a prime number
%% Interesting enough so is:  
%%   1093 (2#10001000101) proved in test1   
%%   1097 (2#10001001001) is not proved in test1 but is harder 
%%   1103 (2#10001001111) proved in test1 
%%   1217 (2#10011000001) proved in test1 
%% So why is 1097 harder than 1093 and 1103?
%% 
%% Trying to satisfy the formula:
%%
%%   (X*Y == V) && (X <= Y) && (X > 1)
%%
is_prime(P) ->
    is_prime(P, 1).

is_prime(2,_) -> 
    {true, axiom};
is_prime(V,T) when V >= 3 ->
    {Fx, Bs0} = prime_formula(V),
    io:format("formula: vars = ~w, unbound = ~w\n", 
	      [varp:number_of_variables(Bs0),
	       varp:number_of_unbound(Bs0)]),
    case varp:ev(Fx,1,Bs0) of
	false ->
	    {true, ev};
	{true,Bs1} ->
	    %% varp:show(Bs1),
	    io:format("ev: unbound = ~w\n", 
		      [varp:number_of_unbound(Bs1)]),
	    case varp:test(T, Bs1) of
		false ->
		    {true, test};
		{true, Bs2} ->
		    io:format("backtrack: unbound = ~w\n", 
			      [varp:number_of_unbound(Bs2)]),
		    case varp:backtrack(Bs2,1) of
			{0,[]} ->
			    {true,backtrack};  %% no models
			{1,_Ms} ->
			    %% io:format("model = ~p\n", [Ms]),
			    {false, _Ms}
		    end
	    end
    end.

prime_formula(V) ->
    N = imath:ilog2(V) + 1,
    %% is_prime == no model to the following formula
    X = {uint,N,x},
    Y = {uint,N,y},
    F = 
	{'all', 
	 [
	  {'==', {uint,N,V}, {'*', X, Y}},
	  {'<=', X, Y},             %% only solution where X <= Y
	  {'>',  X, {uint,N,1}}     %% and X > 1  (implies Y > 1 of course)
	 ]},
    varp:formula(F).


%%
%% Find first prime that need backtrack
%% For TEST(1) the first prime is 593  then 601, 617 ..
%% For TEST(2) the first prime is > 11047
%%
backtrack_prime() ->
    backtrack_prime(3).

backtrack_prime(I) ->
    backtrack_prime(I, 1, -1).

backtrack_prime(_I, _T, 0) -> 
    not_found;
backtrack_prime(I, T, N) ->
    case primes:is_prime(I) of
	false ->
	    %% Here we can investigate how difficult it is to produce
	    %% the first model
	    backtrack_prime(I+1, T, N-1);
	true ->
	    R = is_prime(I,T),
	    io:format("~w: ~w\n", [I, R]),
	    case R of
		false ->
		    {error, I};
		{true, backtrack} ->
		    {found, I};
		{true, test} ->
		    backtrack_prime(I+1, T, N-1);
		X ->
		    {error, {return, X}}
	    end
    end.

%% 
%% Prove arihtmentic identities for fixed number of bits
%%
commutative_plus(N) ->
    F = {'==',
	 {'+', {uint,N,x}, {uint,N,y}},
	 {'+', {uint,N,y}, {uint,N,x}}},
    varp:provek(F, 2).

commutative_times(N) ->
    F = {'==',
	 {'*', {uint,N,x}, {uint,N,y}},
	 {'*', {uint,N,y}, {uint,N,x}}},
    varp:provek(F, 2).
    

%% N pigeons in N-1 pigeon holes
pigeon(N) ->
    Ns = lists:seq(1,N),
    Hs = lists:seq(1,N-1),
    %% All pigeons must be in a hole
    F1 = {all,
	  lists:map(
	    fun(Pi) ->
		    %% pigeon Pi must be in one of the holes Hj
		    {any,lists:map(fun(Hj) -> ph(Pi,Hj) end, Hs)}
	    end, Ns)},
    %% Any two pigeons must be in different holes
    F2 = {all,
	  lists:map(
	    fun(Hi) ->
		    {all, lists:map(
			    fun({Pi,Pj}) ->
				    {'not',{'and',ph(Pi,Hi),ph(Pj,Hi)}}
			    end, [{Pi,Pj} || Pi <- Ns, Pj <- Ns, Pi < Pj ])}
	    end, Hs)},
    {'and',F1,F2}.

ph(Pi,Hj) -> {var,{ph,Pi,Hj}}.    
