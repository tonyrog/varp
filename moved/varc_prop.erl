%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2011, Tony Rogvall
%%% @doc
%%%    varc properties
%%% @end
%%% Created : 18 Dec 2011 by Tony Rogvall <tony@rogvall.se>

-module(varc_prop).

-export([num_variables/0]).
-export([one_class_equal/0]).
-export([two_class_unequal/0]).
-export([backtrack/0]).

-include_lib("proper/include/proper.hrl").

-define(TRUE,   1).
-define(FALSE, -1).

%%
%% Create N variables
%% make the variables equivalent, check that they all belog to the same
%% class. Assign to value and check the property again
%%
num_variables() ->
    ?FORALL(N, integer(2,100), num_variables_(N)).

one_class_equal() ->
    ?FORALL(N, integer(2,100), one_class_equal_(N)).

two_class_unequal() ->
    ?FORALL(N, integer(2,100), 
	    ?FORALL(M, integer(2,100),
		    two_classes_unequal_(N,M))).

backtrack() ->
    ?FORALL(N, integer(2,1000), backtrack_(N)).


num_variables_(N) ->
    VCt0 = varc:new(),
    {_VList,VCt1} = new_variable_list(N, VCt0),
    varc:number_of_variables(VCt1) =:= N.


one_class_equal_(N) ->
    random:seed(erlang:now()),
    VCt0 = varc:new(),
    {VList,VCt1} = new_variable_list(N, VCt0),
    %% make sure all variables are unbound
    [ X = varc:value(X,VCt1) || X <- VList],
    %% make all variables equivalent
    {W,VCt2} = all_equal_list_(VList, VCt1),
    %% check that the class_list is complete
    WClassList = lists:sort(varc:r_class_list(W, VCt2)),
    WClassList = lists:sort(VList),
    %% check that all pairs of variables are equivalent
    [ true = varc:is_equivalent(X,Y,VCt2) || X <- [W|VList], Y <- [W|VList]],
    %% set W = false
    VCt3 = varc:equivalent(W, ?FALSE, VCt2),
    [ ?FALSE = varc:value(X,VCt3) || X <- [W|VList]],
    true.

%% Test two classes

two_classes_unequal_(N, M) ->
    random:seed(erlang:now()),
    VCt0 = varc:new(),
    {VList,VCt1} = new_variable_list(N, VCt0),
    {WList,VCt2} = new_variable_list(M, VCt1),
    %% make two equivalence classes
    {V,VCt3} = all_equal_list_(VList, VCt2),
    {W,VCt4} = all_equal_list_(WList, VCt3),
    %% 
    VCt5 = varc:equivalent(V, -W, VCt4),
    [ true = varc:is_equivalent(-X,Y,VCt5) || X <- [V|VList], Y <- [W|WList]],
    [ true = varc:is_equivalent(X,-Y,VCt5) || X <- [V|VList], Y <- [W|WList]],
    VCt6 = varc:equivalent(W, ?FALSE, VCt5),
    %%
    [ ?FALSE = varc:value(X,VCt6) || X <- [W|WList]],
    [ ?TRUE = varc:value(X,VCt6)  || X <- [V|VList]],
    true.
%%
%% random set/undo backtrack test
%% pick random variables from list
%% set to random values then backtrack
%%
backtrack_(N) ->
    random:seed(erlang:now()),
    VCt0 = varc:new(),
    {VList,VCt1} = new_variable_list(N, VCt0),
    random_bind_(VList, VCt1, 0).

random_bind_([], _VCt, _D) ->
    %% io:format("depth: ~w\n", [_D]),
    true;
random_bind_(VList0, VCt0, D) ->
    %% io:format("random_bind_: VList0=~w\n", [VList0]),
    {BList, VList1} = random_binding_list(VList0),
    %% io:format("random_bind_: BList=~w\n", [BList]),
    VCt1 = varc:mark(VCt0),
    VCt2 = bind_list(BList, VCt1),
    random_bind_(VList1, VCt2, D+1),
    [ Y = varc:value(X,VCt2) || {X,Y} <- BList],
    VCt3 = varc:undo(VCt2),
    [ X = varc:value(X,VCt3) || {X,_} <- BList],
    true.

bind_list(BList, VCt) ->
    lists:foldl(
      fun({V,Value}, VCt0) ->
	      %% io:format("set: ~w = ~w\n", [V, Value]),
	      varc:equivalent(V, Value, VCt0)
      end, VCt, BList).
    
    
random_binding_list(VList) ->
    N = length(VList),
    N0 = random:uniform(N),
    {VList1,VList2} = lists:split(N0, VList),
    BList = 
	lists:map(
      fun(V) ->
	      M = length(VList2),
	      case random:uniform(4) of
		  1 -> {V, ?FALSE};
		  2 -> {V, ?TRUE};
		  3 when M =:= 0 ->
		      {V, ?FALSE};
		  3 -> 
		      I = random:uniform(M),
		      W = lists:nth(I, VList2),
		      {V, -W};
		  4 when M =:= 0 ->
		      {V, ?TRUE};
		  4 -> 
		      I = random:uniform(M),
		      W = lists:nth(I, VList2),
		      {V, W}
	      end
      end, VList1),
    {BList, VList2}.

%%
%% Create a list of N variables
%% return {V, Cvt'} 
%%

new_variable_list(N, VCt0) ->
    lists:foldl(
      fun(_I, {VList0,VCt00}) ->
	      {V,VCt01} = varc:new_variable(VCt00),
	      {[V|VList0],VCt01}
      end,  {[],VCt0},  lists:seq(1,N)).

%%
%% combine all elements in List in random order into one
%% equivalence class.
%%
all_equal_list_([A|List], VCt) ->
    N = length(List),
    all_equal_list_(A, N, List, VCt).

all_equal_list_(A,_,[], VCt) ->
    {A,VCt};
all_equal_list_(A,_,[B], VCt) ->
    VCt1 = varc:equivalent(A, B, VCt),
    {B, VCt1};
all_equal_list_(A,N,List, VCt) ->
    I = random:uniform(N-1),
    {List1,[B|List2]} = lists:split(I, List),
    VCt1 = varc:equivalent(A, B, VCt),
    all_equal_list_(B,N-1,List1++List2, VCt1).

