%%
%% UNIT TESTS
%%
-module(varc_test).

 -include_lib("eunit/include/eunit.hrl").

%%
%% Test 
%%   V = W, W = 1 => V = 1
%%
basic_test() ->
    Vct = varc:new(),
    {V,Vct1} = varc:new_variable(Vct),
    ?assert(varc:value(V,Vct1) =:= V),
    {W,Vct2} = varc:new_variable(Vct1),
    ?assert(varc:value(W,Vct2) =:= W),
    Vct3 = varc:equivalent(V, W, Vct2),
    ?assert(varc:is_equivalent(V, W, Vct3)),
    ?assert(varc:value(V,Vct3) =:= W),
    ?assert(varc:value(W,Vct3) =:= W),
    Vct4 = varc:equivalent(W, 1, Vct3),
    ?assert(varc:value(V, Vct4) =:= 1).

    

    
    
    
    
    
    
