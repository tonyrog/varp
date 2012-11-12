%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2010, Tony Rogvall
%%% @doc
%%%   Testing varp
%%% @end
%%% Created : 28 Aug 2010 by Tony Rogvall <tony@rogvall.se>

-module(varp_test).

-compile(export_all).

-define(TRUE, 1).
-define(FALSE, -1).

test_class() ->
    Bs0 = varp:new_bs(),
    {[{bool,A},{bool,B},{bool,C},{bool,D},{bool,E}],Bs1} =
	varp:args([a,b,c,d,e],Bs0),
    Bs = set_list([{A,B},{C,-D}, {D,-E},{B,E},{E,?FALSE}], Bs1),

    ?FALSE  = varp:value(E,Bs),
    ?TRUE   = varp:value(D,Bs),
    ?FALSE  = varp:value(C,Bs),
    ?FALSE = varp:value(B,Bs),
    ?FALSE = varp:value(A,Bs),
    ok.

test_class1() ->
    Bs0 = varp:new_bs(),
    {[{bool,A},{bool,B},{bool,C},{bool,D},{bool,E},{bool,F}],Bs1} =
	varp:args([a,b,c,d,e,f],Bs0),
    Bs = set_list([{A,B},{B,-C}, {D,-E},{E,-F}, {C,-F}, {F,?FALSE}], Bs1),

    ?FALSE  = varp:value(F,Bs),
    ?TRUE   = varp:value(E,Bs),
    ?FALSE  = varp:value(D,Bs),
    ?TRUE   = varp:value(C,Bs),
    ?FALSE  = varp:value(B,Bs),
    ?FALSE  = varp:value(A,Bs),
    ok.

test_class2() ->
    Bs0 = varp:new_bs(),
    {[{bool,A},{bool,B},{bool,C},{bool,D},{bool,E},{bool,F}],Bs1} =
	varp:args([a,b,c,d,e,f],Bs0),
    Bs = set_list([{-A,-B},{B,-C}, {-D,-E},{-E,-F}, {-C,-F}, {F,?FALSE}], Bs1),

    ?FALSE  = varp:value(F,Bs),
    ?FALSE  = varp:value(E,Bs),
    ?FALSE  = varp:value(D,Bs),
    ?FALSE  = varp:value(C,Bs),
    ?TRUE   = varp:value(B,Bs),
    ?TRUE   = varp:value(A,Bs),
    ok.

set_list([{X,Y}|Xs],Bs) ->
    {_,Bs1} = varp:equal(X,Y,Bs),
    set_list(Xs, Bs1);
set_list([], Bs) ->
    Bs.
    

    

