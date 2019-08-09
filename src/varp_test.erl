%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2019, Tony Rogvall
%%% @doc
%%%     Test various codings
%%% @end
%%% Created : 15 Jul 2019 by Tony Rogvall <tony@rogvall.se>

-module(varp_test).

-compile(export_all).
-include("varp.hrl").

all() ->
    application:start(varp),
    test_constants(),
    test_inc(),
    test_add(),
    test_sub(),
    test_mul(),
    test_div(),
    test_cmp(),
    test_shift(),
    test_rotate(),
    test_equation1(),
    test_equation2(),
    ok.

test_constants() ->
    {{uint,1,[?F]},_} = varp_formula:build({uint,1,0}),

    {{uint,1,[?T]},_} = varp_formula:build({uint,1,1}),

    {{int,1,[?F]},_} = varp_formula:build({int,1,0}),

    {{int,1,[?T]},_} = varp_formula:build({int,1,-1}),

    {{uint,4,[?T,?F,?F,?F]},_} = varp_formula:build({uint,4,1}),

    {{int,4,[?T,?T,?T,?T]},_} = varp_formula:build({int,4,-1}),

    {{uint,4,[?T,?T,?T,?F]},_} = varp_formula:build({uint,4,7}),

    {{int,4,[?T,?T,?F,?T]},_} = varp_formula:build({int,4,-5}),
    ok.

test_inc() ->
    true = sat({'==', {'+',{int,4,3},{uint,1,1}}, {int,4,4}},
	       [[]]),
    true = sat({'==', {'-',{int,4,3},{uint,1,1}}, {int,4,2}},
	       [[]]),
    ok.

test_add() ->
    X = {p,'X',[]},
    Y = {p,'Y',[]},

    true = sat({'==', {'+',{int,4,3},{uint,4,2}}, {int,4,5}},
	       [[]]),
    true = sat({'==', {'+',{int,4,3},{uint,4,2}}, {int,4,X}},
	       [[{X,5}]]),
    true = sat({'==', {'+',{int,4,3},{uint,4,X}}, {int,4,5}},
	       [[{X,2}]]),
    true = sat({'==', {'+',{int,4,X},{uint,4,2}}, {int,4,5}},
	       [[{X,3}]]),
    true = sat({'<', {'+',{uint,2,X},{uint,2,Y}}, {uint,3,4}},
	       [[{X,3},{Y,0}],
		[{X,2},{Y,1}],
		[{X,2},{Y,0}],
		[{X,1},{Y,2}],
		[{X,1},{Y,1}],
		[{X,1},{Y,0}],
		[{X,0},{Y,3}],
		[{X,0},{Y,2}],
		[{X,0},{Y,1}],
		[{X,0},{Y,0}]]),
    true = sat({'<', {'+',{int,2,X},{int,2,Y}}, {int,3,-1}},
	       [[{X,-1},{Y,-1}],
		[{X,-1},{Y,-2}],
		[{X,-2},{Y,-1}],
		[{X,-2},{Y,-2}],
		[{X,-2},{Y,0}],
		[{X,0},{Y,-2}]]),
    true = sat({'==',{'+',{uint,2,X},{uint,3,Y}},{uint,3,5}},
		    [[{X,3},{Y,2}],
		     [{X,2},{Y,3}],
		     [{X,1},{Y,4}],
		     [{X,0},{Y,5}]]),
    ok.

test_sub() ->
    X = {p,'X',[]},

    true = sat({'==', {'-',{int,4,3},{uint,4,2}}, {int,4,1}},
	       [[]]),
    true = sat({'==', {'-',{int,4,3},{uint,4,2}}, {int,4,X}},
	       [[{X,1}]]),
    ok.

test_mul() ->
    X = {p,'X',[]},
    Y = {p,'Y',[]},

    true = sat({'==', {'*',{uint,4,3},{uint,4,2}}, {uint,8,6}},
		    [[]]),

    true = sat({'==', {'*',{int,4,3},{uint,4,2}}, {int,8,6}},
		    [[]]),

    true = sat({'==', {'*',{int,4,3},{uint,4,2}}, {int,8,X}},
		    [[{X,6}]]),

    true = sat({'==', {'*',{int,4,-3},{uint,4,2}}, {int,8,X}},
		    [[{X,-6}]]),

    true = sat({'==', {'*',{uint,4,X},{uint,4,Y}}, {int,8,7}},
		    [[{X,1},{Y,7}], 
		     [{X,7},{Y,1}]]),

    true = sat({'==', {'*',{int,4,X},{int,4,Y}}, {int,8,7}},
		    [[{X,1},{Y,7}], 
		     [{X,7},{Y,1}],
		     [{X,-1},{Y,-7}], 
		     [{X,-7},{Y,-1}]]),
    ok.

test_div() ->
    X = {p,'X',[]},
    Y = {p,'Y',[]},

    true = sat({'==', {'/',{uint,4,3},{uint,4,2}}, {uint,4,1}},
	       [[]]),
    true = sat({'==', {'/',{uint,6,4},{uint,4,2}}, {uint,4,X}},
	       [[{X,2}]]),
    true = sat({'==', {'/',{uint,6,X},{uint,4,2}}, {uint,4,5}},
	       [[{X,11}], 
		[{X,10}]]),
    true = sat({'==', {'/',{uint,4,X},{uint,4,Y}}, {uint,4,5}},
		    [[{X,15},{Y,3}],
		     [{X,11},{Y,2}],
		     [{X,10},{Y,2}],
		     [{X,5},{Y,1}]]),
    ok.

test_cmp() ->
    X = {p,'X',[]},

    true = sat({'<', {uint,4,X},{uint,4,2}},
	       [[{X,0}],[{X,1}]]),
    true = sat({'<', {int,4,X},{int,4,2}},
	       [[{X,V}] || V <- lists:seq(-8,1)]),
    true = sat({'>', {uint,4,X},{uint,4,2}},
	       [[{X,V}] || V <- lists:seq(3,15)]),
    true = sat({'>', {int,4,X},{int,4,2}},
	       [[{X,V}] || V <- lists:seq(3,7)]),
    ok.

test_shift() ->
    X = {p,'X',[]},

    true = sat({'==', {'<<',{uint,4,3}, {uint,1,1}}, {uint,4,6}},
	       [[]]),
    true = sat({'==', {'<<',{uint,4,3}, {uint,1,1}}, {uint,4,X}},
	       [[{X,6}]]),
    true = sat({'==', {'>>',{uint,4,3}, {uint,1,1}}, {uint,4,1}},
	       [[]]),
    true = sat({'==', {'>>',{uint,4,3}, {uint,1,1}}, {uint,4,X}},
	       [[{X,1}]]),
    true = sat({'==', {'>>',{int,4,-1}, {uint,1,1}}, {int,4,X}},
	       [[{X,-1}]]),
    true = sat({'==', {'<<',{int,4,-1}, {uint,1,1}}, {int,4,X}},
	       [[{X,-2}]]),
    ok.

test_rotate() ->
    X = {p,'X',[]},

    true = sat({'==', {'<<<',{uint,4,X}, {uint,1,1}}, {uint,4,X}},
	       [[{X,15}], [{X,0}]]),
    true = sat({'==', {'<<<',{int,4,X}, {uint,1,1}}, {int,4,X}},
	       [[{X,-1}], [{X,0}]]),
    ok.
%%
%%  X + Y - Z -  12 = 0
%%  X*X + Y*Y - Z*Z - 12 = 0
%%
%%   (X-12)(Y-12) == 66,   X     Y
%%   1     66             13    78
%%   2     33             14    45
%%   3     22             15    34
%%   6     11             18    23
%%   11    6              23    18
%%   22    3              34    15
%%   33    2              45    14
%%   66    1              78    13
%%
%%   Z = X+Y-12  
%%
test_equation1() ->
    N = 8,
    Xv = {p,'X',[]},
    Yv = {p,'Y',[]},
    Zv = {p,'Z',[]},
    X = {uint,N,Xv},
    Y = {uint,N,Yv},
    Z = {uint,N,Zv},
    true = 
sat(
  {'ALL',
   [
    {'==', {'SUM', [X,Y,{'-',Z},-12]}, 0},
    {'==', {'SUM', [{'*',X,X},{'*',Y,Y},{'-',{'*',Z,Z}},-12]},0}
   ]},
  [[{Xv,13},{Yv,78},{Zv,(13+78)-12}],
   [{Xv,14},{Yv,45},{Zv,(14+45)-12}],
   [{Xv,15},{Yv,34},{Zv,(15+34)-12}],
   [{Xv,18},{Yv,23},{Zv,(18+23)-12}],
   [{Xv,23},{Yv,18},{Zv,(23+18)-12}],
   [{Xv,34},{Yv,15},{Zv,(34+15)-12}],
   [{Xv,45},{Yv,14},{Zv,(45+14)-12}],
   [{Xv,78},{Yv,13},{Zv,(78+13)-12}]]),

    ok.
    

%% solve 7x + 11y + 26z = 123
test_equation2() ->
    N = 10,
    Xv = {p,'X',[]},
    Yv = {p,'Y',[]},
    Zv = {p,'Z',[]},
    X = {uint,N,Xv},
    Y = {uint,N,Yv},
    Z = {uint,N,Zv},
    true = sat(
	     {'==', {'SUM',[{'*',7,X},{'*',11,Y},{'*',26,Z},-123]}, 0},
	     [
	      [{Xv,5},{Yv,8},{Zv,0}],
	      [{Xv,6},{Yv,5},{Zv,1}],
	      [{Xv,7},{Yv,2},{Zv,2}],
	      [{Xv,16},{Yv,1},{Zv,0}]
	     ]),
    ok.
        

sat(Formula, ExpectedModels) ->
    N = length(ExpectedModels),
    Options = [{print,false}],
    Do = [{satisfy,[]}, {backtrack,[]}],
    GOpts = varp:load_option_list(Options),
    GDo = varp:parse_do(Do),
    case varp:do_run(GDo,Formula,GOpts) of
	{N,Ms} ->
	    lists:sort(Ms) == lists:sort(ExpectedModels);
	Res ->
	    io:format("Res=~w\n", [Res]),
	    false
    end.
