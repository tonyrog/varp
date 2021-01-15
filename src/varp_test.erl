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
    Failed = 
	lists:foldl(
	  fun(Test,Failed) ->
		  io:format("< ~w: ", [Test]),
		  case sync_apply(?MODULE, Test, []) of
		      ok -> 
			  io:format("> OK\n"),
			  Failed;
		      error ->
			  io:format("> ERROR\n"),
			  Failed+1
		  end
	  end, 0, 
	  [
	   constants,
	   inc,
	   add,
	   sub,
	   mul,
	   'div',
	   cmp_1, cmp_2, cmp_3, cmp_4,
	   shift,
	   rotate,
	   equation1,
	   equation2,
	   %% saturations
	   saturate_a1,
	   saturate_a2,
	   saturate_b1
	  ]),
        if Failed > 0 ->
	    io:format("~w FAILED CASES\n", [Failed]);
       true ->
	    io:format("ALL OK\n")
    end.

sync_apply(Mod, Fun, Args) ->
    PARENT = self(),
    Pid = spawn(fun() ->
			try apply(Mod, Fun, Args) of
			    _Res -> PARENT ! {self(),ok}
			catch 
			    error:_ ->
				PARENT ! {self(),error}
			end
		end),
    receive
	{Pid, Result} ->
	    Result
    end.

constants() ->
    {{uint,1,[?F]},_} = varp_formula:build({uint,1,0}),

    {{uint,1,[?T]},_} = varp_formula:build({uint,1,1}),

    {{int,1,[?F]},_} = varp_formula:build({int,1,0}),

    {{int,1,[?T]},_} = varp_formula:build({int,1,-1}),

    {{uint,4,[?T,?F,?F,?F]},_} = varp_formula:build({uint,4,1}),

    {{int,4,[?T,?T,?T,?T]},_} = varp_formula:build({int,4,-1}),

    {{uint,4,[?T,?T,?T,?F]},_} = varp_formula:build({uint,4,7}),

    {{int,4,[?T,?T,?F,?T]},_} = varp_formula:build({int,4,-5}),
    ok.

inc() ->
    true = sat({'eq', {'add',{int,4,3},{uint,1,1}}, {int,4,4}},
	       [[]]),
    true = sat({'eq', {'sub',{int,4,3},{uint,1,1}}, {int,4,2}},
	       [[]]),
    ok.

add() ->
    X = {p,'X',[]},
    Y = {p,'Y',[]},

    true = sat({'eq', {'add',{int,4,3},{uint,4,2}}, {int,4,5}},
	       [[]]),
    true = sat({'eq', {'add',{int,4,3},{uint,4,2}}, {int,4,X}},
	       [[{X,5}]]),
    true = sat({'eq', {'add',{int,4,3},{uint,4,X}}, {int,4,5}},
	       [[{X,2}]]),
    true = sat({'eq', {'add',{int,4,X},{uint,4,2}}, {int,4,5}},
	       [[{X,3}]]),
    true = sat({'lt', {'add',{uint,2,X},{uint,2,Y}}, {uint,3,4}},
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
    true = sat({'eq',{'add',{uint,2,X},{uint,3,Y}},{uint,3,5}},
	       [[{X,Xi},{Y,Yi}] || 
		   Xi <- [0,1,2,3], Yi <- [0,1,2,3,4,5,6,7], Xi+Yi == 5]),
    true = sat({'lt', {'add',{int,2,X},{int,2,Y}}, {int,3,-1}},
	       [[{X,Xi},{Y,Yi}] || 
		   Xi <- [-2,-1,0,1], Yi <- [-2,-1,0,1], Xi+Yi< -1]),
    ok.

sub() ->
    X = {p,'X',[]},

    true = sat({'eq', {'sub',{int,4,3},{uint,4,2}}, {int,4,1}},
	       [[]]),
    true = sat({'eq', {'sub',{int,4,3},{uint,4,2}}, {int,4,X}},
	       [[{X,1}]]),
    ok.

mul() ->
    X = {p,'X',[]},
    Y = {p,'Y',[]},

    true = sat({'eq', {'mul',{uint,4,3},{uint,4,2}}, {uint,8,6}},
		    [[]]),

    true = sat({'eq', {'mul',{int,4,3},{uint,4,2}}, {int,8,6}},
		    [[]]),

    true = sat({'eq', {'mul',{int,4,3},{uint,4,2}}, {int,8,X}},
		    [[{X,6}]]),

    true = sat({'eq', {'mul',{int,4,-3},{uint,4,2}}, {int,8,X}},
		    [[{X,-6}]]),

    true = sat({'eq', {'mul',{uint,4,X},{uint,4,Y}}, {int,8,7}},
		    [[{X,1},{Y,7}], 
		     [{X,7},{Y,1}]]),

    true = sat({'eq', {'mul',{int,4,X},{int,4,Y}}, {int,8,7}},
		    [[{X,1},{Y,7}], 
		     [{X,7},{Y,1}],
		     [{X,-1},{Y,-7}], 
		     [{X,-7},{Y,-1}]]),
    ok.

'div'() ->
    X = {p,'X',[]},
    Y = {p,'Y',[]},

    true = sat({'eq', {'div',{uint,4,3},{uint,4,2}}, {uint,4,1}},
	       [[]]),
    true = sat({'eq', {'div',{uint,6,4},{uint,4,2}}, {uint,4,X}},
	       [[{X,2}]]),
    true = sat({'eq', {'div',{uint,6,X},{uint,4,2}}, {uint,4,5}},
	       [[{X,11}], 
		[{X,10}]]),
    true = sat({'eq', {'div',{uint,4,X},{uint,4,Y}}, {uint,4,5}},
		    [[{X,15},{Y,3}],
		     [{X,11},{Y,2}],
		     [{X,10},{Y,2}],
		     [{X,5},{Y,1}]]),
    ok.

cmp_1() ->
    X = {p,'X',[]},
    true = sat({'lt', {uint,4,X},{uint,4,2}},
	       [[{X,0}],[{X,1}]]).

cmp_2() ->
    X = {p,'X',[]},
    true = sat({'lt', {int,4,X},{int,4,2}},
	       [[{X,V}] || V <- lists:seq(-8,1)]).

cmp_3() ->
    X = {p,'X',[]},
    true = sat({'gt', {uint,4,X},{uint,4,2}},
	       [[{X,V}] || V <- lists:seq(3,15)]).

cmp_4() ->
    X = {p,'X',[]},
    true = sat({'gt', {int,4,X},{int,4,2}},
	       [[{X,V}] || V <- lists:seq(3,7)]).

shift() ->
    X = {p,'X',[]},

    true = sat({'eq', {'shl',{uint,4,3}, {uint,1,1}}, {uint,4,6}},
	       [[]]),
    true = sat({'eq', {'shl',{uint,4,3}, {uint,1,1}}, {uint,4,X}},
	       [[{X,6}]]),
    true = sat({'eq', {'shr',{uint,4,3}, {uint,1,1}}, {uint,4,1}},
	       [[]]),
    true = sat({'eq', {'shr',{uint,4,3}, {uint,1,1}}, {uint,4,X}},
	       [[{X,1}]]),
    true = sat({'eq', {'shr',{int,4,-1}, {uint,1,1}}, {int,4,X}},
	       [[{X,-1}]]),
    true = sat({'eq', {'shl',{int,4,-1}, {uint,1,1}}, {int,4,X}},
	       [[{X,-2}]]),
    ok.

rotate() ->
    X = {p,'X',[]},

    true = sat({'eq', {'rol',{uint,4,X}, {uint,1,1}}, {uint,4,X}},
	       [[{X,15}], [{X,0}]]),
    true = sat({'eq', {'rol',{int,4,X}, {uint,1,1}}, {int,4,X}},
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
equation1() ->
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
    {'eq', {'SUM', [X,Y,{'neg',Z},-12]}, 0},
    {'eq', {'SUM', [{'mul',X,X},{'mul',Y,Y},{'neg',{'mul',Z,Z}},-12]},0}
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
equation2() ->
    N = 10,
    Xv = {p,'X',[]},
    Yv = {p,'Y',[]},
    Zv = {p,'Z',[]},
    X = {uint,N,Xv},
    Y = {uint,N,Yv},
    Z = {uint,N,Zv},
    true = sat(
	     {'eq', {'SUM',[{'mul',7,X},{'mul',11,Y},{'mul',26,Z},-123]}, 0},
	     [
	      [{Xv,5},{Yv,8},{Zv,0}],
	      [{Xv,6},{Yv,5},{Zv,1}],
	      [{Xv,7},{Yv,2},{Zv,2}],
	      [{Xv,16},{Yv,1},{Zv,0}]
	     ]),
    ok.

saturate_a1() ->
    Vp = varp_nif:new(#{ xref => true }),
    X1 = {p,'X1',[]},
    X2 = {p,'X2',[]},
    X3 = {p,'X3',[]},
    X4 = {p,'X4',[]},
    X5 = {p,'X5',[]},
    X6 = {p,'X6',[]},
    X7 = {p,'X7',[]},
    F = varp_ast:build(
	  {'ALL',[{imp, X1, X2},
		  {imp, {'not',X1}, X2},
		  {imp, X1, {'not',X3}},
		  {imp, {'not',X1}, {'not',X3}},
		  {imp, X1, X4},
		  {imp, {'not',X1}, {'not',X4}},
		  {imp, X1, {'not',X5}},
		  {imp, {'not',X1}, X5},
		  {imp, X1, X6},
		  {imp, X6, X7}]}, Vp),
    varp_nif:bind(Vp, F),
    true = varp_nif:bcp(Vp),
    varp:vec_sat_lap(Vp,1,0,0,0),
    Bs = [binding(Vp, Var) || Var <- [X1,X2,X3,X4,X5,X6,X7]], 
    ?dbg("~p\n", [Bs]),
    u = proplists:get_value("X1", Bs),
    t = proplists:get_value("X2", Bs),
    f = proplists:get_value("X3", Bs),
    "X1" = proplists:get_value("X4", Bs),
    "!X1" = proplists:get_value("X5", Bs),
    u = proplists:get_value("X6", Bs),
    u = proplists:get_value("X7", Bs),
    ok.
    
saturate_a2() ->
    Vp = varp_nif:new(#{ xref => true }),
    X = {p,'X',[]},
    A = {p,'A',[]},
    B = {p,'B',[]},
    C = {p,'C',[]},
    D = {p,'D',[]},
    F = varp_ast:build(
	  {'ALL',[{imp, X, {'ALL',[A,{'not',B},C,{'not',D}]}},
		  {imp, {'not',X}, {'ALL',[A,{'not',B},{'not',C},D]}}]},
	  Vp),
    varp_nif:bind(Vp, F),
    true = varp_nif:bcp(Vp),
    varp:vec_sat_lap(Vp,1,0,0,0),
    Bs = [binding(Vp, Var) || Var <- [X,A,B,C,D]],
    ?dbg("~p\n", [Bs]),
    t = proplists:get_value("A", Bs),
    f = proplists:get_value("B", Bs),
    "X" = proplists:get_value("C", Bs),
    "!X" = proplists:get_value("D", Bs),
    ok.
    
saturate_b1() ->
    Vp = varp_nif:new(#{ xref => true }),
    X = {p,'X',[]},
    Y = {p,'Y',[]},
    A = {p,'A',[]},
    F = varp_ast:build(
	  {'ALL',[{imp, {'and',X,Y}, A},
		  {imp, {'and',X,{'not',Y}}, A},
		  {imp, {'and',{'not',X},Y}, A},
		  {imp, {'and',{'not',X},{'not',Y}}, A}
		 ]},
	  Vp),
    ?dbg0("~w\n", [[{A, varp:find_symbol(Vp,varp_ast:var_term(A))},
		    {X, varp:find_symbol(Vp,varp_ast:var_term(X))},
		    {Y, varp:find_symbol(Vp,varp_ast:var_term(Y))}]]),
    varp_nif:bind(Vp, F),
    true = varp_nif:bcp(Vp),

    varp:vec_sat_lap(Vp,2,0,0,0),
					
    Bs = [binding(Vp, Var) || Var <- [X,Y,A]],
    ?dbg0("~p\n", [Bs]),
    t = proplists:get_value("A", Bs),
    u = proplists:get_value("X", Bs),
    u = proplists:get_value("Y", Bs),
    ok.


saturate_c1() ->
    Vp = varp_nif:new(#{ xref => true }),
    X = {p,'X',[]},
    Y = {p,'Y',[]},
    Z = {p,'Z',[]},
    A = {p,'A',[]},
    F = varp_ast:build(
	  {'ALL',[
		  {imp, {'ALL',[{'not',X},{'not',Y},{'not',Z}]}, A},
		  {imp, {'ALL',[{'not',X},{'not',Y},Z]}, A},
		  {imp, {'ALL',[{'not',X},Y,{'not',Z}]}, A},
		  {imp, {'ALL',[{'not',X},Y,Z]}, A},
		  {imp, {'ALL',[X,{'not',Y},{'not',Z}]}, A},
		  {imp, {'ALL',[X,{'not',Y},{'not',Z}]}, A},
		  {imp, {'ALL',[X,{'not',Y},Z]}, A},
		  {imp, {'ALL',[X,Y,{'not',Z}]}, A},
		  {imp, {'ALL',[X,Y,Z]}, A}
		 ]},
	  Vp),
    ?dbg0("~w\n", [[{A, varp:find_symbol(Vp,varp_ast:var_term(A))},
		    {X, varp:find_symbol(Vp,varp_ast:var_term(X))},
		    {Y, varp:find_symbol(Vp,varp_ast:var_term(Y))},
		    {Z, varp:find_symbol(Vp,varp_ast:var_term(Z))}]]),
    varp_nif:bind(Vp, F),
    true = varp_nif:bcp(Vp),
    %% varp:vec_sat_lap(Vp,3,0,0,0),
    Xi = varp:find_symbol(Vp,varp_ast:var_term(X)),
    Yi = varp:find_symbol(Vp,varp_ast:var_term(Y)),
    Zi = varp:find_symbol(Vp,varp_ast:var_term(Z)),
    varp:vec_sat(Vp, [Xi,Yi,Zi]),
					
    Bs = [binding(Vp, Var) || Var <- [X,Y,Z,A]],
    ?dbg0("~p\n", [Bs]),
    t = proplists:get_value("A", Bs),
    u = proplists:get_value("X", Bs),
    u = proplists:get_value("Y", Bs),
    u = proplists:get_value("Z", Bs),
    ok.

saturate_c2() ->
    Vp = varp_nif:new(#{ xref => true }),
    X = {p,'X',[]},
    Y = {p,'Y',[]},
    Z = {p,'Z',[]},
    A = {p,'A',[]},
    B = {p,'B',[]},
    F = varp_ast:build(
	  {'ALL',[
		  {imp, {'ALL',[{'not',X},{'not',Y},{'not',Z}]},
		   {'and',{'not',A},{'not',B}}},
		  {imp, {'ALL',[{'not',X},{'not',Y},Z]}, 
		   {'and',{'not',A},{'not',B}}},
		  {imp, {'ALL',[{'not',X},Y,{'not',Z}]}, 
		   {'and',{'not',A},B}},
		  {imp, {'ALL',[{'not',X},Y,Z]},
		   {'and',{'not',A},B}},
		  {imp, {'ALL',[X,{'not',Y},{'not',Z}]}, 
		   {'and',A,{'not',B}}},
		  {imp, {'ALL',[X,{'not',Y},{'not',Z}]}, 
		   {'and',A,{'not',B}}},
		  {imp, {'ALL',[X,{'not',Y},Z]}, 
		   {'and',A,{'not',B}}},
		  {imp, {'ALL',[X,Y,{'not',Z}]}, 
		   {'and',A,B}},
		  {imp, {'ALL',[X,Y,Z]}, 
		   {'and',A,B}}
		 ]},
	  Vp),
    Ai = varp:find_symbol(Vp,varp_ast:var_term(A)),
    Bi = varp:find_symbol(Vp,varp_ast:var_term(B)),
    Xi = varp:find_symbol(Vp,varp_ast:var_term(X)),
    Yi = varp:find_symbol(Vp,varp_ast:var_term(Y)),
    Zi = varp:find_symbol(Vp,varp_ast:var_term(Z)),

    ?dbg0("~w\n", [[{A,Ai},{B,Bi},{X,Xi},{Y,Yi},{Z,Zi}]]),
    varp_nif:bind(Vp, F),
    true = varp_nif:bcp(Vp),
    %% varp:vec_sat_lap(Vp,3,0,0,0),

    varp:vec_sat(Vp, [Xi,Yi,Zi]),
					
    Bs = [binding(Vp, Var) || Var <- [X,Y,Z,A,B]],
    ?dbg0("~p\n", [Bs]),
    "X" = proplists:get_value("A", Bs),
    "Y" = proplists:get_value("B", Bs),
    u = proplists:get_value("X", Bs),
    u = proplists:get_value("Y", Bs),
    u = proplists:get_value("Z", Bs),
    ok.
    
binding(Vp, X={p,_,_}) ->
    XSym = varp_ast:var_term(X),
    case varp:find_symbol(Vp, XSym) of
	Xi when is_integer(Xi) ->
	    XName = format_symbol(false, XSym),
	    case varp:bound(Vp,Xi) of
		true -> {XName, t};
		false -> {XName, f};
		undefined -> {XName, u};
		Yi ->
		    case varp:variable_info(Vp, abs(Yi), symbol) of
			[{Y,_}] ->
			    YName = format_symbol(Yi < 0, Y),
			    {XName, YName}
		    end
	    end
    end.

format_symbol(Sym) ->
    format_symbol(false, Sym).

format_symbol(false, Sym) ->
    lists:flatten(varp_formula:format_internal_symbol(Sym));
format_symbol(true, Sym) ->
    [$! | lists:flatten(varp_formula:format_internal_symbol(Sym))].

sat(Formula, ExpectedModels) ->
    sat_(Formula, ExpectedModels, backtrack).
%%	andalso 
%%    sat_(Formula, ExpectedModels, backjump).

sat_(Formula, ExpectedModels, Method) ->
    application:start(varp),
    Options = [{print,false}],
    Do = [{satisfy,[]}, {Method,[{max,0}]}],
    GOpts = varp:load_option_list(Options),
    GDo = varp:parse_do(Do),
    case varp:do_run(GDo,Formula,GOpts) of
	{?DONE,Ms0,_Bs1} ->
	    Ms = [int_model(Mi) || Mi <- Ms0],
	    %% io:format("Ms = ~w\n", [Ms]),
	    lists:sort(Ms) == lists:sort(ExpectedModels);
	{?INCONSISTENT,Ms,_Bs1} ->
	    Ms == [];
	Res ->
	    io:format("Res=~w\n", [Res]),
	    false
    end.

%% translate Model so that int vectors are translated to integers
int_model([{X,{uint,Vec}} | Ms]) ->
    [{X,list_to_integer(tuple_to_list(Vec), 2)} | int_model(Ms)];
int_model([{X,{int,Vec}} | Ms]) ->
    U = list_to_integer(tuple_to_list(Vec), 2),
    V = if element(1,Vec) =:= $1 -> %% signed
		-(((bnot U) band ((1 bsl tuple_size(Vec))-1))+1);
	   true ->
		U
	end,
    [{X,V} | int_model(Ms)];
int_model([{X,{bit,Vec}} | Ms]) ->
    [{X,Vec} | int_model(Ms)];
int_model([ M | Ms]) ->
    io:format("did not match ~w\n", [M]),
    [M | int_model(Ms)];
int_model([]) ->
    [].
