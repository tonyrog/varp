%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2019, Tony Rogvall
%%% @doc
%%%    Test of varp_nif
%%% @end
%%% Created : 14 Mar 2019 by Tony Rogvall <tony@rogvall.se>

-module(varp_nif_test).

-compile(export_all).

-export([all/0]).
-export([bench/0, bench/1]).
-export([bench0/0, bench0/1]).
-export([bench_purge/0, bench_purge/1, bench_purge/2]).

-include("varp.hrl").

%% -define(verbose(F,A), ok).
-define(verbose(F,A), io:format((F),(A))).

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
	  [test0, test1, test2, test3,
	   symbols, clause_simplify,
	   bcp2, bcp3, bcp4, bcp_turbo1,
	   clause_bcp, clause_learn_d1, clause_learn_a1,
	   watch_1,
	   %% mark intersect
	   intersect1, intersect2, intersect_var0,
	   intersect_var1, intersect_var2,
	   
	   %% order checks
	   order_identity, order_degree,
	   order_rank, order_first,
	   order_last,
	   order_first_and_last,
	   order_random,
	   %% uorder
	   uorder_basic,
	   uorder_bump,
	   uorder_bt,
	   
	   subst0a, subst0b, subst0c, subst0d, 
	   subst1, subst2, subst3, subst4, subst5, subst6,
	   cnf_install,
	   cnf_delete_sort,
	   cnf_sort_offset_delete,
	   decide1,
	   
	   %% partial eval
	   build_all,
	   build_any
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

bindings1() ->
    V = varp_nif:new(#{}),
    X1 = var(V),
    X2 = var(V),
    X3 = var(V),
    X4 = var(V),
    X5 = var(V),
    X6 = var(V),

    clause(V, [-X1, X3]),
    clause(V, [-X1,-X2]),
    varp_nif:push(V),
    varp_nif:bind(V, X1),
    true = varp_nif:bcp(V),

    clause(V, [X4, -X6]),
    clause(V, [X4, X5]),
    varp_nif:push(V),
    varp_nif:bind(V, -X4),
    true = varp_nif:bcp(V),

    %% FIXME tests are deependent on clause order!!
    Match1a = [X1,-X2,X3],
    Match1a = varp:get_bindings_list(V, 1),
    Match1b = [X3,-X2,X1],
    Match1b = varp:get_bindings_list(V, 1, true),

    Match2a = [-X4,X5,-X6],
    Match2a = varp:get_bindings_list(V, 2),
    Match2b = [-X6,X5,-X4],
    Match2b = varp:get_bindings_list(V, 2, true),
    ok.

test0() ->
    V = varp_nif:new(#{}),
    X1 = var(V),
    X1 = 1,
    {X2,X7} = varp_nif:add_variables(V, 6),
    X2 = 2,
    X7 = 7,
    ok.

test1() ->
    V = varp_nif:new(#{}),
    X1 = var(V),
    X2 = var(V),
    X3 = var(V),

    Ls0 = lists:usort([X1, X2, X3]),
    CL0 = Ls0,
    ?verbose("CL0=~w\n", [CL0]),
    C0 = clause(V, Ls0),
    Ls0 = get_clause(V, C0),
    
    Ls1 = lists:usort([X1,-X2,X3]),
    CL1 = Ls1,
    ?verbose("CL1=~w\n", [CL1]),
    C1 = clause(V, Ls1),
    Ls1 = get_clause(V, C1),


    Ls2 = lists:usort([-X1,X2,-X3]),
    CL2 = list_to_tuple(Ls2),
    ?verbose("CL2=~w\n", [CL2]),
    C2 = clause(V, CL2),
    Ls2 = get_clause(V, C2),
    ok.

test1_gamma() ->
    V = varp_nif:new(#{}),
    X1 = var(V),
    X2 = var(V),
    X3 = var(V),
    Ls0 = lists:usort([X1, X2, X3]),
    C0 = clause(V, Ls0, gamma),
    ?verbose("C0=~w\n", [C0]),
    Ls0 = get_clause(V, C0),
    ?verbose("Ls0=~w\n", [Ls0]),
    
    Ls1 = lists:usort([X1,-X2,X3]),
    C1 = clause(V, Ls1),
    ?verbose("C0=~w\n", [C1]),
    Ls1 = get_clause(V, C1),
    ?verbose("Ls0=~w\n", [Ls1]),
    ok.
    
test2() ->
    V = varp_nif:new(#{}),
    X1 = var(V),
    X2 = var(V),
    X3 = var(V),
    X4 = var(V),
    
    C0 = clause(V, [X1, X2, X3]),
    C1 = clause(V, [X2, X3, X4]),

    [X1, X2, X3] = get_clause(V, C0),
    [X2, X3, X4] = get_clause(V, C1),
    ok.

%%
%% Test clause / queue 
%%    
test3() ->
    V = varp_nif:new(#{xref=>true}),
    X1 = var(V),
    X2 = var(V),
    X3 = var(V),
    X4 = var(V),
    X5 = var(V),
    X6 = var(V),
    X7 = var(V),

    C0 = clause(V, [X1, X2, X3]),
    C1 = clause(V, [X2, X3, X4]),
    C2 = clause(V, [X3, X4, X5, X6]),
    C3 = clause(V, [X5, X6, X7]),

    [X1,X2,X3] = get_clause(V, C0),
    [X2,X3,X4] = get_clause(V, C1),
    [X3,X4,X5,X6] = get_clause(V, C2),
    [X5,X6,X7] = get_clause(V, C3),

    true = lists:sort([C0]) =:= lists:sort(varp:get_clauses(V, X1)),

    true = lists:sort([C0,C1]) =:= lists:sort(varp:get_clauses(V, X2)),
    true = lists:sort([C0,C1,C2]) =:= lists:sort(varp:get_clauses(V, X3)),
    true = lists:sort([C1,C2]) =:= lists:sort(varp:get_clauses(V, X4)),
    true = lists:sort([C2,C3]) =:= lists:sort(varp:get_clauses(V, X5)),
    true = lists:sort([C2,C3]) =:= lists:sort(varp:get_clauses(V, X6)),
    true = lists:sort([C3]) =:= lists:sort(varp:get_clauses(V, X7)),

    ?verbose("X5 clauses = ~p\n", [varp:get_clauses(V, X5)]),
    ?verbose("X6 clauses = ~p\n", [varp:get_clauses(V, X6)]),
    ?verbose("X7 clauses = ~p\n", [varp:get_clauses(V, X7)]),

    true = varp_nif:bcp(V),
    varp_nif:push(V),
    true = varp_nif:bind(V, X2),
    true = varp_nif:bind(V, X3),
    {varp:get_bindings_list(V, 1), varp:get_number_of_clauses(V)}.

symbols() ->
    V = varp_nif:new(#{}),
    X1 = var(V),
    {X2,X7} = varp_nif:add_variables(V, 6),
    ok = varp_nif:add_symbol(V, X1, "X1"),
    ok = varp_nif:add_symbol(V, lists:seq(X2,X7), "X27"),
    X1 = varp_nif:find_symbol(V, "X1"),
    [X2,_X3,_X4,_X5,_X6,X7] = varp_nif:find_symbol(V, "X27"),
    ok.

symbol_as_uint(V, Sym) ->
    b2u([case varp_nif:value(V,X) of
	     ?T -> 1;
	     ?F -> 0
	 end || X <- varp_nif:find_symbol(V, Sym)]).

b2u(Ds) ->
    b2u(Ds,0,0).

b2i(Ds) ->
    U = b2u(Ds,0,0),
    N = length(Ds),
    (1 bsl (N-1)) - U.

b2u([D|Ds],Shift,Sum) ->
    b2u(Ds,Shift+1,(D bsl Shift)+Sum);
b2u([],_,Sum) ->
    Sum.


%% Test all clause simplifications
clause_simplify() ->
    V = varp_nif:new(#{}),
    X1 = var(V),
    X2 = var(V),
    X3 = var(V),
    X4 = var(V),
    X5 = var(V),
    C0 = clause(V, [X2,X3,X4,X5]),
    C1 = clause(V, [X5,X4,X3,X2]),
    C20 = clause(V, [X1,X1,X1,X1,X1]),
    C23 = clause(V, [X2,X3,X3,X3,X2]),
    L3 = [X2,X3,X2,X3,X4,?F],
    ?verbose("L3 = ~w\n", [L3]),
    C3 = clause(V, L3),
    C4 = clause(V, [X2,X3,X2,X3,X4]),
    C5 = clause(V, [X2,?T,X3,?F,X4,?T,X4,?T, X5,?F]),
    C6 = clause(V, [X2,?T,X3,?F,-X3,?T,X3,?T,-X3,?F,X4]),

    ?verbose("C3=~w, C4=~w\n", [C3,C4]),

    [X2,X3,X4,X5] = get_clause(V, C0),
    [X2,X3,X4,X5] = get_clause(V, C1),
    C20 = true,
    %% [X2] = get_clause(V, C2),
    [X2,X3] = get_clause(V, C23),
    [X2,X3,X4] = get_clause(V, C3),
    [X2,X3,X4] = get_clause(V, C4),
    C5 = true,
    C6 = true,
    ok.

bcp2() ->
    V = varp_nif:new(#{}),
    X = var(V, <<"X">>),
    Y = var(V, <<"Y">>),
    clause(V, [X, Y]),

    [Y] = eval_bindings(V, [-X]),
    [X] = eval_bindings(V, [-Y]),
    [] = eval_bindings(V, [X]),
    [] = eval_bindings(V, [Y]),
    ok.

bcp3() ->
    V = varp_nif:new(#{}),
    X = var(V, <<"X">>),
    Y = var(V, <<"Y">>),
    Z = var(V, <<"Z">>),
    _Cix = clause(V, [X, Y, Z]),

    [Z] = eval_bindings(V, [-X,-Y]),
    [X] = eval_bindings(V, [-Y,-Z]),
    [Y] = eval_bindings(V, [-Z,-X]),
    ok.

bcp4() ->
    V = varp_nif:new(#{}),
    X = var(V, <<"X">>),
    Y = var(V, <<"Y">>),
    Z = var(V, <<"Z">>),
    T = var(V, <<"T">>),
    _Cix = clause(V, [X, Y, Z, T]),

    [T] = eval_bindings(V, [-X,-Y,-Z]),
    [X] = eval_bindings(V, [-Y,-Z,-T]),
    [Y] = eval_bindings(V, [-X,-Z,-T]),
    [Z] = eval_bindings(V, [-X,-Y,-T]),

    ok.

vbcp() ->
    V = varp_nif:new(#{}),
    X1 = var(V, <<"X1">>),
    X2 = var(V, <<"X2">>),
    X3 = var(V, <<"X3">>),
    X4 = var(V, <<"X4">>),
    X5 = var(V, <<"X5">>),
    X6 = var(V, <<"X6">>),
    _ = clause(V, [-X1, X2]),
    _ = clause(V, [-X3, X4]),
    _ = clause(V, [-X4, X5]),
    _ = clause(V, [-X5, X6]),

    L = varp_nif:push(V),
    {2,X3} = varp_nif:vbcp(V, [X1, X3, -X4]),
    varp_nif:pop(V, L),

    L = varp_nif:push(V),
    {3,X3} = varp_nif:vbcp(V, [X5, X1, X3, -X4, X6]),
    varp_nif:pop(V, L),

    L = varp_nif:push(V),
    true = varp_nif:vbcp(V, [X1, X3]),
    varp_nif:pop(V, L),

    L = varp_nif:push(V),
    varp_nif:bind(V, -X3),
    {2,X3} = varp_nif:vbcp(V, [X1, X3, -X4], true),
    varp_nif:pop(V, L).
    
    

bcp_turbo1() ->
    V = varp_nif:new(#{xref=>true}),
    X = var(V, <<"X">>),
    Y = var(V, <<"Y">>),
    Y1 = var(V, <<"Y1">>),
    Y2 = var(V, <<"Y2">>),
    Y3 = var(V, <<"Y3">>),
    A  = var(V, <<"A">>),
    B  = var(V, <<"B">>),
    Z1 = var(V, <<"Z1">>),
    Z2 = var(V, <<"Z2">>),
    Z3 = var(V, <<"Z3">>),

    clause(V, [-X,A]),
    clause(V, [-X,B]),
    clause(V, [-A,Y1]),
    clause(V, [-B,Y2]),
    clause(V, [-A,-B,Y3]),
    clause(V, [X, Z1, Y1]),
    clause(V, [X, Z2, Y2]),
    clause(V, [X, Z3, Y3]),
    clause(V, [Y, Z1, Y1]),
    clause(V, [Y, Z2, Y2]),
    clause(V, [Y, Z3, Y3]),

    varp_nif:push(V),
    varp_nif:bind(V, X),  %% X=1
    turbo = varp_nif:bcp(V, [X]),
    turbo = varp_nif:bcp(V, [Y]),
    {turbo,[Y,X]} = varp_nif:bcp(V, [X,Y], true),
    ok.

bcp_add() ->
    V = varp_nif:new(#{}),
    X = var(V, <<"X">>),
    Y = var(V, <<"Y">>),
    Z = var(V, <<"Z">>),
    varp_nif:push(V),
    varp_nif:bind(V, -Y),
    _Cix1 = clause(V, [X, Y, Z]),
    varp_nif:pop(V),
    varp_nif:bind(V, -X),
    true = varp_nif:bcp(V),
    _Cix2 = clause(V, [X, -Z]),
    true = varp_nif:bcp(V),
    Match = [-X,-Z,Y],
    Match = varp:get_bindings_list(V, 0),
    %% dump(V).
    ok.

%% saturate test where first bcp is missing
sat_no_bcp() ->
    Vp = varp_nif:new(#{}),
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
    Bs = saturate_var(Vp,  varp_nif:find_symbol(Vp,{"X1",[]})),
    install_bindings(Vp, Bs),
    saturate_lap(Vp).

saturate_lap(Vp) ->
    saturate_lap(Vp, varp_nif:next_unbound(Vp)).

saturate_lap(_Vp, false) ->
    true;
saturate_lap(Vp, X) ->
    io:format("saturate var ~w\n", [X]),
    case saturate_var(Vp, X) of
	false -> 
	    false;
	Bs ->
	    install_bindings(Vp, Bs),
	    saturate_lap(Vp, varp_nif:next_unbound(Vp, X))
    end.

install_bindings(_Vp, {}) ->
    ok;
install_bindings(Vp, Bs) ->
    varp_nif:pop(Vp, 0),
    lists:foreach(
      fun(A) when is_integer(A) ->
	      io:format("bind ~w\n", [A]),
	      varp_nif:bind(Vp, A);
	 ({A,B}) ->
	      io:format("subst ~w / ~w\n", [A, B]),
	      varp_nif:subst(Vp, A, B)
      end, tuple_to_list(Bs)).


%% saturate variable x return bindings or False
saturate_var(Vp, X) ->
    case l_eval(Vp, X) of
	true ->
	    varp_nif:mark(Vp, 2),
	    l_undo(Vp),
	    case l_eval(Vp, -X) of
		true ->
		    Bs = varp_nif:intersect_var(Vp, X, 2, true),
		    varp_nif:unmark(Vp),
		    l_undo(Vp),
		    Bs;
		false ->
		    varp_nif:mark(Vp, 1),
		    Bs = varp_nif:get_marked(Vp, true),
		    varp_nif:unmark(Vp),
		    l_undo(Vp),
		    Bs
	    end;
	false ->
	    l_undo(Vp),
	    case l_eval(Vp, -X) of
		true ->
		    Bs = varp_nif:get_bindings(Vp, 2),
		    l_undo(Vp),
		    Bs;
		false ->
		    l_undo(Vp),
		    false
	    end
    end.

l_eval(Vp, X) ->
    varp_nif:push(Vp),
    case varp_nif:bind(Vp, X) of
	true ->
	    varp_nif:push(Vp),
	    varp_nif:bcp(Vp);
	false ->
	    false
    end.

l_undo(Vp) ->
    varp_nif:pop(Vp),
    varp_nif:pop(Vp).
	      
%% Test eval
clause_bcp() ->
    V = varp_nif:new(#{}),
    X1 = var(V),
    X2 = var(V),
    X3 = var(V),
    X4 = var(V),

    undefined = varp_nif:value(V, X1),
    undefined = varp_nif:value(V, X2),
    undefined = varp_nif:value(V, X3),
    undefined = varp_nif:value(V, X4),

    varp_nif:push(V),
    _C0 = clause(V, [X1, ?F, ?F]),
    _C1 = clause(V, [X2, ?T, ?T, ?T]),
    _C2 = clause(V, [-X3, ?F, ?F, ?F]),
    _C3 = clause(V, [X4, ?F, ?T, ?F, ?T]),
    %% ?verbose("clause_bcp: clauses=~p\n", [[_C0,_C1,_C2,_C3]]),
    %% print_clauses(V),

    true = varp_nif:bcp(V),

    V1 = varp_nif:value(V, X1),
    true = V1 =:= ?T,

    V2 = varp_nif:value(V, X2),
    true = V2 =:= undefined,

    V3 = varp_nif:value(V, X3),
    true = V3 =:= ?F,

    V4 = varp_nif:value(V, X4),
    true = V4 =:= undefined,

    true.

%% 
%% add clause with bindings
%%
or_bcp_bindings() ->
    V = varp_nif:new(#{}),
    X1 = var(V),
    X2 = var(V),
    X3 = var(V),
    X4 = var(V),

    varp_nif:push(V),
    clause(V, [-X1, -X2, -X3]),
    clause(V, [-X1, -X2,  X4]),
    clause(V, [-X1,  X2, -X3]),
    clause(V, [-X1,  X2,  X3]),
    ?verbose("Bindings@0 = ~w\n", [varp_nif:get_bindings(V,0)]),
    ?verbose("Bindings@1 = ~w\n", [varp_nif:get_bindings(V,1)]),
    ?verbose("watched = ~w\n", [get_watched(V)]),
    
    %% print_clauses(V),
    ?verbose("2/1\n", []),
    varp_nif:bind(V, X1),
    true = varp_nif:bcp(V),
    ?verbose("Bindings@1 = ~w\n", [varp_nif:get_bindings(V,1)]),
    ?verbose("watched = ~w\n", [get_watched(V)]),
    %% print_clauses(V),

    varp_nif:push(V),
    clause(V, [-X1,  X2,  X3, -X4]),
    ?verbose("watched = ~w\n", [get_watched(V)]),
    ?verbose("3/1\n", []),
    varp_nif:bind(V, X2),
    true = varp_nif:bcp(V),
    ?verbose("bindings@2 = ~w\n", [varp_nif:get_bindings(V,2)]),
    ?verbose("bindings@1 = ~w\n", [varp_nif:get_bindings(V,1)]),
    ?verbose("bindings@0 = ~w\n", [varp_nif:get_bindings(V,0)]),
    ?verbose("watched = ~w\n", [get_watched(V)]),
    %% print_clauses(V),

    ?verbose("undo 2\n", []),
    varp_nif:pop(V, 2),
    ?verbose("bindings@2 = ~w\n", [varp_nif:get_bindings(V,2)]),
    ?verbose("bindings@1 = ~w\n", [varp_nif:get_bindings(V,1)]),
    ?verbose("bindings@0 = ~w\n", [varp_nif:get_bindings(V,0)]),
    ?verbose("watched = ~w\n", [get_watched(V)]),
    %% print_clauses(V),

    ?verbose("undo 1\n", []),
    varp_nif:pop(V, 1),
    ?verbose("bindings@2 = ~w\n", [varp_nif:get_bindings(V,2)]),
    ?verbose("bindings@1 = ~w\n", [varp_nif:get_bindings(V,1)]),
    ?verbose("bindings@0 = ~w\n", [varp_nif:get_bindings(V,0)]),
    ?verbose("watched = ~w\n", [get_watched(V)]),
    %% print_clauses(V),
    ok.

%% pigeon=3
p3() ->
    V = varp_nif:new(#{}),
    X1 = var(V, <<"P(1,1)">>),
    X2 = var(V, <<"P(1,2)">>),
    X3 = var(V, <<"P(2,1)">>),
    X4 = var(V, <<"P(2,2)">>),
    X5 = var(V, <<"P(3,1)">>),
    X6 = var(V, <<"P(3,2)">>),
    clause(V, [X1,X2]),
    clause(V, [X3, X4]),
    clause(V, [X5, X6]),
    clause(V, [-X1, -X3]),
    clause(V, [-X1, -X5]),
    clause(V, [-X3, -X5]),
    clause(V, [-X2, -X4]),
    clause(V, [-X2, -X6]),
    clause(V, [-X4, -X6]),
    V.

%% pigeon=4
p4() ->
    V = varp_nif:new(#{}),
    X1 = var(V, <<"P(1,1)">>),
    X2 = var(V, <<"P(1,2)">>),
    X3 = var(V, <<"P(1,3)">>),
    X4 = var(V, <<"P(2,1)">>),
    X5 = var(V, <<"P(2,2)">>),
    X6 = var(V, <<"P(2,3)">>),
    X7 = var(V, <<"P(3,1)">>),
    X8 = var(V, <<"P(3,2)">>),
    X9 = var(V, <<"P(3,3)">>),
    X10 = var(V, <<"P(4,1)">>),
    X11 = var(V, <<"P(4,2)">>),
    X12 = var(V, <<"P(4,3)">>),

    clause(V, [X1,X2,X3]),
    clause(V, [X4,X5,X6]),
    clause(V, [X7,X8,X9]),
    clause(V, [X10,X11,X12]),
    clause(V, [-X1,-X4]),
    clause(V, [-X1,-X7]),
    clause(V, [-X1,-X10]),
    clause(V, [-X4,-X7]),
    clause(V, [-X4,-X10]),
    clause(V, [-X7,-X10]),
    clause(V, [-X2,-X5]),
    clause(V, [-X2,-X8]),
    clause(V, [-X2,-X11]),
    clause(V, [-X5,-X8]),
    clause(V, [-X5,-X11]),
    clause(V, [-X8,-X11]),
    clause(V, [-X3,-X6]),
    clause(V, [-X3,-X9]),
    clause(V, [-X3,-X12]),
    clause(V, [-X6,-X9]),
    clause(V, [-X6,-X12]),
    clause(V, [-X9,-X12]),
    V.

nbcp_p3() ->
    P3 = p3(),
    varp_nif:push(P3),
    false = varp_nif:nbcp(P3),
    _Bn1 = varp:get_all_bindings(P3),
    ?verbose("bindings = ~w\n", [_Bn1]),
    varp_nif:undo(P3),
    false = varp_nif:nbcp(P3),
    _Bn2 = varp:get_all_bindings(P3),
    ?verbose("bindings = ~w\n", [_Bn2]),
    varp_nif:undo(P3),
    _BnX = varp:get_all_bindings(P3),
    ?verbose("bindings = ~w\n", [_BnX]),
    ok.

nbcp_p4() ->
    P4 = p4(),
    ok = symlist_sort_first(P4,
			    [<<"P(1,2)">>,
			     <<"P(2,1)">>,
			     <<"P(2,3)">>,
			     <<"P(3,2)">>,
			     <<"P(4,1)">>,
			     <<"P(4,3)">>,
			     <<"P(1,1)">>,
			     <<"P(1,3)">>,
			     <<"P(2,2)">>,
			     <<"P(3,1)">>,
			     <<"P(3,3)">>,
			     <<"P(4,2)">>]),
    varp_nif:push(P4),
    nbcp_loop(P4).

symlist_sort_first(V, SymList) ->
    varp_nif:order_first(V, [varp_nif:find_symbol(V, Sym) || Sym <- SymList]).

nbcp_loop(V) ->
    false = varp_nif:nbcp(V),
    _Bs = varp:get_all_bindings(V),
    ?verbose("bindings = ~w\n", [_Bs]),
    case varp_nif:undo(V) of
	false ->
	    ?verbose("bcp_count = ~w\n", [varp_nif:info(V, bcp_counter)]),
	    contradiction;
	true ->
	    nbcp_loop(V)
    end.
    
order_install() ->
    V = varp_nif:new(#{}),
    X1 = var(V, <<"X1">>),
    X2 = var(V, <<"X2">>),
    X3 = var(V, <<"X3">>),
    X4 = var(V, <<"X4">>),
    X5 = var(V, <<"X5">>),
    X6 = var(V, <<"X6">>),
    Y1 = var(V),
    Y2 = var(V),
    Y3 = var(V),

    _Z0 = clause(V, [Y2, Y3], ?GAMMA),
    _Z1 = clause(V, [Y2, -Y3], ?GAMMA),
    _C0 = clause(V, [X1, X2, X3, X4, X5, X6, Y1], ?GAMMA),
    _C1 = clause(V, [    X2, X3, X4, X5, X6, Y1], ?GAMMA),
    _C2 = clause(V, [        X3, X4, X5, X6, Y1], ?GAMMA),
    _C3 = clause(V, [            X4, X5, X6, Y1], ?GAMMA),
    _C4 = clause(V, [                X5, X6, Y1], ?GAMMA),
    _C5 = clause(V, [                    X6, Y1], ?GAMMA),
    varp_nif:bind(V, Y1),
    varp_nif:bind(V, Y2),
    varp_nif:bind(V, Y3),
    {V, [X1,X2,X3,X4,X5,X6]}.


order_identity() ->    
    {V, [X1,X2,X3,X4,X5,X6]} = order_install(),
    ok = varp:order_sort(V, identity),
    [X1, X2, X3, X4, X5, X6] = varp:order_all(V),
    ok.

order_degree() ->
    {V, [X1,X2,X3,X4,X5,X6]} = order_install(),
    %% d(X1) = 1
    %% d(X2) = 2
    %% d(X3) = 3
    %% d(X4) = 4
    %% d(X5) = 5
    %% d(X6) = 6

    ok = varp:order_sort(V, '-degree'),
    [X6, X5, X4, X3, X2, X1] = varp:order_all(V),

    ok = varp:order_sort(V, '+degree'),
    [X1, X2, X3, X4, X5, X6] = varp:order_all(V),
    ok.

order_rank() ->
    {V, [X1,X2,X3,X4,X5,X6]} = order_install(),
    %% r(X1) = 1/7,
    %% r(X2) = 1/7+1/6
    %% r(X3) = 1/7+1/6+1/5
    %% r(X4) = 1/7+1/6+1/5+1/4
    %% r(X5) = 1/7+1/6+1/5+1/4+1/3
    %% r(X6) = 1/7+1/6+1/5+1/4+1/3+1/2

    ok = varp:order_sort(V, '-rank'),
    [X6, X5, X4, X3, X2, X1] = varp:order_all(V),

    ok = varp:order_sort(V, '+rank'),
    [X1, X2, X3, X4, X5, X6] = varp:order_all(V),
    ok.

order_random() ->
    {V, [X1,X2,X3,X4,X5,X6]} = order_install(),    
    ok = varp_nif:order_sort(V, '=random', undefined, 1001),
    [X4,X5,X3,X6,X1,X2] = varp:order_all(V),
    [-1,-1,-1,1,1,1] = varp:phase_all(V),
    
    %% ?verbose("random,1001, Vs = ~p\n", [Sort1]),

    ok = varp_nif:order_sort(V, '=random', undefined, 1003),
    %% Rand1003 = [-X1,X4,-X6,-X2,X3,X5],
    [X1,X2,X3,X6,X4,X5] = varp:order_all(V),
    [1,-1,1,-1,1,1] = varp:phase_all(V),
    %% ?verbose("random,1003, Vs = ~p\n", [Sort2]),

    %% variants
    ok = varp_nif:order_sort(V, '+random', undefined, 1001),
    [X4,X5,X3,X6,X1,X2] = varp:order_all(V),
    ok = varp_nif:order_sort(V, '+random', 1001),
    [X4,X5,X3,X6,X1,X2] = varp:order_all(V),
    ok = varp_nif:order_sort(V, undefined, '+random', 1001),
    [X4,X5,X3,X6,X1,X2] = varp:order_all(V),

    ok.


order_first() ->
    {V, [X1,X2,X3,X4,X5,X6]} = order_install(),
    %% first check
    ok = varp:order_sort(V, identity, undefined, 0),
    ok = varp_nif:order_first(V, [X5, X6]),
    [X5, X6, X1, X2, X3, X4] = varp:order_all(V),
    ok.

order_last() ->
    {V, [X1,X2,X3,X4,X5,X6]} = order_install(),
    %% last check
    ok = varp_nif:order_sort(V, identity, undefined, 0),
    ok = varp_nif:order_last(V, [X1,X2]),
    [X3, X4, X5, X6, X1, X2] = varp:order_all(V),
    ok.

order_first_and_last() ->
    {V, [X1,X2,X3,X4,X5,X6]} = order_install(),
    %% first & last check
    ok = varp_nif:order_sort(V, identity, undefined, 0),
    ok = varp_nif:order_first(V, [X5, X6]),
    ok = varp_nif:order_last(V, [X1,X2]),
    [X5, X6, X3, X4, X1, X2] = varp:order_all(V),
    ok.


unbound(Vp, X) ->
    X1 = varp_nif:next_unbound(Vp,X),
    %% io:format("Xi = ~w\n", [X1]),
    if X1 =:= false -> [];
       true -> [X1 | unbound(Vp, X1)]
    end.

unbound(Vp) ->
    case varp_nif:next_unbound(Vp) of
	false -> [];
	X0 -> [X0 | unbound(Vp, X0)]
    end.
    
%% check basic variable unbound variables
uorder_basic() ->
    Vp = varp_nif:new(#{}),
    {1,10} = varp_nif:add_variables(Vp, 10),
    [] = unbound(Vp),
    varp_nif:isused(Vp, 5, true),
    [5] = unbound(Vp),
    _ = [varp_nif:isused(Vp, I, true) || I <- lists:seq(1,10)],
    [1,2,3,4,5,6,7,8,9,10] = unbound(Vp),
    varp_nif:bind(Vp, 1),
    varp_nif:bind(Vp, 5),
    [2,3,4,6,7,8,9,10] = unbound(Vp),
    varp_nif:config(Vp, xref, true),
    varp_nif:subst(Vp, 4, 6),
    [2,3,4,7,8,9,10] = unbound(Vp),
    ok.

uorder_bump() ->
    Vp = varp_nif:new(#{vsids=>true}),
    {1,10} = varp_nif:add_variables(Vp, 10, _Atom=true, _Used=true),
    [1,2,3,4,5,6,7,8,9,10] = unbound(Vp),
    varp_nif:bump(Vp, 5, 1),  %% move 5 one step
    [1,2,3,5,4,6,7,8,9,10] = unbound(Vp),
    varp_nif:bump(Vp, 5, 2),  %% move 5 two steps
    [1,5,2,3,4,6,7,8,9,10] = unbound(Vp),
    varp_nif:bump(Vp, 5, 13),  %% test more bumps than needed
    [5,1,2,3,4,6,7,8,9,10] = unbound(Vp),
    %%
    varp_nif:push(Vp),
    varp_nif:bind(Vp, 5),
    varp_nif:bind(Vp, 1),
    varp_nif:bump(Vp, 8, 'next'),  %% 8 should be next
    [8,2,3,4,6,7,9,10] = unbound(Vp),

    varp_nif:pop(Vp, 1),
    varp_nif:pop(Vp),
    [8,5,1,2,3,4,6,7,9,10] = unbound(Vp),

    varp_nif:bump(Vp, 4, 'none'),
    [8,5,1,2,3,4,6,7,9,10] = unbound(Vp),

    varp_nif:bump(Vp, 4, "log2"),
    [8,5,4,1,2,3,6,7,9,10] = unbound(Vp),

    varp_nif:bump(Vp, 6, 'log10'),
    [8,5,4,1,2,6,3,7,9,10] = unbound(Vp),

    varp_nif:push(Vp),
    varp_nif:bind(Vp, 5),
    varp_nif:bind(Vp, 1),
    varp_nif:bind(Vp, 3),
    varp_nif:add_clause(Vp, [-5, -1, -3, 9]),
    true = varp_nif:bcp(Vp),
    true = varp_nif:value(Vp, 9),
    varp_nif:bump(Vp, 9, "rank"),
    varp_nif:pop(Vp),
    [8,5,4,1,9,2,6,3,7,10] = unbound(Vp),    

    ok.

%% simulate backtracking over variables
uorder_bt() ->
    Vp = varp_nif:new(#{vsids=>true, all_used=>true }),
    {1,10} = varp_nif:add_variables(Vp, 10),
    varp_nif:add_clause(Vp, lists:seq(1,10)),  %% all variables are used!
    [1,2,3,4,5,6,7,8,9,10] = unbound(Vp),
    1 = varp_nif:next_unbound(Vp),
    varp_nif:push(Vp),
    varp_nif:bind(Vp, 1), varp_nif:bind(Vp, 3), varp_nif:bind(Vp, 5),
    2 = varp_nif:next_unbound(Vp),
    varp_nif:push(Vp),
    varp_nif:bind(Vp, 2), varp_nif:bind(Vp, 4), varp_nif:bind(Vp, 6),
    7 = varp_nif:next_unbound(Vp),
    varp_nif:push(Vp),
    varp_nif:bind(Vp, 7), varp_nif:bind(Vp, 8), varp_nif:bind(Vp, 9),
    10 = varp_nif:next_unbound(Vp),
    varp_nif:push(Vp),
    varp_nif:bind(Vp, 10),
    false = varp_nif:next_unbound(Vp),
    %% no undo and check
    varp_nif:pop(Vp),
    10 = varp_nif:next_unbound(Vp),
    varp_nif:pop(Vp),
    7 = varp_nif:next_unbound(Vp),
    varp_nif:pop(Vp),
    2 = varp_nif:next_unbound(Vp),
    varp_nif:pop(Vp),
    1 = varp_nif:next_unbound(Vp),
    ok.

subst0a() ->
    V = varp_nif:new(#{xref=>true}),
    A = var(V),
    B = var(V),
    C = var(V),
    X = var(V),
    Y = var(V),

    _C0 = clause(V, [A, B, Y, C]),

    %% print_clauses(V),

    ?verbose(" [~w/~w]\n", [X,Y]),
    varp_nif:subst(V, X, Y),

    ?verbose("clause after\n",[]),
    %% print_clauses(V,true),
    Bs = varp_nif:get_bindings(V,0),
    ?verbose("bindings@0 = ~w\n", [Bs]),
    Bs.

subst0b() ->
    V = varp_nif:new(#{xref=>true}),
    A = var(V),
    B = var(V),
    C = var(V),
    X = var(V),
    Y = var(V),

    _C0 = clause(V, [A, X, B, Y, C]),

    %% print_clauses(V),

    ?verbose(" [~w/~w]\n", [X,Y]),
    varp_nif:subst(V, X, Y),

    ?verbose("clause after\n",[]),
    %% print_clauses(V,true),
    Bs = varp_nif:get_bindings(V,0),
    ?verbose("bindings@0 = ~w\n", [Bs]),
    Bs.

subst0c() ->
    V = varp_nif:new(#{xref=>true}),
    A = var(V),
    B = var(V),
    C = var(V),
    X = var(V),
    Y = var(V),

    _C0 = clause(V, [A, X, B, -Y, C]),

    %% print_clauses(V),

    ?verbose(" [~w/~w]\n", [X,Y]),
    varp_nif:subst(V, X, Y),

    ?verbose("clause after\n",[]),
    %% print_clauses(V,true),
    Bs = varp_nif:get_bindings(V,0),
    ?verbose("bindings@0 = ~w\n", [Bs]),
    Bs.

subst0d() ->
    V = varp_nif:new(#{xref=>true}),
    X = var(V),
    Y = var(V),

    _C0 = clause(V, [X, Y]),

    %% print_clauses(V),

    ?verbose(" [~w/~w]\n", [X,Y]),
    varp_nif:subst(V, X, Y),

    %% ?verbose("clause after\n",[]),
    %% print_clauses(V,true),
    Bs = varp_nif:get_bindings(V,0),
    ?verbose("bindings@0 = ~w\n", [Bs]),
    Bs.
    
%% simply substitute {X2,X3},{X2,-X3} [X4/X3] => {X2,X4},{X2,-X4}
subst1() ->
    V = varp_nif:new(#{xref=>true}), 
    X1 = var(V),
    X2 = var(V),
    X3 = var(V),
    NX3 = -X3,
    C0 = clause(V, [X1,X2]),
    C1 = clause(V, [X1,-X2]),
    ?verbose("\nbefore\n", []),
    %% print_clauses(V),
    varp_nif:subst(V, X3, X2),
    %% ?verbose("clause after\n",[]),
    %% print_clauses(V),
    [X1,X3] = lists:sort(varp_nif:get_clause(V, C0)),
    [NX3,X1] = lists:sort(varp_nif:get_clause(V, C1)),
    ok.

%% simply substitute {X1,X2} [X1/X2] => {X1}
subst2() ->
    V = varp_nif:new(#{xref=>true}), 
    X1 = var(V),
    X2 = var(V),
    C0 = clause(V, [X1,X2]),
    %% ?verbose("\nbefore\n",[]),
    %% print_clauses(V),
    varp_nif:subst(V, X1, X2),
    %% ?verbose("clause after\n",[]),
    %% print_clauses(V),
    ?verbose("raw clause = ~w\n", [varp_nif:get_clause(V, C0, undefined, true)]),
    true = varp_nif:get_clause(V, C0),
    ?T = varp_nif:value(V, X1),
    ok.

subst3() ->
    V = varp_nif:new(#{xref=>true}), 
    X2 = var(V),
    X3 = var(V),
    C0 = clause(V, [-X2,X3]),
    %% ?verbose("\nbefore\n",[]),
    %% print_clauses(V),
    varp_nif:subst(V, -X2, X3),
    %% ?verbose("clause after\n",[]),
    %% print_clauses(V),
    ?verbose("raw clause = ~w\n", [varp_nif:get_clause(V, C0, undefined, true)]),
    true = varp_nif:get_clause(V, C0),
    ?F = varp_nif:value(V, X2),
    ok.
    
subst4() ->
    V = varp_nif:new(#{xref=>true}),
    X1 = var(V),
    X2 = var(V),
    X3 = var(V),
    X4 = var(V),
    X5 = var(V),
    X6 = var(V),
    
    _C0 = clause(V, [-X3,-X2,-X1]),
    _C1 = clause(V, [-X4,-X3,-X2]),
    _C2 = clause(V, [X5, X2, X1]),
    _C3 = clause(V, [X6, X5, X1]),
    _C4 = clause(V, [-X5, X2]),
    _C5 = clause(V, [X3, X1]),
    _C6 = clause(V, [X6, X3, -X1]),
    ?verbose("\nbefore\n",[]),
    print_clauses(V),
    io:format("xref(5) = ~w\n", [varp_nif:literal_info(V, X5, xref)]),
    io:format("xref(2) = ~w\n", [varp_nif:literal_info(V, X2, xref)]),
    io:format("xref(-5) = ~w\n", [varp_nif:literal_info(V, -X5, xref)]),
    io:format("xref(-2) = ~w\n", [varp_nif:literal_info(V, -X2, xref)]),

    ?verbose(" [~w/~w]\n", [X5,X2]),
    varp_nif:subst(V, X5, X2),
    io:format("xref(5) = ~w\n", [varp_nif:literal_info(V, X5, xref)]),
    io:format("xref(2) = ~w\n", [varp_nif:literal_info(V, X2, xref)]),
    io:format("xref(-5) = ~w\n", [varp_nif:literal_info(V, -X5, xref)]),
    io:format("xref(-2) = ~w\n", [varp_nif:literal_info(V, -X2, xref)]),
    io:format("_C0 = ~w\n", [varp_nif:get_clause(V, _C0, undefined, true)]),

    ?verbose("clause after\n",[]),

    %% FIXME: clause 2 has bad watch points should be {0,1} is {0,2}!
    print_clauses(V),

    true = varp_nif:bcp(V),
    Bs = varp_nif:get_bindings(V,0),
    ?verbose("bindings@0 = ~w\n", [Bs]),
    Bs.

subst5() ->
    V = varp_nif:new(#{xref=>true}),
    X2 = var(V),
    X3 = var(V),
    X4 = var(V),
    X5 = var(V),
    X6 = var(V),
    X7 = var(V),

    _C0 = clause(V, [X4,-X3]),
    _C1 = clause(V, [X7,X3]),
    _C2 = clause(V, [X7,-X5]),
    _C3 = clause(V, [X3,X2]),
    _C4 = clause(V, [-X4,X6]),

    %%print_clauses(V),
    %% ?verbose(" [~w/~w]\n", [X7,X3]),
    %% varp_nif:subst(V, X7, X3),
    ?verbose(" [~w/~w]\n", [X3,X7]),
    varp_nif:subst(V, X3, X7),

    %% FIXME: clause 1 has bad watch points should be {0,1} should be {-1,-1}

    %% ?verbose("clause after\n",[]),
    %% print_clauses(V,true),
    true = varp_nif:bcp(V),
    Bs = [X3,X4,X6] = lists:sort(varp:get_bindings_list(V,0)),
    ?verbose("bindings@0 = ~w\n", [Bs]),
    Bs.

subst6() ->
    V = varp_nif:new(#{xref=>true}),
    Y = var(V),
    B = var(V),
    C = var(V),
    X = var(V),
    A = var(V),

    _C0 = clause(V, [A, X, B, Y, C]),
    _C1 = clause(V, [A, -X, B, Y, C]),
    _C2 = clause(V, [A, X, B, -C]),
    _C3 = clause(V, [-A, B, -Y, C]),
    _C4 = clause(V, [-A, B, -X, C]),
    _C5 = clause(V, [A, -Y, B, -X, C]),

    %% print_clauses(V),

    ?verbose(" [~w/~w]\n", [X,Y]),
    varp_nif:subst(V, X, Y),

    %% ?verbose("clause after\n",[]),
    %% print_clauses(V,true),
    ok.

intersect1() ->
    V = varp_nif:new(#{}),
    _Vs = [ var(V) || _ <- lists:seq(1,20)], %% install variables
    varp_nif:mark(V, [1,3,5,7,9,11,13,15,17,19]),
    [1,3,5,7,9,11,13,15,17,19] = get_marked(V),

    varp_nif:intersect_marks(V, [2,4,6,8,10,12,14,16,18,20]),
    [] = get_marked(V),

    varp_nif:mark(V, [1,3,5,7,-8,9,10,11,-12,13,15,17,19]),
    varp_nif:intersect_marks(V, [2,4,6,8,10,12,14,16,18,20]),
    [10] = get_marked(V),

    varp_nif:mark(V, [1,3,5,7,-8,9,-10,11,-12,13,15,17,19]),
    varp_nif:intersect_marks(V, [2,4,6,-8,10,-12,14,16,18,20]),
    [-12,-8] = get_marked(V),

    varp_nif:mark(V, []),
    [] = get_marked(V),
    ok.

intersect2() ->
    V = varp_nif:new(#{}),    
    _Vs = [ var(V) || _ <- lists:seq(1,20)], %% install variables
    varp_nif:mark(V, {1,3,5,7,9,11,13,15,17,19}),
    varp_nif:intersect_marks(V, {2,4,6,8,10,12,14,16,18,20}),
    [] = get_marked(V),

    varp_nif:mark(V, {1,3,5,7,-8,9,10,11,-12,13,15,17,19}),
    varp_nif:intersect_marks(V, {2,4,6,8,10,12,14,16,18,20}),
    [10] = get_marked(V),

    varp_nif:mark(V, {1,3,5,7,-8,9,-10,11,-12,13,15,17,19}),
    varp_nif:intersect_marks(V, {2,4,6,-8,10,-12,14,16,18,20}),
    [-12,-8] =  get_marked(V),

    varp_nif:mark(V, {}),
    [] = get_marked(V),
    ok.

intersect_var0() ->
    X1 = 1, X2 = 2, X3 = 3, X4 = 4, X5 = 5, X6 = 6,
    Bs0 = [-X2,X3,-X4,X5,X6],
    Bs1 = [-X2,X3,X4,-X5],
    Di = [-X2,X3,{X1,X4},{X1,-X5}],
    Di = varp:intersect_var0(dummy, X1, Bs0, Bs1),
    ok.

intersect_var1() ->
    V = varp_nif:new(#{}),
    X1 = var(V),
    X2 = var(V),
    X3 = var(V),
    X4 = var(V),
    X5 = var(V),
    X6 = var(V),
    %% X1 -> {-X2,X3,X4,-X5}
    varp_nif:mark(V, {-X2,X3,X4,-X5}),  
    %% -X1 -> {-X2,X3,-X4,X5,X6}
    Di = {-X2,X3,{X1,X4},{X1,-X5}},
    Di = varp_nif:intersect_var(V, X1, {-X2,X3,-X4,X5,X6}, true),
    ok.

intersect_var2() ->
    V = varp_nif:new(#{}),
    X1 = var(V),
    X2 = var(V),
    X3 = var(V),
    X4 = var(V),
    X5 = var(V),
    X6 = var(V),
    %% X1 -> {-X2,X3,X4,-X5}
    varp_nif:mark(V, {-X2,X3,X4,-X5}),
    varp_nif:push(V),
    %% -X1 -> {-X2,X3,-X4,X5,X6}
    _ = [begin true = varp_nif:bind(V,Xi) end || Xi <- [-X2,X3,-X4,X5,X6]],
    Di = {-X2,X3,{X1,X4},{X1,-X5}},
    Di = varp_nif:intersect_var(V, X1, 1, true),
    ok.
    

watch_1() ->
    V = varp_nif:new(#{}),
    X1 = var(V),
    X2 = var(V),
    X3 = var(V),
    X4 = var(V),
    X5 = var(V),

    C1 = clause(V, [X1,X2,X3,X4,X5]),
    CL = varp:get_clause(V, C1),
    io:format("CL = ~w\n", [CL]),

    %% X4=0
    varp_nif:push(V),
    varp_nif:bind(V, -X4),
    true = varp_nif:bcp(V),

    %% X3=0
    varp_nif:push(V),
    varp_nif:bind(V, -X3),
    true = varp_nif:bcp(V),

    %% X1=0
    varp_nif:push(V),
    varp_nif:bind(V, -X1),
    true = varp_nif:bcp(V),

    %% X5=0
    varp_nif:push(V),
    varp_nif:bind(V, -X5),
    true = varp_nif:bcp(V),

    ?T = varp_nif:value(V, X2),

    C1 = varp_nif:implication_clause(V, X2),
    4 = varp_nif:implication_level(V, X2),

    %% add clauses under the above bindings
    Y3 = -X5, Y2 = -X4, Y1 = -X2, 
    C2 = clause(V, [Y3, Y2, Y1]),
    [Y3, Y2, Y1] = get_clause(V, C2),

    Z3 = X4, Z2 = X3, Z1 = -X1,
    C3 = clause(V, [Z3,Z2,Z1]),
    [Z1,Z2,Z3] = get_clause(V, C3),

    ok.

clone1() ->
    V = varp_nif:new(#{}),
    X1 = var(V, <<"P(1,1)">>),
    X2 = var(V, <<"P(1,2)">>),
    X3 = var(V, <<"P(2,1)">>),
    X4 = var(V, <<"P(2,2)">>),
    X5 = var(V, <<"P(3,1)">>),
    X6 = var(V, <<"P(3,2)">>),

    clause(V, [X1,X2]),
    clause(V, [X3, X4]),
    clause(V, [X5, X6]),
    clause(V, [-X1, -X3]),
    clause(V, [-X1, -X5]),
    clause(V, [-X3, -X5]),
    clause(V, [-X2, -X4]),
    clause(V, [-X2, -X6]),
    clause(V, [-X4, -X6]),

    varp_nif:push(V),
    false = varp_nif:nbcp(V),

    %% print_clauses(V),
    %% dump_variables(V, [X1,X2,X3,X4,X5,X6]),

    W = varp_nif:clone(V),

    varp_nif:push(W),
    false = varp_nif:nbcp(W),

    %% print_clauses(W),
    %% dump_variables(W, [X1,X2,X3,X4,X5,X6]),
    ok.

decide1() ->
    V = varp_nif:new(#{ xref => true,
			init_phase => undefined,
			use_phase => true }),
    X1 = var(V),
    X2 = var(V),
    X3 = var(V),
    X4 = var(V),
    varp_nif:add_clause(V, [X1,X2]),
    varp_nif:add_clause(V, [-X2,X3]),
    varp_nif:add_clause(V, [-X3,-X4]),
    varp_nif:push(V),
    true = varp_nif:bind(V, -X1),
    true = varp_nif:bcp(V),
    ?F = varp_nif:value(V, X1),
    ?T = varp_nif:value(V, X2),
    ?T = varp_nif:value(V, X3),
    ?F = varp_nif:value(V, X4),
    varp_nif:pop(V),

    -1 = varp_nif:variable_info(V, X1, phase),
    1  = varp_nif:variable_info(V, X2, phase),
    1  = varp_nif:variable_info(V, X3, phase),
    -1 = varp_nif:variable_info(V, X4, phase),
    ok.

%% Check that install of variables partial evaluate!
build_all() ->
    Vp = varp_nif:new(#{}),
    X1 = var(Vp, {'P',[1]}),
    X2 = var(Vp, {'P',[2]}),
    X3 = var(Vp, {'P',[3]}),
    X4 = var(Vp, {'P',[4]}),
    X5 = var(Vp, {'P',[5]}),
    
    varp_nif:bind(Vp, -X3),

    F = varp_circuit:all(Vp, [X1,X2,X3,X4,X5]),
    print_clauses(Vp,false,true),
    false = varp_nif:value(Vp, F).

%% Check that install of variables partial evaluate!
build_any() ->
    Vp = varp_nif:new(#{}),
    X1 = var(Vp, {'P',[1]}),
    X2 = var(Vp, {'P',[2]}),
    X3 = var(Vp, {'P',[3]}),
    X4 = var(Vp, {'P',[4]}),
    X5 = var(Vp, {'P',[5]}),
    
    varp_nif:bind(Vp, X3),

    F = varp_circuit:any(Vp, [X1,X2,X3,X4,X5]),
    %% print_clauses(Vp,false,true),
    true = varp_nif:value(Vp, F).
    

%% install and check integrity
cnf_install() ->
    %% install 20 clauses of size 3 with literals -10 .. 10
    cnf_install(20, 3, 10).

cnf_install(N,M,K) ->
    V = varp_nif:new(#{xref=>true,hash=>true}),
    _Vs = [ var(V) || _ <- lists:seq(1,K)], %% install K variables
    CNF = generate_cnf(N, M, K),
    _ = install_cnf(V, CNF, delta),
    verify_xref(V, CNF),
    verify_hash(V, CNF),
    V.    

%% install random 3-CNF
%% remove clause 5
%% sort 
%% check integrity
%%
cnf_delete_sort() ->
    %% install 20 clauses of size 3 with literals -10 .. 10
    cnf_delete_sort(20, 3, 10).

cnf_delete_sort(N, M, K) ->
    V = varp_nif:new(#{xref=>true,hash=>true}),
    _Vs = [ var(V) || _ <- lists:seq(1,K)], %% install K variables
    CNF = generate_cnf(N, M, K),
    _ = install_cnf(V, CNF, delta),
    C5 = lists:nth(5, CNF),
    Ci = varp_nif:find_clause(V, C5),
    varp_nif:del_clause(V, Ci),
    CNF1 = CNF -- [C5],
    varp_nif:clauseset_sort(V, delta),
    verify_xref(V, CNF1),
    verify_hash(V, CNF1),
    V.

%% install random 3-CNF
%% use_clauses
%% sort
%% remove clauses 5..19
%% check integrity
%%
cnf_sort_offset_delete() ->
    %% install 20 clauses of size 3 with literals -10 .. 10
    cnf_sort_offset_delete(20, 3, 10).

cnf_sort_offset_delete(N, M, K) ->
    V = varp_nif:new(#{xref=>true,hash=>true}),
    _Vs = [ var(V) || _ <- lists:seq(1,K)], %% install K variables
    CNF = generate_cnf(N, M, K),
    _ = install_cnf(V, CNF, delta),
    use_clauses(V, delta),
    varp_nif:clauseset_sort(V, delta),
    varp_nif:clauseset_offset(V, delta, 5),
    CiList = clause_list(V, delta),
    CNF1 = lists:foldr(
	     fun(Ci,CNFi) ->
		     Clause = varp_nif:get_clause(V, Ci),
		     CNFi -- [Clause]
	     end, CNF, CiList),
    ok = delete_clauses(V, delta),
    varp_nif:clauseset_offset(V, delta, 0),
    verify_xref(V, CNF1),
    verify_hash(V, CNF1),    
    V.

clause_learn_d1() ->
    V = varp_nif:new(#{}),
    ok = varp_nif:config(V, max_conflicting, 1),
    A = var(V, <<"A">>),  %% 1
    B = var(V, <<"B">>),  %% 2
    C = var(V, <<"C">>),  %% 3
    X = var(V, <<"X">>),  %% 4
    Y = var(V, <<"Y">>),  %% 5
    Z = var(V, <<"Z">>),  %% 6
    clause(V, [A,B]),
    clause(V, [B,C]),
    clause(V, [-A,-X,Y]),  %% Y=1
    clause(V, [-A,X,Z]),
    clause(V, [-A,-Y,Z]),  %% Z=1
    clause(V, [-A,X,-Z]),
    clause(V, [-A,-Y,-Z]), %% Z=0

    %% ?verbose("DUMP1\n"),
    %% dump(V, false),

    %% bind A/1 B/1 C/1 X/1
    true = push_bind_and_bcp(V, A),
    true = push_bind_and_bcp(V, B),
    true = push_bind_and_bcp(V, C),
    false = push_bind_and_bcp(V, X),

    CCix1 = varp_nif:conflicting_clause(V, 0),
    ?verbose("conflicting_clause1: ~w: ~w\n",
	     [CCix1,varp_nif:get_clause(V,CCix1)]),
    Cix1 = varp_nif:conflict(V, 1.0, CCix1),
    Learnt1 = varp_nif:get_clause(V, Cix1),
    ?verbose("learnt_clause: ~w\n", [Learnt1]),
    true = ([-1,-5] == abs_sort(Learnt1)),

    varp_nif:pop(V, 1),

    %% ?verbose("DUMP2\n"),
    %% dump(V, false),

    %% add learnt clause to gamma
    _Gix1 = clause(V, Learnt1, gamma),
    %% ?verbose("DUMP3\n"),
    %% dump(V, false),

    false = varp_nif:bcp(V),
    CCix2 = varp_nif:conflicting_clause(V, 0),
    ?verbose("conflicting_clause2: ~w: ~w\n", 
	     [CCix2,varp_nif:get_clause(V,CCix2)]),
    Cix2 = varp_nif:conflict(V, 1.0, CCix2),
    Learnt2 = varp_nif:get_clause(V, Cix2),
    ?verbose("learnt_clause: ~w\n", [Learnt2]),
    true = ([-1] == abs_sort(Learnt2)),
    varp_nif:pop(V,0),
    true = clause(V, Learnt2, gamma),
    
    true = varp_nif:bcp(V),
    Match = [-A,B],
    Match = varp:get_bindings_list(V, 0),
    ok.


clause_learn_a1() ->
    V = varp_nif:new(#{}),
    ok = varp_nif:config(V, max_conflicting, 1),
    A = var(V, <<"A">>),  %% 1
    B = var(V, <<"B">>),  %% 2
    C = var(V, <<"C">>),  %% 3
    X = var(V, <<"X">>),  %% 4
    Y = var(V, <<"Y">>),  %% 5
    Z = var(V, <<"Z">>),  %% 6
    clause(V, [A,B]),
    clause(V, [B,C]),
    clause(V, [-A,-X,Y]),  %% Y=1
    clause(V, [-A,X,Z]),
    clause(V, [-A,-Y,Z]),  %% Z=1
    clause(V, [-A,X,-Z]),
    clause(V, [-A,-Y,-Z]), %% Z=0

    %% ?verbose("DUMP1\n"),
    %% dump(V, false),

    %% bind A/1 B/1 C/1 X/1
    true = push_bind_and_bcp(V, A),
    true = push_bind_and_bcp(V, B),
    true = push_bind_and_bcp(V, C),
    false = push_bind_and_bcp(V, X),

    CAix1 = varp_nif:conflicting_clause(V, 0),
    Aix1 = varp_nif:conflict(V, 1.0, CAix1),
    Learnt1 = varp_nif:get_clause(V,Aix1),
    ?verbose("conflicting_clause1: ~w: ~w\n",
	      [split_cix(Aix1),Learnt1]),
    ?verbose("learnt_clause: ~w\n", [Learnt1]),
    true = ([-1,-5] == abs_sort(Learnt1)),

    varp_nif:pop(V, 1),

    %% ?verbose("DUMP2\n",[]),
    %% dump(V, false),

    %% add learnt clause to gamma
    {true,_Gix1} = varp_nif:move_clause(V, Aix1, gamma),

    %% ?verbose("DUMP3\n",[]),
    %% dump(V, false),

    false = varp_nif:bcp(V),
    CAix2 = varp_nif:conflicting_clause(V, 0),
    Aix2 = varp_nif:conflict(V, 1.0, CAix2),
    Learnt2 = varp_nif:get_clause(V,Aix2),
    ?verbose("conflicting_clause2: ~w: ~w\n",
	      [split_cix(Aix2),Learnt2]),
    ?verbose("learnt_clause: ~w\n", [Learnt2]),
    true = ([-1] == abs_sort(Learnt2)),

    %% ?verbose("DUMP4\n",[]),
    %% dump(V, false),

    varp_nif:pop(V, 0),
    true = varp_nif:move_clause(V, Aix2, gamma),
    
    true = varp_nif:bcp(V),
    Match = [-A,B],
    Match = varp:get_bindings_list(V, 0),

    %% ?verbose("DUMP5\n",[]),
    %% dump(V, false),
    ok.

%% invert graph (all arrow point backwards)
invert_graph(G) ->
    maps:fold(
      fun(V, Ws, Gi) ->
	      lists:foldl(
		fun(W, Gii) ->
			Rs = maps:get(W,Gii,[]),
			Gii#{ W => [V|Rs] }
		end, Gi, Ws)
      end, #{}, G).

%% build clauses from reverse implicatin graph
implication_clauses(Vp, G) ->
    maps:fold(
      fun(W,Rs,_Acc) ->
	      Ds = [-Di || Di <- Rs],
	      {true,Ci} = varp_nif:add_clause(Vp, Ds++[W]),
	      io:format("add ~w = ~p\n", [Ci, get_sym_clause(Vp, Ci)])
      end, ok, G).

%% build conflict clause from graph!
clause_learn_g1() ->
    clause_learn_g1(local),
    clause_learn_g1(global),
    clause_learn_g1(recursive).
    
clause_learn_g1(Type) ->
    Vp = varp_nif:new(#{ qtype => fifo }),
    [A,B,C,D,E,F,G,H,I,J] = [var(Vp, Name) || 
				Name <- ["A","B","C","D","E",
					 "F","G","H","I","J"]],
    %% implication graph
    Graph = #{A => [E],
	      B => [F],
	      C => [F,G],
	      D => [G],
	      E => [H,I],
	      F => [H,I],
	      G => [I,H],
	      H => [J],
	      I => [-J]
	     },
    RGraph = invert_graph(Graph),
    io:format("Graph=~w\n", [Graph]),
    io:format("RGraph=~w\n", [RGraph]),
    %% build clauses from implication graph
    implication_clauses(Vp, RGraph),
    %% trigger leaf nodes A,B,C,D in this graph
    varp_nif:push(Vp),
    true = varp_nif:bind(Vp, A),
    true = varp_nif:bcp(Vp),
    varp_nif:push(Vp),
    true = varp_nif:bind(Vp, B),
    true = varp_nif:bcp(Vp),
    varp_nif:push(Vp),
    true = varp_nif:bind(Vp, C),
    true = varp_nif:bcp(Vp),
    varp_nif:push(Vp),
    true = varp_nif:bind(Vp, D),
    false = varp_nif:bcp(Vp),
    dump_levels(Vp),

    Dix = varp_nif:conflicting_clause(Vp, 0),
    io:format("conflicting ~w = ~p\n", [Dix,get_sym_clause(Vp, Dix)]),
    CCix = varp_nif:conflicting_clause(Vp, 0),
    Cix = varp_nif:conflict(Vp, 1, CCix),
    io:format("learned clause ~w = ~p\n", 
	      [Cix, get_sym_clause(Vp, Cix)]),
    Len = varp_nif:minimize(Vp, Cix, Type),
    io:format("~s minimize clause ~w[len=~w] = ~p\n", 
	      [Type, Cix, Len, get_sym_clause(Vp, Cix)]),
    ok.


clause_learn_vg1(Type) ->
    Vp = varp_nif:new(#{ qtype => fifo }),
    [A,B,C,D,E,F,G,H,I,J] = [var(Vp, Name) || 
				Name <- ["A","B","C","D","E",
					 "F","G","H","I","J"]],
    %% implication graph
    Graph = #{A => [E],
	      B => [F],
	      C => [F,G],
	      D => [G],
	      E => [H,I],
	      F => [H,I],
	      G => [I,H],
	      H => [J],
	      I => [-J]
	     },
    RGraph = invert_graph(Graph),
    
    implication_clauses(Vp, RGraph), %% build clauses from implication graph
    %% trigger leaf nodes A,B,C,D in this graph
    varp_nif:push(Vp),
    false = varp_nif:vbcp(Vp, [A, B, C, D]),
    dump_levels(Vp),

    Dix = varp_nif:conflicting_clause(Vp, 0),
    io:format("conflicting ~w = ~p\n", [Dix,get_sym_clause(Vp, Dix)]),
    CCix = varp_nif:conflicting_clause(Vp, 0),
    Cix = varp_nif:conflict(Vp, 1, CCix),
    io:format("learned clause ~w = ~p\n", 
	      [Cix, get_sym_clause(Vp, Cix)]),
    Len = varp_nif:minimize(Vp, Cix, Type),
    io:format("~s minimize clause ~w[len=~w] = ~p\n", 
	      [Type, Cix, Len, get_sym_clause(Vp, Cix)]),
    ok.


clause_learn_vg1_1(Type) ->
    Vp = varp_nif:new(#{ qtype => fifo }),
    [A,B,C,D,E,F,G,H,I,J] = [var(Vp, Name) || 
				Name <- ["A","B","C","D","E",
					 "F","G","H","I","J"]],
    %% implication graph
    Graph = #{A => [E],
	      B => [F],
	      C => [F,G],
	      D => [G],
	      E => [H,I],
	      F => [H,I],
	      G => [I,H],
	      H => [J]
%%	      I => [-J]
	     },
    RGraph = invert_graph(Graph),
    
    implication_clauses(Vp, RGraph), %% build clauses from implication graph
    %% trigger leaf nodes A,B,C,D in this graph
    varp_nif:push(Vp),
    {5,Lj} = varp_nif:vbcp(Vp, [A, B, C, -J, D]),
    %% dump all levels
    dump_levels(Vp),

    CCix = varp_nif:implication_clause(Vp, Lj),

    %% Dix = varp_nif:conflicting_clause(Vp, 0),
    io:format("conflicting ~w = ~p\n", [CCix,get_sym_clause(Vp, CCix)]),
    %% CCix = varp_nif:conflicting_clause(Vp, 0),
    Cix = varp_nif:conflict(Vp, 1, CCix),
    io:format("learned clause ~w = ~p\n", 
	      [Cix, get_sym_clause(Vp, Cix)]),
    Len = varp_nif:minimize(Vp, Cix, Type),
    io:format("~s minimize clause ~w[len=~w] = ~p\n", 
	      [Type, Cix, Len, get_sym_clause(Vp, Cix)]),
    ok.





%% example from conflict driven learning
%% V7,V9,V14,15  and level=4 are not used
clause_learn_g2() ->
    clause_learn_g2(local),
    clause_learn_g2(global),
    clause_learn_g2(recursive).
    
clause_learn_g2(Type) ->
    Vp = varp_nif:new(#{ qtype => fifo }),
    [V1,V2,V3,V4,V5,V6,V8,V10,V11,V12,V13,V16,V17,V18,V19] =
	[var(Vp, Name) || 
	    Name <- ["V1","V2","V3","V4","V5","V6","V8","V10",
		     "V11","V12","V13","V16","V17","V18","V19"]],
    %% implication graph
    Graph = #{V1 => [V18],
	      -V2 => [-V10],
	      V3 => [V18,-V18],
	      V4 => [-V10],
	      -V5 => [V18],
	      -V6 => [-V12],
	      V8 => [V1],
	      -V10 => [V1,V3,-V5],
	      V11 => [-V12,V16],
	      -V12 => [-V2],
	      -V13 => [V16],
	      V16 => [-V2],
	      -V17 => [V18],
	      V19 => [-V18]
	     },
    RGraph = invert_graph(Graph),
    implication_clauses(Vp, RGraph),

    %% trigger leaf nodes A,B,C,D in this graph
    varp_nif:push(Vp),
    true = varp_nif:bind(Vp, -V6),
    true = varp_nif:bind(Vp, -V17),
    true = varp_nif:bcp(Vp),
    varp_nif:push(Vp),
    true = varp_nif:bind(Vp, V8),
    true = varp_nif:bind(Vp, -V13),
    true = varp_nif:bcp(Vp),
    varp_nif:push(Vp),
    true = varp_nif:bind(Vp, V4),
    true = varp_nif:bind(Vp, V19),
    true = varp_nif:bcp(Vp),
    varp_nif:push(Vp),
    true = varp_nif:bind(Vp, V11),
    false = varp_nif:bcp(Vp),
    
    CCix = varp_nif:conflicting_clause(Vp, 0),
    io:format("conflicting ~w = ~p\n", [CCix,get_sym_clause(Vp, CCix)]),
    Cix = varp_nif:conflict(Vp, 1, CCix),
    io:format("learned clause ~w = ~p\n", 
	      [Cix, get_sym_clause(Vp, Cix)]),
    Len = varp_nif:minimize(Vp, Cix, Type),
    io:format("~s minimize clause ~w[len=~w] = ~p\n", 
	      [Type, Cix, Len, get_sym_clause(Vp, Cix)]),
    ok.


%% Example from Sorensson & Bier paper
%% Graph:
%%  A => D
%%  B => E
%%  C => D
%%  D => [E, G, T]
%%  E => [H]
%%  F => [G]
%%  G => [H, T]
%%  H => [I, Y]
%%  I => [Y]
%%  K => [L]
%%  L => [S]
%%  R => [S]
%%  S => [T,X]
%%  T => [Y]
%%  X => [Z]
%%  Y => [V]
%%  Z => [-V]

clause_learn_g3() ->
    clause_learn_g3(local),
    clause_learn_g3(global),
    clause_learn_g3(recursive).

clause_learn_g3(Type) ->
    Vp = varp_nif:new(#{ qtype => fifo }),
    [A,B,C,D,E,F,G,H,I,K,L,R,S,T,X,Y,Z,CONFLICT] =
	[var(Vp, Name) || 
	    Name <- ["A","B","C","D","E",
		     "F","G","H","I",
		     "K","L",
		     "R","S","T",
		     "X","Y","Z",
		     "CONFLICT"]],
    %% implication graph
    Graph = 
	#{ A => [D],
	   B => [E],
	   C => [D],
	   D => [E, G, T],
	   E => [H],
	   F => [G],
	   G => [H, T],
	   H => [I, Y],
	   I => [Y],
	   K => [L],
	   L => [S],
	   R => [S],
	   S => [T,X],
	   T => [Y],
	   X => [Z],
	   Y => [CONFLICT],
	   Z => [-CONFLICT] },
    RGraph = invert_graph(Graph),
    implication_clauses(Vp, RGraph),

    %% bind A and B on level 0
    true = varp_nif:bind(Vp, A),
    true = varp_nif:bind(Vp, B),
    %% decide C on level 1 
    0 = varp_nif:push(Vp),  %% push return previous level!!
    true = varp_nif:bind(Vp, C),
    true = varp_nif:bcp(Vp),
    %% decide F on level 2
    1 = varp_nif:push(Vp),
    true = varp_nif:bind(Vp, F),
    true = varp_nif:bcp(Vp),
    %% decide K on level 3
    2 = varp_nif:push(Vp),
    true = varp_nif:bind(Vp, K),
    true = varp_nif:bcp(Vp),
    %% decide R on level 4
    3 = varp_nif:push(Vp),
    true = varp_nif:bind(Vp, R),
    false = varp_nif:bcp(Vp),
    %% CONFLICT should be the conflict
    CCix = varp_nif:conflicting_clause(Vp, 0),
    io:format("conflicting ~w = ~p\n", [CCix,get_sym_clause(Vp, CCix)]),
    Cix = varp_nif:conflict(Vp, 1, CCix),
    io:format("learned clause ~w = ~p\n", 
	      [Cix, get_sym_clause(Vp, Cix)]),
    Len = varp_nif:minimize(Vp, Cix, Type),
    io:format("~s minimize clause ~w[len=~w] = ~p\n", 
	      [Type, Cix, Len, get_sym_clause(Vp, Cix)]),
    ok.
    

implication_depth() ->
    V = varp_nif:new(#{}),
    Y1 = var(V, <<"Y1">>),
    Y2 = var(V, <<"Y2">>),
    Y3 = var(V, <<"Y3">>),
    Y4 = var(V, <<"Y4">>),
    Y5 = var(V, <<"Y5">>),
    Y6 = var(V, <<"Y6">>),
    X  = var(V, <<"X">>),
    clause(V, [-X, Y1]),
    clause(V, [-X, Y2]),
    clause(V, [-Y1,-Y2,Y3]),
    clause(V, [-X,-Y2,Y4]),
    clause(V, [-X,-Y3,Y5]),
    clause(V, [-Y4,-Y5,Y6]),
    true = push_bind_and_bcp(V, X),
    ?T = varp_nif:value(V, Y1),
    ?T = varp_nif:value(V, Y2),
    ?T = varp_nif:value(V, Y3),
    ?T = varp_nif:value(V, Y4),
    ?T = varp_nif:value(V, Y5),
    ?T = varp_nif:value(V, Y6),
    M0 = #{ X => 0 },
    {1, M1} = depth(V, Y1, M0),
    {1, M2} = depth(V, Y2, M1),
    {2, M3} = depth(V, Y3, M2),
    {2, M4} = depth(V, Y4, M3),
    {3, M5} = depth(V, Y5, M4),
    {4, _}  = depth(V, Y6, M5),
    ok.

depth(V, Yi, DepthMap) ->
    Cix = varp_nif:implication_clause(V, Yi),
    Clause = varp_nif:get_clause(V, Cix, Yi),
    Depth = lists:max([maps:get(-Li, DepthMap) || Li <- Clause])+1,
    {Depth, DepthMap#{ Yi => Depth }}.

get_sym_clause(Vp, Cix) ->
    [get_sym_literal(Vp,Li) || Li <- varp_nif:get_clause(Vp, Cix)].

get_sym_literal(Vp, Li) ->
    case varp_nif:variable_info(Vp, Li, symbol) of
	[] -> "?";
	[{S,_}|_] ->
	    Sym = binary_to_list(S),
	    if Li < 0 -> [$!|Sym];
	       true -> Sym
	    end
    end.

get_marked(Vp) ->
    lists:sort(varp_nif:get_marked(Vp, false)).

%% bench0 
bench0() ->
    bench0(20000).

bench0(N) ->
    V = varp_nif:new(#{}),
    T0 = erlang:monotonic_time(),
    ok = bench0_(V,N),
    T1 = erlang:monotonic_time(),
    Time = erlang:convert_time_unit(T1-T0,native,microsecond),
    Ts = Time/1000000,
    N / Ts.

bench0_(_V, 0) ->
    ok;
bench0_(V, I) ->
    varp_nif:noop(V),
    bench0_(V, I-1).
%% 
%% bcp 999 clauses
%% 2021-02-01
%% {literal_integer,true},{literal_size,32},{value_packing,1} => 79064
%% {literal_integer,true},{literal_size,32},{value_packing,1} => 78260
%% 2021-02-01
%% {literal_integer,true},{literal_size,32},{value_packing,1} => 77176
%% 2021-01-25
%% {literal_integer,true},{literal_size,32},{value_packing,1} => 75404
%% {literal_integer,true},{literal_size,32},{value_packing,1} => 74103
%% 2021-01-19
%% {literal_integer,true},{literal_size,32},{value_packing,1} => 62035
%% 2021-01-18
%% {literal_integer,true},{literal_size,32},{value_packing,1} => 55013
%% 2021-01-15
%% {literal_integer,true},{literal_size,32},{value_packing,1} => 54684
%% 2021-01-13
%% {literal_integer,true},{literal_size,32},{value_packing,1} => 51582
%% 2020-11-01?
%% {literal_integer,true},{literal_size,32},{value_packing,1} => 45477
%% {literal_integer,false},{literal_size,64},{value_packing,1} => 34047
%% {literal_integer,false},{literal_size,64},{value_packing,no} => 35276
%% OLD VALUE:
%% 2020-06-01?
%% {literal_integer,true},{literal_size,32},{value_packing,1} => 33412
%%
bench() ->
    bench(20000).

bench(N) ->
    V = bench_cnf_build(),
    T0 = erlang:monotonic_time(),
    Bcp = bench_(V,1,N),
    T1 = erlang:monotonic_time(),
    Time = erlang:convert_time_unit(T1-T0,native,microsecond),
    Ts = Time/1000000,
    ?verbose("BCP/s=~w,"
	      "NUM_CLAUSES=~w,"
	      "LIT_INTEGER=~w,"
	      "LITERAL_SIZE=~w,"
	      "VALUE_PACKING=~w\n",
	      [Bcp/Ts, 
	       varp_nif:info(V, number_of_clauses),
	       varp_nif:info(V, literal_integer),
	       varp_nif:info(V, literal_size),
	       varp_nif:info(V, value_packing)]),
    ?verbose("#DEAD clauses=~w,"
	     "#CONFLICTS=~w,"
	     "#PROPAGATIONS=~w,"
	     "#DECISIONS=~w,"
	     "#BCP=~w"
	     "#CLAUSE-2=~w,"
	     "#CLAUSE-3=~w,"
	     "#CLAUSE-n=~w,"
	     "MAX_LEVEL=~w,"
	     "MIN_LEVEL=~w,"
	     "MAX_BOUND=~w,"
	     "\n",
	     [varp_nif:info(V, clause_d_counter),
	      varp_nif:info(V, conflict_counter),
	      varp_nif:info(V, number_of_propagations),
	      varp_nif:info(V, decision_counter),
	      varp_nif:info(V, bcp_counter),
	      varp_nif:info(V, clause_2_counter),
	      varp_nif:info(V, clause_3_counter),
	      varp_nif:info(V, clause_n_counter),
	      varp_nif:info(V, max_level),
	      varp_nif:info(V, min_level),
	      varp_nif:info(V, max_bound)
	     ]),
    Bcp / Ts.

bench_(V, _X0, 0) ->
    varp_nif:info(V, bcp_counter);
bench_(V, X0, I) ->
    varp_nif:push(V),
    true = varp_nif:bind(V, X0),
    true = varp_nif:bcp(V),
    varp_nif:pop(V),
    bench_(V, X0, I-1).

bench_cnf_build() ->
    bench_install_cnf(bench_cnf()).

bench_cnf_build(N) ->
    bench_install_cnf(bench_cnf(N)).
    
bench_install_cnf(CNF) ->
    V = varp_nif:new(#{}),
    Vs = lists:usort(lists:append([[abs(L) || L <- Ci] || Ci <- CNF])),
    K  = lists:max(Vs),
    _ = [ var(V) || _ <- lists:seq(1,K)], %% install K variables
    install_cnf(V, CNF),
    V.

bench_cnf() ->
    bench_cnf(111).
bench_cnf(N) ->
    bench_var_init(),
    Xs0 = [bench_var()],
    lists:reverse(
      lists:foldl(
	fun(_, CNF0) ->
		Xs1 = [bench_var()|| _ <- lists:seq(1,2)],
		CNF1 = bench_clauses(Xs0, Xs1, CNF0),
		Xs2 = [bench_var()|| _ <- lists:seq(1,3)],
		CNF2 = bench_clauses(Xs1, Xs2, CNF1),
		Xs3 = [bench_var()|| _ <- lists:seq(1,4)],
		CNF3 = bench_clauses(Xs2, Xs3, CNF2),
		CNF3
	end, [], lists:seq(1, N))).

bench_var_init() ->
    put(bench_var_next, 1).

bench_var() ->
    I = get(bench_var_next),
    put(bench_var_next, I+1),
    I.

%% first variable 
bench_clauses([X1],[Y1,Y2],T) ->
    [[Y1,-X1], [Y2,-X1] | T];

bench_clauses([X1,X2],[Y1,Y2,Y3],T) ->
    [[Y1,-X1,-X2],[Y2,-X1,-X2],[Y3,-X1,-X2] | T];

bench_clauses([X1,X2,X3],[Y1,Y2,Y3,Y4], T) ->
    [[Y1,-X1,-X2,-X3],[Y2,-X1,-X2,-X3],
     [Y3,-X1,-X2,-X3],[Y4,-X1,-X2,-X3] | T];

bench_clauses(Xs, Ys, T) ->
    NXs = [-Xi || Xi <- Xs],
    [ [ [Yi | NXs] || Yi <- Ys] | T].

%% benchmark purge 

-define(NCLAUSES, 30000).
-define(NVARS(N), (N div 100)).
-define(MIN_LEN, 30).
-define(MAX_LEN, 50).
-define(KEEP, 0.25).

%% benchmark clause install
bench_install() ->
    bench_install(10, #{}).

bench_install(Opts) when is_map(Opts) ->
    bench_install(10, Opts).
    
bench_install(Loop, Opts) ->
    bench_install_(Loop, Opts).

bench_install_(0, _Opts) ->
    ok;
bench_install_(I, Opts) ->
    Vp = varp_nif:new(#{xref=>maps:get(xref,Opts,false),
			hash=>maps:get(hash,Opts,false)}),
    N = maps:get(nclauses, Opts, ?NCLAUSES),
    V = maps:get(nvars,Opts,?NVARS(N)),
    {1,V} = varp_nif:add_variables(Vp, V),
    N = maps:get(nclauses, Opts, ?NCLAUSES),
    MinLen = maps:get(min_clause_len, Opts, ?MIN_LEN),
    MaxLen = maps:get(max_clause_len, Opts, ?MAX_LEN),
    rand:seed(exsss, 1347),
    Clauses = 
	[make_random_clause(MinLen, MaxLen, V) ||
	    _ <- lists:seq(1, N)],
    T0 = erlang:monotonic_time(),
    lists:foreach(
	fun(Clause) ->
		{true,_Ci} = varp_nif:add_clause(Vp, Clause, 'gamma')
	end, Clauses),
    T1 = erlang:monotonic_time(),    
    Time = erlang:convert_time_unit(T1-T0,native,microsecond),
    io:format("installed ~w clauses in time=~.2fs\n", [N, Time/1000000]),
    bench_install_(I-1, Opts).


bench_purge() ->
    bench_purge(10, #{}).

bench_purge(Opts) when is_map(Opts) ->
    bench_purge(10, Opts).
    
bench_purge(Loop, Opts) ->
    Vp = varp_nif:new(#{xref=>maps:get(xref,Opts,false),
			hash=>maps:get(hash,Opts,false)}),
    N = maps:get(nclauses, Opts, ?NCLAUSES),
    V = maps:get(nvars,Opts,?NVARS(N)),
    {1,V} = varp_nif:add_variables(Vp, V),
    bench_purge_(Vp, Loop, V, Opts).

bench_purge_(_Vp, 0, _V, _Opts) ->
    ok;
bench_purge_(Vp, I, V, Opts) ->
    Size = varp_nif:clauseset_size(Vp, 'gamma'),
    N = maps:get(nclauses, Opts, ?NCLAUSES),
    Fill = N - Size,
    MinLen = maps:get(min_clause_len, Opts, ?MIN_LEN),
    MaxLen = maps:get(max_clause_len, Opts, ?MAX_LEN),
    Keep = maps:get(keep, Opts, ?KEEP),
    install_random_clauses(Vp, Fill, MinLen, MaxLen, V),
    T0 = erlang:monotonic_time(),
    Count = purge(Vp, Keep),
    T1 = erlang:monotonic_time(),    
    Time = erlang:convert_time_unit(T1-T0,native,microsecond),
    io:format("purged ~w in time=~.2fs\n", [Count, Time/1000000]),
    bench_purge_(Vp, I-1, V, Opts).
    
purge(Vp, Keep) ->
    K = if is_float(Keep) ->
		Size = varp_nif:clauseset_size(Vp, 'gamma'),
		trunc(Size*Keep);
	   true  ->
		Keep
	end,
    _Offs = varp_nif:clauseset_offset(Vp, 'gamma', K),
    varp_nif:clauseset_sort(Vp, 'gamma'),
    I = varp_nif:clauseset_first(Vp, 'gamma'),
    Count = purge_loop(Vp, I, 0),
    varp_nif:clauseset_offset(Vp, 'gamma', 0),
    Count.

purge_loop(_Vp, false, Count) ->
    Count;
purge_loop(Vp, I, Count) ->
    varp_nif:del_clause(Vp, I),
    I1 = varp_nif:clauseset_next(Vp, I),
    purge_loop(Vp, I1, Count+1).


install_random_clauses(Vp, 0, _MinLen, _MaxLen, _V) ->
    Vp;
install_random_clauses(Vp, I, MinLen, MaxLen, V) ->
    Ls = make_random_clause(MinLen, MaxLen, V),
    {true,_Ci} = varp_nif:add_clause(Vp, Ls, 'gamma'),
    %% io:format("V=~w, clause=~w\n", [V, Ls]),
    install_random_clauses(Vp, I-1, MinLen, MaxLen, V).

make_random_clause(MinLen, MaxLen, V) ->
    Width = MaxLen - MinLen,
    Len = MinLen + (rand:uniform(Width) - 1),
    make_clause(Len, [], V, sets:new()).

make_clause(0, Ls, _V, _Vs) ->
    Ls;
make_clause(N, Ls, V, Vs) ->
    Vi = V - (rand:uniform(2*V+1)-1),  %% 2V+1, V=5  6 - r(11) 
    if Vi =:= 0 -> 
	    make_clause(N, Ls, V, Vs);
       true ->
	    case sets:is_element(abs(Vi), Vs) of
		true ->
		    make_clause(N, Ls, V, Vs);
		false ->
		    make_clause(N-1, [Vi|Ls], V,
				sets:add_element(abs(Vi),Vs))
	    end
    end.




push_bind_and_bcp(V, X) ->
    varp_nif:push(V),
    varp_nif:bind(V, X) andalso varp_nif:bcp(V).

%% multi bind and eval
eval_bindings(V, Xs) ->
    varp_nif:push(V),
    _ = [(true = varp_nif:bind(V, X)) || X <- Xs ],
    varp_nif:push(V),
    true = varp_nif:bcp(V),
    R = varp:get_bindings_list(V, 2),
    varp_nif:pop(V),
    varp_nif:pop(V),
    R.

%% will have the effect that clause 1 have stamp T1 and clause N have stamp Tn
use_clauses(V, Set) ->
    use_clauses(V, Set, varp_nif:clauseset_first(V, Set)).

use_clauses(_V, _Set, false) ->
    ok;
use_clauses(V, Set, I) ->
    varp_nif:bcp(V),
    use_clauses(V, Set, varp_nif:clauseset_next(V, I)).

%% get list of all clauses
clause_list(V) ->
    clause_list(V, delta).

clause_list(V, Set) ->
    clause_list_(V, Set, varp_nif:clauseset_first(V, Set)).

clause_list_(_V, _Set, false) ->
    [];
clause_list_(V, Set, I) ->
    [I|clause_list_(V, Set, varp_nif:clauseset_next(V, I))].
    

%% delete all clauses (from offset to end)
delete_clauses(V, Set) ->
    delete_clauses(V, Set, varp_nif:clauseset_first(V, Set)).

delete_clauses(_V, _Set, false) ->
    ok;
delete_clauses(V, Set, I) ->
    ?verbose("delete clause ~w\n", [I]),
    ok = varp_nif:del_clause(V, I),
    delete_clauses(V, Set, varp_nif:clauseset_next(V, I)).

random_cnf() ->
    random_cnf(20, 6, 7).

random_cnf(N, M, K) ->
    random_cnf(N, M, K, delta).
random_cnf(N, M, K, Set) ->
    V = varp_nif:new(#{}),
    _Vs = [ var(V) || _ <- lists:seq(1,K)], %% install K variables
    CNF = generate_cnf(N, M, K),
    _ = install_cnf(V, CNF, Set),
    V.

write_cnf(CNF) ->
    io:put_chars(
      [format_preamable(CNF),"\n",
       [[format_clause(C),"\n"] || C <- CNF]]).

format_clause(C) ->
    [[[integer_to_list(L)," "] || L <- C],"0"].

format_preamable(CNF) ->
    M = length(CNF),
    Vs = lists:usort(lists:append([[abs(L) || L <- Ci] || Ci <- CNF])),
    N = length(Vs),
    ["p cnf ", integer_to_list(N), " ", integer_to_list(M)].

install_cnf(V, CNF) ->
    install_cnf(V, CNF, delta).

install_cnf(V, CNF, Set) ->
    lists:foldr(
      fun(Clause,Acc) ->
	      case clause(V, Clause, Set) of
		  false ->
		      %% the clause is contradictory 
		      assert_val(V, Clause, false),
		      [false|Acc];
		  true ->
		      %% the clause is true 
		      %% either evaluate to true or has X -X in the clause
		      assert_val(V, Clause, true),
		      [true|Acc];
		  Ci ->
		      %% check the clause
		      GetClause = varp_nif:get_clause(V, Ci),
		      assert_equal(abs_sort(GetClause), abs_sort(Clause)),
		      [Ci|Acc]
	      end
      end, [], CNF).

assert_val(V, Clause, Value) ->
    case val(V, Clause) of
	Value -> ok;
	_Other -> 
	    ?verbose("assertion failed: eval(~w) ~w =/= ~w\n",
		      [Clause,_Other,Value]),
	    throw(badmatch)
    end.

assert_equal(Value1, Value2) ->
    if Value1 =:= Value2 -> ok;
       true ->
	    ?verbose("assertion failed: get ~w =/= norm ~w\n",
		      [Value1,Value2]),
	    throw(badmatch)
    end.
	    
val(_V, true) ->
    true;
val(V, [Li]) ->
    case varp_nif:value(V, Li) of
	?T -> true;
	?F -> false;
	undefined -> true
    end;
val(V, Ls) ->
    val(V, Ls, false).

val(V, [Li|Ls], Val) ->
    case varp_nif:value(V, Li) of
	?T -> true;
	?F -> val(V, Ls, Val);
	undefined -> val(V,Ls,undefined)
    end;
val(_V, [], Val) -> Val.

%% Verify that we can reach all clauses via xref
verify_xref(V, CNF) ->
    true = varp_nif:info(V, xref),  %% assert we have xref enabled
    DegLs = deg_literal_list(CNF),
    %% check that clauses reached by Ls are in CNF
    lists:foreach(
      fun({Li,Deg}) ->
	      XRefs = varp_nif:get_clauses(V, Li, literal),
	      XRefLen = length(XRefs),
	      if XRefLen =:= Deg -> ok;
		 true ->
		      ?verbose("Literal degree mismatch: ~w xref = ~w\n",
				[Li,XRefs]),
		      ?verbose("cnf = \n~w\n", [CNF]),
		      error(bad_degree)
	      end,
	      lists:foreach(
		fun(Ci) ->
			Clause = varp_nif:get_clause(V, Ci),
			true = lists:member(Clause, CNF)
		end, XRefs)
      end, DegLs).

verify_hash(V, CNF) ->
    true = varp_nif:info(V, hash),  %% assert we have hash enabled
    lists:foreach(
      fun(Clause) ->
	      Ci = varp_nif:find_clause(V, Clause),
	      Clause = varp_nif:get_clause(V, Ci)
      end, CNF).

%% Utils

get_watched(V) ->
    get_watched(V, lists:seq(1, varp_nif:info(V, number_of_variables))).

get_watched(V, [Xi|Xs]) ->
    Wi0 = varp_nif:get_clauses(V, Xi, watch),
    Wi1 = varp_nif:get_clauses(V, -Xi, watch),
    [{Xi,Wi0},{-Xi,Wi1}|get_watched(V, Xs)];
get_watched(_V, []) ->
    [].

dump(V) ->
    dump(V, true).
dump(V, Verb) ->
    io:format("STATE of ~p\n", [V]),
    if Verb ->
	    lists:foreach(
	      fun({Key, Value}) ->
		      io:format("  ~s: ~p\n", [Key,Value])
	      end, varp:info(V));
       true -> ok
    end,
    io:format("VARIABLES\n"),
    dump_variables(V, lists:seq(1, varp_nif:info(V,number_of_variables)), Verb),
    io:format("CLAUSES DELTA\n"),
    dump_clauses(V, true, varp_nif:clauseset_first(V,delta), Verb),
    io:format("CLAUSES GAMMA\n"),
    dump_clauses(V, true, varp_nif:clauseset_first(V,gamma), Verb),
    io:format("CLAUSES BETA\n"),
    dump_clauses(V, true, varp_nif:clauseset_first(V,beta), Verb),
    io:format("CLAUSES ALPHA\n"),
    dump_clauses(V, true, varp_nif:clauseset_first(V,alpha), Verb),
    io:format("BINDINGS\n"),
    lists:foreach(
      fun(L) ->
	      io:format("~w: ~p\n", [L, varp_nif:get_bindings(V, L)])
      end, lists:seq(0, varp_nif:level(V))),
    ok.

print_clauses(V) ->  print_clauses(V, true).
print_clauses(V, Verb) ->  print_clauses(V,false,Verb).

print_clauses(V,Raw,Verb) ->
    dump_clauses(V, Raw, varp_nif:clauseset_first(V,delta), Verb).

dump_clauses(_V, _Raw, false, _Verb) ->
    ok;
dump_clauses(V, Raw, I, Verb) ->
    {_,SI,IX} = split_cix(I),
    WATCH = case varp_nif:clause_info(V, I, watch) of
		false -> "";
		{P1,P2} -> " watch:"++integer_to_list(P1)++","++
			       integer_to_list(P2)
	    end,
    STATUS = case varp_nif:clause_info(V, I, status) of
		 ok -> "";
		 Status -> io_lib:format(" ~p", [Status])
	     end,
    io:format("~w - ~s:~w~s~s\n", [I,SI,IX,WATCH,STATUS]),
    io:format("  ~w\n", [varp_nif:get_clause(V,I,undefined,Raw)]),
    dump_clauses(V, Raw, varp_nif:clauseset_next(V, I), Verb).

dump_levels(V) ->
    io:format("bindings:\n"),
    dump_levels(V, 0, varp_nif:level(V)).

dump_levels(V, I, N) when I =< N ->
    Bs = varp_nif:get_bindings(V, I, false, false),
    io:format("~w: ~s\n", 
	      [I, [[" ",lit_sym(V,Li)] || Li <- Bs]]),
    dump_levels(V, I+1, N);
dump_levels(_V, I, N) when I > N ->
    ok.


dump_variables(V, List) ->
    dump_variables(V, List, true).

dump_variables(V, List, Verb) ->
    lists:foreach(
      fun(X) ->
	      Keys = varp:variable_info_keys() -- [implication,symbol,level],
	      Sym = var_sym(V, X),
	      Level = varp_nif:variable_info(V,X,level),
	      Value = varp_nif:value(V, X),
	      io:format("~w: ~s = ~w @~w\n", [X, Sym, Value,Level]),
	      if Verb ->
		      lists:foreach(
			fun(Key) ->
				io:format("  ~s: ~p\n", 
					  [Key,varp_nif:variable_info(V,X,Key)])
			end, Keys),
		      io:format(" +xref: ~p\n", [get_cix_list(V,X,literal)]),
		      io:format(" +watch: ~p\n", [get_cix_list(V,X,watch)]),
		      io:format(" -xref: ~p\n", [get_cix_list(V,-X,literal)]),
		      io:format(" -watch: ~p\n", [get_cix_list(V,-X,watch)]);
		 true ->
		      ok
	      end
      end, List).

lit_sym(V, X) when X > 0 ->
    var_sym(V, X);
lit_sym(V, X) when X < 0 ->
    [$!|var_sym(V, -X)].

var_sym(V, X) ->
    case varp_nif:variable_info(V,X,symbol) of
	[] -> no_symbol;
	[{S,_}|_] -> var_str(S)
    end.
    
var_str({p,P,As}) -> var_str(P,As);
var_str({P,As}) when is_list(As) -> var_str(P,As);
var_str(P) when is_list(P) -> P;
var_str(P) when is_binary(P) -> binary_to_list(P);
var_str(P) when is_atom(P) -> atom_to_list(P).

var_str(P,As) ->
    P ++ "(" ++ string:join([var_arg(Ai) || Ai <- As], ",") ++ ")".

var_arg({F,As}) ->
    F ++ "(" ++ string:join([var_arg(Ai) || Ai <- As], ",") ++ ")";
var_arg(A) when is_integer(A) -> integer_to_list(A);
var_arg(A) when is_atom(A) -> atom_to_list(A);
var_arg(A) when is_list(A) -> A.
    

get_cix_list(V, X, How) ->
    [split_cix(I) || I <- varp_nif:get_clauses(V, X, How)].

split_cix(I) ->
    {I, case (I bsr 30) band 3 of 
	    ?DELTA -> delta;
	    ?GAMMA -> gamma;
	    ?BETA -> beta;
	    ?ALPHA -> alpha
	end,
     I band 16#3fffffff}.
    
var(Vp) ->
    Var = varp_nif:add_variable(Vp),
    varp_nif:isused(Vp, Var, true),
    Var.

var(Vp, Sym) ->
    Var = varp_nif:add_variable(Vp),
    varp_nif:add_symbol(Vp, Var, Sym),
    varp_nif:isused(Vp, Var, true),
    Var.

clause(V, Ls) ->
    clause(V, Ls, delta).

clause(V, Ls, Set) ->
    case varp_nif:add_clause(V, Ls, Set) of
	{true,Ci} -> Ci;
	true -> true;
	false -> false
    end.

get_clause(V, ClauseIndex) ->
    Literals = varp_nif:get_clause(V, ClauseIndex),
    lists:sort(Literals).

format_clause_flags(Fs) ->
    lists:join(",", [format_clause_flag(F) || F <- Fs]).

format_clause_flag({watch,{P1,P2}}) -> io_lib:format("w:(~w,~w)",[P1,P2]);
format_clause_flag({status,inqueue}) -> "s:inqueue";
format_clause_flag({status,dead}) -> "s:dead";
format_clause_flag({status,ok}) -> "s:ok".

%% literal list from clauses (CNF or DNF)
literal_list(Cs) ->
    literal_list_(Cs,#{},false).

deg_literal_list(Cs) ->
    literal_list_(Cs,#{},true).

literal_list_([C|Cs],Map,Deg) ->
    Map1 = lists:foldl(
	     fun(Li,Mi) ->
		     maps:put(Li,maps:get(Li,Mi,0)+1,Mi)
	     end, Map, C),
    literal_list_(Cs, Map1, Deg);
literal_list_([], Map, true) ->
    maps:fold(fun(Li,Deg,Acc) -> [{Li,Deg}|Acc] end, [], Map);
literal_list_([], Map, false) ->
    maps:fold(fun(Li,_Deg,Acc) -> [Li|Acc] end, [], Map).

%% make CNF from DNF

dnf_to_cnf([]) ->
    [];
dnf_to_cnf([D]) ->
    normalize_cnf([[Di] || Di <- D]);
dnf_to_cnf([D1,D2|Ds]) ->
    normalize_cnf(dnf_to_cnf_(Ds, [[Di,Dj] || Di <- D1, Dj <- D2])).

dnf_to_cnf_([D|Ds], CNF) ->
    dnf_to_cnf_(Ds,  lists:append([[[Di|Ci] || Di <- D] || Ci <- CNF]));
dnf_to_cnf_([], CNF) ->
    CNF.

%% Generate a random CNF
%% N clauses with clause length M with K variables (-K..K)

generate_cnf(N,M,K) ->
    [generate_clause(M,K) || _ <- lists:seq(1,N)].

%% generate a clause of length M of literals in range -K .. K
%% The clause can only contain wither X or -X 
%% do not include repeats
%%
generate_clause(M,K) ->
    L = lists:sort([{rand:uniform(),rand_sign(),Li} || 
		       Li <- lists:seq(1, K)]),
    abs_sort([S*Li || {_,S,Li} <- lists:sublist(L, M)]).

%% (1,2)  
%% (1,2)*2   = (2,4)
%% (2,4) - 3 = (-1,1)

rand_sign() ->
    rand:uniform(2)*2 -3.
       
%% generate one literal in range -K .. K but skip 0
generate_literal(K) ->
    A = rand:uniform(2*K-1)-(K+1),
    if A < 0 -> A;
       true -> A + 1
    end.

abs_sort(L) ->
    lists:sort(fun(A,B) -> abs(B) >= abs(A) end, L).

rev_abs_sort(L) ->
    lists:sort(fun(A,B) -> abs(A) >= abs(B) end, L).

%% remove repeats, kill clauses with both X and -X
normalize_clause(Clause) ->
    L = rev_abs_sort(Clause),
    normalize_abs_clause(L).

normalize_abs_clause([]) -> 
    [];
normalize_abs_clause([Li|L]) ->
    normalize_abs_clause_(L, Li, []).

normalize_abs_clause_([Li|L], Li, Acc) ->
    normalize_abs_clause_(L, Li, Acc);
normalize_abs_clause_([Lj|_L], Li, _Acc) when Li =:= -Lj ->
    true;
normalize_abs_clause_([Lj|L], Li, Acc) ->
    normalize_abs_clause_(L, Lj,[Li|Acc]);
normalize_abs_clause_([], Li, Acc) ->
    [Li|Acc].

%%
%% "normalize" cnf
%% 1 - remove tautology clauses X,..,!X
%% 2 - remove repeats X...X
%% 3 - propagate units
%%
normalize_cnf(Cs) ->
    propagate_cnf(normalize_cnf_(Cs,[])).

normalize_cnf_([Ci|Cs],Acc) ->
    case normalize_clause(Ci) of
	true ->
	    normalize_cnf_(Cs,Acc);
	[] ->
	    [];
	Cj ->
	    normalize_cnf_(Cs,[Cj|Acc])
    end;
normalize_cnf_([],Acc) ->
    Acc.

%% propagate unit clauses
propagate_cnf(Cs) ->
    {Units, Clauses} = lists:partition(fun([_]) -> true; (_) -> false end, Cs),
    propagate_units_(Units, Clauses, Units).

propagate_units_([[Q]|Qs], Clauses, Units) ->
    propagate_unit_(Q, Qs, Clauses, [], Units);
propagate_units_([], Clauses, Units) ->
    Units ++ Clauses.

%% propagte U
propagate_unit_(U, Qs, [Clause|Clauses], Acc, Units) ->
    case lists:member(U, Clause) of
	true ->
	    propagate_unit_(U, Qs, Clauses, Acc, Units);
	false ->
	    case Clause -- [-U] of
		[V] ->  %% new unit
		    propagate_unit_(U, Qs++[V], Clauses, Acc, [V|Units]);
		Clause1 ->
		    propagate_unit_(U, Qs, Clauses, [Clause1|Acc], Units)
	    end
    end;
propagate_unit_(_U, Qs, [], Acc, Units) ->
    propagate_units_(Qs, Acc, Units).
			       
