%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2017, Tony Rogvall
%%% @doc
%%%    Backtrack 
%%% @end
%%% Created : 22 Dec 2017 by Tony Rogvall <tony@rogvall.se>

-module(varp_backtrack).

-compile(export_all).

-define(START_MARK, 2).

-define(dbg(F,A), ok).
%%-define(dbg(F,A), io:format((F),(A))).

backtrack(false) ->
    false;
backtrack(Bs) ->
    N     = varp_formula:getopt(Bs,max),
    Print = varp_formula:getopt(Bs,print),
    Order = varp_formula:getopt(Bs,order),
    if Order =:= undefined -> ok;
       true -> varp_formula:order_sort(Bs, Order)
    end,
    case varp_formula:getopt(Bs,method) of
	collect ->
	    bt(Bs, fun({Count0,Acc},Bs1) ->
			   Count = Count0+1,
			   Mdl = varp_formula:model(Bs1),
			   varp_formula:print(Print,Count,Mdl),
			   Continue = (N =:= 0) orelse (Count < N),
			   {Continue,{Count,[Mdl|Acc]}}
		   end, {0,[]});
	count ->
	    bt(Bs, fun(Count0,Bs1) -> 
			   Count = Count0+1,
			   if Print =:= false -> ok;
			      true ->
				   Mdl = varp_formula:model(Bs1),
				   varp_formula:print(Print,Count,Mdl)
			   end,
			   if Count rem 1000 =:= 0 ->
				   io:format("~w\n", [Count]);
			      true -> 
				   ok
			   end,
			   Continue = (N =:= 0) orelse (Count < N),
			   {Continue,Count} 
		   end, 0)
    end.


%%
%% Explicit recursion version, allow times backtracking
%% mix alogorithms etc.
%%
bt(Bs,Func,Acc) ->
    case init(Bs) of
	{model,_Stack} ->
	    {_,Acc1} = Func(Acc,Bs),
	    Acc1;
	{true,Stack} ->
	    {_,Acc1} = loop(Stack,Func,Acc,Bs),
	    Acc1;
	false ->
	    Acc
    end.

-define(BT_ORDER, [true,false]).
-define(BT_FIRST, hd(?BT_ORDER)).
-define(BT_LAST,  hd(tl(?BT_ORDER))).

%% initalise backtrack stack
init(Bs) ->
    I0 = varp_formula:first_init(Bs),
    Next = varp_formula:next_unbound(Bs,I0),
    case Next  of
	false  -> {model,[]};
	{I,Xi} -> {true,[{I,Xi,?BT_ORDER,?START_MARK}]}
    end.

next([{_,Xi,[],_}|Stack1],Bs) ->
    case varp_formula:getopt(Bs, backjump) of
	true ->
	    case backjump(Bs,Xi,?BT_LAST,Stack1) of
		false -> false;
		Stack2 -> next(Stack2,Bs)
	    end;
	false ->
	    undo(Bs,Stack1),
	    next(Stack1,Bs)
    end;
next([{I,Xi,[V|Vs],Mark}|Stack],Bs) ->
    varp_formula:mark(Bs,Mark),
    case eq_eval(Bs,Xi,V,Mark) of
	false -> %% hook this?
	    varp_formula:undo(Bs,Mark),
	    next([{I,Xi,Vs,Mark}|Stack],Bs);
	true ->
	    case varp_formula:next_unbound(Bs,I) of
		false ->
		    {model,[{I,Xi,Vs,Mark}|Stack]};
		{J,Xj} ->
		    {true,[{J,Xj,?BT_ORDER,Mark+1},{I,Xi,Vs,Mark}|Stack]}
	    end
    end;
next([],_Bs) ->
    false.

%% Given contradiction in both branches
%% find the shortest prefix that has no conflict
%% example:
%%    [A,B,C,D,E,F]  has a conflict
%%    [A,B,C,D,E,~F] has a conflict
%%    [A,B,C,D,~F]   conflict
%%    [A,B,C,~F]     conflict
%%    [A,B,~F]       no conflict
%%
%%    [A,~F]
%%    [~F]   (contradiction ?)

backjump(Bs, Xi, Xv, Stack) ->
    %% io:format("backjump: ~1000p\n", [Stack]),
    varp_formula:undo(Bs,?START_MARK), %% undo all bindings
    Stack1 = bj(Bs, {Xi,Xv}, Stack, 0),
    %% io:format("backjump: stack1=~1000p\n", [Stack1]),
    %% J = length(Stack)-length(Stack1),
    %% if J > 0 ->
    %% io:format("backjump length=~w\n", [J]);
    %% true -> ok
    %% end,
    Stack1.

bj(_Bs, _Bn, [], _N) ->
    [];
bj(Bs, Bn, Stack0=[_|Stack], N) ->
    Ys = [Bn | stack(Stack)],
    varp_formula:mark(Bs,?START_MARK),
    case varp_prover:eval_list(Bs,Ys) of
	false ->
	    varp_formula:undo(Bs,?START_MARK),
	    bj(Bs, Bn, Stack, N+1);
	Bs1 ->
	    varp_formula:undo(Bs1,?START_MARK),
	    bj_reinstall(Bs1,lists:reverse(Stack)),
	    Stack0
    end.


backjump1(Bs, Xi, Xv, Stack) ->
    io:format("backjump1: ~1000p\n", [Stack]),
    varp_formula:undo(Bs,?START_MARK), %% undo all bindings
    varp_formula:mark(Bs,?START_MARK), %% mark point again
    ?dbg("~w=~w,",[Xi,Xv]),
    case eqv(Bs,Xi,Xv) of
	false ->
	    varp_formula:undo(Bs,?START_MARK),
	    bj_reinstall(Bs,Stack),
	    Stack;
	true ->
	    Stack1 = bj1(Bs, lists:reverse(Stack), []),
	    io:format("backjump1: stack1=~1000p\n", [Stack1]),
	    varp_formula:undo(Bs,?START_MARK),
	    bj_reinstall(Bs,Stack1),
	    io:format("backjump length=~w\n", [length(Stack)-length(Stack1)]),
	    Stack1
    end.

bj1(Bs, [E={_I,Xi,Vs,_Mark}|Stack], Acc) ->
    Xv = if Vs =:= [] -> ?BT_LAST; true -> ?BT_FIRST end,
    case eqv(Bs,Xi,Xv) of
	true ->
	    ?dbg("~w=~w,",[Xi,Xv]),
	    bj1(Bs, Stack, [E|Acc]);
	false ->
	    ?dbg("!~w=~w\n",[Xi,Xv]),
	    [E|Acc]
    end;
bj1(_Bs, [], Acc) ->
    ?dbg("![]\n",[]),
    Acc.

bj_reinstall(Bs,[{_I,Xi,Vs,Mark}|Stack]) ->
    Xv = if Vs =:= [] -> ?BT_LAST; true -> ?BT_FIRST end,
    varp_formula:mark(Bs,Mark),
    true = eqv(Bs,Xi,Xv),
    bj_reinstall(Bs, Stack);
bj_reinstall(_Bs,[]) ->
    ok.

%% Get a list of bound values on backtrack stack
%% Value are in order [true,false]
stack([{_,Xi,[],_}|Stack]) ->
    [{Xi,?BT_LAST}|stack(Stack)];
stack([{_,Xi,[_],_}|Stack]) ->
    [{Xi,?BT_FIRST}|stack(Stack)];
stack([]) -> [].

loop(Stack,Func,Acc,Bs) ->
    case next(Stack,Bs) of
	{model,Stack1} ->
	    case Func(Acc,Bs) of
		{true,Acc1} ->
		    undo(Bs,Stack1),
		    loop(Stack1,Func,Acc1,Bs);
		{false,Acc1} ->
		    {false,Acc1}
	    end;
	{true,Stack1} ->
	    loop(Stack1,Func,Acc,Bs);
	false ->
	    {false,Acc}
    end.

undo(Bs,[{_,_,_,Mark}|_]) ->
    varp_formula:undo(Bs,Mark);
undo(_Bs,[]) ->
    ok.

eq_eval(Bs,V,Value,_D) ->
    ?dbg("~seq_eval: ~w, ~s/~s\n", 
	 [indent(_D), V,
	  varp_formula:fmt_var(Bs,V),
	  varp_formula:fmt_var(Bs,Value)]),
    eqv(Bs,V,Value).

eqv(Bs,V,Value) ->
    varp_formula:equal(Bs,V,Value) andalso varp_formula:eval(Bs).

indent(D) -> lists:duplicate(D, $\s).
