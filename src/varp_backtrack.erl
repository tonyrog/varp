%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2017, Tony Rogvall
%%% @doc
%%%    Backtrack 
%%% @end
%%% Created : 22 Dec 2017 by Tony Rogvall <tony@rogvall.se>

-module(varp_backtrack).

-compile(export_all).

-define(dbg(F,A), ok).
%% -define(dbg(F,A), io:format((F),(A))).

backtrack(false) ->
    false;
backtrack(Bs) ->
    N     = varp_formula:getopt(Bs,max),
    Print = varp_formula:getopt(Bs,print),
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
    ?dbg("I0=~w N=~w\n", [I0,varp_formula:number_of_variables(Bs)]),
    Next = varp_formula:next_unbound(Bs,I0),
    ?dbg("Next=~p\n",[Next]),
    case Next  of
	false  -> {model,[]};
	{I,Xi} -> {true,[{I,Xi,?BT_ORDER,0}]}
    end.

next([{_,Xi,[],_}|Stack1],Bs) ->
    case varp_formula:getopt(Bs, backjump) of
	true ->
	    case backjump(Bs,Xi,Stack1) of
		false -> false;
		Stack2 -> next(Stack2,Bs)
	    end;
	false ->
	    undo(Bs,Stack1),
	    next(Stack1,Bs)
    end;
next([{I,Xi,[V|Vs],Mark}|Stack],Bs) ->
    ?dbg("~s~s/~w\n", [indent(Mark),varp_formula:fmt_var(Bs,Xi),V]),
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

%% Given contradaction in both branches, we 
%% example:
%%    [A,B,C,D,E,F]
%%    [A,B,C,D,E,~F]
%% find the shortest prefix that is not contradictory:
%%    [A,B,C,D,~F]
%%    [A,B,C,~F]
%%    [A,B,~F]
%%    [A,~F]
%%    [~F]   (contradiction ?)

backjump(Bs, Xi, Stack) ->
    %% io:format("backjump: ~p\n", [Stack]),
    varp_formula:undo(Bs,0), %% undo all bindings
    bj(Bs, {Xi,hd(tl(?BT_ORDER))}, Stack, 0).

bj(_Bs, _Bn, [], _N) ->
    false;
bj(Bs, Bn, Stack0=[_|Stack], N) ->
    Ys = [Bn | stack(Stack)],
    %% io:format("eval_list: ~p\n", [Ys]),
    varp_formula:mark(Bs,0),
    case varp_prover:eval_list(Bs,Ys) of
	false ->
	    varp_formula:undo(Bs,0),
	    %% io:format("bj=~p\n", [Ys]),
	    bj(Bs, Bn, Stack, N+1);
	Bs1 ->
	    %% if N > 0 -> io:format("bj = ~w\n", [N]); true -> ok end,
	    varp_formula:undo(Bs1,0),
	    bj_reinstall(Bs1,lists:reverse(Stack)),
	    Stack0
    end.

bj_reinstall(Bs,[{_I,Xi,Vs,Mark}|Stack]) ->
    case Vs of
	[] ->
	    varp_formula:mark(Bs,Mark),
	    eq_eval(Bs,Xi,?BT_LAST,Mark),
	    bj_reinstall(Bs, Stack);
	[V] when V =:= ?BT_LAST ->
	    varp_formula:mark(Bs,Mark),
	    eq_eval(Bs,Xi,?BT_FIRST,Mark),
	    bj_reinstall(Bs, Stack)
    end;
bj_reinstall(_Bs,[]) ->
    ok.

%% Get a list of bound values on backtrack stack
%% Value are in order [true,false]
stack([{_,Xi,[V],_}|Stack]) when V =:= hd(tl(?BT_ORDER))->
    [{Xi,hd(?BT_ORDER)}|stack(Stack)];
stack([{_,Xi,[],_}|Stack]) ->
    [{Xi,hd(tl(?BT_ORDER))}|stack(Stack)];
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
    varp_formula:equal(Bs,V,Value) andalso varp_formula:eval(Bs).

indent(D) -> lists:duplicate(D, $\s).
