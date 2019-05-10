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
    varp_formula:config(Bs, max_conflicting, 1),
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
%% mix algorithms etc.
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

%% initalise backtrack stack
init(Bs) ->
    I0 = varp_formula:first_init(Bs),
    Next = varp_formula:next_unbound(Bs,I0),
    case Next  of
	false  -> {model,[]};
	{I,Xi} -> {true,[{I,Xi,?BT_ORDER,?START_MARK}]}
    end.

next([{_,_Xi,[],_}|Stack1],Bs) ->
    undo(Bs,Stack1),
    next(Stack1,Bs);
next([{I,Xi,[V|Vs],Mark}|Stack],Bs) ->
    varp_formula:set_level(Bs,Mark),
    case eq_eval(Bs,Xi,V,Mark) of
	false -> %% hook this?
	    varp_formula:undo_level(Bs,Mark),
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

undo(Bs,[{_,_,_,Level}|_]) ->
    varp_formula:undo_level(Bs,Level);
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
