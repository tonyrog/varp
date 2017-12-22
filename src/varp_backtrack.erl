%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2017, Tony Rogvall
%%% @doc
%%%    Backtrack 
%%% @end
%%% Created : 22 Dec 2017 by Tony Rogvall <tony@rogvall.se>

-module(varp_backtrack).

-compile(export_all).

-define(dbg(F,A), ok).
%%-define(dbg(F,A), io:format((F),(A))).

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

%% initalise backtrack stack
init(Bs) ->
    I0 = varp_formula:first_init(Bs),
    ?dbg("I0=~w N=~w\n", [I0,varp_formula:number_of_variables(Bs)]),
    Next = varp_formula:next_unbound(Bs,I0),
    ?dbg("Next=~p\n",[Next]),
    case Next  of
	false  -> {model,[]};
	{I,Xi} -> {true,[{I,Xi,[true,false],0}]}
    end.

next([{_,_Xi,[],_}|Stack],Bs) ->
    %% io:format("backjump?: stack = ~p\n", [stack(Stack)]),
    undo(Bs,Stack), %% pop/undo
    next(Stack,Bs);
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
		    {true,[{J,Xj,[true,false],Mark+1},{I,Xi,Vs,Mark}|Stack]}
	    end
    end;
next([],_Bs) ->
    false.

%% Get a list of bound values on backtrack stack
stack([{_,Xi,[true],_}|Stack])  -> [{Xi,false}|stack(Stack)];
stack([{_,Xi,[false],_}|Stack]) -> [{Xi,true}|stack(Stack)];
stack([{_,Xi,[],_}|Stack])      -> [{Xi,none}|stack(Stack)];
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
    ?dbg("~seq_eval: ~s/~s\n", 
	 [indent(_D),
	  varp_formula:fmt_var(Bs,V),
	  varp_formula:fmt_var(Bs,Value)]),
    varp_formula:equal(Bs,V,Value) andalso varp_formula:eval(Bs).

indent(D) -> lists:duplicate(D, $\s).

