%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2010, Tony Rogvall
%%% @doc
%%%
%%% @end
%%% Created : 21 Jul 2010 by Tony Rogvall <tony@rogvall.se>

-module(varp_prover).

-export([run_formula/1,run_formula/2]).
-export([prove_formula/1,prove_formula/2]).
-export([falsify_formula/1,falsify_formula/2,falsify/1,falsify/2]).
-export([satisfy_formula/1,satisfy_formula/2,satisfy/1,satisfy/2]).
-export([eval_formula/1, eval_formula/2]).
-export([saturate_formula/1, saturate_formula/2, saturate_formula/3]).
-export([backtrack_formula/1, backtrack_formula/2, backtrack/1]).

-compile(export_all).

%% -define(TRUE,   1).
%% -define(FALSE, -1).
-define(dbg(F,A), ok).
%% -define(dbg(F,A), io:format((F),(A))).


apply_opts(Bs,F) ->
    case varp_formula:getopt(Bs,value) of
	none ->
	    apply_opts_(none, Bs);
	true -> 
	    Q = varp_formula:equal(Bs,F,true),
	    apply_opts_(Q, Bs);
	false ->
	    Q = varp_formula:equal(Bs,F,false),
	    apply_opts_(Q, Bs)
    end.

apply_opts_(false, _Bs) ->
    false;
apply_opts_(_, Bs) ->
    case varp_formula:getopt(Bs,order) of
	none -> Bs;
	Order -> varp_formula:order(Bs,Order)
    end.

run_formula(F) ->
    run_formula(F, []).
run_formula(F,Opts) ->
    run(varp_formula:build(F,Opts)).

run({F,Bs}) ->
    run(F, Bs).

run(undefined, Bs) ->
    no_models(Bs);
run({bool,X}, Bs) ->
    method(X,Bs);
run({_Sign,_N,Xs}, Bs) ->
    %% or just a dummy variable?
    %% {bool,?FALSE}
    {X,Bs1} = varp_formula:vfold_op(Bs,'or',false,Xs),
    method(X,Bs1).

prove_formula(F) ->
    prove_formula(F,[{method,count},{max,1},{order,reverse_depth}]).
prove_formula(F,Opts) ->
    case falsify_formula(F,Opts) of
	{0,_} -> true;
	0     -> true;
	undefined -> undefined;
	_ -> false
    end.

falsify_formula(F) ->
    falsify_formula(F,[{method,collect},{print,true},{order,depth}]).
falsify_formula(F,Opts) ->
    falsify(varp_formula:build(F,Opts)).

falsify({F,Bs}) ->
    falsify(F, Bs).

falsify({bool,X}, Bs) ->
    Bs1 = varp_formula:setopt(Bs,value,false),
    method(X,Bs1).

%%
%% Find one or more models to formula F
%%
satisfy_formula(F) ->
    satisfy_formula(F, [{method,collect},{print,true},{order,depth}]).

satisfy_formula(F,Opts) ->
    satisfy(varp_formula:build(F,Opts)).

satisfy({F,Bs}) ->
    satisfy(F, Bs).

satisfy({bool,X}, Bs) ->
    Bs1 = varp_formula:setopt(Bs,value,true),
    method(X,Bs1).

%%
%% Plain eval (saturate-0)
%%

eval_formula(F) ->
    eval_formula(F, []).

eval_formula(F,Opts) ->
    eval_bs(varp_formula:build(F,Opts)).

eval_bs({F,Bs}) ->
    case apply_opts(Bs,F) of
	false -> false;
	Bs1 -> eval(Bs1)
    end.

%%
%% K saturate a clause set
%% 
saturate_formula(F) ->
    saturate_formula(1,F,[]).

saturate_formula(K,F) when is_integer(K), K>=0 ->
    saturate_formula(K,F,[]).

saturate_formula(K,F,Opts) ->
    {Fv,Bs} = varp_formula:build(F,Opts),
    case apply_opts(Bs,Fv) of
	false -> false;
	Bs1 -> saturate(Bs1,K)
    end.
    
saturate(Bs,0) ->
    eval(Bs);
saturate(Bs,K) when is_integer(K), K >= 1 ->
    case eval(Bs) of
	false -> false;
	Bs1 -> varp_saturate:saturate(Bs1,K)
    end.

%% do plain backtrack over formula
backtrack_formula(F) ->
    backtrack_formula(F,[]).

backtrack_formula(F,Opts) ->
    backtrack(varp_formula:build(F,Opts)).

backtrack({F,Bs}) ->
    backtrack(Bs,F).


%% Basic run
method(X,Bs) ->
    passes([apply,eval,saturate,backtrack],X,Bs).

passes([Pass|Ps],X,Bs) ->
    case pass_enabled(Pass,Bs) of
	true -> pass_(Pass,Ps,X,Bs);
	false -> passes(Ps,X,Bs)
    end;
passes([],_X,_Bs) ->
    undefined.

pass_(Pass,Ps,X,Bs) ->
    case one_model(Bs) of
	false ->
	    ClauseCount0 = varp_formula:clause_eval_counter(Bs),
	    EvalCount0   = varp_formula:eval_counter(Bs),
	    Bound0       = varp_formula:number_of_bound(Bs),
	    varp_formula:info(Bs, "pass ~s\n", [Pass]),
	    T0 = erlang:monotonic_time(),
	    R = pass(Pass,X,Bs),
	    T1 = erlang:monotonic_time(),
	    Time = erlang:convert_time_unit(T1-T0,native,microsecond),
	    Ts = Time/1000000,
	    ClauseCount1 = varp_formula:clause_eval_counter(Bs),
	    EvalCount1   = varp_formula:eval_counter(Bs),
	    varp_formula:info(Bs, "    | eval: ~w, clause = ~w, time=~.2fs\n",
			      [EvalCount1-EvalCount0,
			       ClauseCount1-ClauseCount0, Ts]),
	    case R of
		false ->
		    varp_formula:info(Bs,"    | contradiction\n", []),
		    no_models(Bs);
		0 ->
		    varp_formula:info(Bs,"    | contradiction\n", []),
		    no_models(Bs);
		{0,[]} ->
		    varp_formula:info(Bs,"    | contradiction\n", []),
		    no_models(Bs);
		N when is_integer(N) -> N;
		NM={N,_Models} when is_integer(N) -> NM;
		Bs1 -> 
		    varp_formula:info(Bs,"    | bound: ~w [~w/~w]\n",
				      [varp_formula:number_of_bound(Bs)-Bound0,
				       varp_formula:number_of_unbound(Bs),
				       varp_formula:number_of_variables(Bs)
				      ]),
		    passes(Ps,X,Bs1)
	    end;
	R -> R
    end.

%% check if we are supposed to run a pass at all.
pass_enabled(apply,_Bs) -> 
    true;
pass_enabled(eval,_Bs) ->
    true;
pass_enabled(saturate,Bs) ->
    case varp_formula:getopt(Bs,saturate) of
	0 -> false;
	_ -> true
    end;
pass_enabled(backtrack,Bs) ->
    varp_formula:getopt(Bs,backtrack).

%% each pass return
%%   false             - contradiction ( = 0 ? )
%%   {N, [model()]}    - method=collect
%%   N                 - method=count
%%   Bs                - continue new environment

pass(apply,X,Bs) ->
    apply_opts(Bs,X);
pass(eval,_X,Bs) ->
    eval_(varp_formula:enqueue_all(Bs));
pass(saturate,_X,Bs) ->
    varp_saturate:saturate(Bs,varp_formula:getopt(Bs,saturate));
pass(backtrack,_X,Bs) ->
    backtrack_bs(Bs).

%% check if there is already a "unique" model
one_model(Bs) ->
    NV = varp_formula:number_of_variables(Bs),
    NB = varp_formula:number_of_bound(Bs),
    if NV =:= NB ->
	    Print = varp_formula:getopt(Bs,print),
	    Mdl = varp_formula:model(Bs),
	    print(Print,1,Mdl),
	    case varp_formula:getopt(Bs,method) of
		collect -> {1,[Mdl]};
		count -> 1
	    end;
       true ->
	    false
    end.

no_models(Bs) ->
    case varp_formula:getopt(Bs,partial) of
	true ->
	    %% print partial model, the variables bound
	    Mdl = varp_formula:model(Bs),
	    io:format("partial: ~s\n",[format_model(Mdl)]);
	false ->
	    ok
    end,
    case varp_formula:getopt(Bs,method) of
	collect -> {0,[]};
	count -> 0
    end.

eval_list([],Bs) ->
    eval(Bs);
eval_list([{F,V}|Ps],Bs) ->
    case varp_formula:equal(Bs,F,V) of
	true -> eval_list(Ps,Bs);
	false -> false
    end.

%% eval all triples (push all triples on queue)
eval(Bs) ->
    eval_(varp_formula:enqueue_all(Bs)).
	    
eval_list_([],Bs) ->
    eval_(Bs);
eval_list_([{F,V}|Ps],Bs) ->
    case varp_formula:equal(Bs,F,V) of
	true -> eval_list_(Ps,Bs);
	false -> false
    end.

eval_(Bs) ->
    case varp_formula:eval(Bs) of
	true -> Bs;
	false -> false
    end.

backtrack(Bs,F) ->
    varp_formula:info(Bs,"BACKTRACK method=~w\n", 
		      [varp_formula:getopt(Bs,method)]),
    case apply_opts(Bs,F) of
	false -> no_models(Bs);
	Bs1 -> backtrack_bs(eval(Bs1))
    end.


backtrack_bs(Bs) ->
    N     = varp_formula:getopt(Bs,max),
    Print = varp_formula:getopt(Bs,print),
    case varp_formula:getopt(Bs,method) of
	collect ->
	    bt(Bs, fun({Count0,Acc},Bs1) ->
			   Count = Count0+1,
			   Mdl = varp_formula:model(Bs1),
			   print(Print,Count,Mdl),
			   Continue = (N =:= 0) orelse (Count < N),
			   {Continue,{Count,[Mdl|Acc]}}
		   end, {0,[]});
	count ->
	    bt(Bs, fun(Count0,Bs1) -> 
			   Count = Count0+1,
			   if Print =:= false -> ok;
			      true ->
				   Mdl = varp_formula:model(Bs1),
				   print(Print,Count,Mdl)
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

print(true,I,Bindings) ->
    Bindings1 = filter_bindings(Bindings),
    io:format("~w: ~s\n",
	      [I,concat([ format_binding(Bound) || Bound <- Bindings1 ], ",")]);
print(literal,I,Bindings) ->
    Bindings1 = filter_bindings(Bindings),
    io:format("~w: ~s\n",
	      [I,concat([ format_binding(Bound) || Bound <- Bindings1 ], ",")]);
print(model,I,Bindings) ->
    Bindings1 = filter_bindings(Bindings),
    io:format("~w: ~s\n",
	      [I,concat([ format_binding(Bound) || 
			    Bound <- Bindings1,
			    element(2,Bound) =/= false ], ",")]);
print(umodel,I,Bindings) ->
    io:format("~w: ~s\n",
	      [I,concat([ format_binding(Bound) || 
			    Bound <- Bindings,
			    element(2,Bound) =/= false ], ",")]);
print(erlang,_I,Bindings) ->
    Bindings1 = filter_bindings(Bindings),
    io:format("~w.\n", [Bindings1]);
print(false,_I,_Bindings) ->
    ok.

filter_bindings(Bindings) ->
    [ B || B={{p,V,_},_} <- Bindings, hd(atom_to_list(V)) =/= $_].

format_model(Model) ->
    concat([ format_binding(Bound) || Bound <- Model ], ",").

format_binding({Var,Value}) ->
    VarFmt = format_var(Var),
    if Value =:= true -> VarFmt;
       Value =:= false -> [$~|VarFmt];
       is_integer(Value) -> [VarFmt,"=",integer_to_list(Value)]
    end.

%% format_var(V) when is_atom(V) ->
%%    [atom_to_list(V)];
format_var({p,V,[]}) ->
    [atom_to_list(V)];
format_var({p,V,As}) ->
    [atom_to_list(V),"(", concat([io_lib:format("~w",[X])||X<-As], ","), ")"].

concat([], _) -> [];
concat([H],_) -> [H];
concat([H|T],S) -> [H,S | concat(T,S)].

%%
%% Explicit recursion version, allow times backtracking
%% mix alogorithms etc.
%%
bt(Bs,Func,Acc) ->
    case bt_init(Bs) of
	{model,_Stack} ->
	    {_,Acc1} = Func(Acc,Bs),
	    Acc1;
	{true,Stack} ->
	    {_,Acc1} = bt_loop(Stack,Func,Acc,Bs),
	    Acc1;
	false ->
	    Acc
    end.

bt_loop(Stack,Func,Acc,Bs) ->
    case bt_next(Stack,Bs) of
	{model,Stack1} ->
	    case Func(Acc,Bs) of
		{true,Acc1} ->
		    bt_undo(Bs,Stack1),
		    bt_loop(Stack1,Func,Acc1,Bs);
		{false,Acc1} ->
		    {false,Acc1}
	    end;
	{true,Stack1} ->
	    bt_loop(Stack1,Func,Acc,Bs);
	false ->
	    {false,Acc}
    end.

bt_undo(Bs,[{_,_,_,Mark}|_]) ->
    varp_formula:undo(Bs,Mark);
bt_undo(_Bs,[]) ->
    ok.

%% initalise backtrack stack
bt_init(Bs) ->
    I0 = varp_formula:first_init(Bs),
    ?dbg("I0=~w N=~w\n", [I0,varp_formula:number_of_variables(Bs)]),
    Next = varp_formula:next_unbound(Bs,I0),
    ?dbg("Next=~p\n",[Next]),
    case Next  of
	false  -> {model,[]};
	{I,Xi} -> {true,[{I,Xi,[true,false],0}]}
    end.

bt_next([{_,_,[],_}|Stack],Bs) ->
    bt_undo(Bs,Stack), %% pop/undo
    bt_next(Stack,Bs);
bt_next([{I,Xi,[V|Vs],Mark}|Stack],Bs) ->
    ?dbg("~s~s/~w\n", [indent(Mark),varp_formula:fmt_var(Bs,Xi),V]),
    varp_formula:mark(Bs,Mark),
    case eq_eval(Bs,Xi,V,Mark) of
	false -> %% hook this?
	    varp_formula:undo(Bs,Mark),
	    bt_next([{I,Xi,Vs,Mark}|Stack],Bs);
	true ->
	    case varp_formula:next_unbound(Bs,I) of
		false -> 
		    {model,[{I,Xi,Vs,Mark}|Stack]};
		{J,Xj} ->
		    {true,[{J,Xj,[true,false],Mark+1},{I,Xi,Vs,Mark}|Stack]}
	    end
    end;
bt_next([],_Bs) ->
    false.

indent(D) -> lists:duplicate(D, $\s).

eq_eval(Bs,V,Value,_D) ->
    ?dbg("~seq_eval: ~s/~s\n", 
	 [indent(_D),
	  varp_formula:fmt_var(Bs,V),
	  varp_formula:fmt_var(Bs,Value)]),
    varp_formula:equal(Bs,V,Value) andalso varp_formula:eval(Bs).
