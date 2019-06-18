%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2010, Tony Rogvall
%%% @doc
%%%
%%% @end
%%% Created : 21 Jul 2010 by Tony Rogvall <tony@rogvall.se>

-module(varp_prover).

-export([run_formula/2]).
-export([prove_formula/1,prove_formula/2]).
-export([falsify_formula/1,falsify_formula/2,falsify/1,falsify/2]).
-export([satisfy_formula/1,satisfy_formula/2,satisfy/1,satisfy/2]).
-export([eval_formula/1, eval_formula/2]).
-export([saturate_formula/1, saturate_formula/2, saturate_formula/3]).
-export([backtrack_formula/1, backtrack_formula/2, backtrack/1]).

-compile(export_all).

%% -define(DEBUG, true).
-include("varp.hrl").

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

apply_opts_(false, Bs) ->
    display_order(Bs),
    false;
apply_opts_(_, Bs) ->
    order_literals(Bs).

order_literals(Bs) ->
    Seed = varp_formula:getopt(Bs,seed),
    case varp_formula:getopt(Bs,order) of
	[Key1,Key2] -> 
	    varp_formula:order_sort(Bs,Key1,Key2,Seed);
	[Key1] -> 
	    varp_formula:order_sort(Bs,Key1,undefined,Seed)
    end,
    Bs1 = case varp_formula:getopt(Bs,order_first) of
	      [] -> Bs;
	      First -> varp_formula:order_sort_first(Bs,First)
	  end,
    Bs2 = case varp_formula:getopt(Bs1,order_last) of
	      [] -> Bs1;
	      Last -> varp_formula:order_sort_last(Bs1,Last)
	  end,
    display_order(Bs2),
    Bs2.
    
display_order(Bs) ->
    case varp_formula:getopt(Bs,display_order) of
	false ->
	    ok;
	true ->
	    Order = collect_order(Bs,varp_formula:first_init(Bs),[]),
	    lists:foreach(fun(V) ->
				  io:format("~s ",[varp_formula:fmt_var(Bs,V)])
			  end, Order),
	    io:format("\n")
    end.

collect_order(Bs,I,Acc) ->
    case varp_formula:next_unbound(Bs,I) of
	false -> lists:reverse(Acc);
	{J,Xj} -> collect_order(Bs,J,[Xj|Acc])
    end.

run_formula(F,Opts) when is_list(Opts) ->
    {X, Bs} = varp_formula:build(F,Opts),
    run(X,Bs);
run_formula(F,Bs0) when is_record(Bs0, bs) ->
    {X, Bs} = varp_formula:build(F,Bs0),
    run(X,Bs).


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
	Bs1 -> varp_saturate:saturate(Bs1,#{ saturate=>K })
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
    %% run saturate/reduction/saturate?
    passes([assert,
	    {dump,0}, apply,
	    {dump,1}, eval,
	    {dump,2}, reduction,
	    {dump,3}, saturate,
	    {dump,4}, backjump,
	    {dump,5}, backtrack],X,Bs).

passes([Pass|Ps],X,Bs) ->
    case pass_enabled(Pass,Bs) of
	true -> pass_(Pass,Ps,X,Bs);
	{true,Ps1} -> passes(Ps1++Ps,X,Bs);
	false -> passes(Ps,X,Bs)
    end;
passes([],_X,Bs) ->
    case one_model(Bs) of
	false -> undefined;
	R -> R
    end.

pass_({dump,_I},Ps,X,Bs) ->
    varp_dump:run(Bs, #{}),
    passes(Ps,X,Bs);
pass_(assert,Ps,X,Bs) ->
    assert(Bs#bs.assert, Bs),
    passes(Ps,X,Bs);
pass_(Pass,Ps,X,Bs) ->
    case one_model(Bs) of
	false ->
	    ClauseCount_0 = varp_formula:clause_eval_counter(Bs,0),
	    ClauseCount2_0 = varp_formula:clause_eval_counter(Bs,2),
	    ClauseCount3_0 = varp_formula:clause_eval_counter(Bs,3),
	    EvalCount0   = varp_formula:eval_counter(Bs),
	    Bound0       = varp_formula:number_of_bound(Bs),
	    varp_formula:info(Bs, "pass ~p\n", [Pass]),
	    T0 = erlang:monotonic_time(),
	    R = pass(Pass,X,Bs),
	    T1 = erlang:monotonic_time(),
	    Time = erlang:convert_time_unit(T1-T0,native,microsecond),
	    Ts = Time/1000000,
	    ClauseCount_1 = varp_formula:clause_eval_counter(Bs,0),
	    ClauseCount2_1 = varp_formula:clause_eval_counter(Bs,2),
	    ClauseCount3_1 = varp_formula:clause_eval_counter(Bs,3),
	    EvalCount1   = varp_formula:eval_counter(Bs),
	    Clauses1     = varp_formula:number_of_clauses(Bs),
	    varp_formula:info(Bs, "    | eval: ~w, clause:~w,~w(2),~w(3), #clauses = ~w time=~.2fs\n",
			      [EvalCount1-EvalCount0,
			       ClauseCount_1-ClauseCount_0,
			       ClauseCount2_1-ClauseCount2_0,
			       ClauseCount3_1-ClauseCount3_0,
			       Clauses1,
			       Ts]),
	    case R of
		false ->
		    varp_formula:info(Bs,"    | contradiction\n", []),
		    no_models(Bs);
		0 -> %% model count = 0
		    varp_formula:info(Bs,"    | contradiction\n", []),
		    no_models(Bs);
		{0,[]} -> %% model count = 0, no model collected
		    varp_formula:info(Bs,"    | contradiction\n", []),
		    no_models(Bs);
		N when is_integer(N) -> N;
		NM={N,_Models} when is_integer(N) -> NM;
		Bs1 -> 
		    varp_formula:info(Bs,"    | bound: ~w [~w/~w]\n",
				      [varp_formula:number_of_bound(Bs)-Bound0,
				       varp_formula:number_of_bound(Bs),
				       varp_formula:number_of_variables(Bs)
				      ]),
		    case one_model(Bs1) of
			false ->
			    passes(Ps,X,Bs1);
			R1 ->
			    R1
		    end
	    end;
	R -> 
	    R
    end.

%% check if we are supposed to run a pass at all.
pass_enabled(apply,_Bs) -> 
    true;
pass_enabled(assert,_Bs) ->
    true;
pass_enabled(eval,_Bs) -> 
    true;
pass_enabled({dump,I}, Bs) ->
    case varp_formula:getopt(Bs,dump) of
	I -> true;
	_ -> false
    end;
pass_enabled({saturate,Params},_Bs) ->
    maps:get(saturate,Params,0) > 0;
pass_enabled(saturate,Bs) ->
    case varp_formula:getopt(Bs,saturations) of
	[] ->
	    false;
	List -> 
	    %% io:format("saturations = ~p\n", [List]),
	    {true,[{saturate,Params}||Params<-List]}
    end;
pass_enabled(reduction,Bs) ->
    case varp_formula:getopt(Bs,reduction) of
	0 -> false;
	_ -> true
    end;
pass_enabled(backtrack,Bs) ->
    varp_formula:getopt(Bs,backtrack);
pass_enabled(backjump,Bs) ->
    varp_formula:getopt(Bs,backjump).

%% each pass return
%%   false             - contradiction ( = 0 ? )
%%   {N, [model()]}    - method=collect
%%   N                 - method=count
%%   Bs                - continue new environment

pass(apply,X,Bs) ->
    apply_opts(Bs,X);
pass(eval,_X,Bs) ->
    eval_(Bs);
pass({saturate,Params},_X,Bs) ->
    varp_saturate:run(Bs,Params);
pass(saturate,_X,Bs) ->
    Params = #{ saturate => varp_formula:getopt(Bs,saturate) },
    varp_saturate:run(Bs,Params);
pass(reduction,_X,Bs) ->
    Bs1 = varp_reduction:run(Bs),
    order_literals(Bs1), %% fixme!
    Bs1;
pass(rat,_X,Bs) ->
    Bs1 = varp_rat:run(Bs),
    order_literals(Bs1),  %% fixme!
    Bs1;
pass(backtrack,_X,Bs) ->
    varp_backtrack:run(Bs);
pass(backjump,_X,Bs) ->
    varp_backjump:run(Bs).

%% check if there is already a "unique" model
one_model(Bs) ->
    NV = varp_formula:number_of_variables(Bs),
    NB = varp_formula:number_of_bound(Bs),
    if NV =:= NB ->
	    Model = varp:output_model(Bs,1),
	    case varp_formula:getopt(Bs,method) of
		collect -> {1,[Model]};
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

assert([Assert|As], Bs) ->
    case varp_formula:eval_meta(Assert,Bs) of
	false ->
	    io:format("assertion '~s' failed\n", 
		      [varp_formula:format_meta(Assert)]),
	    erlang:error(assertion),
	    ok;
	true ->
	    assert(As,Bs)
    end;
assert([], _Bs) ->
    ok.
	    

eval_list(Bs,[]) ->
    eval(Bs);
eval_list(Bs,[{F,V}|Ps]) ->
    case varp_formula:equal(Bs,F,V) of
	true -> eval_list(Bs,Ps);
	false -> false
    end.

%% eval all triples (push all triples on queue)
eval(Bs) ->
    eval_(Bs).
	    
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
	Bs1 -> varp_backtrack:backtrack(eval(Bs1))
    end.

format_model(Model) ->
    lists:join(",",[ varp_format:format_binding(Bound) || Bound <- Model ]).
