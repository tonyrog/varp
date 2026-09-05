%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2026, Tony Rogvall
%%% @doc
%%%    Bounded model checking driver, see doc/MODEL_CHECKING.md.
%%%
%%%      varp bmc [--k-min 0] [--k-max 20] [--step 1] [bj ...] <file>
%%%
%%%    The plugin rebuilds the formula for every bound k, binding the
%%%    meta variable `k' (option --bound), and runs the search plugins
%%%    that follow it (satisfy and backjump are added when missing).
%%%    A model is a counterexample: it is printed as a trace, one row
%%%    per step, and the answer is `% 1'.  No model up to k-max is
%%%    `% 0'.
%%%
%%%    bmc is a driver: varp:do_run/4 hands it the rest of the plugin
%%%    chain and the source of the formula (drive/5) instead of a built
%%%    clause database, since the database differs for every k.
%%% @end

-module(varp_bmc).
-behaviour(varp_plugin).

-export([options/0, run/2, drive/5]).
-export([trace/1, format_trace/1]).

-include("varp.hrl").

options() ->
    [#{ long => "k-min",
	key => k_min,
	spec => unsigned,
	default => 0,
	description => "First bound to try."
      },
     #{ long => "k-max",
	key => k_max,
	spec => unsigned,
	default => 20,
	description => "Last bound to try."
      },
     #{ long => "step",
	key => step,
	spec => unsigned,
	default => 1,
	description => "Bound increment."
      },
     #{ long => "bound",
	key => bound,
	spec => string,
	default => "k",
	description => "Name of the meta variable that carries the bound."
      },
     #{ long => "trace",
	key => trace,
	spec => {enum,[?BOOL]},
	default => true,
	description => "Print a counterexample as a table, one row per step."
      },
     #{ long => "keep-learned",
	key => keep_learned,
	spec => {enum,[?BOOL,{"auto",auto}]},
	default => auto,
	description => "Incremental: keep learned clauses between bounds "
	    "(auto: only with --bump-decay)."
      },
     #{ long => "reset-order",
	key => reset_order,
	spec => {enum,[?BOOL,{"auto",auto}]},
	default => auto,
	description => "Incremental: restore the variable order between bounds "
	    "(auto: only without --bump-decay)."
      },
     #{ long => "incremental",
	key => incremental,
	spec => {enum,[?BOOL]},
	default => true,
	description => "Keep the clause database between bounds "
	    "(needs a system definition and the backjump plugin)."
      }
    ].

%% never reached: varp:do_run/4 calls drive/5 for a driver plugin
run(Bs, _Param) when is_record(Bs,bs) ->
    {?ERROR, "bmc must be the first plugin", Bs}.

%% Do is the rest of the plugin chain
drive(Do, Assignments, Formula, GOpts, Param) ->
    Do1 = with_search(with_mode(Do)),
    Bound = list_to_binary(maps:get(bound, Param)),
    KMin = maps:get(k_min, Param),
    KMax = maps:get(k_max, Param),
    Step = max(1, maps:get(step, Param)),
    Trace = maps:get(trace, Param),
    Print = maps:get(print, GOpts, true) =/= false,
    Target = case maps:get(incremental, Param) of
		 true -> incremental_target(Formula, Bound, GOpts, Do1);
		 false -> false
	     end,
    case Target of
	{Info, Kind, BjParam} ->
	    ?info(GOpts, "bmc: incremental, ~s ~s\n",
		  [maps:get(name, Info), Kind]),
	    incremental(KMin, KMax, Step, Trace, Print, Info, Kind, BjParam,
			Assignments,
			GOpts#{ print => false,
				keep_learned => auto(keep_learned, Param, GOpts),
				reset_order => auto(reset_order, Param, GOpts) });
	false ->
	    loop(KMin, KMax, Step, Bound, Trace, Print,
		 Do1, Assignments, Formula, GOpts#{ print => false })
    end.

%% With activity decay (a VSIDS heap) old learned clauses and activity
%% help the next bound; with the order list they hurt, see
%% doc/MODEL_CHECKING.md.
auto(Key, Param, GOpts) ->
    Decay = maps:get(bump_decay, GOpts, 0) > 0,
    case maps:get(Key, Param) of
	auto when Key =:= keep_learned -> Decay;
	auto when Key =:= reset_order -> not Decay;
	V -> V
    end.

%% incremental mode needs the formula to be a property of a system,
%% {p,Name,[Bound]}, and a chain of just satisfy and backjump
incremental_target({p,Name,[Bound]}, Bound, GOpts, Do) ->
    Systems = maps:get(systems, GOpts, []),
    Found = [{Info, Kind} || Info <- Systems,
			     Kind <- [varp_system:property_kind(Info, Name)],
			     Kind =/= false],
    Plugins = [P || {P,_} <- Do],
    case {Found, Plugins -- [varp_satisfy, varp_backjump]} of
	{[{Info,Kind}|_], []} ->
	    case lists:keyfind(varp_backjump, 1, Do) of
		{_, BjParam} -> {Info, Kind, BjParam};
		false -> false
	    end;
	_ ->
	    false
    end;
incremental_target(_Formula, _Bound, _GOpts, _Do) ->
    false.

%% ------------------------------------------------------------------
%% Incremental: one clause database for all bounds.  The initial
%% state and every transition step are permanent; the property of
%% bound K is built to a variable which the search assumes, and which
%% is bound false for good when the bound is refuted.
%% ------------------------------------------------------------------

incremental(KMin, KMax, Step, Trace, Print, Info, Kind, BjParam, As, GOpts) ->
    put(output_model_header, false),
    Bs0 = varp_formula:new(GOpts),
    Bs1 = varp:set_global_timeout(Bs0, maps:get(timeout, GOpts, infinity)),
    Init = varp_system:init_formula(Info),
    try
	Bs2 = varp_formula:build_assignment_defs(As, Bs1),
	case assert_formula(Init, Bs2) of
	    {true, Bs3} ->
		istep(0, KMin, KMax, Step, Trace, Print, Info, Kind,
		      BjParam, GOpts, Bs3);
	    {false, Bs3} ->
		?info(GOpts, "bmc: no initial state\n", []),
		result(Print, "% 0\n", []),
		{?INCONSISTENT, [], Bs3}
	end
    catch
	throw:contradiction ->
	    result(Print, "% 0\n", []),
	    {?INCONSISTENT, [], Bs1}
    end.

istep(K, _KMin, KMax, _Step, _Trace, Print, _Info, _Kind, _BjParam, _GOpts, Bs)
  when K > KMax ->
    result(Print, "% 0\n", []),
    {?INCONSISTENT, [], Bs};
istep(K, KMin, KMax, Step, Trace, Print, Info, Kind, BjParam, GOpts, Bs) ->
    Next = K + 1,
    %% the transition into step K, permanent
    StepOk = case K of
		 0 -> {true, Bs};
		 _ -> assert_formula(varp_system:next_formula(Info, K), Bs)
	     end,
    case StepOk of
	{false, Bs1} ->
	    ?info(GOpts, "bmc: k=~w no path of that length\n", [K]),
	    result(Print, "% 0\n", []),
	    {?INCONSISTENT, [], Bs1};
	{true, Bs1} when K < KMin; (K - KMin) rem Step =/= 0 ->
	    istep(Next, KMin, KMax, Step, Trace, Print, Info, Kind, BjParam,
		  GOpts, Bs1);
	{true, Bs1} ->
	    Vp = Bs1#bs.vp,
	    Prop = varp_system:step_property(Info, Kind, K, KMin),
	    Mark = {varp_nif:clauseset_size(Vp, ?DELTA),
		    varp:get_number_of_variables(Vp)},
	    {{bool,A}, Bs3} = varp_formula:build(Prop, Bs1),
	    Xref = varp_nif:getopt(Vp, xref),
	    T0 = erlang:monotonic_time(),
	    C0 = varp_nif:getstat(Vp, conflict_counter),
	    {R, Acc, Bs4} =
		case A of
		    false -> {?INCONSISTENT, [], Bs3};
		    true -> varp_backjump:run(Bs3#bs{ main = true }, BjParam);
		    _ -> varp_backjump:run(Bs3#bs{ main = A },
					   BjParam#{ assume => [A] })
		end,
	    varp_nif:setopt(Vp, xref, Xref),
	    Ts = erlang:convert_time_unit(erlang:monotonic_time()-T0,
					  native, microsecond) / 1000000,
	    C1 = varp_nif:getstat(Vp, conflict_counter),
	    ?info(GOpts, "bmc: k=~w ~s ~.2fs conflicts=~w learned=~w models=~w\n",
		  [K, verdict(R, Acc), Ts, C1 - C0,
		   varp_nif:clauseset_size(Vp, ?GAMMA), nmodels(Acc)]),
	    case R of
		_ when R =:= ?DONE; R =:= ?CONTINUE; R =:= ?INCONSISTENT ->
		    case models(Acc) of
			[] ->
			    retire(Bs4, A, Mark, GOpts),
			    istep(Next, KMin, KMax, Step, Trace, Print, Info,
				  Kind, BjParam, GOpts, Bs4);
			[Model|_] ->
			    result(Print, "bmc: counterexample at k=~w\n", [K]),
			    if Trace, Print -> io:put_chars(format_trace(Model));
			       true -> ok
			    end,
			    result(Print, "% 1\n", []),
			    {R, Acc, Bs4}
		    end;
		?TIMEOUT ->
		    result(Print, "% TIMEOUT\n", []),
		    {R, Acc, Bs4};
		?CANCEL ->
		    result(Print, "% USER ABORT\n", []),
		    {R, Acc, Bs4};
		_ ->
		    result(Print, "% ERROR\n", []),
		    {R, Acc, Bs4}
	    end
    end.

del_clauses(_Vp, false) -> ok;
del_clauses(Vp, I) ->
    varp_nif:del_clause(Vp, I),
    del_clauses(Vp, varp_nif:clauseset_next(Vp, I)).

%% build a formula and make it hold at the top level
assert_formula(F, Bs) ->
    case varp_formula:build(F, Bs) of
	{{bool,true}, Bs1} -> {true, Bs1};
	{{bool,false}, Bs1} -> {false, Bs1};
	{{bool,V}, Bs1} ->
	    Vp = Bs1#bs.vp,
	    0 = varp_nif:level(Vp),
	    {varp_nif:bind(Vp, V) andalso varp_nif:bcp(Vp), Bs1};
	{{uint,1,[V]}, Bs1} ->
	    Vp = Bs1#bs.vp,
	    {varp_nif:bind(Vp, V) andalso varp_nif:bcp(Vp), Bs1}
    end.

%% A refuted property is a fact: no path of length k satisfies it,
%% so its negation holds in every model of the database and can be
%% bound at the top level.
retire(_Bs, A, _Mark, _GOpts) when is_boolean(A) ->
    ok;
retire(Bs, A, {ClauseMark, VarMark}, GOpts) ->
    Vp = Bs#bs.vp,
    varp_nif:pop(Vp, ?TOP_LEVEL),
    %% The property's own clauses go, and the variables it created are
    %% bound: left free they would be decided by every later search
    %% and multiply the models by 2^n.
    varp_nif:clauseset_offset(Vp, ?DELTA, ClauseMark),
    del_clauses(Vp, varp_nif:clauseset_first(Vp, ?DELTA)),
    varp_nif:clauseset_offset(Vp, ?DELTA, 0),
    lists:foreach(
      fun(I) ->
	      case varp_nif:value(Vp, I) of
		  undefined -> varp_nif:bind(Vp, -I);
		  _ -> ok
	      end
      end, lists:seq(VarMark+1, varp:get_number_of_variables(Vp))),
    varp_nif:bcp(Vp),
    case maps:get(reset_order, GOpts, true) of
	true -> varp_nif:order_sort(Vp, identity, 0);
	false -> ok
    end,
    case maps:get(keep_learned, GOpts, true) of
	true -> ok;
	false ->
	    varp_nif:clauseset_offset(Vp, ?GAMMA, 0),
	    varp_formula:del_unused_clauses(Bs)
    end,
    case varp_nif:value(Vp, A) of
	false -> ok;
	true -> ?info(GOpts, "bmc: refuted property is true!\n", []);
	undefined ->
	    case varp_nif:bind(Vp, -A) andalso varp_nif:bcp(Vp) of
		true -> ok;
		false -> ?info(GOpts, "bmc: conflict when retiring the bound!\n", [])
	    end
    end.

loop(K, KMax, _Step, _Bound, _Trace, Print, _Do, _As, _Formula, _GOpts)
  when K > KMax ->
    result(Print, "% 0\n", []),
    {?INCONSISTENT, [], undefined};
loop(K, KMax, Step, Bound, Trace, Print, Do, As, Formula, GOpts) ->
    Meta = maps:get(meta, GOpts, #{}),
    GOptsK = GOpts#{ meta => Meta#{ Bound => K } },
    T0 = erlang:monotonic_time(),
    {R, Acc, Bs} = varp:do_run(Do, As, Formula, GOptsK),
    Ts = erlang:convert_time_unit(erlang:monotonic_time()-T0,
				  native, microsecond) / 1000000,
    Conflicts = case Bs of
		    #bs{} -> varp_nif:getstat(Bs#bs.vp, conflict_counter);
		    _ -> 0
		end,
    ?info(GOpts, "bmc: k=~w ~s ~.2fs conflicts=~w\n",
	  [K, verdict(R, Acc), Ts, Conflicts]),
    case R of
	?INCONSISTENT ->
	    loop(K+Step, KMax, Step, Bound, Trace, Print, Do, As, Formula, GOpts);
	_ when R =:= ?DONE; R =:= ?CONTINUE ->
	    case models(Acc) of
		[] ->
		    loop(K+Step, KMax, Step, Bound, Trace, Print,
			 Do, As, Formula, GOpts);
		[Model|_] ->
		    result(Print, "bmc: counterexample at k=~w\n", [K]),
		    if Trace, Print -> io:put_chars(format_trace(Model));
		       true -> ok
		    end,
		    result(Print, "% 1\n", []),
		    {R, Acc, Bs}
	    end;
	?TIMEOUT ->
	    result(Print, "% TIMEOUT\n", []),
	    {R, Acc, Bs};
	?CANCEL ->
	    result(Print, "% USER ABORT\n", []),
	    {R, Acc, Bs};
	_ ->
	    result(Print, "% ERROR\n", []),
	    {R, Acc, Bs}
    end.

result(false, _Fmt, _Args) -> ok;
result(_, Fmt, Args) -> io:format(Fmt, Args).

verdict(?INCONSISTENT, _) -> "UNSAT";
verdict(R, Acc) when R =:= ?DONE; R =:= ?CONTINUE ->
    case models(Acc) of
	[] -> "UNSAT";
	_ -> "SAT"
    end;
verdict(?TIMEOUT, _) -> "TIMEOUT";
verdict(_, _) -> "ERROR".

models(Acc) when is_list(Acc) -> Acc;
models(_) -> [].

nmodels(Acc) when is_list(Acc) -> length(Acc);
nmodels(N) when is_integer(N) -> N;
nmodels(_) -> 0.

%% satisfy unless the user gave a mode plugin
with_mode(Do) ->
    case lists:any(fun({P,_}) -> lists:member(P, [varp_satisfy, varp_falsify,
						  varp_prove]) end, Do) of
	true -> Do;
	false -> [{varp_satisfy, #{}} | Do]
    end.

%% backjump unless the user gave a search plugin
with_search(Do) ->
    case lists:any(fun({P,_}) -> lists:member(P, [varp_backjump,
						  varp_backtrack]) end, Do) of
	true -> Do;
	false -> Do ++ varp:parse_do([{backjump, []}])
    end.

%% ------------------------------------------------------------------
%% Trace: a model as one row per step.  Every symbol whose last
%% argument is an integer is taken as step indexed; bit vectors get a
%% column each, true booleans are listed in the last column.
%% ------------------------------------------------------------------

trace(Model) ->
    Indexed = [{Step, {p,Name,lists:droplast(Args)}, Value}
	       || {{p,Name,Args}, Value} <- Model,
		  Args =/= [], is_integer(lists:last(Args)),
		  binary:first(Name) =/= $$,   %% generated selectors
		  Step <- [lists:last(Args)]],
    Vectors = lists:usort([Var || {_, Var, {_Type,_Bits}} <- Indexed]),
    Steps = lists:usort([S || {S,_,_} <- Indexed]),
    Rows = [{S,
	     [value(lists:keyfind(V, 1, [{Var,Val} || {S1,Var,Val} <- Indexed,
						      S1 =:= S]))
	      || V <- Vectors],
	     lists:sort([var_name(Var) || {S1,Var,true} <- Indexed, S1 =:= S])}
	    || S <- Steps],
    {Vectors, Rows}.

value({_Var, {_Type, Bits}}) -> bits_to_string(Bits);
value(false) -> "-".

bits_to_string(Bits) ->
    L = tuple_to_list(Bits),
    case lists:member($*, L) of
	true -> L;
	false -> integer_to_list(list_to_integer(L, 2))
    end.

var_name({p,Name,[]}) -> binary_to_list(Name);
var_name({p,Name,Args}) ->
    binary_to_list(Name) ++ "(" ++
	string:join([fmt_arg(A) || A <- Args], ",") ++ ")".

fmt_arg(A) when is_integer(A) -> integer_to_list(A);
fmt_arg(A) when is_binary(A) -> binary_to_list(A);
fmt_arg(A) -> lists:flatten(io_lib:format("~p", [A])).

format_trace(Model) ->
    {Vectors, Rows} = trace(Model),
    Header = ["step" | [var_name(V) || V <- Vectors]] ++ ["input"],
    Table = [[integer_to_list(S) | Vals] ++ [string:join(Inputs, " ")]
	     || {S, Vals, Inputs} <- Rows],
    Widths = [lists:max([length(lists:nth(I, R)) || R <- [Header|Table]])
	      || I <- lists:seq(1, length(Header))],
    [format_row(Header, Widths) | [format_row(R, Widths) || R <- Table]].

format_row(Cells, Widths) ->
    N = length(Cells),
    Padded = [begin
		  Cell = lists:nth(I, Cells),
		  W = lists:nth(I, Widths),
		  if I =:= N -> Cell;   %% last column ragged
		     true -> string:pad(Cell, W, leading)
		  end
	      end || I <- lists:seq(1, N)],
    ["  ", string:join(Padded, "  "), "\n"].
