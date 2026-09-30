%%% saturate: level-k saturation with substitution, and the model that
%%% comes out of it. Each formula has a known answer for the level.
%%%
%%% The plugin evaluates every vector of k unbound variables in all 2^k
%%% ways, propagates each, and keeps what all consistent ways agree on:
%%% a value (the variable is bound) or an equivalence with a vector
%%% variable (substitution, --subst). A contradiction in every way is
%%% an inconsistent formula.

-module(varp_saturate_tests).

-include_lib("eunit/include/eunit.hrl").
-include("varp.hrl").

saturate(F, Params) ->
    varp_tc:quiet(fun() -> varp_tc:run(F, [{satisfy,[]},{saturate,Params}]) end).

%% the named variables of the model, undefined for the unbound ones
named(Bs) ->
    [{binary_to_list(Name), V} || {{p,Name,[]},V} <- varp_formula:model(Bs)].

stat(Bs, Key) -> varp_nif:getstat(Bs#bs.vp, Key).

%% the index of a plain variable
index(Bs, Name) ->
    {_Type, X} = varp_nif:find_symbol(Bs#bs.vp, {list_to_binary(Name), []}),
    abs(X).

%% all models of a plugin chain, sorted
models(F, Do) ->
    case varp_tc:quiet(fun() -> varp_tc:run(F, Do) end) of
	{?INCONSISTENT,_,_} -> [];
	{_,Ms,_} -> lists:sort([lists:sort(M) || M <- Ms])
    end.

%%%-------------------------------------------------------------------
%%% level 1
%%%-------------------------------------------------------------------

%% A=1 gives B, A=0 gives B: B is bound. C is left alone.
level1_bind_test() ->
    {R,_,Bs} = saturate("(A || B) && (!A || B) && (B || C)", [{level,1}]),
    ?assertEqual(?CONTINUE, R),
    ?assertEqual([{"A",undefined},{"B",true},{"C",undefined}], named(Bs)).

%% every assignment of A is contradictory
level1_inconsistent_test() ->
    F = "(A || B) && (A || !B) && (!A || B) && (!A || !B)",
    {R,_,_} = saturate(F, [{level,1}]),
    ?assertEqual(?INCONSISTENT, R),
    ?assertEqual([], models(F, [{satisfy,[]},{saturate,[]},{backtrack,[{max,0}]}])).

%% !W is a unit, so after bcp Z holds and the equivalences make X and Y
%% hold as well: nothing is left for saturation, the model is complete
level1_units_test() ->
    {R,_,Bs} = saturate("(X equ Y) && (Y equ Z) && (Z || W) && !W", [{level,1}]),
    ?assertEqual(?DONE, R),
    ?assertEqual([{"W",false},{"X",true},{"Y",true},{"Z",true}], named(Bs)),
    ?assertEqual(0, stat(Bs, number_of_unbound_variables)).

%%%-------------------------------------------------------------------
%%% substitution
%%%-------------------------------------------------------------------

%% A=1 gives B=1, C=1; A=0 gives B=0, C=1. C is bound, B is
%% substituted by A (or the other way round) and stays unbound in the
%% model until a value is decided.
subst_test() ->
    F = "(A equ B) && (B || C) && (!B || C)",
    {R,_,Bs} = saturate(F, [{level,1},{model,false}]),
    ?assertEqual(?CONTINUE, R),
    ?assertEqual([{"A",undefined},{"B",undefined},{"C",true}], named(Bs)),
    ?assertEqual(1, stat(Bs, number_of_subst_variables)),
    A = index(Bs, "A"), B = index(Bs, "B"),
    %% one of them is bound to the other, the same way round
    Ba = varp_nif:bound(Bs#bs.vp, A), Bb = varp_nif:bound(Bs#bs.vp, B),
    ?assert(Ba =:= B orelse Bb =:= A),
    ?assert(Ba =:= undefined orelse Bb =:= undefined),
    %% both keep their own names
    ?assertMatch([{{<<"A">>,[]},bool,1,0}], varp_nif:get_symbol(Bs#bs.vp, A)),
    ?assertMatch([{{<<"B">>,[]},bool,1,0}], varp_nif:get_symbol(Bs#bs.vp, B)).

subst_off_test() ->
    {R,_,Bs} = saturate("(A equ B) && (B || C) && (!B || C)", [{level,1},{subst,false},{model,false}]),
    ?assertEqual(?CONTINUE, R),
    ?assertEqual([{"A",undefined},{"B",undefined},{"C",true}], named(Bs)),
    ?assertEqual(0, stat(Bs, number_of_subst_variables)).

%% a substituted variable reports the value of its representative once
%% that is decided: the model is complete, and the same as without
%% saturation (this is what showed as * in md5 output). --model false,
%% or a lucky shot would end the run with one model
model_through_subst_test_() ->
    Fs = [{"boolean chain", "(A equ B) && (B equ C) && (C || D) && (A || !D)"},
	  {"vectors", "declare A:2, B:2, C:2; A == B && B == C && (C == 2 || C == 3)"},
	  {"arithmetic", "declare X:4, Y:4; X + 1 == Y && (Y == 5 || Y == 9)"}],
    [{Name,
      fun() ->
	      Plain = models(F, [{satisfy,[]},{backtrack,[{max,0}]}]),
	      Sat = models(F, [{satisfy,[]},{saturate,[{model,false}]},{backtrack,[{max,0}]}]),
	      Sat2 = models(F, [{satisfy,[]},{saturate,[{level,2},{model,false}]},{backtrack,[{max,0}]}]),
	      ?assert(Plain =/= []),
	      ?assertEqual(Plain, Sat),
	      ?assertEqual(Plain, Sat2),
	      [?assertNot(lists:keymember(undefined, 2, M)) || M <- Sat]
      end} || {Name, F} <- Fs].

%%%-------------------------------------------------------------------
%%% level 2
%%%-------------------------------------------------------------------

%% B is forced by every assignment of the pair (A,C), but no single
%% variable shows it: level 1 finds nothing, level 2 binds B. The two
%% extra pairs keep any vector of two from binding everything, which
%% would end the run with a model (A || C is a gate g: !g binds A, C
%% and B, and !E binds F)
level2_test_() ->
    F = "(A || C || B) && (A || !C || B) && (!A || C || B) && (!A || !C || B)"
	" && (E || F) && (G || H)",
    [{"level 1 finds nothing",
      fun() ->
	      {R,_,Bs} = saturate(F, [{level,1}]),
	      ?assertEqual(?CONTINUE, R),
	      ?assertEqual([{"A",undefined},{"B",undefined},{"C",undefined},
			    {"E",undefined},{"F",undefined},{"G",undefined},{"H",undefined}],
			   named(Bs))
      end},
     {"level 2 binds B",
      fun() ->
	      {R,_,Bs} = saturate(F, [{level,2}]),
	      ?assertEqual(?CONTINUE, R),
	      ?assertEqual([{"A",undefined},{"B",true},{"C",undefined},
			    {"E",undefined},{"F",undefined},{"G",undefined},{"H",undefined}],
			   named(Bs))
      end},
     {"level 1 with one extra variable (--seq 1) binds B as well",
      fun() ->
	      {R,_,Bs} = saturate(F, [{level,1},{q,1}]),
	      ?assertEqual(?CONTINUE, R),
	      ?assertEqual(true, proplists:get_value("B", named(Bs)))
      end}].

%% a pair that is contradictory in all four ways
level2_inconsistent_test() ->
    F = "(A || C) && (A || !C) && (!A || C) && (!A || !C)",
    {R,_,_} = saturate(F, [{level,2}]),
    ?assertEqual(?INCONSISTENT, R).

%%%-------------------------------------------------------------------
%%% md5 through the command line
%%%-------------------------------------------------------------------

%% the missing byte is found with saturation in the chain and the
%% substituted bits print with their values
md5_saturate_test_() ->
    {timeout, 120,
     fun() ->
	     Md5 = filename:join(varp_tc:formula_dir("varp"), "md5.varp"),
	     H = "5eb63bbbe01eeed093cb22bb8f5acdc3",
	     {0, Out} = varp_tc:cli(["--partial", "sat", "saturate", "bj",
				     "msg=hello *orld", "digest=" ++ H, Md5]),
	     ?assert(string:find(Out, "msg=\"hello world\"") =/= nomatch)
     end}.

%%%-------------------------------------------------------------------
%%% a model by a lucky shot, and substitutions in the output
%%%-------------------------------------------------------------------

%% A=1 propagates C, !D and then B: every variable bound without a
%% conflict is a model, reported at once
lucky_shot_test() ->
    F = "(A || B) && (!A || C) && (!A || !D) && (B || D)",
    {R, Ms, _Bs} = saturate(F, [{level,1}]),
    ?assertEqual(?DONE, R),
    ?assertMatch([[_|_]], Ms),
    [M] = Ms,
    ?assertEqual([{"A",true},{"B",true},{"C",true},{"D",false}],
		 [{binary_to_list(N), V} || {{p,N,[]},V} <- M]),
    %% counted the same way
    {?DONE, 1, _} = varp_tc:quiet(fun() -> varp_tc:run(F, [{satisfy,[]},{saturate,[]}], #{method => count}) end),
    %% and off: B is what every assignment of A agrees on, the rest is open
    {?CONTINUE, [], Bs2} = saturate(F, [{model,false}]),
    ?assertEqual([{"A",undefined},{"B",true},{"C",undefined},{"D",undefined}], named(Bs2)).

%% --print=literal: B is substituted by A, which has no value
print_literal_test() ->
    F = "(A equ B) && (B || C) && (!B || C) && (E || F)",
    {0, Out} = varp_tc:cli(["--partial", "--print=literal", "-f", F, "sat", "saturate"]),
    ?assert(string:find(Out, "B=A") =/= nomatch orelse string:find(Out, "A=B") =/= nomatch),
    %% the default flavour leaves the substituted variable out
    {0, Out2} = varp_tc:cli(["--partial", "-f", F, "sat", "saturate"]),
    ?assertEqual(nomatch, string:find(Out2, "=")).

%% md5: with the message bits first in the order and one byte per
%% vector, the assignment that is the missing byte binds everything
md5_lucky_shot_test_() ->
    {timeout, 120,
     fun() ->
	     Md5 = filename:join(varp_tc:formula_dir("varp"), "md5.varp"),
	     H = "5eb63bbbe01eeed093cb22bb8f5acdc3",
	     {0, Out} = varp_tc:cli(["--partial", "sat", "order", "--first=X",
				     "saturate", "-k=1", "-seq=7",
				     "msg=hello *orld", "digest=" ++ H, Md5]),
	     ?assert(string:find(Out, "msg=\"hello world\"") =/= nomatch),
	     ?assert(string:find(Out, "% 1") =/= nomatch)
     end}.

%% without sat the main variable is unbound and nothing propagates,
%% which is mostly a mistake: a warning, unless --warn=false
warn_test() ->
    {0, Out} = varp_tc:cli(["--partial", "-f", "A && (B || C)", "saturate"]),
    ?assert(string:find(Out, "main variable is not bound") =/= nomatch),
    {0, Out2} = varp_tc:cli(["--partial", "-f", "A && (B || C)", "saturate", "--warn=false"]),
    ?assertEqual(nomatch, string:find(Out2, "main variable")),
    {0, Out3} = varp_tc:cli(["--partial", "-f", "A && (B || C)", "sat", "saturate"]),
    ?assertEqual(nomatch, string:find(Out3, "main variable")).
