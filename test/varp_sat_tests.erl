%%% SAT / PROOF and the solver plugins.
-module(varp_sat_tests).

-include_lib("eunit/include/eunit.hrl").
-include("varp.hrl").

run(T, Do) -> varp_tc:run(T, Do).
run(T, Do, O) -> varp_tc:run(T, Do, O).

result(T, Do) -> element(1, run(T, Do)).
acc(T, Do) -> element(2, run(T, Do)).

%%%-------------------------------------------------------------------
%%% satisfy / prove / falsify
%%%-------------------------------------------------------------------

%% 'satisfy' binds the main variable to true
satisfy_test() ->
    ?assertEqual(?DONE, result("A && B", [{satisfy,[]},{backtrack,[{max,0}]}])),
    ?assertEqual(?INCONSISTENT,
		 result("A && !A", [{satisfy,[]},{backtrack,[{max,0}]}])).

%% 'prove' binds the main variable to false, an inconsistency means the
%% formula is a tautology
prove_test() ->
    ?assertEqual(?INCONSISTENT,
		 result("A or !A", [{prove,[]},{backtrack,[{max,1}]}])),
    ?assertEqual(?INCONSISTENT,
		 result("((A -> B) and (B -> C)) -> (A -> C)",
			[{prove,[]},{backtrack,[{max,1}]}])),
    %% a contingent formula is not a tautology, so a counter model exists
    {R,Ms,_} = run("A and B", [{prove,[]},{backtrack,[{max,1}]}]),
    ?assert(lists:member(R,[?DONE,?CONTINUE])),
    ?assertEqual(1, length(Ms)).

%% 'falsify' binds the main variable to false and looks for a model
falsify_test() ->
    ?assertEqual(?DONE,
		 result("A and B", [{falsify,[]},{backtrack,[{max,0}]}])),
    ?assertEqual(?INCONSISTENT,
		 result("A or !A", [{falsify,[]},{backtrack,[{max,0}]}])).

%%%-------------------------------------------------------------------
%%% backtrack vs backjump
%%%-------------------------------------------------------------------

%% both search plugins must agree on the number of models
search_agreement_test_() ->
    Fs = ["A && B",
	  "A || B || C",
	  "[EQ 2,i=1..4] P(i)",
	  "[E i=1..3] P(i)",
	  "declare X:4,Y:4; (X*Y == 12) && (X>1) && (Y>1) && (X<=Y)"],
    [{F, {timeout, 60, fun() ->
			       Bt = acc(F, [{satisfy,[]},{backtrack,[{max,0}]}]),
			       Bj = acc(F, [{satisfy,[]},{backjump,[{max,0}]}]),
			       ?assertEqual(length(Bt), length(Bj))
		       end}} || F <- Fs].

%% counting mode returns an integer instead of a model list
count_method_test() ->
    {?DONE,N,_} = run("[EQ 2,i=1..4] P(i)",
		      [{satisfy,[]},{backtrack,[{max,0}]}],
		      #{method => count}),
    ?assertEqual(6, N).

%% max limits the number of models
max_models_test() ->
    ?assertEqual(2, length(acc("[E i=1..4] P(i)",
			       [{satisfy,[]},{backtrack,[{max,2}]}]))),
    ?assertEqual(15, length(acc("[E i=1..4] P(i)",
				[{satisfy,[]},{backtrack,[{max,0}]}]))).

%%%-------------------------------------------------------------------
%%% Classic instances
%%%-------------------------------------------------------------------

pigeon_hole_test_() ->
    F = "( ([A p=1..n] [E h=1..(n-1)] P(p,h)) and"
	"  ([A h=1..(n-1)] [A p=1..n] [A q=1..n,p<q]"
	"      not (P(p,h) and P(q,h))) )",
    [{"pigeon "++integer_to_list(N)++" backjump",
      {timeout, 120,
       fun() ->
	       R = run(F, [{satisfy,[]},{backjump,[{max,1}]}],
		       #{meta => #{<<"n">> => N}}),
	       ?assertEqual(?INCONSISTENT, element(1,R))
       end}} || N <- [3,4,5,6]].

%% n pigeons into n holes is satisfiable
pigeon_sat_test() ->
    F = "( ([A p=1..n] [E h=1..n] P(p,h)) and"
	"  ([A h=1..n] [A p=1..n] [A q=1..n,p<q]"
	"      not (P(p,h) and P(q,h))) )",
    {R,Ms,_} = run(F, [{satisfy,[]},{backjump,[{max,1}]}],
		   #{meta => #{<<"n">> => 4}}),
    ?assert(lists:member(R,[?DONE,?CONTINUE])),
    ?assertEqual(1, length(Ms)).

%%%-------------------------------------------------------------------
%%% Proof output
%%%-------------------------------------------------------------------

proof_output_test() ->
    Dir = varp_tc:tmpdir(),
    File = "sat_proof.out",
    Path = filename:join(Dir, File),
    _ = file:delete(Path),
    F = "( ([A p=1..4] [E h=1..3] P(p,h)) and"
	"  ([A h=1..3] [A p=1..4] [A q=1..4,p<q]"
	"      not (P(p,h) and P(q,h))) )",
    R = run(F, [{satisfy,[]},{backjump,[{max,1}]}],
	    #{proof_output => text, proof_file => File, outdir => Dir}),
    ?assertEqual(?INCONSISTENT, element(1,R)),
    ?assert(filelib:is_regular(Path)),
    ?assert(filelib:file_size(Path) > 0),
    {ok,Bin} = file:read_file(Path),
    %% a DRAT style proof is a sequence of a/d lines
    Lines = [L || L <- binary:split(Bin,<<"\n">>,[global,trim]), L =/= <<>>],
    ?assert(length(Lines) > 0).

%%%-------------------------------------------------------------------
%%% Timeouts
%%%-------------------------------------------------------------------

%% a hard instance with a short global timeout must abort, not hang
global_timeout_test_() ->
    F = "( ([A p=1..n] [E h=1..(n-1)] P(p,h)) and"
	"  ([A h=1..(n-1)] [A p=1..n] [A q=1..n,p<q]"
	"      not (P(p,h) and P(q,h))) )",
    Opts = #{meta => #{<<"n">> => 11}, timeout => 0.2},
    [{"backtrack",
      {timeout, 60,
       fun() -> ?assertMatch(?TIMEOUT,
			     element(1,run(F,[{satisfy,[]},
					      {backtrack,[{max,0}]}],Opts)))
       end}},
     {"backjump",
      {timeout, 60,
       fun() -> ?assertMatch(?TIMEOUT,
			     element(1,run(F,[{satisfy,[]},
					      {backjump,[{max,0}]}],Opts)))
       end}}].

%% a plugin local timeout is not fatal, the chain continues
local_timeout_test() ->
    F = "( ([A p=1..n] [E h=1..(n-1)] P(p,h)) and"
	"  ([A h=1..(n-1)] [A p=1..n] [A q=1..n,p<q]"
	"      not (P(p,h) and P(q,h))) )",
    R = run(F, [{satisfy,[]},{backtrack,[{max,0},{timeout,0.05}]}],
	    #{meta => #{<<"n">> => 11}}),
    ?assertEqual(?CONTINUE, element(1,R)).

%% a binary proof written by backjump must be accepted by the
%% validate plugin
proof_validate_test_() ->
    {timeout, 120,
     fun() ->
	     Dir = varp_tc:tmpdir(),
	     Path = filename:join(Dir, "sat_proof.bin"),
	     _ = file:delete(Path),
	     F = "( ([A p=1..4] [E h=1..3] P(p,h)) and"
		 "  ([A h=1..3] [A p=1..4] [A q=1..4,p<q]"
		 "      not (P(p,h) and P(q,h))) )",
	     R = run(F, [{satisfy,[]},{backjump,[{max,1}]}],
		     #{proof_output => binary, proof_file => "sat_proof.bin",
		       outdir => Dir}),
	     ?assertEqual(?INCONSISTENT, element(1,R)),
	     ?assert(filelib:file_size(Path) > 0),
	     Out = varp_tc:quiet(
		     fun() ->
			     run(F, [{satisfy,[]},
				     {validate,[{type,binary},{file,Path}]}])
		     end),
	     ?assert(lists:member(element(1,Out),[?DONE,?CONTINUE]))
     end}.

%% validate on a missing proof file must fail gracefully
validate_missing_file_test() ->
    R = varp_tc:quiet(
	  fun() ->
		  run("A or B",
		      [{validate,[{type,binary},{file,"/no/such/proof"}]}])
	  end),
    ?assertEqual(?ERROR, element(1,R)).

%%%-------------------------------------------------------------------
%%% Other plugins, smoke tests
%%%-------------------------------------------------------------------

%% these must run to completion without crashing
plugin_smoke_test_() ->
    F = "(A or B) and (!A or C) and (B or !C)",
    Plugins = [{order,[]},
	       {saturate,[]},
	       %% NOTE: satord needs a selection vector that fits the number
	       %% of variables, with its defaults (size 10, 1000 iterations)
	       %% it spins forever on a formula this small
	       {satord,[{size,2},{iter,3},{rounds,1}]},
	       {reduction,[]},
	       {rat,[]},
	       {succ,[]},
	       {clean,[]}],
    [{atom_to_list(element(1,P)),
      {timeout, 60,
       fun() ->
	       R = varp_tc:quiet(
		     fun() -> run(F, [{satisfy,[]},P,{backtrack,[{max,1}]}]) end),
	       ?assertMatch({_,_,_}, R),
	       ?assert(lists:member(element(1,R),
				    [?DONE,?CONTINUE,?INCONSISTENT]))
       end}} || P <- Plugins].

%% every plugin named in the application env must be loadable
plugins_loadable_test() ->
    {ok,_} = application:ensure_all_started(varp),
    {ok,Ps} = application:get_env(varp, plugins),
    Map = varp:load_plugins(),
    lists:foreach(
      fun({Short,Long,Mod}) ->
	      ?assertEqual({Short,Mod}, {Short,maps:get(Short,Map,undefined)}),
	      ?assertEqual({Long,Mod}, {Long,maps:get(Long,Map,undefined)}),
	      ?assert(erlang:function_exported(Mod, options, 0)),
	      ?assert(erlang:function_exported(Mod, run, 2))
      end, Ps).

%%%-------------------------------------------------------------------
%%% Propagation order
%%%-------------------------------------------------------------------

%% --qtype selects the order in which implied literals are propagated.
%% It changes which conflict is met first, never the answer.
propagation_order_test_() ->
    Pigeon = "( ([A p=1..n] [E h=1..(n-1)] P(p,h)) and"
	"  ([A h=1..(n-1)] [A p=1..n] [A q=1..n,p<q]"
	"      not (P(p,h) and P(q,h))) )",
    [{atom_to_list(Q),
      {timeout, 120,
       fun() ->
	       O = #{qtype => Q},
	       ?assert(varp_tc:is_unsat(Pigeon, O#{meta => #{<<"n">> => 5}})),
	       ?assertEqual(6, varp_tc:count("[EQ 2,i=1..4] P(i)", O)),
	       ?assertEqual(1, varp_tc:count(
				 "declare X:4,Y:4; (X*Y == 15) && (X>1) && (Y>1) && (X<=Y)", O)),
	       ?assert(varp_tc:is_tautology("(A -> B) and (B -> C) -> (A -> C)", O)),
	       {R,Ms,_} = run(Pigeon, [{satisfy,[]},{backjump,[{max,1}]}],
			      O#{meta => #{<<"n">> => 4}}),
	       ?assertEqual(?INCONSISTENT, R),
	       ?assertEqual([], Ms)
       end}} || Q <- [recursive, lifo, fifo]].
