%%% Arithmetic circuit library (varp_arith) tests.
-module(varp_arith_tests).

-include_lib("eunit/include/eunit.hrl").

%% varp_bitvec is exercised through varp_arith, this only checks the
%% pure conversions.  Bit vectors are least significant bit first.
bitvec_test() ->
    ?assertEqual({uint,3,[false,false,true]}, varp_bitvec:from_unsigned(4,3)),
    ?assertEqual({uint,3,[true,false,true]},  varp_bitvec:from_unsigned(5,3)),
    ?assertEqual({uint,3,[false,false,false]},varp_bitvec:from_unsigned(0,3)),
    ?assertEqual({uint,3,[true,true,true]},   varp_bitvec:from_unsigned(7,3)),
    ?assertEqual({int,4,[true,true,true,true]}, varp_bitvec:from_signed(-1,4)),
    %% a wider vector is zero extended
    ?assertEqual({uint,4,[true,false,true,false]}, varp_bitvec:from_unsigned(5,4)).

math_test() ->
    ?assertEqual(1, varp_math:unsigned_size(0)),
    ?assertEqual(1, varp_math:unsigned_size(1)),
    ?assertEqual(2, varp_math:unsigned_size(3)),
    ?assertEqual(3, varp_math:unsigned_size(4)),
    ?assertEqual(4, varp_math:unsigned_size(8)),
    ?assert(varp_math:signed_size(-1) >= 1),
    ?assert(varp_math:signed_size(-8) >= 4).

%%
%% The varp_arith self test, moved here from the module 2026-11-20.
%%

% every encoder against an exhaustive enumeration of its operands: the
% circuit must have exactly the models the Erlang function gives.  The
% test_c* cases are constants only, so unit propagation alone (bcp)
% must produce the model.
library_test_() ->
    {timeout, 900,
     [
     {"test_abs(3)", ?_assert(test_abs(3))},
     {"test_negate(3)", ?_assert(test_negate(3))},
     {"test_uband(3)", ?_assert(test_uband(3))},
     {"test_iband(3)", ?_assert(test_iband(3))},
     {"test_ubor(3)", ?_assert(test_ubor(3))},
     {"test_ibor(3)", ?_assert(test_ibor(3))},
     {"test_ubxor(3)", ?_assert(test_ubxor(3))},
     {"test_ibxor(3)", ?_assert(test_ibxor(3))},
     {"test_ubnot(3)", ?_assert(test_ubnot(3))},
     {"test_ibnot(3)", ?_assert(test_ibnot(3))},
     {"test_veq(3)", ?_assert(test_veq(3))},
     {"test_vlt(3)", ?_assert(test_vlt(3))},
     {"test_umin(3)", ?_assert(test_umin(3))},
     {"test_imin(3)", ?_assert(test_imin(3))},
     {"test_umax(3)", ?_assert(test_umax(3))},
     {"test_imax(3)", ?_assert(test_imax(3))},
     {"test_ult(3)", ?_assert(test_ult(3))},
     {"test_ulte(3)", ?_assert(test_ulte(3))},
     {"test_ugt(3)", ?_assert(test_ugt(3))},
     {"test_ugte(3)", ?_assert(test_ugte(3))},
     {"test_ueq(3)", ?_assert(test_ueq(3))},
     {"test_uneq(3)", ?_assert(test_uneq(3))},
     {"test_clt(4, 2)", ?_assert(test_clt(4, 2))},
     {"test_ilt(3)", ?_assert(test_ilt(3))},
     {"test_ilte(3)", ?_assert(test_ilte(3))},
     {"test_igt(3)", ?_assert(test_igt(3))},
     {"test_igte(3)", ?_assert(test_igte(3))},
     {"test_ieq(3)", ?_assert(test_ieq(3))},
     {"test_ineq(3)", ?_assert(test_ineq(3))},
     {"test_uadd(3)", ?_assert(test_uadd(3))},
     {"test_iadd(3)", ?_assert(test_iadd(3))},
     {"test_usub(3)", ?_assert(test_usub(3))},
     {"test_isub(3)", ?_assert(test_isub(3))},
     {"test_umult(3)", ?_assert(test_umult(3))},
     {"test_imult(3)", ?_assert(test_imult(3))},
     {"test_udiv(4)", ?_assert(test_udiv(4))},
     {"test_idiv(4)", ?_assert(test_idiv(4))},
     {"test_urem(4)", ?_assert(test_urem(4))},
     {"test_irem(4)", ?_assert(test_irem(4))},
     {"test_cadd(3, 5)", ?_assert(test_cadd(3, 5))},
     {"test_cadd(-3, 5)", ?_assert(test_cadd(-3, 5))},
     {"test_csub(3, 5)", ?_assert(test_csub(3, 5))},
     {"test_csub(-3, 5)", ?_assert(test_csub(-3, 5))},
     {"test_cmult(3, 5)", ?_assert(test_cmult(3, 5))},
     {"test_cmult(1, 5)", ?_assert(test_cmult(1, 5))},
     {"test_cmult(5, 0)", ?_assert(test_cmult(5, 0))},
     {"test_cmin(3, 5)", ?_assert(test_cmin(3, 5))},
     {"test_cmin(5, 3)", ?_assert(test_cmin(5, 3))},
     {"test_cmin(-3, 5)", ?_assert(test_cmin(-3, 5))},
     {"test_cmin(-5, 3)", ?_assert(test_cmin(-5, 3))},
     {"test_cmax(2, 4)", ?_assert(test_cmax(2, 4))},
     {"test_cmax(4, 2)", ?_assert(test_cmax(4, 2))},
     {"test_cmax(-2, 4)", ?_assert(test_cmax(-2, 4))},
     {"test_cmax(-4, 2)", ?_assert(test_cmax(-4, 2))}
     ]}.

-define(name(Name), <<??Name>>).
-define(sym(Name), {<<??Name>>,[]}).

%% unsigned range
eval_uu(Fun, N) ->
    Mu = (1 bsl N), U = lists:seq(0,Mu-1),
    lists:foldl(
      fun({Y,Z}, Acc) ->
	      try Fun(Y,Z) of
		  X -> [[{?sym(x),X},{?sym(y),Y},{?sym(z),Z}]|Acc]
	      catch
		  error:_ ->
		      Acc
	      end
      end, [], [{Y,Z} || Y <- U, Z <- U]).

%% unsigned range
eval_iu(Fun, N) ->
    Mi = (1 bsl (N-1)), I = lists:seq(-Mi,Mi-1),
    Mu = (1 bsl N), U = lists:seq(0,Mu-1),
    lists:foldl(
      fun({Y,Z}, Acc) ->
	      try Fun(Y,Z) of
		  X -> [[{?sym(x),X},{?sym(y),Y},{?sym(z),Z}]|Acc]
	      catch
		  error:_ ->
		      Acc
	      end
      end, [], [{Y,Z} || Y <- I, Z <- U]).

%% integer range
eval_ii(Fun, N) ->
    Mi = (1 bsl (N-1)), I = lists:seq(-Mi,Mi-1),
    lists:foldl(
      fun({Y,Z}, Acc) ->
	      try Fun(Y,Z) of
		  X -> [[{?sym(x),X},{?sym(y),Y},{?sym(z),Z}]|Acc]
	      catch
		  error:_ ->
		      Acc
	      end
      end, [], [{Y,Z} || Y <- I, Z <- I]).

%% one integer range
eval_i(Fun, N) ->
    Mi = (1 bsl (N-1)), I = lists:seq(-Mi,Mi-1),
    lists:foldl(
      fun(Y, Acc) ->
	      try Fun(Y) of
		  X -> [[{?sym(x),X},{?sym(y),Y}]|Acc]
	      catch
		  error:_ ->
		      Acc
	      end
      end, [], I).

eval_u(Fun, N) ->
    Mu = (1 bsl N), U = lists:seq(0,Mu-1),
    lists:foldl(
      fun(Y, Acc) ->
	      try Fun(Y) of
		  X -> [[{?sym(x),X},{?sym(y),Y}]|Acc]
	      catch
		  error:_ ->
		      Acc
	      end
      end, [], U).

%% model eval, only true values are returned
meval_u(Fun, N) ->
    Mu = (1 bsl N), U = lists:seq(0,Mu-1),
    lists:foldl(
      fun(Y, Acc) ->
	      try Fun(Y) of
		  true -> [[{?sym(x),true},{?sym(y),Y}]|Acc];
		  false -> Acc
	      catch
		  error:_ ->
		      Acc
	      end
      end, [], U).

add_symbol(Vp, {Type,_,Xs}, Var) ->
    varp_nif:add_symbol(Vp, {Var,[]}, Xs, Type);
add_symbol(Vp, Xs, Var) ->
    varp_nif:add_symbol(Vp, {Var,[]}, Xs, bool).

test_i(N, Opts, Arith, Eval) ->
    Vp = varp_nif:new(Opts),
    Y = varp_arith:ivar(Vp, N),
    add_symbol(Vp, Y, ?name(y)),
    X = Arith(Vp, Y),
    add_symbol(Vp, X, ?name(x)),
    varp_circuit:bt_match(Vp, eval_i(Eval, N)).

test_ii(N, Opts, Arith, Eval) ->
    Vp = varp_nif:new(Opts),
    Y = varp_arith:ivar(Vp, N),
    Z = varp_arith:ivar(Vp, N),
    add_symbol(Vp, Y, ?name(y)),
    add_symbol(Vp, Z, ?name(z)),
    X = Arith(Vp, Y, Z),
    add_symbol(Vp, X, ?name(x)),
    varp_circuit:bt_match(Vp, eval_ii(Eval, N)).

test_iu(N, Opts, Arith, Eval) ->
    Vp = varp_nif:new(Opts),
    Y = varp_arith:ivar(Vp, N),
    Z = varp_arith:uvar(Vp, N),
    add_symbol(Vp, Y, ?name(y)),
    add_symbol(Vp, Z, ?name(z)),
    X = Arith(Vp, Y, Z),
    add_symbol(Vp, X, ?name(x)),
    varp_circuit:bt_match(Vp, eval_iu(Eval, N)).

test_u(N, Opts, Arith, Eval) ->
    Vp = varp_nif:new(Opts),
    Y = varp_arith:uvar(Vp, N),
    add_symbol(Vp, Y, ?name(y)),
    X = Arith(Vp, Y),
    add_symbol(Vp, X, ?name(x)),
    varp_circuit:bt_match(Vp, eval_u(Eval, N)).

test_uu(N, Opts, Arith, Eval) ->
    Vp = varp_nif:new(Opts),
    Y = varp_arith:uvar(Vp, N),
    Z = varp_arith:uvar(Vp, N),
    add_symbol(Vp, Y, ?name(y)),
    add_symbol(Vp, Z, ?name(z)),
    X = Arith(Vp, Y, Z),
    add_symbol(Vp, X, ?name(x)),
    varp_circuit:bt_match(Vp, eval_uu(Eval, N)).

test_cc(A, B, Opts, Arith, Eval) ->
    Vp = varp_nif:new(Opts),
    Y = varp_arith:iconst(A),
    Z = varp_arith:iconst(B),
    add_symbol(Vp, Y, ?name(y)),
    add_symbol(Vp, Z, ?name(z)),
    X = Arith(Vp, Y, Z),
    add_symbol(Vp, X, ?name(x)),
    %% model symbols are {Name,Index}, like eval_* build them
    varp_circuit:bcp_match(Vp, [{?sym(x),Eval(A,B)},
				{?sym(y),A},{?sym(z),B}]).


test_vlt(N) ->
    Vp = varp_nif:new(#{}),
    Y = {_,_,Ys} = varp_arith:uvar(Vp, N),
    Z = {_,_,Zs} = varp_arith:uvar(Vp, N),
    add_symbol(Vp, Y, ?name(y)),
    add_symbol(Vp, Z, ?name(z)),
    Lt = varp_arith:vlt(Vp, Ys, Zs),
    add_symbol(Vp, Lt, ?name(x)),
    varp_circuit:bt_match(Vp, eval_uu(fun erlang:'<'/2, N)).

test_veq(N) ->
    Vp = varp_nif:new(#{}),
    Y = {_,_,Ys} = varp_arith:uvar(Vp, N),
    Z = {_,_,Zs} = varp_arith:uvar(Vp, N),
    add_symbol(Vp, Y, ?name(y)),
    add_symbol(Vp, Z, ?name(z)),
    Eq = varp_arith:veq(Vp, Ys, Zs),
    add_symbol(Vp, Eq, ?name(x)),
    %% varp_nif_test:dump(Vp),
    varp_circuit:bt_match(Vp, eval_uu(fun erlang:'=='/2, N)).

test_uadd(N) ->
    test_uu(N, #{carry=>false},   fun varp_arith:add/3, fun erlang:'+'/2).

test_iadd(N) ->
    test_ii(N, #{}, fun varp_arith:add/3, fun erlang:'+'/2).

test_cadd(A, B) ->
    test_cc(A, B, #{}, fun varp_arith:add/3, fun erlang:'+'/2).
    
test_usub(N) ->
    test_uu(N, #{borrow=>false}, 
	    fun varp_arith:subtract/3, fun (A,B) when A>=B -> A-B end).

test_isub(N) ->
    test_ii(N, #{}, fun varp_arith:subtract/3, fun erlang:'-'/2).

test_csub(A, B) ->
    test_cc(A, B, #{}, fun varp_arith:subtract/3, fun erlang:'-'/2).

test_umult(N) ->
    test_uu(N, #{carry=>false},
	    fun varp_arith:multiply/3, fun erlang:'*'/2).

test_imult(N) ->
    test_ii(N, #{carry=>false},
	    fun varp_arith:multiply/3, fun erlang:'*'/2).

test_cmult(A, B) ->
    test_cc(A, B, #{}, fun varp_arith:multiply/3, fun erlang:'*'/2).

test_udiv(N) ->
    test_uu(N, #{divz=>false}, fun varp_arith:divide/3, fun erlang:'div'/2).

test_idiv(N) ->
    true = test_iu(N, #{divz=>false}, fun varp_arith:divide/3, fun erlang:'div'/2),
    test_ii(N, #{divz=>false}, fun varp_arith:divide/3, fun erlang:'div'/2).

test_urem(N) ->
    test_uu(N, #{divz=>false}, fun varp_arith:reminder/3, fun erlang:'rem'/2).

test_irem(N) ->
    true = test_iu(N, #{divz=>false}, fun varp_arith:reminder/3, fun erlang:'rem'/2),
    test_ii(N, #{divz=>false}, fun varp_arith:reminder/3, fun erlang:'rem'/2).

test_umin(N) ->
    test_uu(N, #{}, fun varp_arith:min/3, fun erlang:min/2).

test_imin(N) ->
    test_ii(N, #{}, fun varp_arith:min/3, fun erlang:min/2).

test_cmin(A,B) ->
    test_cc(A, B, #{}, fun varp_arith:min/3, fun erlang:min/2).

test_umax(N) ->
    test_uu(N, #{}, fun varp_arith:max/3, fun erlang:max/2).

test_imax(N) ->
    test_ii(N, #{}, fun varp_arith:max/3, fun erlang:max/2).

test_cmax(A,B) ->
    test_cc(A, B, #{}, fun varp_arith:max/3, fun erlang:max/2).

test_abs(N) ->
    test_i(N, #{}, fun varp_arith:abs/2, fun erlang:abs/1).

test_negate(N) ->
    test_i(N, #{}, fun varp_arith:negate/2, fun erlang:'-'/1).

test_uband(N) ->
    test_uu(N, #{},   fun varp_arith:bitwise_and/3, fun erlang:'band'/2).

test_iband(N) ->
    test_ii(N, #{}, fun varp_arith:bitwise_and/3, fun erlang:'band'/2).

test_ubor(N) ->
    test_uu(N, #{},   fun varp_arith:bitwise_or/3, fun erlang:'bor'/2).

test_ibor(N) ->
    test_ii(N, #{},   fun varp_arith:bitwise_or/3, fun erlang:'bor'/2).

test_ubxor(N) ->
    test_uu(N, #{},   fun varp_arith:bitwise_xor/3, fun erlang:'bxor'/2).

test_ibxor(N) ->
    test_ii(N, #{},   fun varp_arith:bitwise_xor/3, fun erlang:'bxor'/2).

test_ubnot(N) ->
    Mask = (1 bsl N) - 1,
    test_u(N, #{},   fun varp_arith:bitwise_not/2, 
	   fun(X) -> (bnot X) band Mask end).

test_ibnot(N) ->
    test_i(N, #{},   fun varp_arith:bitwise_not/2, fun erlang:'bnot'/1).

%% Test Y:n < K
test_clt(N, K) ->
    Vp = varp_nif:new(#{}),
    Y = varp_arith:uvar(Vp, N),
    C = varp_arith:iconst(K, N),
    add_symbol(Vp, Y, ?name(y)),
    Lt = varp_arith:lt(Vp, Y, C),
    add_symbol(Vp, Lt, ?name(x)),
    varp_nif:bind(Vp, Lt),
    varp_circuit:bt_match(Vp, meval_u(fun (Yi) -> Yi < 2 end, N)).
    
test_ult(N) ->
    test_uu(N, #{}, fun varp_arith:lt/3, fun erlang:'<'/2).

test_ulte(N) ->
    test_uu(N, #{}, fun varp_arith:lte/3, fun erlang:'=<'/2).

test_ugt(N) ->
    test_uu(N, #{}, fun varp_arith:gt/3, fun erlang:'>'/2).

test_ugte(N) ->
    test_uu(N, #{}, fun varp_arith:gte/3, fun erlang:'>='/2).

test_ueq(N) ->
    test_uu(N, #{}, fun varp_arith:eq/3, fun erlang:'=='/2).

test_uneq(N) ->
    test_uu(N, #{}, fun varp_arith:neq/3, fun erlang:'=/='/2).

test_ilt(N) ->
    test_ii(N, #{}, fun varp_arith:lt/3, fun erlang:'<'/2).

test_ilte(N) ->
    test_ii(N, #{}, fun varp_arith:lte/3, fun erlang:'=<'/2).

test_igt(N) ->
    test_ii(N, #{}, fun varp_arith:gt/3, fun erlang:'>'/2).

test_igte(N) ->
    test_ii(N, #{}, fun varp_arith:gte/3, fun erlang:'>='/2).

test_ieq(N) ->
    test_ii(N, #{}, fun varp_arith:eq/3, fun erlang:'=='/2).

test_ineq(N) ->
    test_ii(N, #{}, fun varp_arith:neq/3, fun erlang:'=/='/2).

%%
%% min/max over every operand type, 3-argument (result sized by
%% varp_arith) and 4-argument (result vector given, as a statement
%% X = min(Y,Z) uses it).  Found 2026-11-20: vite_/6 passed the
%% condition and the result literal to varp_circuit:ite/5 in the wrong
%% order, which broke every X = min/max/abs(..) statement, and min/4
%% over unsigned crashed.
%%

minmax_types_test_() ->
    Types = [uint, int, bit, bool],
    {timeout, 300,
     [{lists:flatten(io_lib:format("~w(~w,~w)", [Op,Ty,Tz])),
       ?_assert(minmax3(Op, Ty, Tz, 3))}
      || Op <- [min,max], Ty <- Types, Tz <- Types] ++
     [{lists:flatten(io_lib:format("~w = ~w(~w,~w)", [Tx,Op,Ty,Tz])),
       ?_assert(minmax4(Op, Tx, Ty, Tz))}
      || Op <- [min,max], Tx <- Types, Ty <- Types, Tz <- Types,
	 fits_bool(Tx, Ty, Tz)]}.

%% a boolean destination is one bit: it holds two unsigned or two
%% boolean operands, but a mixed or signed pair is converted to signed
%% first and the sign bit does not fit
fits_bool(bool, Ty, Tz) -> Ty =:= Tz andalso lists:member(Ty, [uint,bool]);
fits_bool(_, _, _) -> true.

%% a variable of each kind with its value range
mk(Vp, uint, N) -> {varp_arith:uvar(Vp,N), lists:seq(0,(1 bsl N)-1)};
mk(Vp, int, N)  -> {varp_arith:ivar(Vp,N),
		    lists:seq(-(1 bsl (N-1)),(1 bsl (N-1))-1)};
mk(Vp, bit, N)  -> {uint,N,Xs} = varp_arith:uvar(Vp,N),
		   {{bit,N,Xs}, lists:seq(0,(1 bsl N)-1)};
mk(Vp, bool, _) -> {{bool,varp_circuit:var(Vp)}, [0,1]}.

%% bit vectors are registered as unsigned, the bits are the same
msym(Vp, {bool,X}, Name) -> varp_nif:add_symbol(Vp,{Name,[]},X,bool);
msym(Vp, {bit,_,Xs}, Name) -> varp_nif:add_symbol(Vp,{Name,[]},Xs,uint);
msym(Vp, {T,_,Xs}, Name) -> varp_nif:add_symbol(Vp,{Name,[]},Xs,T).

%% the value a symbol of that kind shows in a model
mval({bool,_}, V) -> V =/= 0;
mval({int,_,_}, V) -> V;
mval({_,K,_}, V) -> V band ((1 bsl K) - 1).

minmax3(Op, Ty, Tz, N) ->
    Vp = varp_nif:new(#{}),
    {Y,Ys} = mk(Vp,Ty,N), {Z,Zs} = mk(Vp,Tz,N),
    msym(Vp,Y,<<"y">>), msym(Vp,Z,<<"z">>),
    X = varp_arith:Op(Vp,Y,Z),
    msym(Vp,X,<<"x">>),
    varp_circuit:bt_match(
      Vp, [[{?sym(x),mval(X,erlang:Op(A,B))},
	    {?sym(y),mval(Y,A)},{?sym(z),mval(Z,B)}] || A <- Ys, B <- Zs]).

%% the destination is one bit wider than the operands so a signed
%% conversion of an unsigned operand fits; a boolean destination takes
%% one bit operands.  An unsigned destination shows a negative result
%% as its two's complement bits.
minmax4(Op, Tx, Ty, Tz) ->
    {N, Xn} = case Tx of bool -> {1, 1}; _ -> {3, 4} end,
    Vp = varp_nif:new(#{}),
    {X0,_} = mk(Vp,Tx,Xn), {Y,Ys} = mk(Vp,Ty,N), {Z,Zs} = mk(Vp,Tz,N),
    msym(Vp,Y,<<"y">>), msym(Vp,Z,<<"z">>),
    X = varp_arith:Op(Vp,X0,Y,Z),
    msym(Vp,X,<<"x">>),
    varp_circuit:bt_match(
      Vp, [[{?sym(x),mval(X,erlang:Op(A,B))},
	    {?sym(y),mval(Y,A)},{?sym(z),mval(Z,B)}] || A <- Ys, B <- Zs]).
