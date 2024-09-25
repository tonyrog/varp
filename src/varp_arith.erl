%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2023, Tony Rogvall
%%% @doc
%%%    The arithmetic part 
%%% @end
%%% Created :  6 Jan 2023 by Tony Rogvall <tony@rogvall.se>

-module(varp_arith).

-export([ivar/2]).
-export([uvar/2]).
-export([iconst/1, iconst/2]).
-export([uconst/1, uconst/2]).
-export([negate/2]).
-export([sign/2]).
-export([abs/2]).
-export([add/3]).
-export([subtract/3]).
-export([multiply/3]).
-export([shl/3]).
-export([shr/3]).
-export([rol/3]).
-export([ror/3]).
-export([divide/3]).
-export([reminder/3]).
-export([min/3]).
-export([max/3]).
-export([bitwise_and/3]).
-export([bitwise_or/3]).
-export([bitwise_xor/3]).
-export([bitwise_not/2]).
%% compare
-export([lt/3]).
-export([lte/3]).
-export([gt/3]).
-export([gte/3]).
-export([eq/3]).
-export([neq/3]).

-export([vadd/3, vadd/4]).
-export([vadd_ci/5, vadd_co/4, vadd_co/5, vadd_ci_co/5, vadd_ci_co/6]).
-export([vsub/3, vsub/4]).
-export([vlt/3]).
-export([set_status/3]).
-export([set_overflow/5]).

-export([test/0]).
%% -compile(export_all).

-include("varp.hrl").

%% -type varp_lit() :: integer() | false | true.
%% -type varp_vec_type() :: int | uint | bit.
%% -type varp_vec() :: {varp_vec_type(), Size::integer(),[varp_lit()]}.

neg(true) -> false;
neg(false) -> true;
neg(X) -> -X.

ivar(Vp, N) when is_integer(N), N > 0 ->
    {int, N, varp_bitvec:new(Vp, N)}.

uvar(Vp, N) when is_integer(N), N > 0 ->
    {uint, N, varp_bitvec:new(Vp, N)}.

iconst(I) when is_integer(I) ->
    varp_bitvec:from_signed(I).
iconst(I, N) when is_integer(I), is_integer(N), N>= 0 ->
    varp_bitvec:from_signed(I, N).

uconst(U) when is_integer(U), U >=0  ->
    varp_bitvec:from_unsigned(U).
uconst(U, N) when is_integer(U), U >= 0, is_integer(N), N>= 0 ->
    varp_bitvec:from_unsigned(U, N).

negate(_Vp, {bool,A}) -> neg(A);
negate(Vp, A) -> subtract(Vp, {int,1,[false]}, A).  %% 0 - A

sign(_Vp, {bool,_}) -> false;
sign(_Vp, {uint,_,_}) -> false;
sign(_Vp, {int,_,Xs}) -> lists:last(Xs).

abs(_Vp, {bool,A}) -> A;
abs(_Vp, A={uint,_,_}) -> A;
abs(_Vp, A={bit,_,_}) -> A;
abs(Vp, A={int,An,Ax}) ->
    S = sign(Vp, A),
    {int,Bn,Bx} = negate(Vp, A),
    Ax1 = Ax ++ if An<Bn -> lists:duplicate(Bn-An,S); true -> [] end,
    Cx = vite(Vp,S,Bx,Ax1),
    normalize(uint,Bn,Cx).

add(Vp, A, B) ->
    Ct = case mix_type(A,B) of
	     bool -> uint;
	     Ct0 -> Ct0
	 end,
    {At,An,Ax} = xarg(Ct,A),
    {Bt,Bn,Bx} = xarg(Ct,B),
    Cn = erlang:max(An,Bn)+1,
    Ax1 = vextend(At,Ax,An,Cn),
    Bx1 = vextend(Bt,Bx,Bn,Cn),
    {[Ci,Cj|_],Cx} = vadd(Vp,Ax1,Bx1),
    Carry = varp_nif:getopt(Vp, carry),
    set_status(Vp, Ci, Carry),
    Overflow = varp_nif:getopt(Vp, overflow),
    set_overflow(Vp,Ct,Ci,Cj,Overflow),
    normalize(Ct,length(Cx),Cx).

subtract(Vp, A, B) ->
    Ct = case mix_type(A,B) of
	     bool -> int;
	     uint -> int;
	     T -> T
	 end,
    {At,An,Ax} = xarg(Ct,A),
    {Bt,Bn,Bx} = xarg(Ct,B),
    Cn = erlang:max(An,Bn)+1,
    Ax1 = vextend(At,Ax,An,Cn),
    Bx1 = vextend(Bt,Bx,Bn,Cn),
    {[Ci,Cj|_],Cx} = vsub(Vp,Ax1,Bx1),
    Borrow = varp_nif:getopt(Vp, borrow),
    set_status(Vp,neg(Ci),Borrow),
    Overflow = varp_nif:getopt(Vp, overflow),
    set_overflow(Vp,Ct,Ci,Cj,Overflow),
    normalize(Ct,length(Cx),Cx).

multiply(Vp,A,B) ->
    Ct = case mix_type(A,B) of
	     bool -> uint;
	     Ct0 -> Ct0
	 end,
    {At,An,Ax} = xarg(Ct,A),
    {Bt,Bn,Bx} = xarg(Ct,B),
    Cx =
	if Ct =:= int ->
		Cn0 = erlang:max(An,Bn),
		Ax1 = vextend(At,Ax,An,Cn0),
		Bx1 = vextend(Bt,Bx,Bn,Cn0),
		%% io:format("Ax1=~w, Bx1=~w\n", [Ax1,Bx1]),
		vsmul(Vp,Ax1,Bx1);
	   An < Bn ->
		vmul(Vp,Ax,Bx);
	   true ->
		vmul(Vp,Bx,Ax)
	end,
    Cn = length(Cx),
    normalize(Ct,Cn,Cx).

%% FIXME int
divide(Vp,Y,{uint,Zm,Zs}) ->
    {Yt,Yn,Ys} = abs(Vp,Y), %% varg(Y),
    K = erlang:max(Yn,Zm),
    Ys1 = vextend(Yt,Ys,Yn,K),
    Zs1 = vextend(uint,Zs,Zm,K),
    {Qs,_Rs,DivZero} = vdivrem(Vp,Ys1,Zs1),
    DivZ = varp_nif:getopt(Vp, divz),
    set_status(Vp,DivZero,DivZ),
%%    normalize(Yt,K,Qs).
    normalize(Yt,Qs).

%% FIXME int
reminder(Vp, {uint,N,Ys},{uint,M,Zs}) ->
    K = erlang:max(N,M),
    Ys1 = vextend(uint,Ys,N,K),
    Zs1 = vextend(uint,Zs,M,K),
    {_Qs,Rs,DivZero} = vdivrem(Vp,Ys1,Zs1), %% fixme vrem! 
    DivZ = varp_nif:getopt(Vp, divz),
    set_status(Vp,DivZero,DivZ),
    {uint,K,Rs}.

min(Vp,{bool,Y},{bool,Z}) ->
    varp_circuit:and_gate(Vp,Y,Z);
min(Vp,{uint,An,Ax},{uint,Bn,Bx}) ->
    Cn = erlang:max(An,Bn),
    Ax1 = vextend(uint,Ax,An,Cn),
    Bx1 = vextend(uint,Bx,Bn,Cn),
    Cond = vlt(Vp,Ax1,Bx1),
    Cx = vite(Vp,Cond,Ax1,Bx1),
    {uint,Cn,Cx};
min(Vp,A,B) ->
    {_At,An,Ax} = iarg(A),
    {_Bt,Bn,Bx} = iarg(B),
    Cn = erlang:max(An,Bn),
    Ax1 = vextend(int,Ax,An,Cn),
    Bx1 = vextend(int,Bx,Bn,Cn),
    {Ax2,[Ak]} = lists:split(Cn-1,Ax1),
    {Bx2,[Bk]} = lists:split(Cn-1,Bx1),
    Q = varp_circuit:equ_gate(Vp,Ak,Bk),
    Lt = vlt(Vp,Ax2,Bx2),
    A1 = varp_circuit:and_gate(Vp,Q,Lt),
    L = varp_circuit:lt_gate(Vp,Bk,Ak),
    Cond = varp_circuit:or_gate(Vp, A1, L),
    Cx = vite(Vp,Cond,Ax1,Bx1),
    {int,Cn,Cx}.

max(Vp,{bool,Y},{bool,Z}) ->
    varp_circuit:or_gate(Vp,Y,Z);
max(Vp,{uint,An,Ax},{uint,Bn,Bx}) ->
    Cn = erlang:max(An,Bn),
    Ax1 = vextend(uint,Ax,An,Cn),
    Bx1 = vextend(uint,Bx,Bn,Cn),
    Cond = vlt(Vp,Bx1,Ax1),
    Cx = vite(Vp,Cond,Ax1,Bx1),
    {uint,Cn,Cx};
max(Vp,A,B) ->
    {_At,An,Ax} = iarg(A),
    {_Bt,Bn,Bx} = iarg(B),
    Cn = erlang:max(An,Bn),
    Ax1 = vextend(int,Ax,An,Cn),
    Bx1 = vextend(int,Bx,Bn,Cn),
    {Ax2,[Ak]} = lists:split(Cn-1,Ax1),
    {Bx2,[Bk]} = lists:split(Cn-1,Bx1),
    Q = varp_circuit:equ_gate(Vp,Bk,Ak),
    Lt = vlt(Vp,Bx2,Ax2),
    A1 = varp_circuit:and_gate(Vp,Q,Lt),
    L = varp_circuit:lt_gate(Vp,Ak,Bk),
    Cond = varp_circuit:or_gate(Vp, A1, L),
    Cx = vite(Vp,Cond,Ax1,Bx1),
    {int,Cn,Cx}.

%% shift left
shl(_Vp,A,B) ->
    {At,An,Ax} = varg(A),
    K = vconst(B),
    Ax1 = if K =:= false ->
		  error({shift_not_constant, B});
	     K >=0 ->
		  vshift_left(K,Ax);
	     At =:= int ->
		  vshift_right(-K,An,Ax);
	     true ->
		  vushift_right(-K,An,Ax)
	  end,
    normalize(At,Ax1).

%% shift right
shr(_Vp,A,B) ->
    {At,An,Ax} = varg(A),
    K = vconst(B),
    Ax1 = if K =:= false ->
		  error({shift_not_constant, B});
	     K >=0, At =:= int ->
		  vshift_right(K,An,Ax);
	     K >= 0 ->
		  vushift_right(K,An,Ax);
	     K < 0 ->
		  vshift_left(-K,Ax)
	  end,
    normalize(At,Ax1).
	    
%% rotate
rol(_Vp,A,B) ->
    {At,An,Ax} = varg(A),
    K = vconst(B),
    if K =:= false ->
	    error({shift_not_constant, B});
       K >= 0 ->
	    K1 = K rem An,
	    {Ax1,Ax2} = lists:split(K1, Ax),
	    Ax3 = Ax2++Ax1,
	    {At,An,Ax3}
    end.

%% rotate right
ror(_Vp,A,B) ->
    {At,An,Ax} = varg(A),
    K = vconst(B),
    if K =:= false ->
	    error({shift_not_constant, B});
       K >= 0 ->
	    K1 = K rem An,
	    {Ax1,Ax2} = lists:split(An-K1, Ax),
	    Ax3 = Ax2++Ax1,
	    {At,An,Ax3}
    end.

bitwise_not(_Vp, {bool,A}) ->
    {bool,neg(A)};
bitwise_not(Vp, A) ->
    {At,An,Ax} = varg(A),
    Cx = varp_bitvec:bitwise_not(Vp, Ax),
    {At,An,Cx}.

bitwise_and(Vp, A, B) ->
    {At,An,Ax} = varg(A),
    {Bt,Bn,Bx} = varg(B),
    Cn = erlang:max(An,Bn),
    Ax1 = vextend(At,Ax,An,Cn),
    Bx1 = vextend(Bt,Bx,Bn,Cn),
    Cx = varp_bitvec:bitwise_and(Vp, Ax1, Bx1),
    Ct = mix_type(At,Bt),
    if Ct =:= bool ->
	    [C1] = Cx,
	    {bool,C1};
       true ->
	    {Ct,Cn,Cx}
    end.

bitwise_or(Vp, A, B) ->
    {At,An,Ax} = varg(A),
    {Bt,Bn,Bx} = varg(B),
    Cn = erlang:max(An,Bn),
    Ax1 = vextend(At,Ax,An,Cn),
    Bx1 = vextend(Bt,Bx,Bn,Cn),
    Cx = varp_bitvec:bitwise_or(Vp,Ax1,Bx1),
    Ct = mix_type(At,Bt),
    if Ct =:= bool ->
	    [C1] = Cx,
	    {bool,C1};
       true ->
	    {Ct,Cn,Cx}
    end.

bitwise_xor(Vp, A, B) ->
    {At,An,Ax} = varg(A),
    {Bt,Bn,Bx} = varg(B),
    Cn = erlang:max(An,Bn),
    Ax1 = vextend(At,Ax,An,Cn),
    Bx1 = vextend(Bt,Bx,Bn,Cn),
    Cx = varp_bitvec:bitwise_xor(Vp,Ax1,Bx1),
    Ct = mix_type(At,Bt),
    if Ct =:= bool ->
	    [C1] = Cx,
	    {bool,C1};
       true ->
	    {Ct,Cn,Cx}
    end.

%% A < B  <=>  A - B < 0 ?
lt(Vp,{bool,A},{bool,B}) ->
    varp_circuit:lt_gate(Vp, A, B);
lt(Vp,{uint,An,Ax},{uint,Bn,Bx}) ->
    Cn = erlang:max(An,Bn),
    Ax1 = vextend(uint,Ax,An,Cn),
    Bx1 = vextend(uint,Bx,Bn,Cn),
    vlt(Vp,Ax1,Bx1);
lt(Vp,A,B) ->
    {_At,An,Ax} = iarg(A),
    {_Bt,Bn,Bx} = iarg(B),
    Cn = erlang:max(An,Bn),
    Ax1 = vextend(int,Ax,An,Cn),
    Bx1 = vextend(int,Bx,Bn,Cn),
    {Ax2,[Ak]} = lists:split(Cn-1,Ax1),
    {Bx2,[Bk]} = lists:split(Cn-1,Bx1),
    Q = varp_circuit:equ_gate(Vp,Ak,Bk),
    Lt = vlt(Vp,Ax2,Bx2),
    A1 = varp_circuit:and_gate(Vp,Q,Lt),
    L = varp_circuit:lt_gate(Vp,Bk,Ak),
    varp_circuit:or_gate(Vp, A1, L).

gt(Vp,{bool,A},{bool,B}) ->
    varp_circuit:gt_gate(Vp, A, B);
gt(Vp,A,B) ->
    lt(Vp, B, A).

lte(Vp,A,B) ->
    neg(lt(Vp,B,A)).

gte(Vp,A,B) ->
    lte(Vp,B,A).

neq(Vp,{bool,A},{bool,B}) ->
    varp_circuit:xor_gate(Vp, A, B);
neq(Vp,Y,Z) ->
    neg(eq(Vp, Y, Z)).

eq(Vp,{bool,A},{bool,B}) ->
    varp_circuit:equ_gate(Vp, A, B);
eq(Vp,{uint,An,Ax},{uint,Bn,Bx}) ->
    Cn = erlang:max(An,Bn),
    Ax1 = vextend(uint,Ax,An,Cn),
    Bx1 = vextend(uint,Bx,Bn,Cn),    
    veq(Vp,Ax1,Bx1);
eq(Vp,A,B) ->
    {At,An,Ax} = iarg(A),
    {Bt,Bn,Bx} = iarg(B),
    Cn = erlang:max(An,Bn),
    Ax1 = vextend(At,Ax,An,Cn),
    Bx1 = vextend(Bt,Bx,Bn,Cn),
    veq(Vp,Ax1,Bx1).

%%
%% Multiplier circuit: Y*Z
%%
%%  Y = (y0 + y1*2^1 + y2*2^2 + ... yk*2^k)
%%  Z = (z0 + z1*2^1 + z2*2^2 + ... zl*2^l)
%% 
%%  Y*Z = y0*Z + y1*2^1*Z + ... yk*2^k*Z
%%
%%  yi*2^i*Z = yi*z0*2^(i+0) + yi*z1*2^(i+1) + yi*zj*2^(i+j)
%%
%% Ex1
%% Y=7:3 [1,1,1] * Z=5:3[1,0,1]
%%
%% 0: Xs=[0,0,0]
%% 1: [0,0,0]     + [1,0,1]     = [1,0,1,0]
%% 2: [1,0,1,0]   + [0,1,0,1]   = [1,1,1,1,0]
%% 3: [1,1,1,1,0] + [0,0,1,0,1] = [1,1,0,0,0,1]
%%
vmul(Vp,[Y|Ys],Zs) ->
    Xs = varp_bitvec:map_op(Vp,'and',Zs,Y),
    vmul_(Vp, Ys, Zs, 1, Xs++[false]).

vmul_(Vp, [Y|Ys], Zs, I, Xs) ->
    YZs = varp_bitvec:map_op(Vp,'and',Zs,Y),
    YZs1 = lists:duplicate(I,false)++YZs,
    {[Co|_],Xs1} = vadd(Vp,Xs,YZs1),
    vmul_(Vp,Ys,Zs,I+1,Xs1++[Co]);
vmul_(_Vp,[],_Zs,_I,Xs) ->
    Xs.

%% Signed multiply
vsmul(Vp,[Y|Ys],Zs) ->
    YZs = varp_bitvec:map_op(Vp,'and',Zs,Y),
    Xs1 = vsnot(YZs)++[true],
    vsmul_(Vp,Ys, Zs, 1, Xs1).

vsmul_(Vp,[Y],Zs,I,Xs) ->
    YZs = varp_bitvec:map_op(Vp,'and',Zs,Y),
    YZs1 = lists:duplicate(I,false)++
	vsnot(vnot(Vp,YZs))++[true],
    {[_Co|_],Xs1} = vadd(Vp,Xs++[false],YZs1),
    Xs1;
vsmul_(Vp,[Y|Ys],Zs,I,Xs) ->
    YZs = varp_bitvec:map_op(Vp,'and',Zs,Y),
    YZs1 = lists:duplicate(I,false)++vsnot(YZs),
    {[Co|_],Xs1} = vadd(Vp,Xs,YZs1),
    vsmul_(Vp,Ys, Zs, I+1, Xs1++[Co]);
vsmul_(_Vp,[],_Zs,_I,Xs) ->
    Xs.

%%
%% Divider/Reminder circuit  (X/Y)
%%   X : N bits
%%   Y : N bits
%%
%%   R = 0
%%   for (i = 0; i < N; i++) {
%%	R <<= 1;
%%	if (HIGHBIT(X))
%%	    R |= 1;
%%	X <<= 1;
%%	if (R < Y)
%%	    X &= ~1; %% clear low bit
%%	else {
%%	    R -= Y;
%%	    X |= 1;
%%	}
%%
%%   what about:  X = Q*Y + R !!!
%%
vdivrem(Vp,X,Y) ->
    N = length(Y),
    Zs = vextend(uint,[],0,N),
    {Q,R} = vdivrem_(Vp,X,Y,Zs,N,N),
    DivZero = veq(Vp,Y,Zs),
    {Q,R,DivZero}.

vdivrem_(_Vp, X, _Y, R, _N, 0) ->
    {X, R};
vdivrem_(Vp, X, Y, R, N, I) ->
    %% R << 1
    [R0|Rs] = vshift_left(1, N, R),      
    Xn = lists:last(X),
    %% if (HIGHBIT(X)) R |= 1;
    R00 = varp_circuit:ite(Vp,Xn,true,R0),
    R1 = [R00|Rs],
    %% X <<= 1;
    [_X10|X1] = vshift_left(1, N, X),
    %% if (R < Y)  X &= ~1; else X |= 1;
    Lt = vlt(Vp,R1,Y),
    X2 = [neg(Lt)|X1],
    %% R=R-Y
    {[BorrowNot|_],R2} = vsub(Vp, R1, Y),
    set_status(Vp,neg(BorrowNot),ignore),
    %% if (R < Y) R=R; R=R-Y
    R3 = vite(Vp, Lt, R1, R2),
    vdivrem_(Vp, X2, Y, R3, N, I-1).

%%
%% Reminder circuit  (X%Y)
%%   X : N bits
%%   Y : N bits
%%
%%   R = 0
%%   for (i = 0; i < N; i++) {
%%	R <<= 1;
%%	if (HIGHBIT(X))
%%	    R |= 1;
%%	X <<= 1;
%%	if (R >= Y)
%%	    R -= Y;
%%   }
%%
-ifdef(__UNUSED__).

vrem(Vp, X, Y) ->
    N = length(Y),
    Zs = vextend(uint,[],0,N),  %% R = 0
    {R,Bs1} = vrem(Vp, X, Y, Zs, N, N),
    DivZero = veq(Vp, Y,Zs),
    {R,DivZero}.

vrem(Vp,_X, _Y, R, _N, 0) ->
    R;
vrem(Vp, X, , Y, R, N, I) ->
    %% R << 1
    [R0|Rs] = vshift_left(1, N, R),      
    Xn = lists:last(X),
    %% if (HIGHBIT(X)) R |= 1;
    R00 = varp_circuit:ite(Vp, Xn, true, R0),
    R1 = [R00|Rs],
    Lt = vlt(Vp, R1, Y),
    %% R = R - Y
    {[BorrowNot|_],R2} = vsub(Vp, R1, Y),
    set_status(Vp,neg(BorrowNot),ignore),
    %% if (R < Y) R=R; R = R - Y
    R3 = vite(Vp, Lt, R1, R2),
    vrem(Vp, tl(X), Y, R3, N, I-1).
-endif.

vnot(Vp,Xs) -> 
    varp_bitvec:bitwise_not(Vp,Xs).

%% negate "high" bit
vsnot([X]) -> [neg(X)];
vsnot([X|Xs]) -> [X|vsnot(Xs)];
vsnot([]) -> [].

vsub(Vp, Ys, Zs) ->
    vadd_ci(Vp, Ys, vnot(Vp,Zs), true).

vsub(Vp, Xs, Ys, Zs) ->
    vadd_ci(Vp, Xs, Ys, vnot(Vp,Zs), true).

%% adder
vadd(Vp, Ys, Zs) ->
    vadd_(Vp, Ys, Zs, false, varp_circuit:var(Vp)).

vadd(Vp, Xs, Ys, Zs) ->
    vadd_(Vp, Xs, Ys, Zs, false, varp_circuit:var(Vp)).

%% adder with carry in
vadd_ci(Vp, Ys, Zs, Ci) ->
    vadd_(Vp, Ys, Zs, Ci, varp_circuit:var(Vp)).

vadd_ci(Vp, Xs, Ys, Zs, Ci) ->
    vadd_(Vp, Xs, Ys, Zs, Ci, varp_circuit:var(Vp)).

%% adder with carry out
vadd_co(Vp, Ys, Zs, Co) ->
    vadd_(Vp, Ys, Zs, false, Co).

vadd_co(Vp, Xs, Ys, Zs, Co) ->
    vadd_(Vp, Xs, Ys, Zs, false, Co).

%% adder with carry in and carry out
vadd_ci_co(Vp, Ys, Zs, Ci, Co) ->
    vadd_(Vp, Ys, Zs, Ci, Co).

vadd_ci_co(Vp, Xs, Ys, Zs, Ci, Co) ->
    vadd_(Vp, Xs, Ys, Zs, Ci, Co).

vadd_(Vp, Ys, Zs, Ci, Co) ->
    Xs = varp_circuit:vars(Vp,length(Ys)),
    vadd_(Vp, Xs, Ys, Zs, Ci, Co).

vadd_(Vp, Xs, Ys, Zs, Ci, Co) ->
    Cs = vadd__(Vp, Xs, Ys, Zs, [Ci], Co),
    {[Co|Cs], Xs}.

vadd__(Vp, [X], [Y], [Z], Cs=[Ci|_], Co) ->
    {X,Co} = varp_circuit:full_adder(Vp, X, Y, Z, Ci, Co),
    [Co|Cs];
vadd__(Vp, [X|Xs], [Y|Ys], [Z|Zs], Cs=[Ci|_], Co) ->
    {X,Cx} = varp_circuit:full_adder(Vp, X, Y, Z, Ci),
    vadd__(Vp, Xs, Ys, Zs, [Cx|Cs], Co).

%% 
%% Generate carry look-ahead
%% then feed them into half address also using Gs
%% G(i) = Y(i)Z(i)
%% P(i) = Y(i)+Z(i)
%% C(0) = FALSE | TRUE
%% C(1) = G(0) + P(0)C(0)
%% C(2) = G(1) + P(1)G(0)+P(1)P(0)C(0)
%% C(3) = G(2) + P(2)G(1)+P(2)P(1)G(0)+P(2)P(1)P(0)C(0)
%% C(4) = G(3) + P(3)G(2)+P(3)P(2)G(1)+P(3)P(2)P(1)G(0)+P(3)P(2)P(1)P(0)C(0)
%% C(i+1) = G(i) + (P(i)*(Ci))
%% S(0) = Y(0) xor Z(0)
%% S(1) = Y(1) xor Z(1) xor C(1)
%% S(i) = Y(i) xor Z(i) xor C(i)
%%
%% vadd_fast(Ys,Zs,C0,Bs) ->
%%     %% io:format("vadd_fast: ~w, ~w\n", [Ys,Zs]),
%%     {Gs,Bs1} = map_op('and',Ys,Zs,Bs),
%%     {Ps,Bs2} = map_op('or',Ys,Zs,Bs1),
%%     {Cs,Bs3} = carry_lookahead(Gs,Ps,{bool,C0},Bs2),
%%     vadd_fast_sum(Ys,Zs,Cs,Bs3).

%% vadd_fast_sum(Ys,Zs,Cs,Bs) ->
%%     vadd_fast_sum_(Ys,Zs,Cs,[],[],Bs).

%% vadd_fast_sum_([Yi|Ys],[Zi|Zs],[Ci|Cs],Sum,Ca,Bs) ->
%%     {X1,Bs1} = operation('xor',{bool,Yi},{bool,Zi},Bs),
%%     {{bool,X2},Bs2} = operation('xor',X1,Ci,Bs1),
%%     vadd_fast_sum_(Ys,Zs,Cs,[X2|Sum],[Ci|Ca],Bs2);
%% vadd_fast_sum_([],[],[Co],Sum,Ca,Bs) ->
%%     {[Co|Ca],lists:reverse(Sum),Bs}.

%% carry_lookahead(Gs,Ps,C0,Bs) ->
%%     carry_lookahead_(Gs,Ps,1,length(Gs)+1,[C0],C0,Bs).

%% carry_lookahead_(_Gs,_Ps,I,I,Cs,_C0,Bs) ->
%%     {lists:reverse(Cs),Bs};
%% carry_lookahead_(Gs,Ps,I,N,Cs,C0,Bs) ->
%%     G = lists:sublist(Gs,I),      %% [G(0),G(1),..G(i)]
%%     P = lists:sublist(Ps,I),      %% [P(0),P(1),..P(i)]
%%     {X0,Bs1} = all([C0|P],Bs),
%%     {Ci,Bs1} = carry_ci(G,tl(P),[X0],Bs),
%%     carry_lookahead_(Gs,Ps,I+1,N,[Ci|Cs],C0,Bs1).

%% carry_ci([Gn],[],Xs,Bs) ->
%%     any([Gn|Xs], Bs);
%% carry_ci([Gi|Gs],P,Xs,Bs) ->
%%     {Xi,Bs1} = all([Gi|P],Bs),
%%     carry_ci(Gs,tl(P),[Xi|Xs],Bs1).


%% Handle carry (Is it wise to backtrack over a Carry variable?)
set_status(Vp, Ci, false) ->    %% never generate carry
    varp_circuit:xor_gate(Vp,false,Ci,false);
set_status(Vp, Ci, true) ->     %% always generate carry
    varp_circuit:xor_gate(Vp,false,Ci,true);
set_status(_Vp,_Ci, ignore) ->  %% allow carry overflow
    ignore.


set_overflow(Vp,int,Ci,Cj, false) -> %% never generate overflow
    varp_circuit:xor_gate(Vp,false,Ci,Cj);
set_overflow(Vp,int,Ci,Cj, true) -> %% always generate overflow
    varp_circuit:xor_gate(Vp,true,Ci,Cj);
set_overflow(Vp,_Type,Ci,_Cj,false) -> %% never generate overflow
    varp_circuit:xor_gate(Vp,false,Ci,false);
set_overflow(Vp,_Type,Ci,_Cj,true) -> %% never generate overflow
    varp_circuit:xor_gate(Vp,false,Ci,true);
set_overflow(_Vp,_Type,_Ci,_Cj, ignore) ->  %% allow carry overflow
    ignore.

%% vector version of ite condition control if Ys or Zs is passed
vite(Vp,I,Ys,Zs) ->
    vite_(Vp,I,Ys,Zs,[]).
    
vite_(Vp,I,[Y|Ys],[Z|Zs],Xs) ->
    X = varp_circuit:ite(Vp,I,Y,Z),
    vite_(Vp,I,Ys,Zs,[X|Xs]);
vite_(_Vp,_I,[],[],Xs) ->
    lists:reverse(Xs).

vshift_left(K,Xs) when K >= 0 ->
    lists:duplicate(K,false) ++ Xs.

vshift_left(K,N,Xs) when K >= 0 ->
    K1 = erlang:min(K,N),
    lists:duplicate(K1,false) ++ lists:sublist(Xs,1,N-K1).

%% unsigned shift K steps to the right while keeping the length to N
vushift_right(K,N,Xs) when K >= 0 ->
    K1 = erlang:min(K,N),
    lists:sublist(Xs, K1+1, N) ++ lists:duplicate(K1,false).

%% signed shift right K steps keeping the length to N
vshift_right(K,N,Xs) when K >= 0 ->
    K1 = erlang:min(K,N),
    SignBit = lists:nth(N, Xs),
    lists:sublist(Xs, K1+1, N) ++ lists:duplicate(K1,SignBit).

veq(Vp, Ys, Zs) ->
    Xs = varp_bitvec:map_op(Vp,'equ',Ys,Zs),
    %% io:format("~w = ~w equ ~w\n", [Xs, Ys, Zs]),
    varp_bitvec:fold_op(Vp,'and',true,Xs).

%% Compare less
vlt(Vp, [Y],[Z]) ->
    varp_circuit:lt_gate(Vp, Y, Z);
vlt(Vp,[Y1|Ys],[Z1|Zs]) ->
    {Lt0,Eq0} = vlteq(Vp,Ys,Zs),
    L1 = varp_circuit:lt_gate(Vp,Y1,Z1),
    L2 = varp_circuit:and_gate(Vp,Eq0,L1),
    varp_circuit:or_gate(Vp,L2,Lt0).

%%
%%  Lt0 = Y0 < Z0
%%  Eq0 = Y0 = Z0
%%  Lt1 = (Eq0 && (Y1 < Z1)) | Lt0
%%  Eq1 = Eq0 && (Y1 = Z1)
%%  
vlteq(Vp,[Y0],[Z0]) ->
    Lt0 = varp_circuit:lt_gate(Vp,Y0,Z0),
    Eq0 = varp_circuit:equ_gate(Vp,Y0,Z0),
    {Lt0,Eq0};
vlteq(Vp,[Y1|Ys],[Z1|Zs]) ->
    {Lt0,Eq0} = vlteq(Vp,Ys,Zs),
    L1 = varp_circuit:lt_gate(Vp,Y1,Z1),
    E1 = varp_circuit:equ_gate(Vp,Y1,Z1),
    L2 = varp_circuit:and_gate(Vp,Eq0,L1),
    Lt = varp_circuit:or_gate(Vp,L2,Lt0),
    Eq = varp_circuit:and_gate(Vp,Eq0,E1),
    {Lt,Eq}.

%% do type check and return the common type
-spec mix_type(A::ptype(),B::ptype()) -> ptype();
	      (A::pbits(),B::pbits()) -> ptype().
mix_type({At,_,_},{Bt,_,_}) -> mix_type(At,Bt);
mix_type({At,_,_},{Bt,_}) -> mix_type(At,Bt);
mix_type({At,_},{Bt,_,_}) -> mix_type(At,Bt);
mix_type({At,_},{Bt,_}) -> mix_type(At,Bt);
mix_type(T,T) -> T;
mix_type(uint,int)  -> int;
mix_type(uint,bit)  -> uint;
mix_type(uint,bool) -> uint;

mix_type(int,uint)  -> int;
mix_type(int,bit)   -> int;
mix_type(int,bool)  -> int;

mix_type(bit,uint)  -> uint;
mix_type(bit,int)   -> int;
mix_type(bit,bool)  -> bit;

mix_type(bool,uint) -> uint;
mix_type(bool,int)  -> int;
mix_type(bool,bit)  -> bit.

%% check argument, and convert bool into 1 bit vector form when needed
varg(V={uint,_,_}) -> V;
varg(V={int,_,_}) -> V;
varg(V={bit,_,_}) -> V;
varg({bool,X}) -> {uint,1,[X]}.

%% convert arg to int vector
-spec iarg(A::pbits()) -> ivec().
iarg(A={int,_An,_Ax}) -> A;
iarg({uint,An,Ax})    -> {int,An+1,Ax++[false]};
iarg({bit,An,Ax})     -> {int,An,Ax};
iarg({bool,X})        -> {int,2,[X,false]}.

%% convert arg to uint vector
-spec uarg(A::pbits()) -> uvec().
uarg(A={uint,_An,_Ax}) -> A;
uarg({int,An,Ax}) -> {uint,An,Ax};  %% cast!!
uarg({bit,An,Ax}) -> {uint,An,Ax};
uarg({bool,X})    -> {uint,1,[X]}.

%% convert A into destination type
-spec xarg(Type::ptype(), Src::pbits()) -> Dst::pbits().
xarg(int, A) -> iarg(A);
xarg(uint,A) -> uarg(A);
 %% mix_type should only return bool when boolxbool
xarg(bool,A={bool,_}) -> A;
xarg(bit,{bool,X}) -> {bit,1,[X]};
xarg(bit,A={bit,_,_}) -> A.

vconst({uint,_,Xs}) -> vunsigned(Xs);
vconst({int,_,Xs}) -> vsigned(Xs);
vconst({bit,_,Xs}) -> vunsigned(Xs); %% bitstring?
vconst({bool,X}) -> vunsigned([X]).

%% convert a "vector" with boolean constants to a signed number
%% return false if not all elements are constants
vsigned(Xs) ->
    N = (1 bsl (length(Xs)-1)),
    R = vunsigned(Xs),
    if R =:= false -> false;
       R < N -> R;
       true -> R - 2*N
    end.

vunsigned(Xs) ->
    vunsigned_(lists:reverse(Xs), 0).

vunsigned_([true|Xs],N)  -> vunsigned_(Xs,(N bsl 1)+1);
vunsigned_([false|Xs],N) -> vunsigned_(Xs,(N bsl 1)+0);
vunsigned_([_|_],_N) -> false;
vunsigned_([],N) -> N.


vextend(int,Xs,N,K) ->
    vset_size(Xs,K,lists:nth(N,Xs));
vextend(uint,Xs,_N,K) ->
    vset_size(Xs,K,false);
vextend(bit,Xs,_N,K) ->
    vset_size(Xs,K,false);
vextend(bool,Xs,1,K) ->
    vset_size(Xs,K,false).

%% set vector size to N  extend (with FALSE) at end / cut at end
%% vset_size(Xs,N) ->
%%    vset_size(Xs,N,false).

vset_size(_Xs,0,_D) -> [];
vset_size([],I,D) -> lists:duplicate(I,D);
vset_size([X|Xs],I,D) -> [X|vset_size(Xs,I-1,D)].

%%
%% normalize by remove multiple sign bits (MSB)
%% int:
%%   xyzF...F => xyzF
%%   xyzT...T => xyzT
%%   xyzB...B => xyzB
%% uint: (only remove zeros)
%%   xyzF...F => xyz
%%
normalize(Type,Cx) ->
    normalize(Type,length(Cx),Cx).

normalize(uint,Cn,Cx) ->
    u_norm(Cn,lists:reverse(Cx));
normalize(int,Cn,Cx) ->
    RCx = lists:reverse(Cx),
    i_norm(Cn,hd(RCx),RCx);
normalize(Ct,Cn,Cx) ->
    {Ct,Cn,Cx}.

u_norm(N,[false|Cx=[_|_]]) -> u_norm(N-1,Cx);
u_norm(N,Cx) -> {uint,N,lists:reverse(Cx)}.

i_norm(N,S,[S|Cx=[S|_]]) -> i_norm(N-1,S,Cx);
i_norm(N,_S,Cx) -> {int,N,lists:reverse(Cx)}.

%% TEST

test() ->
    true = test_abs(3),
    true = test_negate(3),
    true = test_uband(3),
    true = test_iband(3),
    true = test_ubor(3),
    true = test_ibor(3),
    true = test_ubxor(3),
    true = test_ibxor(3),
    true = test_ubnot(3),
    true = test_ibnot(3),
    true = test_veq(3),
    true = test_vlt(3),
    true = test_umin(3),
    true = test_imin(3),
    true = test_umax(3),
    true = test_imax(3),
    true = test_ult(3),
    true = test_ulte(3),
    true = test_ugt(3),
    true = test_ugte(3),
    true = test_ueq(3),
    true = test_uneq(3),
    true = test_ilt(3),
    true = test_ilte(3),
    true = test_igt(3),
    true = test_igte(3),
    true = test_ieq(3),
    true = test_ineq(3),

    true = test_uadd(3),
    true = test_iadd(3),
    true = test_usub(3),
    true = test_isub(3),
    true = test_umult(3),
    true = test_imult(3),
    true = test_udiv(4),
    %% true = test_idiv(4),
    true = test_urem(4),
    %% true = test_irem(4),

    %% test constant evaluation on bcp should result in model!
    
    test_cadd(3, 5),
    test_cadd(-3, 5),

    test_csub(3, 5),
    test_csub(-3, 5),

    test_cmult(3, 5),
    test_cmult(1, 5),
    test_cmult(5, 0),

    test_cmin(3, 5),
    test_cmin(5, 3),
    test_cmin(-3, 5),
    test_cmin(-5, 3),

    test_cmax(2, 4),
    test_cmax(4, 2),
    test_cmax(-2, 4),
    test_cmax(-4, 2),

    ok.

%% unsigned range
eval_uu(Fun, N) ->
    Mu = (1 bsl N), U = lists:seq(0,Mu-1),
    lists:foldl(
      fun({Y,Z}, Acc) ->
	      try Fun(Y,Z) of
		  X -> [[{x,X},{y,Y},{z,Z}]|Acc]
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
		  X -> [[{x,X},{y,Y},{z,Z}]|Acc]
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
		  X -> [[{x,X},{y,Y},{z,Z}]|Acc]
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
		  X -> [[{x,X},{y,Y}]|Acc]
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
		  X -> [[{x,X},{y,Y}]|Acc]
	      catch
		  error:_ ->
		      Acc
	      end
      end, [], U).



add_symbol(Vp, {Type,_,Xs}, Var) ->
    varp_nif:add_symbol(Vp, Xs, [Type|Var]);
add_symbol(Vp, Xs, Var) ->
    varp_nif:add_symbol(Vp, Xs, Var).

test_i(N, Opts, Arith, Eval) ->
    Vp = varp_nif:new(maps:from_list([{xref,true}|Opts])),
    Y = ivar(Vp, N),
    add_symbol(Vp, Y, y),
    X = Arith(Vp, Y),
    add_symbol(Vp, X, x),
    varp_circuit:bt_match(Vp, eval_i(Eval, N)).

test_ii(N, Opts, Arith, Eval) ->
    Vp = varp_nif:new(maps:from_list([{xref,true}|Opts])),
    Y = ivar(Vp, N),
    Z = ivar(Vp, N),
    add_symbol(Vp, Y, y),
    add_symbol(Vp, Z, z),
    X = Arith(Vp, Y, Z),
    add_symbol(Vp, X, x),
    varp_circuit:bt_match(Vp, eval_ii(Eval, N)).

test_iu(N, Opts, Arith, Eval) ->
    Vp = varp_nif:new(maps:from_list([{xref,true}|Opts])),
    Y = ivar(Vp, N),
    Z = uvar(Vp, N),
    add_symbol(Vp, Y, y),
    add_symbol(Vp, Z, z),
    X = Arith(Vp, Y, Z),
    add_symbol(Vp, X, x),
    varp_circuit:bt_match(Vp, eval_iu(Eval, N)).

test_u(N, Opts, Arith, Eval) ->
    Vp = varp_nif:new(maps:from_list([{xref,true}|Opts])),
    Y = uvar(Vp, N),
    add_symbol(Vp, Y, y),
    X = Arith(Vp, Y),
    add_symbol(Vp, X, x),
    varp_circuit:bt_match(Vp, eval_u(Eval, N)).

test_uu(N, Opts, Arith, Eval) ->
    Vp = varp_nif:new(maps:from_list([{xref,true}|Opts])),
    Y = uvar(Vp, N),
    Z = uvar(Vp, N),
    add_symbol(Vp, Y, y),
    add_symbol(Vp, Z, z),
    X = Arith(Vp, Y, Z),
    add_symbol(Vp, X, x),
    varp_circuit:bt_match(Vp, eval_uu(Eval, N)).

test_cc(A, B, Opts, Arith, Eval) ->
    Vp = varp_nif:new(maps:from_list([{xref,true}|Opts])),
    Y = iconst(A),
    Z = iconst(B),
    add_symbol(Vp, Y, y),
    add_symbol(Vp, Z, z),
    X = Arith(Vp, Y, Z),
    add_symbol(Vp, X, x),
    varp_circuit:bcp_match(Vp, [{x,Eval(A,B)},{y,A},{z,B}]).

test_vlt(N) ->
    io:format("vlt ~w\n", [N]),
    Vp = varp_nif:new(#{xref => true}),
    Y = {_,_,Ys} = uvar(Vp, N),
    Z = {_,_,Zs} = uvar(Vp, N),
    add_symbol(Vp, Y, y),
    add_symbol(Vp, Z, z),
    Lt = vlt(Vp, Ys, Zs),
    add_symbol(Vp, Lt, x),
    varp_circuit:bt_match(Vp, eval_uu(fun erlang:'<'/2, N)).

test_veq(N) ->
    io:format("veq ~w\n", [N]),
    Vp = varp_nif:new(#{xref => true}),
    Y = {_,_,Ys} = uvar(Vp, N),
    Z = {_,_,Zs} = uvar(Vp, N),
    add_symbol(Vp, Y, y),
    add_symbol(Vp, Z, z),
    Eq = veq(Vp, Ys, Zs),
    add_symbol(Vp, Eq, x),
    %% varp_nif_test:dump(Vp),
    varp_circuit:bt_match(Vp, eval_uu(fun erlang:'=='/2, N)).

test_uadd(N) ->
    io:format("uadd ~w\n", [N]),
    test_uu(N, [{carry,false}],   fun add/3, fun erlang:'+'/2).

test_iadd(N) ->
    io:format("iadd ~w\n", [N]),
    test_ii(N, [], fun add/3, fun erlang:'+'/2).

test_cadd(A, B) ->
    io:format("cadd ~w, ~w\n", [A, B]),
    test_cc(A, B, [], fun add/3, fun erlang:'+'/2).
    
test_usub(N) ->
    io:format("usub ~w\n", [N]),
    test_uu(N, [{borrow,false}], 
	    fun subtract/3, fun (A,B) when A>=B -> A-B end).

test_isub(N) ->
    io:format("isub ~w\n", [N]),
    test_ii(N, [], fun subtract/3, fun erlang:'-'/2).

test_csub(A, B) ->
    io:format("csub ~w, ~w\n", [A, B]),
    test_cc(A, B, [], fun subtract/3, fun erlang:'-'/2).

test_umult(N) ->
    io:format("umult ~w\n", [N]),
    test_uu(N, [{carry,false}],
	    fun multiply/3, fun erlang:'*'/2).

test_imult(N) ->
    io:format("imult ~w\n", [N]),
    test_ii(N, [{carry,false}],
	    fun multiply/3, fun erlang:'*'/2).

test_cmult(A, B) ->
    io:format("cmult ~w, ~w\n", [A, B]),
    test_cc(A, B, [], fun multiply/3, fun erlang:'*'/2).

test_udiv(N) ->
    io:format("udiv ~w\n", [N]),
    test_uu(N, [{divz,false}], fun divide/3, fun erlang:'div'/2).

test_idiv(N) ->
    io:format("idiv ~w\n", [N]),
    test_iu(N, [{divz,false}], fun divide/3, fun erlang:'div'/2).

test_urem(N) ->
    io:format("urem ~w\n", [N]),
    test_uu(N, [{divz,false}], fun reminder/3, fun erlang:'rem'/2).

test_irem(N) ->
    io:format("irem ~w\n", [N]),
    test_iu(N, [{divz,false}], fun reminder/3, fun erlang:'rem'/2).


test_umin(N) ->
    io:format("umin ~w\n", [N]),
    test_uu(N, [], fun min/3, fun erlang:min/2).

test_imin(N) ->
    io:format("imin ~w\n", [N]),
    test_ii(N, [], fun min/3, fun erlang:min/2).

test_cmin(A,B) ->
    io:format("cmin ~w,~w\n", [A,B]),
    test_cc(A, B, [], fun min/3, fun erlang:min/2).

test_umax(N) ->
    io:format("umax ~w\n", [N]),
    test_uu(N, [], fun max/3, fun erlang:max/2).

test_imax(N) ->
    io:format("imax ~w\n", [N]),
    test_ii(N, [], fun max/3, fun erlang:max/2).

test_cmax(A,B) ->
    io:format("cmax ~w,~w\n", [A, B]),
    test_cc(A, B, [], fun max/3, fun erlang:max/2).

test_abs(N) ->
    io:format("abs ~w\n", [N]),
    test_i(N, [], fun abs/2, fun erlang:abs/1).

test_negate(N) ->
    io:format("negate ~w\n", [N]),
    test_i(N, [], fun negate/2, fun erlang:'-'/1).

test_uband(N) ->
    io:format("uband ~w\n", [N]),
    test_uu(N, [],   fun bitwise_and/3, fun erlang:'band'/2).

test_iband(N) ->
    io:format("iband ~w\n", [N]),
    test_ii(N, [], fun bitwise_and/3, fun erlang:'band'/2).

test_ubor(N) ->
    io:format("ubor ~w\n", [N]),
    test_uu(N, [],   fun bitwise_or/3, fun erlang:'bor'/2).

test_ibor(N) ->
    io:format("ibor ~w\n", [N]),
    test_ii(N, [],   fun bitwise_or/3, fun erlang:'bor'/2).

test_ubxor(N) ->
    io:format("ubxor ~w\n", [N]),
    test_uu(N, [],   fun bitwise_xor/3, fun erlang:'bxor'/2).

test_ibxor(N) ->
    io:format("ibxor ~w\n", [N]),
    test_ii(N, [],   fun bitwise_xor/3, fun erlang:'bxor'/2).

test_ubnot(N) ->
    io:format("ubnot ~w\n", [N]),
    Mask = (1 bsl N) - 1,
    test_u(N, [],   fun bitwise_not/2, 
	   fun(X) -> (bnot X) band Mask end).

test_ibnot(N) ->
    io:format("ibnot ~w\n", [N]),
    test_i(N, [],   fun bitwise_not/2, fun erlang:'bnot'/1).
    
test_ult(N) ->
    io:format("ult ~w\n", [N]),
    test_uu(N, [], fun lt/3, fun erlang:'<'/2).

test_ulte(N) ->
    io:format("ulte ~w\n", [N]),
    test_uu(N, [], fun lte/3, fun erlang:'=<'/2).

test_ugt(N) ->
    io:format("ugt ~w\n", [N]),
    test_uu(N, [], fun gt/3, fun erlang:'>'/2).

test_ugte(N) ->
    io:format("ugte ~w\n", [N]),
    test_uu(N, [], fun gte/3, fun erlang:'>='/2).

test_ueq(N) ->
    io:format("ueq ~w\n", [N]),
    test_uu(N, [], fun eq/3, fun erlang:'=='/2).

test_uneq(N) ->
    io:format("uneq ~w\n", [N]),
    test_uu(N, [], fun neq/3, fun erlang:'=/='/2).

test_ilt(N) ->
    io:format("ilt ~w\n", [N]),
    test_ii(N, [], fun lt/3, fun erlang:'<'/2).

test_ilte(N) ->
    io:format("ilte ~w\n", [N]),
    test_ii(N, [], fun lte/3, fun erlang:'=<'/2).

test_igt(N) ->
    io:format("igt ~w\n", [N]),
    test_ii(N, [], fun gt/3, fun erlang:'>'/2).

test_igte(N) ->
    io:format("igte ~w\n", [N]),
    test_ii(N, [], fun gte/3, fun erlang:'>='/2).

test_ieq(N) ->
    io:format("ieq ~w\n", [N]),
    test_ii(N, [], fun eq/3, fun erlang:'=='/2).

test_ineq(N) ->
    io:format("ineq ~w\n", [N]),
    test_ii(N, [], fun neq/3, fun erlang:'=/='/2).
