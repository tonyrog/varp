
-module(waerden).

-compile(export_all).

%%
%% We MUST probably generate progression instead of checking them
%% 
%% ALL coloring of {1,2,...N} with colors {0..R-1} must contain
%% a arithmentic progression of at least K
%%
%% Each slot contain exacly one color: R=3  
%% S(Pos::1..N,Color::0..2
%%
%% [ALL i=1..n] [EQk 1 c=0..r-1] S(i,c)
%% 
%% Formula: W(R=3,K=2) = 4  (n=4)
%%
%%   EQk(1, S(1,0), S(1,1), S(1,2)) & 
%%   EQk(1, S(2,0), S(2,1), S(2,2)) & 
%%   EQk(1, S(3,0), S(3,1), S(3,2)) & 
%%   EQk(1, S(4,0), S(4,1), S(4,2)) &
%%
%%   [ANY c=0..r-1] (
%%     [ANY i=1..n-1] (S(i,c) & S(i+1,c))
%%     [ANY i=1..n-2] (S(i,c) & S(i+2,c))
%%   )
%%
%%   w0(2,3,8) -> counter-models
%%   w0(2,3,9) -> valid
%%
%%   w0(2,4,34) -> counter-models
%%   w0(2,4,35) -> valid
%%
%%   w0(3,3,26) -> counter-models
%%   w0(3,3,27) -> valid
%%
w0(R,K,N) ->
    {'->',
     %% every position 1..n must have uniq color value 0..r-1
     {{all,[{'=',i,{range,1,N}}]},
      {{eqk,[1, {'=',c,{range,0,R-1}}]}, {p,'S',[i,c]}}},
     %% generate a disjunction for of positions needed
     {{any,[{'=',c,{range,0,R-1}}]},
      {any,[{all,[{p,'S',[I,c]} || I <- L]} || L <- gap_pos_eq(K, N)]}}
    }.

%% Generate binary formula:
%%    i=1..n   (F(1)==F(2),F(1)==F(3),F(2)==F(3))

%%   w(2,3,8) -> counter-models
%%   w(2,3,9) -> valid
%%
%%   w(2,4,34) -> counter-models
%%   w(2,4,35) -> valid
%%
%%   w(3,3,26) ->
%%   w(3,3,27) ->

w(R,K,N) when R >= 2 ->
    Rx = imath:ilog2(R-1)+1, %% number of bits to represent 0..R-1
    if R =:= (1 bsl Rx) ->
	    {any,[{all,weq_list(Rx, L)} || L <- gap_pos_eq(K, N)]};
       true -> %% we must limit all Fi < R
	    {'->',
	     {all,[{'<=',var('F',I,Rx),{uint,Rx,R-1}} || I <- lists:seq(1,N)]},
	     {any,[{all,weq_list(Rx, L)} || L <- gap_pos_eq(K, N)]}}
    end.

weq_list(Rx, [G0|Gs=[G1|_]]) ->
    [ {'==', var('F',G0,Rx), var('F',G1,Rx)} | weq_list(Rx, Gs)];
weq_list(_Rs, _) ->
    [].

var(F,I,Size) ->
    {uint,Size,{p,varname(F,I),[]}}.

varname(F,I) ->
    list_to_atom(atom_to_list(F)++integer_to_list(I)).

run(R,K,N) ->
    run(R,K,N,1).
run(R,K,N,S) ->
    prover:run_formula(w(R,K,N),[{value,false},{saturate,S},
				 {log,info},{max,1}]).

%% 4,3,76 => 17000 triples, test1 11931/17935
run0(R,K,N) ->
    run0(R,K,N,1).
run0(R,K,N,S) ->
    prover:run_formula(w0(R,K,N),[{value,false},{saturate,S},
				  {log,info},{max,1}]).


gap_pos_lt(K, N) when K > 1 ->
    gap_pos_eq(K-1, N) ++ gap_pos_lt(K-1,N);
gap_pos_lt(_, _N) -> [].

gap_pos_gte(K, N) when K=< N ->
    gap_pos_eq(K, N) ++ gap_pos_gte(K+1,N);
gap_pos_gte(_, _N) -> [].

%%
%% generate a list of positions of size K, out of a total size of N positions,
%% such that there is a constant gap between them
%%
gap_list_str(K, N) ->
    [ tl(integer_to_list((1 bsl N) + X, 2)) || X <- gap_pos_eq(K, N)].

gap_pos_eq(K, N) ->
    [ [ Pos+1 || Pos <- lists:seq(0,N-1), X band (1 bsl Pos) =/= 0] 
      || X <- gap_list(K, N) ].

gap_list(K, N) when is_integer(K), is_integer(N), K>0, K =< N ->
    gap_list(0, K, N, []).

%%
%%  G=0..(N-K)/(K-1)
%%    I=0..(N-(GK+K-G))
%%
%% Length: -(n-1)(k-n-2) / 2(k-1)
%%   
%%
gap_list(0, K, N, Acc) ->  %% Gap = 0
    M  = K,
    GL = (1 bsl K) - 1,
    Acc1 = gap_list_i(0, N, M, GL, Acc),
    gap_list(1,K,N,Acc1);
gap_list(G, K, N, Acc) when G*K+K-G > N ->
    lists:reverse(Acc);    
gap_list(G, K, N, Acc) -> %% Gap > 0
    M = (G*K+K-G),  %% mask length
    Mask = ((1 bsl M) - 1),             %% mask low bits
    N1 = (N+(G+1)-1) div (G+1),  %% make N multiple of G+1
    %% produce a pattern bit mask with bits at G+1 distance
    GL0 = (1 bsl (N1*(G+1))) div ((1 bsl (G+1)) - 1),
    GL = GL0 band Mask,
    Acc1 = gap_list_i(0, N, M, GL, Acc),
    gap_list(G+1,K,N,Acc1).

gap_list_i(I,N,M,_GL,Acc) when I+M > N ->
    Acc;
gap_list_i(I,N,M,GL,Acc) ->
    gap_list_i(I+1,N,M,GL,[(GL bsl I)|Acc]).
