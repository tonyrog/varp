%%
%% Test formal verification of SHA-1
%%

-module(form_sha1).

-compile(export_all).
-import(lists, [reverse/1]).

%%
%% TEST:
%%
%% SHA1("") =
%%   DA39A3EE 5E6B4B0D 3255BFEF 95601890 AFD80709
%%
%% SHA1("The quick brown fox jumps over the lazy dog") =
%%  2FD4E1C6 7A2D28FC ED849EE1 BB76E7391 B93EB12
%%
%% SHA1("The quick brown fox jumps over the lazy cog") =
%%  DE9F2C7F D25E1B3A FAD3E85A 0BD17D9B 100DB4B3
%%
%% SHA1("hello world") = 
%%   2AAE6C35 C94FCFB4 15DBE95F 408B9CE9 1EE846ED
%%
%%
hex(Binary) when is_binary(Binary) ->
    [hd(erlang:integer_to_list(X,16)) || <<X:4>> <= Binary].
    
sha1_hex(IOList) ->
    hex(crypto:sha(IOList)).


pre_process_bitstring(Bits) ->
    Length = bit_size(Bits),
    L = bit_size(Bits) rem 512,
    if L < 448 -> %% 1+64 bits fit
	    Pad = 512 - (L+1+64),
	    <<Bits/bitstring,1:1,0:Pad,Length:64/big>>;
       true ->  %% does not fit, extend
	    Pad = 512 - (L-1),
	    <<Bits/bitstring,1:1,0:Pad,0:448,Length:64/big>>
    end.

format_block(Bits) when is_bitstring(Bits) ->
    Bs = pre_process_bitstring(Bits),
    W  = array:from_list([ V || <<V:32/big>> <= Bs ]),
    array:to_list(extend_block(16,W)).

extend_block(80, W) ->
    W;
extend_block(I, W) ->
    X0 = array:get(I-3,W) bxor array:get(I-8,W) bxor
	array:get(I-14,W) bxor array:get(I-16,W),
    X1 = ((X0 bsl 1) bor (X0 bsr 31)) band 16#ffffffff,
    extend_block(I+1, array:set(I, X1, W)).

%% eval the sha1 the model is the answer, only works for
%% one block bit_size(Data) < 448!!!    
eval(Data) ->
    Bs0      = formula:new(),
    Vs       = format_block(iolist_to_binary(Data)),
    {Ws,Bs1} = uint32_list(Vs, Bs0, []),
    {{A,B,C,D,E},Bs2} = sha1_block(list_to_tuple(Ws), Bs1),
    {_,Bs3} = formula:operation(':=', a, A, Bs2),
    {_,Bs4} = formula:operation(':=', b, B, Bs3),
    {_,Bs5} = formula:operation(':=', c, C, Bs4),
    {_,Bs6} = formula:operation(':=', d, D, Bs5),
    {_,Bs7} = formula:operation(':=', e, E, Bs6),
    try prover:eval(Bs7) of
	false ->
	    false;
	Bs8 ->
	    Model = formula:model(Bs8),
	    Am = proplists:get_value(a, Model),
	    Bm = proplists:get_value(b, Model),
	    Cm = proplists:get_value(c, Model),
	    Dm = proplists:get_value(d, Model),
	    Em = proplists:get_value(e, Model),
	    R = <<Am:32/big,Bm:32/big,Cm:32/big,Dm:32/big,Em:32/big>>,
	    io:format("eval-sha1: ~s\n", [hex(R)]),
	    io:format("sha1: ~s\n", [sha1_hex(Data)]),
	    {Model, Bs8}
    catch
	throw:contradiction -> false
    end.

%%
%% Find input generating the <<"hello world">> md5 checksum
%%
%%
solve(0) ->
    solve("hello world",
	  [{448,s},{64,l}]);
solve(1) ->
    solve("hello world",
	  [{88,w},<<1:1>>,<<0:359>>,<<88:64/big>>]);
solve(2) ->
    solve("hello world",
	  [<<"hello worl">>,{8,s},<<1:1>>,<<0:359>>,<<88:64/big>>]);
solve(3) ->
    solve("hello world",
	  [{8,s},<<"ello world">>,<<1:1>>,<<0:359>>,<<88:64/big>>]).

solve(Data,Spec) ->
    %% Ai,Bi,Ci,Di,Ei is the output to match
    <<Ai:32/big,Bi:32/big,Ci:32/big,Di:32/big,Ei:32/big>> = crypto:sha(Data),
    {Vs,Bs00} = bit_vector(Spec, formula:new()),
    {Ws,Bs01} = group32_list(w,16,Vs,Bs00),
    %% {Ws,Bs0} = var32_list(w,16,formula:new(),[]),
    {{A,B,C,D,E},Bs1} = sha1_block(list_to_tuple(Ws), Bs01),
    {C0,Cs0} = formula:uint32(Ai,Bs1),
    {C1,Cs1} = formula:uint32(Bi,Cs0),
    {C2,Cs2} = formula:uint32(Ci,Cs1),
    {C3,Cs3} = formula:uint32(Di,Cs2),
    {C4,Cs4} = formula:uint32(Ei,Cs3),

    {X1,Bs2} = formula:operation('==',A,C0,Cs4),
    {X2,Bs3} = formula:operation('==',B,C1,Bs2),
    {X3,Bs4} = formula:operation('==',C,C2,Bs3),
    {X4,Bs5} = formula:operation('==',D,C3,Bs4),
    {X5,Bs6} = formula:operation('==',E,C4,Bs5),
    {F,Bs7} = formula:all([X1,X2,X3,X4,X5], Bs6),
    io:format("EVAL\n"),
    %% Order = [depth_occure,reverse],

    Order = [depth] ++ [{uint,s,8,I} || I <- [0,1,2,3,4,5,6,7]],

    Bs8 = formula:setopts([{order,Order},
			   {saturate,1},
			   {saturate_pair,true},
			   {method,collect},
			   {print,true},
			   {log,info},
			   {max,2}], Bs7),
    prover:satisfy(F, Bs8).

%% 
%% Convert a list of bit/variables in groups of 32 bits
%% in big endian format. + extend into 80 groups
%%
group32_list(W, N, Vs, Bs) ->
    group32_list(W, N, Vs, Bs, []).
    
group32_list(_W, 0, [], Bs, Gs) ->
    extend32_list(16, reverse(Gs), Bs);
group32_list(W, N, Vs, Bs, Gs) when is_atom(W) ->
    {Xs0,Vs1} = lists:split(32, Vs),
    %% Xs = byte_swap(reverse(Xs0)), SHA work on big endian data!
    Xs = reverse(Xs0),
    G = {uint,32,Xs},
    Bs1 = formula:alias_vector(uint,W,32,Xs,Bs),
    group32_list(W, N-1, Vs1, Bs1, [G|Gs]).

%% stupid algorithm but does not matter for now
extend32_list(80, W, Bs) ->
    {W, Bs};
extend32_list(I, W, Bs) ->
    Y0 = lists:nth(I-3+1,W),
    Y1 = lists:nth(I-8+1,W),
    Y2 = lists:nth(I-14+1,W),
    Y3 = lists:nth(I-16+1,W),
    %% W[I] = (Y0 ^ Y1 ^ Y2 ^ Y3) <<< 1
    {X1,Bs1} = formula:operation('^',Y0,Y1,Bs),
    {X2,Bs2} = formula:operation('^',X1,Y2,Bs1),
    {X3,Bs3} = formula:operation('^',X2,Y3,Bs2),
    {Wi,Bs4} = formula:operation('<<<',X3,1,Bs3),
    extend32_list(I+1, W++[Wi], Bs4).

    
byte_swap([A7,A6,A5,A4,A3,A2,A1,A0,  B7,B6,B5,B4,B3,B2,B1,B0,
	   C7,C6,C5,C4,C3,C2,C1,C0,  D7,D6,D5,D4,D3,D2,D1,D0]) ->
    [D7,D6,D5,D4,D3,D2,D1,D0, C7,C6,C5,C4,C3,C2,C1,C0,
     B7,B6,B5,B4,B3,B2,B1,B0, A7,A6,A5,A4,A3,A2,A1,A0].
    
%%
%% create a bit list according to a spec
%% bitstring()        =>  formated as series of true and false
%% N::integer()       =>  N variable bits
%% {N::integer(),Var} =>  N variable bits with Var as alias
bit_vector(Vs, Bs) ->
    bit_vector(Vs, Bs, []).

bit_vector([true|Vs], Bs, Acc) ->
    {{bool,T},Bs1} = formula:build_(true, Bs),
    bit_vector(Vs, Bs1, [[T]|Acc]);
bit_vector([false|Vs], Bs, Acc) ->
    {{bool,F},Bs1} = formula:build_(false, Bs),
    bit_vector(Vs, Bs1, [[F]|Acc]);
bit_vector([Bits|Vs], Bs, Acc) when is_bitstring(Bits) ->
    bit_vector([ I=:=1 || <<I:1>> <= Bits ]++Vs, Bs, Acc);
bit_vector([{N,V}|Vs], Bs, Acc) when is_integer(N), N>0, is_atom(V) ->
    {{_Type,N,Xs},Bs1} = formula:var_vector(uint,V,N,Bs),
    bit_vector(Vs, Bs1, [reverse(Xs)|Acc]);
bit_vector([N|Vs], Bs, Acc) when is_integer(N) ->
    {V,Bs1} = lists:foldl(
		fun(_I, {Vs0,Bs0}) ->
			{V,Bs1} = formula:fresh_var(Bs0),
			{[V|Vs0],Bs1}
		end, {[],Bs}, lists:seq(1, N)),
    bit_vector(Vs, Bs1, [V|Acc]);
bit_vector([], Bs, Acc) ->
    {lists:append(reverse(Acc)), Bs}.

var32_list(_V,0,Bs,Acc) ->
    {lists:reverse(Acc),Bs};
var32_list(V,I,Bs,Acc) ->
    {Vi,Bs1} = var32(V,I+1,Bs),
    var32_list(V,I-1,Bs1,[Vi|Acc]).

var32(V,I,Bs) when is_atom(V), is_integer(I) ->
    W = list_to_atom(atom_to_list(V)++integer_to_list(I)),
    formula:uint32(W,Bs).

uint32_list([V|Vs],Bs,Acc) ->
    {W,Bs1} = formula:uint32(V,Bs),
    uint32_list(Vs,Bs1,[W|Acc]);
uint32_list([],Bs,Acc) ->
    {lists:reverse(Acc),Bs}.


-define(H0, 16#67452301).
-define(H1, 16#EFCDAB89).
-define(H2, 16#98BADCFE).
-define(H3, 16#10325476).
-define(H4, 16#C3D2E1F0).

%% run one W block  512 bits, FIXME handle 64 bit length suffix + bit
sha1_block(W,Bs0) ->
    {A0,Bs1} = formula:uint32(?H0,Bs0),
    {B0,Bs2} = formula:uint32(?H1,Bs1),
    {C0,Bs3} = formula:uint32(?H2,Bs2),
    {D0,Bs4} = formula:uint32(?H3,Bs3),
    {E0,Bs4} = formula:uint32(?H4,Bs3),
    {{A1,B1,C1,D1,E1},Bs5} = sha1_(0,W,A0,B0,C0,D0,E0,Bs4),
    {A2,Bs6} = formula:operation('+',A0,A1,Bs5),
    {B2,Bs7} = formula:operation('+',B0,B1,Bs6),
    {C2,Bs8} = formula:operation('+',C0,C1,Bs7),
    {D2,Bs9} = formula:operation('+',D0,D1,Bs8),
    {E2,Bs10} = formula:operation('+',E0,E1,Bs9),
    {{A2,B2,C2,D2,E2},Bs10}.


sha1_(I,W,A,B,C,D,E,Bs) when I < 20 ->
    %% F = (B & C) | ((~B) & D)
    {B1,Bs1} = formula:operation('~',B,Bs),
    {X1,Bs2} = formula:operation('&',B1,D,Bs1),
    {X2,Bs3} = formula:operation('&',B,C,Bs2),
    {F,Bs4} = formula:operation('|',X1,X2,Bs3),
    K = 16#5A827999,
    sha1t_(I,K,W,A,B,C,D,E,F,Bs4);

sha1_(I,W,A,B,C,D,E,Bs) when I < 40 ->
    %% F = (B ^ C) ^ D
    {X1,Bs1} = formula:operation('^',B,C,Bs),
    {F,Bs2} = formula:operation('^',X1,D,Bs1),
    K = 16#6ED9EBA1,
    sha1t_(I,K,W,A,B,C,D,E,F,Bs2);

sha1_(I,W,A,B,C,D,E,Bs) when I < 60 ->
    %% F = (B & C) | (B & D) | (C & D)
    {X1,Bs1} = formula:operation('&',B,C,Bs),
    {X2,Bs2} = formula:operation('&',B,D,Bs1),
    {X3,Bs3} = formula:operation('&',C,D,Bs2),
    {X4,Bs4} = formula:operation('|',X1,X2,Bs3),
    {F,Bs5}  = formula:operation('|',X4,X3,Bs4),
    K = 16#8F1BBCDC,
    sha1t_(I,K,W,A,B,C,D,E,F,Bs5);

sha1_(I,W,A,B,C,D,E,Bs) when I < 80 ->
    %% F = (B ^ C) ^ D
    {X1,Bs1} = formula:operation('^',B,C,Bs),
    {F,Bs2}  = formula:operation('^',X1,D,Bs1),
    K = 16#CA62C1D6,
    sha1t_(I,K,W,A,B,C,D,E,F,Bs2);

sha1_(80,_W,A,B,C,D,E,Bs) ->
    {{A,B,C,D,E}, Bs}.


sha1t_(I, K, W, A, B, C, D, E, F, Bs) ->
    %% T = (A <<< 5) + F + E + K + W[I]
    %% E = D, D = C, C = B <<< 30, B = A, A = T
    {X0,Bs1} = formula:operation('<<<',A, 5, Bs),
    {X1,Bs2} = formula:operation('+',X0,F,Bs1),
    {X2,Bs3} = formula:operation('+',X1,E,Bs2),
    {KX,Bs4} = formula:uint32(K, Bs3),
    {X3,Bs5} = formula:operation('+',X2,KX,Bs4),
    {T,Bs6}  = formula:operation('+',X3,element(I+1,W),Bs5),
    {B1,Bs7} = formula:operation('<<<',B,30,Bs6),
    sha1_(I+1,W,T,A,B1,C,D,Bs7).
