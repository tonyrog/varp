%%
%% Test formal verification of MD5
%%

-module(form_md5).

-compile(export_all).
-import(lists, [reverse/1]).

k(I) ->
    trunc(abs(math:sin(I+1)) * (1 bsl 32)).

r(I) ->
    element(I+1,
	    {7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22,
	     5,  9, 14, 20, 5,  9, 14, 20, 5,  9, 14, 20, 5,  9, 14, 20,
	     4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23,
	     6, 10, 15, 21, 6, 10, 15, 21, 6, 10, 15, 21, 6, 10, 15, 21}).
%%
%%
%% MD5("") =
%%  D41D8CD9 8F00B20 4E98009 98ECF8427E
%%
%% MD5("The quick brown fox jumps over the lazy dog") =
%%  9E107D9D 372BB68 26BD81D 3542A419D6
%%
%% MD5("The quick brown fox jumps over the lazy cog") =
%%  1055D3E6 98D289F 2AF8663 725127BD4B
%%
%% MD5("hello world") = 
%%  5EB63BBB E01EEED 093CB22 BB8F5ACDC3
%%
%%
hex(Binary) when is_binary(Binary) ->
    [hd(erlang:integer_to_list(X,16)) || <<X:4>> <= Binary].
    
md5_hex(IOList) ->
    hex(erlang:md5(IOList)).

pre_process_bitstring(Bits) ->
    Length = bit_size(Bits),
    L = bit_size(Bits) rem 512,
    if L < 448 -> %% 1+64 bits fit
	    Pad = 512 - (L+1+64),
	    <<Bits/bitstring,1:1,0:Pad,Length:64/little>>;
       true ->  %% does not fit, extend
	    Pad = 512 - (L-1),
	    <<Bits/bitstring,1:1,0:Pad,0:448,Length:64/little>>
    end.
    
format_block(Bits) when is_bitstring(Bits) ->
    Bs = pre_process_bitstring(Bits),
    [ V || <<V:32/little>> <= Bs ].

%% eval the md5 the model is the answer, only works for
%% one block bit_size(Data) < 448!!!    
eval(Data) ->
    Bs0 = formula:new(),
    Vs = format_block(iolist_to_binary(Data)),
    {Ws,Bs1} = uint32_list(Vs, Bs0, []),
    {{A,B,C,D},Bs2} = md5_block(list_to_tuple(Ws), Bs1),
    {_,Bs3} = formula:operation(':=', a, A, Bs2),
    {_,Bs4} = formula:operation(':=', b, B, Bs3),
    {_,Bs5} = formula:operation(':=', c, C, Bs4),
    {_,Bs6} = formula:operation(':=', d, D, Bs5),
    try prover:eval(Bs6) of
	false ->
	    false;
	Bs7 ->
	    Model = formula:model(Bs7),
	    Am = proplists:get_value(a, Model),
	    Bm = proplists:get_value(b, Model),
	    Cm = proplists:get_value(c, Model),
	    Dm = proplists:get_value(d, Model),
	    R = <<Am:32/little,Bm:32/little,Cm:32/little,Dm:32/little>>,
	    io:format("eval-md5: ~s\n", [hex(R)]),
	    io:format("md5: ~s\n", [md5_hex(Data)]),
	    {Model, Bs7}
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
	  [{88,s},<<1:1>>,<<0:359>>,<<88:64/little>>]);
solve(2) ->
    solve("hello world", 
	  [<<"hello worl">>,{8,s},<<1:1>>,<<0:359>>,<<88:64/little>>]);
solve(3) ->
    solve("hello world",
	  [{8,s},<<"ello world">>,<<1:1>>,<<0:359>>,<<88:64/little>>]).

solve(Data, Spec) ->
    %% Ai,Bi,Ci,Di is the output to match
    <<Ai:32/little,Bi:32/little,Ci:32/little,Di:32/little>> = erlang:md5(Data),
    {Vs,Bs00} = bit_vector(Spec, formula:new()),
    {Ws,Bs01} = group32_list(w,16,Vs,Bs00),
    %% {Ws,Bs0} = var32_list(w,16,formula:new(),[]),
    {{A,B,C,D},Bs1} = md5_block(list_to_tuple(Ws), Bs01),
    {C0,Cs0} = formula:uint32(Ai,Bs1),
    {C1,Cs1} = formula:uint32(Bi,Cs0),
    {C2,Cs2} = formula:uint32(Ci,Cs1),
    {C3,Cs3} = formula:uint32(Di,Cs2),
    {X1,Bs2} = formula:operation('==',A,C0,Cs3),
    {X2,Bs3} = formula:operation('==',B,C1,Bs2),
    {X3,Bs4} = formula:operation('==',C,C2,Bs3),
    {X4,Bs5} = formula:operation('==',D,C3,Bs4),
    {F,Bs6} = formula:all([X1,X2,X3,X4], Bs5),
    Order = [depth] ++ [{uint,s,8,I} || I <- [0,1,2,3,4,5,6,7]],
    %% Order = [occure_depth],
    Bs7 = formula:setopts([{order,Order},
			   {saturate,1},
			   {saturate_pair,true},
			   {method,collect},
			   {print,true},
			   {log,info},
			   {max,2}], Bs6),
    prover:satisfy(F, Bs7).

%% 
%% Convert a list of bit/variables in groups of 32 bits
%% in little endian format.
%%
group32_list(W, N, Vs, Bs) ->
    group32_list(W, N, Vs, Bs, []).
    
group32_list(_W, 0, [], Bs, Gs) ->
    {reverse(Gs), Bs};
group32_list(W, N, Vs, Bs, Gs) when is_atom(W) ->
    {Xs0,Vs1} = lists:split(32, Vs),
    %% uint32 operations are little bit endian!!! reverse (I know..)
    Xs = byte_swap(reverse(Xs0)),  %% MD5 work on little endian data
    G = {uint,32,Xs},
    Bs1 = formula:alias_vector(uint,W,32,Xs,Bs),
    group32_list(W, N-1, Vs1, Bs1, [G|Gs]).

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


%% run one W block  512 bits, FIXME handle 64 bit length suffix + bit
md5_block(W,Bs0) ->
    {A0,Bs1} = formula:uint32(16#67452301,Bs0),
    {B0,Bs2} = formula:uint32(16#efcdab89,Bs1),
    {C0,Bs3} = formula:uint32(16#98badcfe,Bs2),
    {D0,Bs4} = formula:uint32(16#10325476,Bs3),
    {{A1,B1,C1,D1},Bs5} = md5_(0,W,A0,B0,C0,D0,Bs4),
    {A2,Bs6} = formula:operation('+',A0,A1,Bs5),
    {B2,Bs7} = formula:operation('+',B0,B1,Bs6),
    {C2,Bs8} = formula:operation('+',C0,C1,Bs7),
    {D2,Bs9} = formula:operation('+',D0,D1,Bs8),
    {{A2,B2,C2,D2},Bs9}.


md5_(I,W,A,B,C,D,Bs) when I < 16 ->
    %% F = {'|',{'&',B,C},{'&',{'~',B},D}},
    {B1,Bs1} = formula:operation('~',B,Bs),
    {X1,Bs2} = formula:operation('&',B1,D,Bs1),
    {X2,Bs3} = formula:operation('&',B,C,Bs2),
    {F,Bs4} = formula:operation('|',X1,X2,Bs3),
    md5t_(I,I,W,A,B,C,D,F,Bs4);

md5_(I, W, A, B, C, D,Bs) when I < 32 ->
    %% F = {'|',{'&',D,B},{'&',{'~',D},C}},
    {D1,Bs1} = formula:operation('~',D,Bs),
    {X1,Bs2} = formula:operation('&',D1,C,Bs1),
    {X2,Bs3} = formula:operation('&',D,B,Bs2),
    {F,Bs4} = formula:operation('|',X1,X2,Bs3),
    md5t_(I,(5*I+1) rem 16,W,A,B,C,D,F,Bs4);

md5_(I, W, A, B, C, D, Bs) when I < 48 ->
    %% F = {'^', {'^',B,C}, D},
    {X1,Bs1} = formula:operation('^',B,C,Bs),
    {F,Bs2} = formula:operation('^',X1,D,Bs1),
    md5t_(I,(3*I+5) rem 16,W,A,B,C,D,F,Bs2);

md5_(I, W, A, B, C, D, Bs) when I < 64 ->
    %% F = {'^', C, {'|',B, {'~', D}}},
    {D1,Bs1} = formula:operation('~',D,Bs),
    {X1,Bs2} = formula:operation('|',B,D1,Bs1),
    {F,Bs3} = formula:operation('^',C,X1,Bs2),
    md5t_(I,(7*I) rem 16,W,A,B,C,D,F,Bs3);

md5_(64, _W, A, B, C, D, Bs) ->
    {{A,B,C,D}, Bs}.

md5t_(I, G, W, A, B, C, D, F, Bs) ->
    %% S = {'+',{'+',{'+',A,F},k(I)},element(G+1,W)}
    {X3,Bs5} = formula:operation('+',A,F,Bs),
    {Ki,Ks}  = formula:uint32(k(I),Bs5),
    {X4,Bs6} = formula:operation('+',X3,Ki,Ks),
    {S,Bs7}  = formula:operation('+',X4,element(G+1,W),Bs6),
    {R,Bs8}  = formula:operation('<<<', S,r(I),Bs7),
    {B2,Bs9} = formula:operation('+',B,R,Bs8),
    md5_(I+1,W,D,B2,B,C,Bs9).
