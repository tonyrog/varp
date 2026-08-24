%%% Scanner (varp_scan.xrl / varp_scani.xrl) tests
-module(varp_scan_tests).

-include_lib("eunit/include/eunit.hrl").

t(Text) -> varp_tc:tokens(Text).

symbol_test() ->
    ?assertEqual([{symbol,1,<<"B">>}], t("B")),
    ?assertEqual([{symbol,1,<<"Foo_1">>}], t("Foo_1")),
    %% A and E are scanned as quantifier keywords, the grammar turns
    %% them back into symbols where a symbol is expected
    ?assertEqual([{'A',1}], t("A")),
    ?assertEqual([{'E',1}], t("E")).

number_test() ->
    ?assertEqual([{decnum,1,"123"}], t("123")),
    ?assertEqual([{hexnum,1,"0x1f"}], t("0x1f")),
    ?assertEqual([{hexnum,1,"0X1F"}], t("0X1F")),
    ?assertEqual([{octnum,1,"017"}], t("017")),
    ?assertEqual([{binnum,1,"0b1011"}], t("0b1011")),
    ?assertEqual([{chrnum,1,"'a'"}], t("'a'")).

operator_test() ->
    Ops = ["->","<->","<<",">>","<<<",">>>","&&","||","<=",">=",
	   "==","!=",":=","..","&","|","^","~","!","+","-","*","/","%",
	   "<",">","?",":",";",",","=","(",")","[","]","{","}","."],
    lists:foreach(
      fun(Op) ->
	      A = list_to_atom(Op),
	      ?assertEqual([{A,1}], t(Op))
      end, Ops).

keyword_test() ->
    Kws = ["and","or","xor","not","imp","equ","implies","equivalent",
	   "true","false","declare","define","literals","order","assert",
	   "input","output","circuit","in","out","return",
	   "rank","degree","random","identity",
	   "min","max","abs",
	   "bool","char","short","int","long","signed","unsigned",
	   "float","double"],
    lists:foreach(
      fun(Kw) ->
	      A = list_to_atom(Kw),
	      ?assertEqual([{A,1}], t(Kw))
      end, Kws).

quantifier_keyword_test() ->
    Qs = ['ALL','ANY','ONE','NONE','EQ','NEQ','GT','GTE','LT','LTE',
	  'SUM','PROD','PARITY','ODD','EVEN'],
    lists:foreach(
      fun(Q) ->
	      ?assertEqual([{Q,1}], t(atom_to_list(Q)))
      end, Qs).

line_number_test() ->
    ?assertEqual([{symbol,1,<<"X">>},{symbol,2,<<"Y">>},{symbol,3,<<"Z">>}],
		 t("X\nY\nZ")).

comment_test() ->
    ?assertEqual("X \n && B", varp:remove_comments("X // hi\n/* x */ && B")),
    ?assertEqual([{symbol,1,<<"X">>},{'&&',2},{symbol,2,<<"B">>}],
		 t(varp:remove_comments("X // comment\n && B"))).

sequence_test() ->
    ?assertEqual([{'A',1},{'&&',1},{symbol,1,<<"B">>},{'(',1},
		  {decnum,1,"1"},{',',1},{decnum,1,"2"},{')',1},
		  {hexnum,1,"0x1f"},{'->',1},{'!',1},{symbol,1,<<"C">>}],
		 t("A && B(1,2) 0x1f -> !C")).

%% the case insensitive scanner accepts keywords in any case
icase_test() ->
    {ok,Ts} = varp:tokens("AND xOr NoT", true),
    ?assertEqual(['and','xor','not'], [element(1,T) || T <- Ts]).
