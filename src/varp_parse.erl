-module(varp_parse).
-export([parse/1, parse_and_scan/1, format_error/1]).
-file("varp_parse.yrl", 166).

op({Op,_Ln}) -> Op.

name({symbol,_,Name}) -> list_to_atom(Name);
name({variable,_,Name}) -> list_to_atom(Name).

value({decnum,_,Num}) -> list_to_integer(Num,10);
value({octnum,_,Num}) -> list_to_integer(Num,8);
value({hexnum,_,"0x"++Num}) -> list_to_integer(Num,16);
value({binnum,_,"0b"++Num}) -> list_to_integer(Num,2).

-file("/usr/local/lib/erlang/lib/parsetools-2.0.7/include/yeccpre.hrl", 0).
%%
%% %CopyrightBegin%
%%
%% Copyright Ericsson AB 1996-2011. All Rights Reserved.
%%
%% The contents of this file are subject to the Erlang Public License,
%% Version 1.1, (the "License"); you may not use this file except in
%% compliance with the License. You should have received a copy of the
%% Erlang Public License along with this software. If not, it can be
%% retrieved online at http://www.erlang.org/.
%%
%% Software distributed under the License is distributed on an "AS IS"
%% basis, WITHOUT WARRANTY OF ANY KIND, either express or implied. See
%% the License for the specific language governing rights and limitations
%% under the License.
%%
%% %CopyrightEnd%
%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% The parser generator will insert appropriate declarations before this line.%

-type yecc_ret() :: {'error', _} | {'ok', _}.

-spec parse(Tokens :: list()) -> yecc_ret().
parse(Tokens) ->
    yeccpars0(Tokens, {no_func, no_line}, 0, [], []).

-spec parse_and_scan({function() | {atom(), atom()}, [_]}
                     | {atom(), atom(), [_]}) -> yecc_ret().
parse_and_scan({F, A}) ->
    yeccpars0([], {{F, A}, no_line}, 0, [], []);
parse_and_scan({M, F, A}) ->
    Arity = length(A),
    yeccpars0([], {{fun M:F/Arity, A}, no_line}, 0, [], []).

-spec format_error(any()) -> [char() | list()].
format_error(Message) ->
    case io_lib:deep_char_list(Message) of
        true ->
            Message;
        _ ->
            io_lib:write(Message)
    end.

%% To be used in grammar files to throw an error message to the parser
%% toplevel. Doesn't have to be exported!
-compile({nowarn_unused_function, return_error/2}).
-spec return_error(integer(), any()) -> no_return().
return_error(Line, Message) ->
    throw({error, {Line, ?MODULE, Message}}).

-define(CODE_VERSION, "1.4").

yeccpars0(Tokens, Tzr, State, States, Vstack) ->
    try yeccpars1(Tokens, Tzr, State, States, Vstack)
    catch 
        error: Error ->
            Stacktrace = erlang:get_stacktrace(),
            try yecc_error_type(Error, Stacktrace) of
                Desc ->
                    erlang:raise(error, {yecc_bug, ?CODE_VERSION, Desc},
                                 Stacktrace)
            catch _:_ -> erlang:raise(error, Error, Stacktrace)
            end;
        %% Probably thrown from return_error/2:
        throw: {error, {_Line, ?MODULE, _M}} = Error ->
            Error
    end.

yecc_error_type(function_clause, [{?MODULE,F,ArityOrArgs,_} | _]) ->
    case atom_to_list(F) of
        "yeccgoto_" ++ SymbolL ->
            {ok,[{atom,_,Symbol}],_} = erl_scan:string(SymbolL),
            State = case ArityOrArgs of
                        [S,_,_,_,_,_,_] -> S;
                        _ -> state_is_unknown
                    end,
            {Symbol, State, missing_in_goto_table}
    end.

yeccpars1([Token | Tokens], Tzr, State, States, Vstack) ->
    yeccpars2(State, element(1, Token), States, Vstack, Token, Tokens, Tzr);
yeccpars1([], {{F, A},_Line}, State, States, Vstack) ->
    case apply(F, A) of
        {ok, Tokens, Endline} ->
            yeccpars1(Tokens, {{F, A}, Endline}, State, States, Vstack);
        {eof, Endline} ->
            yeccpars1([], {no_func, Endline}, State, States, Vstack);
        {error, Descriptor, _Endline} ->
            {error, Descriptor}
    end;
yeccpars1([], {no_func, no_line}, State, States, Vstack) ->
    Line = 999999,
    yeccpars2(State, '$end', States, Vstack, yecc_end(Line), [],
              {no_func, Line});
yeccpars1([], {no_func, Endline}, State, States, Vstack) ->
    yeccpars2(State, '$end', States, Vstack, yecc_end(Endline), [],
              {no_func, Endline}).

%% yeccpars1/7 is called from generated code.
%%
%% When using the {includefile, Includefile} option, make sure that
%% yeccpars1/7 can be found by parsing the file without following
%% include directives. yecc will otherwise assume that an old
%% yeccpre.hrl is included (one which defines yeccpars1/5).
yeccpars1(State1, State, States, Vstack, Token0, [Token | Tokens], Tzr) ->
    yeccpars2(State, element(1, Token), [State1 | States],
              [Token0 | Vstack], Token, Tokens, Tzr);
yeccpars1(State1, State, States, Vstack, Token0, [], {{_F,_A}, _Line}=Tzr) ->
    yeccpars1([], Tzr, State, [State1 | States], [Token0 | Vstack]);
yeccpars1(State1, State, States, Vstack, Token0, [], {no_func, no_line}) ->
    Line = yecctoken_end_location(Token0),
    yeccpars2(State, '$end', [State1 | States], [Token0 | Vstack],
              yecc_end(Line), [], {no_func, Line});
yeccpars1(State1, State, States, Vstack, Token0, [], {no_func, Line}) ->
    yeccpars2(State, '$end', [State1 | States], [Token0 | Vstack],
              yecc_end(Line), [], {no_func, Line}).

%% For internal use only.
yecc_end({Line,_Column}) ->
    {'$end', Line};
yecc_end(Line) ->
    {'$end', Line}.

yecctoken_end_location(Token) ->
    try
        {text, Str} = erl_scan:token_info(Token, text),
        {line, Line} = erl_scan:token_info(Token, line),
        Parts = re:split(Str, "\n"),
        Dline = length(Parts) - 1,
        Yline = Line + Dline,
        case erl_scan:token_info(Token, column) of
            {column, Column} ->
                Col = byte_size(lists:last(Parts)),
                {Yline, Col + if Dline =:= 0 -> Column; true -> 1 end};
            undefined ->
                Yline
        end
    catch _:_ ->
        yecctoken_location(Token)
    end.

-compile({nowarn_unused_function, yeccerror/1}).
yeccerror(Token) ->
    Text = yecctoken_to_string(Token),
    Location = yecctoken_location(Token),
    {error, {Location, ?MODULE, ["syntax error before: ", Text]}}.

-compile({nowarn_unused_function, yecctoken_to_string/1}).
yecctoken_to_string(Token) ->
    case catch erl_scan:token_info(Token, text) of
        {text, Txt} -> Txt;
        _ -> yecctoken2string(Token)
    end.

yecctoken_location(Token) ->
    case catch erl_scan:token_info(Token, location) of
        {location, Loc} -> Loc;
        _ -> element(2, Token)
    end.

-compile({nowarn_unused_function, yecctoken2string/1}).
yecctoken2string({atom, _, A}) -> io_lib:write(A);
yecctoken2string({integer,_,N}) -> io_lib:write(N);
yecctoken2string({float,_,F}) -> io_lib:write(F);
yecctoken2string({char,_,C}) -> io_lib:write_char(C);
yecctoken2string({var,_,V}) -> io_lib:format("~s", [V]);
yecctoken2string({string,_,S}) -> io_lib:write_unicode_string(S);
yecctoken2string({reserved_symbol, _, A}) -> io_lib:write(A);
yecctoken2string({_Cat, _, Val}) -> io_lib:format("~p",[Val]);
yecctoken2string({dot, _}) -> "'.'";
yecctoken2string({'$end', _}) ->
    [];
yecctoken2string({Other, _}) when is_atom(Other) ->
    io_lib:write(Other);
yecctoken2string(Other) ->
    io_lib:write(Other).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%



-file("varp_parse.erl", 199).

yeccpars2(0=S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_0(S, Cat, Ss, Stack, T, Ts, Tzr);
%% yeccpars2(1=S, Cat, Ss, Stack, T, Ts, Tzr) ->
%%  yeccpars2_1(S, Cat, Ss, Stack, T, Ts, Tzr);
%% yeccpars2(2=S, Cat, Ss, Stack, T, Ts, Tzr) ->
%%  yeccpars2_2(S, Cat, Ss, Stack, T, Ts, Tzr);
%% yeccpars2(3=S, Cat, Ss, Stack, T, Ts, Tzr) ->
%%  yeccpars2_3(S, Cat, Ss, Stack, T, Ts, Tzr);
%% yeccpars2(4=S, Cat, Ss, Stack, T, Ts, Tzr) ->
%%  yeccpars2_0(S, Cat, Ss, Stack, T, Ts, Tzr);
%% yeccpars2(5=S, Cat, Ss, Stack, T, Ts, Tzr) ->
%%  yeccpars2_5(S, Cat, Ss, Stack, T, Ts, Tzr);
%% yeccpars2(6=S, Cat, Ss, Stack, T, Ts, Tzr) ->
%%  yeccpars2_6(S, Cat, Ss, Stack, T, Ts, Tzr);
%% yeccpars2(7=S, Cat, Ss, Stack, T, Ts, Tzr) ->
%%  yeccpars2_7(S, Cat, Ss, Stack, T, Ts, Tzr);
%% yeccpars2(8=S, Cat, Ss, Stack, T, Ts, Tzr) ->
%%  yeccpars2_8(S, Cat, Ss, Stack, T, Ts, Tzr);
yeccpars2(9=S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_9(S, Cat, Ss, Stack, T, Ts, Tzr);
yeccpars2(10=S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_10(S, Cat, Ss, Stack, T, Ts, Tzr);
yeccpars2(11=S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_11(S, Cat, Ss, Stack, T, Ts, Tzr);
yeccpars2(12=S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_12(S, Cat, Ss, Stack, T, Ts, Tzr);
yeccpars2(13=S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_13(S, Cat, Ss, Stack, T, Ts, Tzr);
yeccpars2(14=S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_14(S, Cat, Ss, Stack, T, Ts, Tzr);
yeccpars2(15=S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_15(S, Cat, Ss, Stack, T, Ts, Tzr);
yeccpars2(16=S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_16(S, Cat, Ss, Stack, T, Ts, Tzr);
yeccpars2(17=S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_17(S, Cat, Ss, Stack, T, Ts, Tzr);
yeccpars2(18=S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_18(S, Cat, Ss, Stack, T, Ts, Tzr);
yeccpars2(19=S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_19(S, Cat, Ss, Stack, T, Ts, Tzr);
yeccpars2(20=S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_20(S, Cat, Ss, Stack, T, Ts, Tzr);
yeccpars2(21=S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_21(S, Cat, Ss, Stack, T, Ts, Tzr);
%% yeccpars2(22=S, Cat, Ss, Stack, T, Ts, Tzr) ->
%%  yeccpars2_22(S, Cat, Ss, Stack, T, Ts, Tzr);
%% yeccpars2(23=S, Cat, Ss, Stack, T, Ts, Tzr) ->
%%  yeccpars2_23(S, Cat, Ss, Stack, T, Ts, Tzr);
yeccpars2(24=S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_24(S, Cat, Ss, Stack, T, Ts, Tzr);
yeccpars2(25=S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_25(S, Cat, Ss, Stack, T, Ts, Tzr);
%% yeccpars2(26=S, Cat, Ss, Stack, T, Ts, Tzr) ->
%%  yeccpars2_26(S, Cat, Ss, Stack, T, Ts, Tzr);
yeccpars2(27=S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_27(S, Cat, Ss, Stack, T, Ts, Tzr);
%% yeccpars2(28=S, Cat, Ss, Stack, T, Ts, Tzr) ->
%%  yeccpars2_28(S, Cat, Ss, Stack, T, Ts, Tzr);
%% yeccpars2(29=S, Cat, Ss, Stack, T, Ts, Tzr) ->
%%  yeccpars2_29(S, Cat, Ss, Stack, T, Ts, Tzr);
%% yeccpars2(30=S, Cat, Ss, Stack, T, Ts, Tzr) ->
%%  yeccpars2_30(S, Cat, Ss, Stack, T, Ts, Tzr);
%% yeccpars2(31=S, Cat, Ss, Stack, T, Ts, Tzr) ->
%%  yeccpars2_31(S, Cat, Ss, Stack, T, Ts, Tzr);
yeccpars2(32=S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_28(S, Cat, Ss, Stack, T, Ts, Tzr);
yeccpars2(33=S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_33(S, Cat, Ss, Stack, T, Ts, Tzr);
yeccpars2(34=S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_34(S, Cat, Ss, Stack, T, Ts, Tzr);
yeccpars2(35=S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_28(S, Cat, Ss, Stack, T, Ts, Tzr);
%% yeccpars2(36=S, Cat, Ss, Stack, T, Ts, Tzr) ->
%%  yeccpars2_36(S, Cat, Ss, Stack, T, Ts, Tzr);
%% yeccpars2(37=S, Cat, Ss, Stack, T, Ts, Tzr) ->
%%  yeccpars2_28(S, Cat, Ss, Stack, T, Ts, Tzr);
%% yeccpars2(38=S, Cat, Ss, Stack, T, Ts, Tzr) ->
%%  yeccpars2_28(S, Cat, Ss, Stack, T, Ts, Tzr);
yeccpars2(39=S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_39(S, Cat, Ss, Stack, T, Ts, Tzr);
yeccpars2(40=S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_40(S, Cat, Ss, Stack, T, Ts, Tzr);
yeccpars2(41=S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_41(S, Cat, Ss, Stack, T, Ts, Tzr);
yeccpars2(42=S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_42(S, Cat, Ss, Stack, T, Ts, Tzr);
yeccpars2(43=S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_43(S, Cat, Ss, Stack, T, Ts, Tzr);
yeccpars2(44=S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_44(S, Cat, Ss, Stack, T, Ts, Tzr);
yeccpars2(45=S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_45(S, Cat, Ss, Stack, T, Ts, Tzr);
yeccpars2(46=S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_46(S, Cat, Ss, Stack, T, Ts, Tzr);
yeccpars2(47=S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_47(S, Cat, Ss, Stack, T, Ts, Tzr);
yeccpars2(48=S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_48(S, Cat, Ss, Stack, T, Ts, Tzr);
yeccpars2(49=S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_49(S, Cat, Ss, Stack, T, Ts, Tzr);
%% yeccpars2(50=S, Cat, Ss, Stack, T, Ts, Tzr) ->
%%  yeccpars2_50(S, Cat, Ss, Stack, T, Ts, Tzr);
%% yeccpars2(51=S, Cat, Ss, Stack, T, Ts, Tzr) ->
%%  yeccpars2_51(S, Cat, Ss, Stack, T, Ts, Tzr);
yeccpars2(52=S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_28(S, Cat, Ss, Stack, T, Ts, Tzr);
%% yeccpars2(53=S, Cat, Ss, Stack, T, Ts, Tzr) ->
%%  yeccpars2_53(S, Cat, Ss, Stack, T, Ts, Tzr);
yeccpars2(54=S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_54(S, Cat, Ss, Stack, T, Ts, Tzr);
%% yeccpars2(55=S, Cat, Ss, Stack, T, Ts, Tzr) ->
%%  yeccpars2_55(S, Cat, Ss, Stack, T, Ts, Tzr);
yeccpars2(56=S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_56(S, Cat, Ss, Stack, T, Ts, Tzr);
yeccpars2(57=S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_28(S, Cat, Ss, Stack, T, Ts, Tzr);
%% yeccpars2(58=S, Cat, Ss, Stack, T, Ts, Tzr) ->
%%  yeccpars2_58(S, Cat, Ss, Stack, T, Ts, Tzr);
yeccpars2(59=S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_59(S, Cat, Ss, Stack, T, Ts, Tzr);
%% yeccpars2(60=S, Cat, Ss, Stack, T, Ts, Tzr) ->
%%  yeccpars2_60(S, Cat, Ss, Stack, T, Ts, Tzr);
%% yeccpars2(61=S, Cat, Ss, Stack, T, Ts, Tzr) ->
%%  yeccpars2_61(S, Cat, Ss, Stack, T, Ts, Tzr);
%% yeccpars2(62=S, Cat, Ss, Stack, T, Ts, Tzr) ->
%%  yeccpars2_62(S, Cat, Ss, Stack, T, Ts, Tzr);
yeccpars2(63=S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_63(S, Cat, Ss, Stack, T, Ts, Tzr);
yeccpars2(64=S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_64(S, Cat, Ss, Stack, T, Ts, Tzr);
%% yeccpars2(65=S, Cat, Ss, Stack, T, Ts, Tzr) ->
%%  yeccpars2_0(S, Cat, Ss, Stack, T, Ts, Tzr);
%% yeccpars2(66=S, Cat, Ss, Stack, T, Ts, Tzr) ->
%%  yeccpars2_0(S, Cat, Ss, Stack, T, Ts, Tzr);
%% yeccpars2(67=S, Cat, Ss, Stack, T, Ts, Tzr) ->
%%  yeccpars2_0(S, Cat, Ss, Stack, T, Ts, Tzr);
%% yeccpars2(68=S, Cat, Ss, Stack, T, Ts, Tzr) ->
%%  yeccpars2_0(S, Cat, Ss, Stack, T, Ts, Tzr);
yeccpars2(69=S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_69(S, Cat, Ss, Stack, T, Ts, Tzr);
yeccpars2(70=S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_70(S, Cat, Ss, Stack, T, Ts, Tzr);
yeccpars2(71=S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_71(S, Cat, Ss, Stack, T, Ts, Tzr);
yeccpars2(72=S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_72(S, Cat, Ss, Stack, T, Ts, Tzr);
yeccpars2(73=S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_73(S, Cat, Ss, Stack, T, Ts, Tzr);
yeccpars2(74=S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_74(S, Cat, Ss, Stack, T, Ts, Tzr);
yeccpars2(75=S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_75(S, Cat, Ss, Stack, T, Ts, Tzr);
yeccpars2(76=S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_76(S, Cat, Ss, Stack, T, Ts, Tzr);
yeccpars2(77=S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_77(S, Cat, Ss, Stack, T, Ts, Tzr);
yeccpars2(78=S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_78(S, Cat, Ss, Stack, T, Ts, Tzr);
yeccpars2(79=S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_79(S, Cat, Ss, Stack, T, Ts, Tzr);
yeccpars2(80=S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_80(S, Cat, Ss, Stack, T, Ts, Tzr);
yeccpars2(81=S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_81(S, Cat, Ss, Stack, T, Ts, Tzr);
yeccpars2(82=S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_82(S, Cat, Ss, Stack, T, Ts, Tzr);
yeccpars2(83=S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_83(S, Cat, Ss, Stack, T, Ts, Tzr);
%% yeccpars2(84=S, Cat, Ss, Stack, T, Ts, Tzr) ->
%%  yeccpars2_84(S, Cat, Ss, Stack, T, Ts, Tzr);
yeccpars2(85=S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_85(S, Cat, Ss, Stack, T, Ts, Tzr);
yeccpars2(86=S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_75(S, Cat, Ss, Stack, T, Ts, Tzr);
%% yeccpars2(87=S, Cat, Ss, Stack, T, Ts, Tzr) ->
%%  yeccpars2_87(S, Cat, Ss, Stack, T, Ts, Tzr);
yeccpars2(88=S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_88(S, Cat, Ss, Stack, T, Ts, Tzr);
%% yeccpars2(89=S, Cat, Ss, Stack, T, Ts, Tzr) ->
%%  yeccpars2_89(S, Cat, Ss, Stack, T, Ts, Tzr);
%% yeccpars2(90=S, Cat, Ss, Stack, T, Ts, Tzr) ->
%%  yeccpars2_90(S, Cat, Ss, Stack, T, Ts, Tzr);
%% yeccpars2(91=S, Cat, Ss, Stack, T, Ts, Tzr) ->
%%  yeccpars2_91(S, Cat, Ss, Stack, T, Ts, Tzr);
%% yeccpars2(92=S, Cat, Ss, Stack, T, Ts, Tzr) ->
%%  yeccpars2_92(S, Cat, Ss, Stack, T, Ts, Tzr);
%% yeccpars2(93=S, Cat, Ss, Stack, T, Ts, Tzr) ->
%%  yeccpars2_93(S, Cat, Ss, Stack, T, Ts, Tzr);
yeccpars2(94=S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_94(S, Cat, Ss, Stack, T, Ts, Tzr);
yeccpars2(95=S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_61(S, Cat, Ss, Stack, T, Ts, Tzr);
%% yeccpars2(96=S, Cat, Ss, Stack, T, Ts, Tzr) ->
%%  yeccpars2_96(S, Cat, Ss, Stack, T, Ts, Tzr);
yeccpars2(97=S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_97(S, Cat, Ss, Stack, T, Ts, Tzr);
yeccpars2(98=S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_98(S, Cat, Ss, Stack, T, Ts, Tzr);
%% yeccpars2(99=S, Cat, Ss, Stack, T, Ts, Tzr) ->
%%  yeccpars2_99(S, Cat, Ss, Stack, T, Ts, Tzr);
%% yeccpars2(100=S, Cat, Ss, Stack, T, Ts, Tzr) ->
%%  yeccpars2_100(S, Cat, Ss, Stack, T, Ts, Tzr);
%% yeccpars2(101=S, Cat, Ss, Stack, T, Ts, Tzr) ->
%%  yeccpars2_101(S, Cat, Ss, Stack, T, Ts, Tzr);
yeccpars2(102=S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_102(S, Cat, Ss, Stack, T, Ts, Tzr);
yeccpars2(103=S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_103(S, Cat, Ss, Stack, T, Ts, Tzr);
yeccpars2(104=S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_98(S, Cat, Ss, Stack, T, Ts, Tzr);
yeccpars2(105=S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_98(S, Cat, Ss, Stack, T, Ts, Tzr);
yeccpars2(106=S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_98(S, Cat, Ss, Stack, T, Ts, Tzr);
yeccpars2(107=S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_98(S, Cat, Ss, Stack, T, Ts, Tzr);
%% yeccpars2(108=S, Cat, Ss, Stack, T, Ts, Tzr) ->
%%  yeccpars2_108(S, Cat, Ss, Stack, T, Ts, Tzr);
%% yeccpars2(109=S, Cat, Ss, Stack, T, Ts, Tzr) ->
%%  yeccpars2_109(S, Cat, Ss, Stack, T, Ts, Tzr);
%% yeccpars2(110=S, Cat, Ss, Stack, T, Ts, Tzr) ->
%%  yeccpars2_110(S, Cat, Ss, Stack, T, Ts, Tzr);
%% yeccpars2(111=S, Cat, Ss, Stack, T, Ts, Tzr) ->
%%  yeccpars2_111(S, Cat, Ss, Stack, T, Ts, Tzr);
yeccpars2(112=S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_112(S, Cat, Ss, Stack, T, Ts, Tzr);
%% yeccpars2(113=S, Cat, Ss, Stack, T, Ts, Tzr) ->
%%  yeccpars2_113(S, Cat, Ss, Stack, T, Ts, Tzr);
yeccpars2(114=S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_114(S, Cat, Ss, Stack, T, Ts, Tzr);
%% yeccpars2(115=S, Cat, Ss, Stack, T, Ts, Tzr) ->
%%  yeccpars2_2(S, Cat, Ss, Stack, T, Ts, Tzr);
%% yeccpars2(116=S, Cat, Ss, Stack, T, Ts, Tzr) ->
%%  yeccpars2_2(S, Cat, Ss, Stack, T, Ts, Tzr);
%% yeccpars2(117=S, Cat, Ss, Stack, T, Ts, Tzr) ->
%%  yeccpars2_2(S, Cat, Ss, Stack, T, Ts, Tzr);
yeccpars2(118=S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_118(S, Cat, Ss, Stack, T, Ts, Tzr);
yeccpars2(119=S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_119(S, Cat, Ss, Stack, T, Ts, Tzr);
yeccpars2(120=S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_120(S, Cat, Ss, Stack, T, Ts, Tzr);
yeccpars2(121=S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_121(S, Cat, Ss, Stack, T, Ts, Tzr);
yeccpars2(122=S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_122(S, Cat, Ss, Stack, T, Ts, Tzr);
yeccpars2(123=S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_123(S, Cat, Ss, Stack, T, Ts, Tzr);
%% yeccpars2(124=S, Cat, Ss, Stack, T, Ts, Tzr) ->
%%  yeccpars2_124(S, Cat, Ss, Stack, T, Ts, Tzr);
yeccpars2(125=S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_125(S, Cat, Ss, Stack, T, Ts, Tzr);
%% yeccpars2(126=S, Cat, Ss, Stack, T, Ts, Tzr) ->
%%  yeccpars2_126(S, Cat, Ss, Stack, T, Ts, Tzr);
%% yeccpars2(127=S, Cat, Ss, Stack, T, Ts, Tzr) ->
%%  yeccpars2_127(S, Cat, Ss, Stack, T, Ts, Tzr);
yeccpars2(128=S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_21(S, Cat, Ss, Stack, T, Ts, Tzr);
%% yeccpars2(129=S, Cat, Ss, Stack, T, Ts, Tzr) ->
%%  yeccpars2_129(S, Cat, Ss, Stack, T, Ts, Tzr);
%% yeccpars2(130=S, Cat, Ss, Stack, T, Ts, Tzr) ->
%%  yeccpars2_130(S, Cat, Ss, Stack, T, Ts, Tzr);
%% yeccpars2(131=S, Cat, Ss, Stack, T, Ts, Tzr) ->
%%  yeccpars2_131(S, Cat, Ss, Stack, T, Ts, Tzr);
%% yeccpars2(132=S, Cat, Ss, Stack, T, Ts, Tzr) ->
%%  yeccpars2_132(S, Cat, Ss, Stack, T, Ts, Tzr);
yeccpars2(133=S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_10(S, Cat, Ss, Stack, T, Ts, Tzr);
%% yeccpars2(134=S, Cat, Ss, Stack, T, Ts, Tzr) ->
%%  yeccpars2_134(S, Cat, Ss, Stack, T, Ts, Tzr);
%% yeccpars2(135=S, Cat, Ss, Stack, T, Ts, Tzr) ->
%%  yeccpars2_135(S, Cat, Ss, Stack, T, Ts, Tzr);
yeccpars2(136=S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_0(S, Cat, Ss, Stack, T, Ts, Tzr);
%% yeccpars2(137=S, Cat, Ss, Stack, T, Ts, Tzr) ->
%%  yeccpars2_137(S, Cat, Ss, Stack, T, Ts, Tzr);
%% yeccpars2(138=S, Cat, Ss, Stack, T, Ts, Tzr) ->
%%  yeccpars2_138(S, Cat, Ss, Stack, T, Ts, Tzr);
yeccpars2(139=S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_139(S, Cat, Ss, Stack, T, Ts, Tzr);
yeccpars2(Other, _, _, _, _, _, _) ->
 erlang:error({yecc_bug,"1.4",{missing_state_in_action_table, Other}}).

yeccpars2_0(S, '!', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 9, Ss, Stack, T, Ts, Tzr);
yeccpars2_0(S, '(', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 10, Ss, Stack, T, Ts, Tzr);
yeccpars2_0(S, '+', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 11, Ss, Stack, T, Ts, Tzr);
yeccpars2_0(S, '-', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 12, Ss, Stack, T, Ts, Tzr);
yeccpars2_0(S, 'not', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 16, Ss, Stack, T, Ts, Tzr);
yeccpars2_0(S, symbol, Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 18, Ss, Stack, T, Ts, Tzr);
yeccpars2_0(S, '~', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 19, Ss, Stack, T, Ts, Tzr);
yeccpars2_0(S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_cont_0(S, Cat, Ss, Stack, T, Ts, Tzr).

yeccpars2_cont_0(S, binnum, Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 13, Ss, Stack, T, Ts, Tzr);
yeccpars2_cont_0(S, decnum, Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 14, Ss, Stack, T, Ts, Tzr);
yeccpars2_cont_0(S, hexnum, Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 15, Ss, Stack, T, Ts, Tzr);
yeccpars2_cont_0(S, octnum, Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 17, Ss, Stack, T, Ts, Tzr);
yeccpars2_cont_0(_, _, _, _, T, _, _) ->
 yeccerror(T).

yeccpars2_1(S, '!', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 9, Ss, Stack, T, Ts, Tzr);
yeccpars2_1(S, '(', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 133, Ss, Stack, T, Ts, Tzr);
yeccpars2_1(S, '+', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 11, Ss, Stack, T, Ts, Tzr);
yeccpars2_1(S, '-', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 12, Ss, Stack, T, Ts, Tzr);
yeccpars2_1(S, 'not', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 16, Ss, Stack, T, Ts, Tzr);
yeccpars2_1(S, symbol, Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 18, Ss, Stack, T, Ts, Tzr);
yeccpars2_1(S, '~', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 19, Ss, Stack, T, Ts, Tzr);
yeccpars2_1(S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_cont_0(S, Cat, Ss, Stack, T, Ts, Tzr).

yeccpars2_2(S, '+', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 11, Ss, Stack, T, Ts, Tzr);
yeccpars2_2(S, '-', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 12, Ss, Stack, T, Ts, Tzr);
yeccpars2_2(S, symbol, Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 125, Ss, Stack, T, Ts, Tzr);
yeccpars2_2(S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_cont_0(S, Cat, Ss, Stack, T, Ts, Tzr).

yeccpars2_3(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccgoto_lexpr(hd(Ss), Cat, Ss, Stack, T, Ts, Tzr).

%% yeccpars2_4: see yeccpars2_0

yeccpars2_5(S, '&', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 69, Ss, Stack, T, Ts, Tzr);
yeccpars2_5(S, '&&', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 70, Ss, Stack, T, Ts, Tzr);
yeccpars2_5(S, '->', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 72, Ss, Stack, T, Ts, Tzr);
yeccpars2_5(S, '<->', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 73, Ss, Stack, T, Ts, Tzr);
yeccpars2_5(S, '=', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 74, Ss, Stack, T, Ts, Tzr);
yeccpars2_5(S, '[', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 75, Ss, Stack, T, Ts, Tzr);
yeccpars2_5(S, '^', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 76, Ss, Stack, T, Ts, Tzr);
yeccpars2_5(S, 'and', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 77, Ss, Stack, T, Ts, Tzr);
yeccpars2_5(S, equ, Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 78, Ss, Stack, T, Ts, Tzr);
yeccpars2_5(S, imp, Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 79, Ss, Stack, T, Ts, Tzr);
yeccpars2_5(S, 'or', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 80, Ss, Stack, T, Ts, Tzr);
yeccpars2_5(S, 'xor', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 81, Ss, Stack, T, Ts, Tzr);
yeccpars2_5(S, '|', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 82, Ss, Stack, T, Ts, Tzr);
yeccpars2_5(S, '||', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 83, Ss, Stack, T, Ts, Tzr);
yeccpars2_5(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccgoto_formula(hd(Ss), Cat, Ss, Stack, T, Ts, Tzr).

yeccpars2_6(S, ':', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 128, Ss, Stack, T, Ts, Tzr);
yeccpars2_6(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 NewStack = yeccpars2_6_(Stack),
 yeccgoto_aexpr(hd(Ss), Cat, Ss, NewStack, T, Ts, Tzr).

yeccpars2_7(_S, '$end', _Ss, Stack, _T, _Ts, _Tzr) ->
 {ok, hd(Stack)};
yeccpars2_7(_, _, _, _, T, _, _) ->
 yeccerror(T).

yeccpars2_8(S, '!=', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 118, Ss, Stack, T, Ts, Tzr);
yeccpars2_8(S, '<', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 119, Ss, Stack, T, Ts, Tzr);
yeccpars2_8(S, '<=', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 120, Ss, Stack, T, Ts, Tzr);
yeccpars2_8(S, '==', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 121, Ss, Stack, T, Ts, Tzr);
yeccpars2_8(S, '>', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 122, Ss, Stack, T, Ts, Tzr);
yeccpars2_8(S, '>=', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 123, Ss, Stack, T, Ts, Tzr);
yeccpars2_8(S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_cont_8(S, Cat, Ss, Stack, T, Ts, Tzr).

yeccpars2_cont_8(S, '%', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 40, Ss, Stack, T, Ts, Tzr);
yeccpars2_cont_8(S, '*', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 41, Ss, Stack, T, Ts, Tzr);
yeccpars2_cont_8(S, '+', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 42, Ss, Stack, T, Ts, Tzr);
yeccpars2_cont_8(S, '-', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 43, Ss, Stack, T, Ts, Tzr);
yeccpars2_cont_8(S, '/', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 44, Ss, Stack, T, Ts, Tzr);
yeccpars2_cont_8(S, '<<', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 45, Ss, Stack, T, Ts, Tzr);
yeccpars2_cont_8(S, '<<<', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 46, Ss, Stack, T, Ts, Tzr);
yeccpars2_cont_8(S, '>>', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 47, Ss, Stack, T, Ts, Tzr);
yeccpars2_cont_8(S, '>>>', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 48, Ss, Stack, T, Ts, Tzr);
yeccpars2_cont_8(_, _, _, _, T, _, _) ->
 yeccerror(T).

yeccpars2_9(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccgoto_not_op(hd(Ss), Cat, Ss, Stack, T, Ts, Tzr).

yeccpars2_10(S, '!', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 9, Ss, Stack, T, Ts, Tzr);
yeccpars2_10(S, '(', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 10, Ss, Stack, T, Ts, Tzr);
yeccpars2_10(S, '+', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 11, Ss, Stack, T, Ts, Tzr);
yeccpars2_10(S, '-', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 12, Ss, Stack, T, Ts, Tzr);
yeccpars2_10(S, 'not', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 16, Ss, Stack, T, Ts, Tzr);
yeccpars2_10(S, symbol, Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 63, Ss, Stack, T, Ts, Tzr);
yeccpars2_10(S, '~', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 19, Ss, Stack, T, Ts, Tzr);
yeccpars2_10(S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_cont_0(S, Cat, Ss, Stack, T, Ts, Tzr).

yeccpars2_11(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccgoto_prefix_op(hd(Ss), Cat, Ss, Stack, T, Ts, Tzr).

yeccpars2_12(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccgoto_prefix_op(hd(Ss), Cat, Ss, Stack, T, Ts, Tzr).

yeccpars2_13(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccgoto_integer(hd(Ss), Cat, Ss, Stack, T, Ts, Tzr).

yeccpars2_14(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccgoto_integer(hd(Ss), Cat, Ss, Stack, T, Ts, Tzr).

yeccpars2_15(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccgoto_integer(hd(Ss), Cat, Ss, Stack, T, Ts, Tzr).

yeccpars2_16(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccgoto_not_op(hd(Ss), Cat, Ss, Stack, T, Ts, Tzr).

yeccpars2_17(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccgoto_integer(hd(Ss), Cat, Ss, Stack, T, Ts, Tzr).

yeccpars2_18(S, '(', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 20, Ss, Stack, T, Ts, Tzr);
yeccpars2_18(S, ':', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 21, Ss, Stack, T, Ts, Tzr);
yeccpars2_18(_S, '!=', Ss, Stack, T, Ts, Tzr) ->
 NewStack = 'yeccpars2_18_!='(Stack),
 yeccgoto_aexpr(hd(Ss), '!=', Ss, NewStack, T, Ts, Tzr);
yeccpars2_18(_S, '%', Ss, Stack, T, Ts, Tzr) ->
 NewStack = 'yeccpars2_18_%'(Stack),
 yeccgoto_aexpr(hd(Ss), '%', Ss, NewStack, T, Ts, Tzr);
yeccpars2_18(_S, '*', Ss, Stack, T, Ts, Tzr) ->
 NewStack = 'yeccpars2_18_*'(Stack),
 yeccgoto_aexpr(hd(Ss), '*', Ss, NewStack, T, Ts, Tzr);
yeccpars2_18(_S, '+', Ss, Stack, T, Ts, Tzr) ->
 NewStack = 'yeccpars2_18_+'(Stack),
 yeccgoto_aexpr(hd(Ss), '+', Ss, NewStack, T, Ts, Tzr);
yeccpars2_18(_S, '-', Ss, Stack, T, Ts, Tzr) ->
 NewStack = 'yeccpars2_18_-'(Stack),
 yeccgoto_aexpr(hd(Ss), '-', Ss, NewStack, T, Ts, Tzr);
yeccpars2_18(_S, '/', Ss, Stack, T, Ts, Tzr) ->
 NewStack = 'yeccpars2_18_/'(Stack),
 yeccgoto_aexpr(hd(Ss), '/', Ss, NewStack, T, Ts, Tzr);
yeccpars2_18(_S, '<', Ss, Stack, T, Ts, Tzr) ->
 NewStack = 'yeccpars2_18_<'(Stack),
 yeccgoto_aexpr(hd(Ss), '<', Ss, NewStack, T, Ts, Tzr);
yeccpars2_18(_S, '<<', Ss, Stack, T, Ts, Tzr) ->
 NewStack = 'yeccpars2_18_<<'(Stack),
 yeccgoto_aexpr(hd(Ss), '<<', Ss, NewStack, T, Ts, Tzr);
yeccpars2_18(_S, '<<<', Ss, Stack, T, Ts, Tzr) ->
 NewStack = 'yeccpars2_18_<<<'(Stack),
 yeccgoto_aexpr(hd(Ss), '<<<', Ss, NewStack, T, Ts, Tzr);
yeccpars2_18(_S, '<=', Ss, Stack, T, Ts, Tzr) ->
 NewStack = 'yeccpars2_18_<='(Stack),
 yeccgoto_aexpr(hd(Ss), '<=', Ss, NewStack, T, Ts, Tzr);
yeccpars2_18(_S, '==', Ss, Stack, T, Ts, Tzr) ->
 NewStack = 'yeccpars2_18_=='(Stack),
 yeccgoto_aexpr(hd(Ss), '==', Ss, NewStack, T, Ts, Tzr);
yeccpars2_18(_S, '>', Ss, Stack, T, Ts, Tzr) ->
 NewStack = 'yeccpars2_18_>'(Stack),
 yeccgoto_aexpr(hd(Ss), '>', Ss, NewStack, T, Ts, Tzr);
yeccpars2_18(_S, '>=', Ss, Stack, T, Ts, Tzr) ->
 NewStack = 'yeccpars2_18_>='(Stack),
 yeccgoto_aexpr(hd(Ss), '>=', Ss, NewStack, T, Ts, Tzr);
yeccpars2_18(_S, '>>', Ss, Stack, T, Ts, Tzr) ->
 NewStack = 'yeccpars2_18_>>'(Stack),
 yeccgoto_aexpr(hd(Ss), '>>', Ss, NewStack, T, Ts, Tzr);
yeccpars2_18(_S, '>>>', Ss, Stack, T, Ts, Tzr) ->
 NewStack = 'yeccpars2_18_>>>'(Stack),
 yeccgoto_aexpr(hd(Ss), '>>>', Ss, NewStack, T, Ts, Tzr);
yeccpars2_18(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 NewStack = yeccpars2_18_(Stack),
 yeccgoto_pexpr(hd(Ss), Cat, Ss, NewStack, T, Ts, Tzr).

yeccpars2_19(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccgoto_not_op(hd(Ss), Cat, Ss, Stack, T, Ts, Tzr).

yeccpars2_20(S, '(', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 32, Ss, Stack, T, Ts, Tzr);
yeccpars2_20(S, ')', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 33, Ss, Stack, T, Ts, Tzr);
yeccpars2_20(S, '+', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 11, Ss, Stack, T, Ts, Tzr);
yeccpars2_20(S, '-', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 12, Ss, Stack, T, Ts, Tzr);
yeccpars2_20(S, variable, Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 34, Ss, Stack, T, Ts, Tzr);
yeccpars2_20(S, '|', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 35, Ss, Stack, T, Ts, Tzr);
yeccpars2_20(S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_cont_0(S, Cat, Ss, Stack, T, Ts, Tzr).

yeccpars2_21(S, '-', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 24, Ss, Stack, T, Ts, Tzr);
yeccpars2_21(S, variable, Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 25, Ss, Stack, T, Ts, Tzr);
yeccpars2_21(S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_cont_0(S, Cat, Ss, Stack, T, Ts, Tzr).

yeccpars2_22(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 [_,_|Nss] = Ss,
 NewStack = yeccpars2_22_(Stack),
 yeccgoto_aexpr(hd(Nss), Cat, Nss, NewStack, T, Ts, Tzr).

yeccpars2_23(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 NewStack = yeccpars2_23_(Stack),
 yeccgoto_nexpr(hd(Ss), Cat, Ss, NewStack, T, Ts, Tzr).

yeccpars2_24(S, variable, Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 27, Ss, Stack, T, Ts, Tzr);
yeccpars2_24(S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_cont_0(S, Cat, Ss, Stack, T, Ts, Tzr).

yeccpars2_25(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 NewStack = yeccpars2_25_(Stack),
 yeccgoto_nexpr(hd(Ss), Cat, Ss, NewStack, T, Ts, Tzr).

yeccpars2_26(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 [_|Nss] = Ss,
 NewStack = yeccpars2_26_(Stack),
 yeccgoto_nexpr(hd(Nss), Cat, Nss, NewStack, T, Ts, Tzr).

yeccpars2_27(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 [_|Nss] = Ss,
 NewStack = yeccpars2_27_(Stack),
 yeccgoto_nexpr(hd(Nss), Cat, Nss, NewStack, T, Ts, Tzr).

yeccpars2_28(S, '(', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 32, Ss, Stack, T, Ts, Tzr);
yeccpars2_28(S, '+', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 11, Ss, Stack, T, Ts, Tzr);
yeccpars2_28(S, '-', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 12, Ss, Stack, T, Ts, Tzr);
yeccpars2_28(S, variable, Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 34, Ss, Stack, T, Ts, Tzr);
yeccpars2_28(S, '|', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 35, Ss, Stack, T, Ts, Tzr);
yeccpars2_28(S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_cont_0(S, Cat, Ss, Stack, T, Ts, Tzr).

yeccpars2_29(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 NewStack = yeccpars2_29_(Stack),
 yeccgoto_expr(hd(Ss), Cat, Ss, NewStack, T, Ts, Tzr).

yeccpars2_30(S, ')', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 59, Ss, Stack, T, Ts, Tzr);
yeccpars2_30(_, _, _, _, T, _, _) ->
 yeccerror(T).

yeccpars2_31(S, '!', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 39, Ss, Stack, T, Ts, Tzr);
yeccpars2_31(S, '%', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 40, Ss, Stack, T, Ts, Tzr);
yeccpars2_31(S, '*', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 41, Ss, Stack, T, Ts, Tzr);
yeccpars2_31(S, '+', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 42, Ss, Stack, T, Ts, Tzr);
yeccpars2_31(S, ',', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 57, Ss, Stack, T, Ts, Tzr);
yeccpars2_31(S, '-', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 43, Ss, Stack, T, Ts, Tzr);
yeccpars2_31(S, '/', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 44, Ss, Stack, T, Ts, Tzr);
yeccpars2_31(S, '<<', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 45, Ss, Stack, T, Ts, Tzr);
yeccpars2_31(S, '<<<', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 46, Ss, Stack, T, Ts, Tzr);
yeccpars2_31(S, '>>', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 47, Ss, Stack, T, Ts, Tzr);
yeccpars2_31(S, '>>>', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 48, Ss, Stack, T, Ts, Tzr);
yeccpars2_31(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 NewStack = yeccpars2_31_(Stack),
 yeccgoto_exprs(hd(Ss), Cat, Ss, NewStack, T, Ts, Tzr).

%% yeccpars2_32: see yeccpars2_28

yeccpars2_33(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 [_,_|Nss] = Ss,
 NewStack = yeccpars2_33_(Stack),
 yeccgoto_pexpr(hd(Nss), Cat, Nss, NewStack, T, Ts, Tzr).

yeccpars2_34(S, '(', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 52, Ss, Stack, T, Ts, Tzr);
yeccpars2_34(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 NewStack = yeccpars2_34_(Stack),
 yeccgoto_expr(hd(Ss), Cat, Ss, NewStack, T, Ts, Tzr).

%% yeccpars2_35: see yeccpars2_28

yeccpars2_36(S, '!', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 39, Ss, Stack, T, Ts, Tzr);
yeccpars2_36(S, '|', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 49, Ss, Stack, T, Ts, Tzr);
yeccpars2_36(S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_cont_8(S, Cat, Ss, Stack, T, Ts, Tzr).

%% yeccpars2_37: see yeccpars2_28

%% yeccpars2_38: see yeccpars2_28

yeccpars2_39(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 [_|Nss] = Ss,
 NewStack = yeccpars2_39_(Stack),
 yeccgoto_expr(hd(Nss), Cat, Nss, NewStack, T, Ts, Tzr).

yeccpars2_40(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccgoto_mul_op(hd(Ss), Cat, Ss, Stack, T, Ts, Tzr).

yeccpars2_41(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccgoto_mul_op(hd(Ss), Cat, Ss, Stack, T, Ts, Tzr).

yeccpars2_42(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccgoto_add_op(hd(Ss), Cat, Ss, Stack, T, Ts, Tzr).

yeccpars2_43(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccgoto_add_op(hd(Ss), Cat, Ss, Stack, T, Ts, Tzr).

yeccpars2_44(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccgoto_mul_op(hd(Ss), Cat, Ss, Stack, T, Ts, Tzr).

yeccpars2_45(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccgoto_mul_op(hd(Ss), Cat, Ss, Stack, T, Ts, Tzr).

yeccpars2_46(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccgoto_mul_op(hd(Ss), Cat, Ss, Stack, T, Ts, Tzr).

yeccpars2_47(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccgoto_mul_op(hd(Ss), Cat, Ss, Stack, T, Ts, Tzr).

yeccpars2_48(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccgoto_mul_op(hd(Ss), Cat, Ss, Stack, T, Ts, Tzr).

yeccpars2_49(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 [_,_|Nss] = Ss,
 NewStack = yeccpars2_49_(Stack),
 yeccgoto_expr(hd(Nss), Cat, Nss, NewStack, T, Ts, Tzr).

yeccpars2_50(S, '%', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 40, Ss, Stack, T, Ts, Tzr);
yeccpars2_50(S, '*', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 41, Ss, Stack, T, Ts, Tzr);
yeccpars2_50(S, '/', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 44, Ss, Stack, T, Ts, Tzr);
yeccpars2_50(S, '<<', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 45, Ss, Stack, T, Ts, Tzr);
yeccpars2_50(S, '<<<', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 46, Ss, Stack, T, Ts, Tzr);
yeccpars2_50(S, '>>', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 47, Ss, Stack, T, Ts, Tzr);
yeccpars2_50(S, '>>>', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 48, Ss, Stack, T, Ts, Tzr);
yeccpars2_50(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 [_,_|Nss] = Ss,
 NewStack = yeccpars2_50_(Stack),
 yeccgoto_expr(hd(Nss), Cat, Nss, NewStack, T, Ts, Tzr).

yeccpars2_51(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 [_,_|Nss] = Ss,
 NewStack = yeccpars2_51_(Stack),
 yeccgoto_expr(hd(Nss), Cat, Nss, NewStack, T, Ts, Tzr).

%% yeccpars2_52: see yeccpars2_28

yeccpars2_53(S, ')', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 54, Ss, Stack, T, Ts, Tzr);
yeccpars2_53(_, _, _, _, T, _, _) ->
 yeccerror(T).

yeccpars2_54(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 [_,_,_|Nss] = Ss,
 NewStack = yeccpars2_54_(Stack),
 yeccgoto_expr(hd(Nss), Cat, Nss, NewStack, T, Ts, Tzr).

yeccpars2_55(S, '!', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 39, Ss, Stack, T, Ts, Tzr);
yeccpars2_55(S, ')', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 56, Ss, Stack, T, Ts, Tzr);
yeccpars2_55(S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_cont_8(S, Cat, Ss, Stack, T, Ts, Tzr).

yeccpars2_56(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 [_,_|Nss] = Ss,
 NewStack = yeccpars2_56_(Stack),
 yeccgoto_expr(hd(Nss), Cat, Nss, NewStack, T, Ts, Tzr).

%% yeccpars2_57: see yeccpars2_28

yeccpars2_58(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 [_,_|Nss] = Ss,
 NewStack = yeccpars2_58_(Stack),
 yeccgoto_exprs(hd(Nss), Cat, Nss, NewStack, T, Ts, Tzr).

yeccpars2_59(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 [_,_,_|Nss] = Ss,
 NewStack = yeccpars2_59_(Stack),
 yeccgoto_pexpr(hd(Nss), Cat, Nss, NewStack, T, Ts, Tzr).

yeccpars2_60(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 [_|Nss] = Ss,
 NewStack = yeccpars2_60_(Stack),
 yeccgoto_expr(hd(Nss), Cat, Nss, NewStack, T, Ts, Tzr).

yeccpars2_61(S, variable, Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 94, Ss, Stack, T, Ts, Tzr);
yeccpars2_61(_, _, _, _, T, _, _) ->
 yeccerror(T).

yeccpars2_62(S, '&', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 69, Ss, Stack, T, Ts, Tzr);
yeccpars2_62(S, '&&', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 70, Ss, Stack, T, Ts, Tzr);
yeccpars2_62(S, ')', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 71, Ss, Stack, T, Ts, Tzr);
yeccpars2_62(S, '->', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 72, Ss, Stack, T, Ts, Tzr);
yeccpars2_62(S, '<->', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 73, Ss, Stack, T, Ts, Tzr);
yeccpars2_62(S, '=', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 74, Ss, Stack, T, Ts, Tzr);
yeccpars2_62(S, '[', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 75, Ss, Stack, T, Ts, Tzr);
yeccpars2_62(S, '^', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 76, Ss, Stack, T, Ts, Tzr);
yeccpars2_62(S, 'and', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 77, Ss, Stack, T, Ts, Tzr);
yeccpars2_62(S, equ, Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 78, Ss, Stack, T, Ts, Tzr);
yeccpars2_62(S, imp, Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 79, Ss, Stack, T, Ts, Tzr);
yeccpars2_62(S, 'or', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 80, Ss, Stack, T, Ts, Tzr);
yeccpars2_62(S, 'xor', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 81, Ss, Stack, T, Ts, Tzr);
yeccpars2_62(S, '|', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 82, Ss, Stack, T, Ts, Tzr);
yeccpars2_62(S, '||', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 83, Ss, Stack, T, Ts, Tzr);
yeccpars2_62(_, _, _, _, T, _, _) ->
 yeccerror(T).

yeccpars2_63(S, '!', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 64, Ss, Stack, T, Ts, Tzr);
yeccpars2_63(S, '(', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 20, Ss, Stack, T, Ts, Tzr);
yeccpars2_63(S, ':', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 21, Ss, Stack, T, Ts, Tzr);
yeccpars2_63(_S, '!=', Ss, Stack, T, Ts, Tzr) ->
 NewStack = 'yeccpars2_63_!='(Stack),
 yeccgoto_aexpr(hd(Ss), '!=', Ss, NewStack, T, Ts, Tzr);
yeccpars2_63(_S, '%', Ss, Stack, T, Ts, Tzr) ->
 NewStack = 'yeccpars2_63_%'(Stack),
 yeccgoto_aexpr(hd(Ss), '%', Ss, NewStack, T, Ts, Tzr);
yeccpars2_63(_S, '*', Ss, Stack, T, Ts, Tzr) ->
 NewStack = 'yeccpars2_63_*'(Stack),
 yeccgoto_aexpr(hd(Ss), '*', Ss, NewStack, T, Ts, Tzr);
yeccpars2_63(_S, '+', Ss, Stack, T, Ts, Tzr) ->
 NewStack = 'yeccpars2_63_+'(Stack),
 yeccgoto_aexpr(hd(Ss), '+', Ss, NewStack, T, Ts, Tzr);
yeccpars2_63(_S, '-', Ss, Stack, T, Ts, Tzr) ->
 NewStack = 'yeccpars2_63_-'(Stack),
 yeccgoto_aexpr(hd(Ss), '-', Ss, NewStack, T, Ts, Tzr);
yeccpars2_63(_S, '/', Ss, Stack, T, Ts, Tzr) ->
 NewStack = 'yeccpars2_63_/'(Stack),
 yeccgoto_aexpr(hd(Ss), '/', Ss, NewStack, T, Ts, Tzr);
yeccpars2_63(_S, '<', Ss, Stack, T, Ts, Tzr) ->
 NewStack = 'yeccpars2_63_<'(Stack),
 yeccgoto_aexpr(hd(Ss), '<', Ss, NewStack, T, Ts, Tzr);
yeccpars2_63(_S, '<<', Ss, Stack, T, Ts, Tzr) ->
 NewStack = 'yeccpars2_63_<<'(Stack),
 yeccgoto_aexpr(hd(Ss), '<<', Ss, NewStack, T, Ts, Tzr);
yeccpars2_63(_S, '<<<', Ss, Stack, T, Ts, Tzr) ->
 NewStack = 'yeccpars2_63_<<<'(Stack),
 yeccgoto_aexpr(hd(Ss), '<<<', Ss, NewStack, T, Ts, Tzr);
yeccpars2_63(_S, '<=', Ss, Stack, T, Ts, Tzr) ->
 NewStack = 'yeccpars2_63_<='(Stack),
 yeccgoto_aexpr(hd(Ss), '<=', Ss, NewStack, T, Ts, Tzr);
yeccpars2_63(_S, '==', Ss, Stack, T, Ts, Tzr) ->
 NewStack = 'yeccpars2_63_=='(Stack),
 yeccgoto_aexpr(hd(Ss), '==', Ss, NewStack, T, Ts, Tzr);
yeccpars2_63(_S, '>', Ss, Stack, T, Ts, Tzr) ->
 NewStack = 'yeccpars2_63_>'(Stack),
 yeccgoto_aexpr(hd(Ss), '>', Ss, NewStack, T, Ts, Tzr);
yeccpars2_63(_S, '>=', Ss, Stack, T, Ts, Tzr) ->
 NewStack = 'yeccpars2_63_>='(Stack),
 yeccgoto_aexpr(hd(Ss), '>=', Ss, NewStack, T, Ts, Tzr);
yeccpars2_63(_S, '>>', Ss, Stack, T, Ts, Tzr) ->
 NewStack = 'yeccpars2_63_>>'(Stack),
 yeccgoto_aexpr(hd(Ss), '>>', Ss, NewStack, T, Ts, Tzr);
yeccpars2_63(_S, '>>>', Ss, Stack, T, Ts, Tzr) ->
 NewStack = 'yeccpars2_63_>>>'(Stack),
 yeccgoto_aexpr(hd(Ss), '>>>', Ss, NewStack, T, Ts, Tzr);
yeccpars2_63(_S, '&', Ss, Stack, T, Ts, Tzr) ->
 NewStack = 'yeccpars2_63_&'(Stack),
 yeccgoto_pexpr(hd(Ss), '&', Ss, NewStack, T, Ts, Tzr);
yeccpars2_63(_S, '&&', Ss, Stack, T, Ts, Tzr) ->
 NewStack = 'yeccpars2_63_&&'(Stack),
 yeccgoto_pexpr(hd(Ss), '&&', Ss, NewStack, T, Ts, Tzr);
yeccpars2_63(_S, ')', Ss, Stack, T, Ts, Tzr) ->
 NewStack = 'yeccpars2_63_)'(Stack),
 yeccgoto_pexpr(hd(Ss), ')', Ss, NewStack, T, Ts, Tzr);
yeccpars2_63(_S, ',', Ss, Stack, T, Ts, Tzr) ->
 NewStack = 'yeccpars2_63_,'(Stack),
 yeccgoto_pexpr(hd(Ss), ',', Ss, NewStack, T, Ts, Tzr);
yeccpars2_63(_S, '->', Ss, Stack, T, Ts, Tzr) ->
 NewStack = 'yeccpars2_63_->'(Stack),
 yeccgoto_pexpr(hd(Ss), '->', Ss, NewStack, T, Ts, Tzr);
yeccpars2_63(_S, '<->', Ss, Stack, T, Ts, Tzr) ->
 NewStack = 'yeccpars2_63_<->'(Stack),
 yeccgoto_pexpr(hd(Ss), '<->', Ss, NewStack, T, Ts, Tzr);
yeccpars2_63(_S, '=', Ss, Stack, T, Ts, Tzr) ->
 NewStack = 'yeccpars2_63_='(Stack),
 yeccgoto_pexpr(hd(Ss), '=', Ss, NewStack, T, Ts, Tzr);
yeccpars2_63(_S, '[', Ss, Stack, T, Ts, Tzr) ->
 NewStack = 'yeccpars2_63_['(Stack),
 yeccgoto_pexpr(hd(Ss), '[', Ss, NewStack, T, Ts, Tzr);
yeccpars2_63(_S, '^', Ss, Stack, T, Ts, Tzr) ->
 NewStack = 'yeccpars2_63_^'(Stack),
 yeccgoto_pexpr(hd(Ss), '^', Ss, NewStack, T, Ts, Tzr);
yeccpars2_63(_S, 'and', Ss, Stack, T, Ts, Tzr) ->
 NewStack = yeccpars2_63_and(Stack),
 yeccgoto_pexpr(hd(Ss), 'and', Ss, NewStack, T, Ts, Tzr);
yeccpars2_63(_S, equ, Ss, Stack, T, Ts, Tzr) ->
 NewStack = yeccpars2_63_equ(Stack),
 yeccgoto_pexpr(hd(Ss), equ, Ss, NewStack, T, Ts, Tzr);
yeccpars2_63(_S, imp, Ss, Stack, T, Ts, Tzr) ->
 NewStack = yeccpars2_63_imp(Stack),
 yeccgoto_pexpr(hd(Ss), imp, Ss, NewStack, T, Ts, Tzr);
yeccpars2_63(_S, 'or', Ss, Stack, T, Ts, Tzr) ->
 NewStack = yeccpars2_63_or(Stack),
 yeccgoto_pexpr(hd(Ss), 'or', Ss, NewStack, T, Ts, Tzr);
yeccpars2_63(_S, 'xor', Ss, Stack, T, Ts, Tzr) ->
 NewStack = yeccpars2_63_xor(Stack),
 yeccgoto_pexpr(hd(Ss), 'xor', Ss, NewStack, T, Ts, Tzr);
yeccpars2_63(_S, '|', Ss, Stack, T, Ts, Tzr) ->
 NewStack = 'yeccpars2_63_|'(Stack),
 yeccgoto_pexpr(hd(Ss), '|', Ss, NewStack, T, Ts, Tzr);
yeccpars2_63(_S, '||', Ss, Stack, T, Ts, Tzr) ->
 NewStack = 'yeccpars2_63_||'(Stack),
 yeccgoto_pexpr(hd(Ss), '||', Ss, NewStack, T, Ts, Tzr);
yeccpars2_63(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 NewStack = yeccpars2_63_(Stack),
 yeccgoto_qtype(hd(Ss), Cat, Ss, NewStack, T, Ts, Tzr).

yeccpars2_64(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 [_|Nss] = Ss,
 NewStack = yeccpars2_64_(Stack),
 yeccgoto_qtype(hd(Nss), Cat, Nss, NewStack, T, Ts, Tzr).

%% yeccpars2_65: see yeccpars2_0

%% yeccpars2_66: see yeccpars2_0

%% yeccpars2_67: see yeccpars2_0

%% yeccpars2_68: see yeccpars2_0

yeccpars2_69(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccgoto_and_op(hd(Ss), Cat, Ss, Stack, T, Ts, Tzr).

yeccpars2_70(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccgoto_and_op(hd(Ss), Cat, Ss, Stack, T, Ts, Tzr).

yeccpars2_71(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 [_,_|Nss] = Ss,
 NewStack = yeccpars2_71_(Stack),
 yeccgoto_lexpr(hd(Nss), Cat, Nss, NewStack, T, Ts, Tzr).

yeccpars2_72(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccgoto_imp_op(hd(Ss), Cat, Ss, Stack, T, Ts, Tzr).

yeccpars2_73(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccgoto_equ_op(hd(Ss), Cat, Ss, Stack, T, Ts, Tzr).

yeccpars2_74(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccgoto_equ_op(hd(Ss), Cat, Ss, Stack, T, Ts, Tzr).

yeccpars2_75(S, symbol, Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 85, Ss, Stack, T, Ts, Tzr);
yeccpars2_75(_, _, _, _, T, _, _) ->
 yeccerror(T).

yeccpars2_76(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccgoto_equ_op(hd(Ss), Cat, Ss, Stack, T, Ts, Tzr).

yeccpars2_77(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccgoto_and_op(hd(Ss), Cat, Ss, Stack, T, Ts, Tzr).

yeccpars2_78(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccgoto_equ_op(hd(Ss), Cat, Ss, Stack, T, Ts, Tzr).

yeccpars2_79(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccgoto_imp_op(hd(Ss), Cat, Ss, Stack, T, Ts, Tzr).

yeccpars2_80(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccgoto_or_op(hd(Ss), Cat, Ss, Stack, T, Ts, Tzr).

yeccpars2_81(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccgoto_equ_op(hd(Ss), Cat, Ss, Stack, T, Ts, Tzr).

yeccpars2_82(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccgoto_or_op(hd(Ss), Cat, Ss, Stack, T, Ts, Tzr).

yeccpars2_83(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccgoto_or_op(hd(Ss), Cat, Ss, Stack, T, Ts, Tzr).

yeccpars2_84(S, '/', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 86, Ss, Stack, T, Ts, Tzr);
yeccpars2_84(_, _, _, _, T, _, _) ->
 yeccerror(T).

yeccpars2_85(S, '(', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 20, Ss, Stack, T, Ts, Tzr);
yeccpars2_85(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 NewStack = yeccpars2_85_(Stack),
 yeccgoto_pexpr(hd(Ss), Cat, Ss, NewStack, T, Ts, Tzr).

%% yeccpars2_86: see yeccpars2_75

yeccpars2_87(S, ']', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 88, Ss, Stack, T, Ts, Tzr);
yeccpars2_87(_, _, _, _, T, _, _) ->
 yeccerror(T).

yeccpars2_88(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 [_,_,_,_,_|Nss] = Ss,
 NewStack = yeccpars2_88_(Stack),
 yeccgoto_lexpr(hd(Nss), Cat, Nss, NewStack, T, Ts, Tzr).

yeccpars2_89(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 [_,_|Nss] = Ss,
 NewStack = yeccpars2_89_(Stack),
 yeccgoto_lexpr(hd(Nss), Cat, Nss, NewStack, T, Ts, Tzr).

yeccpars2_90(S, '&', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 69, Ss, Stack, T, Ts, Tzr);
yeccpars2_90(S, '&&', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 70, Ss, Stack, T, Ts, Tzr);
yeccpars2_90(S, '->', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 72, Ss, Stack, T, Ts, Tzr);
yeccpars2_90(S, 'and', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 77, Ss, Stack, T, Ts, Tzr);
yeccpars2_90(S, imp, Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 79, Ss, Stack, T, Ts, Tzr);
yeccpars2_90(S, 'or', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 80, Ss, Stack, T, Ts, Tzr);
yeccpars2_90(S, '|', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 82, Ss, Stack, T, Ts, Tzr);
yeccpars2_90(S, '||', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 83, Ss, Stack, T, Ts, Tzr);
yeccpars2_90(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 [_,_|Nss] = Ss,
 NewStack = yeccpars2_90_(Stack),
 yeccgoto_lexpr(hd(Nss), Cat, Nss, NewStack, T, Ts, Tzr).

yeccpars2_91(S, '&', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 69, Ss, Stack, T, Ts, Tzr);
yeccpars2_91(S, '&&', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 70, Ss, Stack, T, Ts, Tzr);
yeccpars2_91(S, 'and', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 77, Ss, Stack, T, Ts, Tzr);
yeccpars2_91(S, 'or', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 80, Ss, Stack, T, Ts, Tzr);
yeccpars2_91(S, '|', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 82, Ss, Stack, T, Ts, Tzr);
yeccpars2_91(S, '||', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 83, Ss, Stack, T, Ts, Tzr);
yeccpars2_91(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 [_,_|Nss] = Ss,
 NewStack = yeccpars2_91_(Stack),
 yeccgoto_lexpr(hd(Nss), Cat, Nss, NewStack, T, Ts, Tzr).

yeccpars2_92(S, '&', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 69, Ss, Stack, T, Ts, Tzr);
yeccpars2_92(S, '&&', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 70, Ss, Stack, T, Ts, Tzr);
yeccpars2_92(S, 'and', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 77, Ss, Stack, T, Ts, Tzr);
yeccpars2_92(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 [_,_|Nss] = Ss,
 NewStack = yeccpars2_92_(Stack),
 yeccgoto_lexpr(hd(Nss), Cat, Nss, NewStack, T, Ts, Tzr).

yeccpars2_93(S, ')', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 97, Ss, Stack, T, Ts, Tzr);
yeccpars2_93(S, '=', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 98, Ss, Stack, T, Ts, Tzr);
yeccpars2_93(_, _, _, _, T, _, _) ->
 yeccerror(T).

yeccpars2_94(S, ',', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 95, Ss, Stack, T, Ts, Tzr);
yeccpars2_94(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 NewStack = yeccpars2_94_(Stack),
 yeccgoto_vars(hd(Ss), Cat, Ss, NewStack, T, Ts, Tzr).

%% yeccpars2_95: see yeccpars2_61

yeccpars2_96(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 [_,_|Nss] = Ss,
 NewStack = yeccpars2_96_(Stack),
 yeccgoto_vars(hd(Nss), Cat, Nss, NewStack, T, Ts, Tzr).

yeccpars2_97(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 [_,_,_|Nss] = Ss,
 NewStack = yeccpars2_97_(Stack),
 yeccgoto_quantifier(hd(Nss), Cat, Nss, NewStack, T, Ts, Tzr).

yeccpars2_98(S, variable, Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 102, Ss, Stack, T, Ts, Tzr);
yeccpars2_98(S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_cont_0(S, Cat, Ss, Stack, T, Ts, Tzr).

yeccpars2_99(S, '..', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 112, Ss, Stack, T, Ts, Tzr);
yeccpars2_99(_, _, _, _, T, _, _) ->
 yeccerror(T).

yeccpars2_100(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 NewStack = yeccpars2_100_(Stack),
 yeccgoto_rexpr(hd(Ss), Cat, Ss, NewStack, T, Ts, Tzr).

yeccpars2_101(S, ')', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 103, Ss, Stack, T, Ts, Tzr);
yeccpars2_101(S, '*', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 104, Ss, Stack, T, Ts, Tzr);
yeccpars2_101(S, '+', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 105, Ss, Stack, T, Ts, Tzr);
yeccpars2_101(S, '-', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 106, Ss, Stack, T, Ts, Tzr);
yeccpars2_101(S, '/', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 107, Ss, Stack, T, Ts, Tzr);
yeccpars2_101(_, _, _, _, T, _, _) ->
 yeccerror(T).

yeccpars2_102(_S, ')', Ss, Stack, T, Ts, Tzr) ->
 NewStack = 'yeccpars2_102_)'(Stack),
 yeccgoto_dexpr(hd(Ss), ')', Ss, NewStack, T, Ts, Tzr);
yeccpars2_102(_S, '*', Ss, Stack, T, Ts, Tzr) ->
 NewStack = 'yeccpars2_102_*'(Stack),
 yeccgoto_dexpr(hd(Ss), '*', Ss, NewStack, T, Ts, Tzr);
yeccpars2_102(_S, '+', Ss, Stack, T, Ts, Tzr) ->
 NewStack = 'yeccpars2_102_+'(Stack),
 yeccgoto_dexpr(hd(Ss), '+', Ss, NewStack, T, Ts, Tzr);
yeccpars2_102(_S, '-', Ss, Stack, T, Ts, Tzr) ->
 NewStack = 'yeccpars2_102_-'(Stack),
 yeccgoto_dexpr(hd(Ss), '-', Ss, NewStack, T, Ts, Tzr);
yeccpars2_102(_S, '/', Ss, Stack, T, Ts, Tzr) ->
 NewStack = 'yeccpars2_102_/'(Stack),
 yeccgoto_dexpr(hd(Ss), '/', Ss, NewStack, T, Ts, Tzr);
yeccpars2_102(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 NewStack = yeccpars2_102_(Stack),
 yeccgoto_rexpr(hd(Ss), Cat, Ss, NewStack, T, Ts, Tzr).

yeccpars2_103(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 [_,_,_,_,_|Nss] = Ss,
 NewStack = yeccpars2_103_(Stack),
 yeccgoto_quantifier(hd(Nss), Cat, Nss, NewStack, T, Ts, Tzr).

%% yeccpars2_104: see yeccpars2_98

%% yeccpars2_105: see yeccpars2_98

%% yeccpars2_106: see yeccpars2_98

%% yeccpars2_107: see yeccpars2_98

yeccpars2_108(S, '*', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 104, Ss, Stack, T, Ts, Tzr);
yeccpars2_108(S, '+', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 105, Ss, Stack, T, Ts, Tzr);
yeccpars2_108(S, '-', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 106, Ss, Stack, T, Ts, Tzr);
yeccpars2_108(S, '/', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 107, Ss, Stack, T, Ts, Tzr);
yeccpars2_108(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 [_,_|Nss] = Ss,
 NewStack = yeccpars2_108_(Stack),
 yeccgoto_dexpr(hd(Nss), Cat, Nss, NewStack, T, Ts, Tzr).

yeccpars2_109(S, '*', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 104, Ss, Stack, T, Ts, Tzr);
yeccpars2_109(S, '+', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 105, Ss, Stack, T, Ts, Tzr);
yeccpars2_109(S, '-', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 106, Ss, Stack, T, Ts, Tzr);
yeccpars2_109(S, '/', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 107, Ss, Stack, T, Ts, Tzr);
yeccpars2_109(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 [_,_|Nss] = Ss,
 NewStack = yeccpars2_109_(Stack),
 yeccgoto_dexpr(hd(Nss), Cat, Nss, NewStack, T, Ts, Tzr).

yeccpars2_110(S, '*', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 104, Ss, Stack, T, Ts, Tzr);
yeccpars2_110(S, '+', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 105, Ss, Stack, T, Ts, Tzr);
yeccpars2_110(S, '-', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 106, Ss, Stack, T, Ts, Tzr);
yeccpars2_110(S, '/', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 107, Ss, Stack, T, Ts, Tzr);
yeccpars2_110(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 [_,_|Nss] = Ss,
 NewStack = yeccpars2_110_(Stack),
 yeccgoto_dexpr(hd(Nss), Cat, Nss, NewStack, T, Ts, Tzr).

yeccpars2_111(S, '*', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 104, Ss, Stack, T, Ts, Tzr);
yeccpars2_111(S, '+', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 105, Ss, Stack, T, Ts, Tzr);
yeccpars2_111(S, '-', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 106, Ss, Stack, T, Ts, Tzr);
yeccpars2_111(S, '/', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 107, Ss, Stack, T, Ts, Tzr);
yeccpars2_111(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 [_,_|Nss] = Ss,
 NewStack = yeccpars2_111_(Stack),
 yeccgoto_dexpr(hd(Nss), Cat, Nss, NewStack, T, Ts, Tzr).

yeccpars2_112(S, variable, Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 114, Ss, Stack, T, Ts, Tzr);
yeccpars2_112(S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_cont_0(S, Cat, Ss, Stack, T, Ts, Tzr).

yeccpars2_113(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 [_,_|Nss] = Ss,
 NewStack = yeccpars2_113_(Stack),
 yeccgoto_dexpr(hd(Nss), Cat, Nss, NewStack, T, Ts, Tzr).

yeccpars2_114(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 NewStack = yeccpars2_114_(Stack),
 yeccgoto_rexpr(hd(Ss), Cat, Ss, NewStack, T, Ts, Tzr).

%% yeccpars2_115: see yeccpars2_2

%% yeccpars2_116: see yeccpars2_2

%% yeccpars2_117: see yeccpars2_2

yeccpars2_118(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccgoto_rel_op(hd(Ss), Cat, Ss, Stack, T, Ts, Tzr).

yeccpars2_119(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccgoto_rel_op(hd(Ss), Cat, Ss, Stack, T, Ts, Tzr).

yeccpars2_120(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccgoto_rel_op(hd(Ss), Cat, Ss, Stack, T, Ts, Tzr).

yeccpars2_121(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccgoto_rel_op(hd(Ss), Cat, Ss, Stack, T, Ts, Tzr).

yeccpars2_122(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccgoto_rel_op(hd(Ss), Cat, Ss, Stack, T, Ts, Tzr).

yeccpars2_123(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccgoto_rel_op(hd(Ss), Cat, Ss, Stack, T, Ts, Tzr).

yeccpars2_124(S, '%', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 40, Ss, Stack, T, Ts, Tzr);
yeccpars2_124(S, '*', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 41, Ss, Stack, T, Ts, Tzr);
yeccpars2_124(S, '/', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 44, Ss, Stack, T, Ts, Tzr);
yeccpars2_124(S, '<<', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 45, Ss, Stack, T, Ts, Tzr);
yeccpars2_124(S, '<<<', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 46, Ss, Stack, T, Ts, Tzr);
yeccpars2_124(S, '>>', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 47, Ss, Stack, T, Ts, Tzr);
yeccpars2_124(S, '>>>', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 48, Ss, Stack, T, Ts, Tzr);
yeccpars2_124(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 [_,_|Nss] = Ss,
 NewStack = yeccpars2_124_(Stack),
 yeccgoto_aexpr(hd(Nss), Cat, Nss, NewStack, T, Ts, Tzr).

yeccpars2_125(S, ':', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 21, Ss, Stack, T, Ts, Tzr);
yeccpars2_125(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 NewStack = yeccpars2_125_(Stack),
 yeccgoto_aexpr(hd(Ss), Cat, Ss, NewStack, T, Ts, Tzr).

yeccpars2_126(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 [_,_|Nss] = Ss,
 NewStack = yeccpars2_126_(Stack),
 yeccgoto_aexpr(hd(Nss), Cat, Nss, NewStack, T, Ts, Tzr).

yeccpars2_127(S, '%', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 40, Ss, Stack, T, Ts, Tzr);
yeccpars2_127(S, '*', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 41, Ss, Stack, T, Ts, Tzr);
yeccpars2_127(S, '+', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 42, Ss, Stack, T, Ts, Tzr);
yeccpars2_127(S, '-', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 43, Ss, Stack, T, Ts, Tzr);
yeccpars2_127(S, '/', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 44, Ss, Stack, T, Ts, Tzr);
yeccpars2_127(S, '<<', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 45, Ss, Stack, T, Ts, Tzr);
yeccpars2_127(S, '<<<', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 46, Ss, Stack, T, Ts, Tzr);
yeccpars2_127(S, '>>', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 47, Ss, Stack, T, Ts, Tzr);
yeccpars2_127(S, '>>>', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 48, Ss, Stack, T, Ts, Tzr);
yeccpars2_127(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 [_,_|Nss] = Ss,
 NewStack = yeccpars2_127_(Stack),
 yeccgoto_lexpr(hd(Nss), Cat, Nss, NewStack, T, Ts, Tzr).

%% yeccpars2_128: see yeccpars2_21

yeccpars2_129(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 [_,_|Nss] = Ss,
 NewStack = yeccpars2_129_(Stack),
 yeccgoto_aexpr(hd(Nss), Cat, Nss, NewStack, T, Ts, Tzr).

yeccpars2_130(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 [_|Nss] = Ss,
 NewStack = yeccpars2_130_(Stack),
 yeccgoto_lexpr(hd(Nss), Cat, Nss, NewStack, T, Ts, Tzr).

yeccpars2_131(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 [_|Nss] = Ss,
 NewStack = yeccpars2_131_(Stack),
 yeccgoto_aexpr(hd(Nss), Cat, Nss, NewStack, T, Ts, Tzr).

yeccpars2_132(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 [_|Nss] = Ss,
 NewStack = yeccpars2_132_(Stack),
 yeccgoto_lexpr(hd(Nss), Cat, Nss, NewStack, T, Ts, Tzr).

%% yeccpars2_133: see yeccpars2_10

yeccpars2_134(S, ')', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 139, Ss, Stack, T, Ts, Tzr);
yeccpars2_134(_, _, _, _, T, _, _) ->
 yeccerror(T).

yeccpars2_135(S, ',', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 136, Ss, Stack, T, Ts, Tzr);
yeccpars2_135(S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_62(S, Cat, Ss, Stack, T, Ts, Tzr).

%% yeccpars2_136: see yeccpars2_0

yeccpars2_137(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 [_,_|Nss] = Ss,
 NewStack = yeccpars2_137_(Stack),
 yeccgoto_lexprs(hd(Nss), Cat, Nss, NewStack, T, Ts, Tzr).

yeccpars2_138(S, '&', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 69, Ss, Stack, T, Ts, Tzr);
yeccpars2_138(S, '&&', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 70, Ss, Stack, T, Ts, Tzr);
yeccpars2_138(S, ',', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 136, Ss, Stack, T, Ts, Tzr);
yeccpars2_138(S, '->', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 72, Ss, Stack, T, Ts, Tzr);
yeccpars2_138(S, '<->', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 73, Ss, Stack, T, Ts, Tzr);
yeccpars2_138(S, '=', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 74, Ss, Stack, T, Ts, Tzr);
yeccpars2_138(S, '[', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 75, Ss, Stack, T, Ts, Tzr);
yeccpars2_138(S, '^', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 76, Ss, Stack, T, Ts, Tzr);
yeccpars2_138(S, 'and', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 77, Ss, Stack, T, Ts, Tzr);
yeccpars2_138(S, equ, Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 78, Ss, Stack, T, Ts, Tzr);
yeccpars2_138(S, imp, Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 79, Ss, Stack, T, Ts, Tzr);
yeccpars2_138(S, 'or', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 80, Ss, Stack, T, Ts, Tzr);
yeccpars2_138(S, 'xor', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 81, Ss, Stack, T, Ts, Tzr);
yeccpars2_138(S, '|', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 82, Ss, Stack, T, Ts, Tzr);
yeccpars2_138(S, '||', Ss, Stack, T, Ts, Tzr) ->
 yeccpars1(S, 83, Ss, Stack, T, Ts, Tzr);
yeccpars2_138(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 NewStack = yeccpars2_138_(Stack),
 yeccgoto_lexprs(hd(Ss), Cat, Ss, NewStack, T, Ts, Tzr).

yeccpars2_139(_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 [_,_,_|Nss] = Ss,
 NewStack = yeccpars2_139_(Stack),
 yeccgoto_lexpr(hd(Nss), Cat, Nss, NewStack, T, Ts, Tzr).

yeccgoto_add_op(8, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_2(117, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_add_op(31, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_28(38, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_add_op(36, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_28(38, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_add_op(50, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_28(38, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_add_op(51, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_28(38, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_add_op(55, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_28(38, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_add_op(60, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_28(38, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_add_op(124, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_2(117, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_add_op(126, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_2(117, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_add_op(127, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_2(117, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_add_op(131, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_2(117, Cat, Ss, Stack, T, Ts, Tzr).

yeccgoto_aexpr(0, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_8(8, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_aexpr(1, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_8(8, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_aexpr(2=_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_131(_S, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_aexpr(4, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_8(8, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_aexpr(10, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_8(8, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_aexpr(65, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_8(8, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_aexpr(66, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_8(8, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_aexpr(67, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_8(8, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_aexpr(68, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_8(8, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_aexpr(115, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_127(127, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_aexpr(116=_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_126(_S, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_aexpr(117, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_124(124, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_aexpr(133, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_8(8, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_aexpr(136, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_8(8, Cat, Ss, Stack, T, Ts, Tzr).

yeccgoto_and_op(5, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_0(68, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_and_op(62, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_0(68, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_and_op(89, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_0(68, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_and_op(90, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_0(68, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_and_op(91, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_0(68, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_and_op(92, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_0(68, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_and_op(130, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_0(68, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_and_op(132, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_0(68, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_and_op(135, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_0(68, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_and_op(138, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_0(68, Cat, Ss, Stack, T, Ts, Tzr).

yeccgoto_dexpr(98, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_101(101, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_dexpr(104, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_111(111, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_dexpr(105, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_110(110, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_dexpr(106, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_109(109, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_dexpr(107, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_108(108, Cat, Ss, Stack, T, Ts, Tzr).

yeccgoto_equ_op(5, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_0(67, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_equ_op(62, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_0(67, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_equ_op(89, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_0(67, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_equ_op(90, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_0(67, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_equ_op(91, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_0(67, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_equ_op(92, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_0(67, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_equ_op(130, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_0(67, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_equ_op(132, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_0(67, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_equ_op(135, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_0(67, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_equ_op(138, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_0(67, Cat, Ss, Stack, T, Ts, Tzr).

yeccgoto_expr(20, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_31(31, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_expr(28=_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_60(_S, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_expr(32, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_55(55, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_expr(35, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_36(36, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_expr(37=_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_51(_S, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_expr(38, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_50(50, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_expr(52, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_31(31, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_expr(57, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_31(31, Cat, Ss, Stack, T, Ts, Tzr).

yeccgoto_exprs(20, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_30(30, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_exprs(52, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_53(53, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_exprs(57=_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_58(_S, Cat, Ss, Stack, T, Ts, Tzr).

yeccgoto_formula(0, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_7(7, Cat, Ss, Stack, T, Ts, Tzr).

yeccgoto_imp_op(5, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_0(66, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_imp_op(62, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_0(66, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_imp_op(89, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_0(66, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_imp_op(90, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_0(66, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_imp_op(91, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_0(66, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_imp_op(92, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_0(66, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_imp_op(130, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_0(66, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_imp_op(132, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_0(66, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_imp_op(135, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_0(66, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_imp_op(138, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_0(66, Cat, Ss, Stack, T, Ts, Tzr).

yeccgoto_integer(0, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_6(6, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_integer(1, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_6(6, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_integer(2, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_6(6, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_integer(4, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_6(6, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_integer(10, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_6(6, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_integer(20=_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_29(_S, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_integer(21=_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_23(_S, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_integer(24=_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_26(_S, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_integer(28=_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_29(_S, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_integer(32=_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_29(_S, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_integer(35=_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_29(_S, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_integer(37=_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_29(_S, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_integer(38=_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_29(_S, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_integer(52=_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_29(_S, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_integer(57=_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_29(_S, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_integer(65, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_6(6, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_integer(66, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_6(6, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_integer(67, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_6(6, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_integer(68, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_6(6, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_integer(98=_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_100(_S, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_integer(104=_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_100(_S, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_integer(105=_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_100(_S, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_integer(106=_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_100(_S, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_integer(107=_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_100(_S, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_integer(112=_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_100(_S, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_integer(115, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_6(6, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_integer(116, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_6(6, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_integer(117, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_6(6, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_integer(128=_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_23(_S, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_integer(133, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_6(6, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_integer(136, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_6(6, Cat, Ss, Stack, T, Ts, Tzr).

yeccgoto_lexpr(0, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_5(5, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_lexpr(1=_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_132(_S, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_lexpr(4=_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_130(_S, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_lexpr(10, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_62(62, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_lexpr(65, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_92(92, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_lexpr(66, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_91(91, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_lexpr(67, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_90(90, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_lexpr(68=_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_89(_S, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_lexpr(133, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_135(135, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_lexpr(136, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_138(138, Cat, Ss, Stack, T, Ts, Tzr).

yeccgoto_lexprs(133, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_134(134, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_lexprs(136=_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_137(_S, Cat, Ss, Stack, T, Ts, Tzr).

yeccgoto_mul_op(8, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_2(116, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_mul_op(31, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_28(37, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_mul_op(36, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_28(37, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_mul_op(50, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_28(37, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_mul_op(51, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_28(37, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_mul_op(55, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_28(37, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_mul_op(60, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_28(37, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_mul_op(124, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_2(116, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_mul_op(126, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_2(116, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_mul_op(127, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_2(116, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_mul_op(131, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_2(116, Cat, Ss, Stack, T, Ts, Tzr).

yeccgoto_nexpr(21=_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_22(_S, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_nexpr(128=_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_129(_S, Cat, Ss, Stack, T, Ts, Tzr).

yeccgoto_not_op(0, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_0(4, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_not_op(1, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_0(4, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_not_op(4, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_0(4, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_not_op(10, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_0(4, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_not_op(65, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_0(4, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_not_op(66, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_0(4, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_not_op(67, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_0(4, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_not_op(68, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_0(4, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_not_op(133, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_0(4, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_not_op(136, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_0(4, Cat, Ss, Stack, T, Ts, Tzr).

yeccgoto_or_op(5, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_0(65, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_or_op(62, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_0(65, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_or_op(89, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_0(65, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_or_op(90, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_0(65, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_or_op(91, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_0(65, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_or_op(92, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_0(65, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_or_op(130, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_0(65, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_or_op(132, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_0(65, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_or_op(135, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_0(65, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_or_op(138, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_0(65, Cat, Ss, Stack, T, Ts, Tzr).

yeccgoto_pexpr(0=_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_3(_S, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_pexpr(1=_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_3(_S, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_pexpr(4=_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_3(_S, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_pexpr(10=_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_3(_S, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_pexpr(65=_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_3(_S, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_pexpr(66=_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_3(_S, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_pexpr(67=_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_3(_S, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_pexpr(68=_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_3(_S, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_pexpr(75, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_84(84, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_pexpr(86, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_87(87, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_pexpr(133=_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_3(_S, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_pexpr(136=_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_3(_S, Cat, Ss, Stack, T, Ts, Tzr).

yeccgoto_prefix_op(0, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_2(2, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_prefix_op(1, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_2(2, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_prefix_op(2, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_2(2, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_prefix_op(4, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_2(2, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_prefix_op(10, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_2(2, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_prefix_op(20, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_28(28, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_prefix_op(28, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_28(28, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_prefix_op(32, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_28(28, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_prefix_op(35, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_28(28, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_prefix_op(37, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_28(28, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_prefix_op(38, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_28(28, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_prefix_op(52, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_28(28, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_prefix_op(57, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_28(28, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_prefix_op(65, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_2(2, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_prefix_op(66, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_2(2, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_prefix_op(67, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_2(2, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_prefix_op(68, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_2(2, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_prefix_op(115, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_2(2, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_prefix_op(116, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_2(2, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_prefix_op(117, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_2(2, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_prefix_op(133, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_2(2, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_prefix_op(136, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_2(2, Cat, Ss, Stack, T, Ts, Tzr).

yeccgoto_qtype(10, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_61(61, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_qtype(133, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_61(61, Cat, Ss, Stack, T, Ts, Tzr).

yeccgoto_quantifier(0, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_1(1, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_quantifier(1, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_1(1, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_quantifier(4, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_1(1, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_quantifier(10, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_1(1, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_quantifier(65, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_1(1, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_quantifier(66, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_1(1, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_quantifier(67, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_1(1, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_quantifier(68, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_1(1, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_quantifier(133, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_1(1, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_quantifier(136, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_1(1, Cat, Ss, Stack, T, Ts, Tzr).

yeccgoto_rel_op(8, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_2(115, Cat, Ss, Stack, T, Ts, Tzr).

yeccgoto_rexpr(98, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_99(99, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_rexpr(104, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_99(99, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_rexpr(105, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_99(99, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_rexpr(106, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_99(99, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_rexpr(107, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_99(99, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_rexpr(112=_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_113(_S, Cat, Ss, Stack, T, Ts, Tzr).

yeccgoto_vars(61, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_93(93, Cat, Ss, Stack, T, Ts, Tzr);
yeccgoto_vars(95=_S, Cat, Ss, Stack, T, Ts, Tzr) ->
 yeccpars2_96(_S, Cat, Ss, Stack, T, Ts, Tzr).

-compile({inline,yeccpars2_6_/1}).
-file("varp_parse.yrl", 92).
yeccpars2_6_(__Stack0) ->
 [__1 | __Stack] = __Stack0,
 [begin
   value ( __1 )
  end | __Stack].

-compile({inline,'yeccpars2_18_!='/1}).
-file("varp_parse.yrl", 91).
'yeccpars2_18_!='(__Stack0) ->
 [__1 | __Stack] = __Stack0,
 [begin
   { var , name ( __1 ) }
  end | __Stack].

-compile({inline,'yeccpars2_18_%'/1}).
-file("varp_parse.yrl", 91).
'yeccpars2_18_%'(__Stack0) ->
 [__1 | __Stack] = __Stack0,
 [begin
   { var , name ( __1 ) }
  end | __Stack].

-compile({inline,'yeccpars2_18_*'/1}).
-file("varp_parse.yrl", 91).
'yeccpars2_18_*'(__Stack0) ->
 [__1 | __Stack] = __Stack0,
 [begin
   { var , name ( __1 ) }
  end | __Stack].

-compile({inline,'yeccpars2_18_+'/1}).
-file("varp_parse.yrl", 91).
'yeccpars2_18_+'(__Stack0) ->
 [__1 | __Stack] = __Stack0,
 [begin
   { var , name ( __1 ) }
  end | __Stack].

-compile({inline,'yeccpars2_18_-'/1}).
-file("varp_parse.yrl", 91).
'yeccpars2_18_-'(__Stack0) ->
 [__1 | __Stack] = __Stack0,
 [begin
   { var , name ( __1 ) }
  end | __Stack].

-compile({inline,'yeccpars2_18_/'/1}).
-file("varp_parse.yrl", 91).
'yeccpars2_18_/'(__Stack0) ->
 [__1 | __Stack] = __Stack0,
 [begin
   { var , name ( __1 ) }
  end | __Stack].

-compile({inline,'yeccpars2_18_<'/1}).
-file("varp_parse.yrl", 91).
'yeccpars2_18_<'(__Stack0) ->
 [__1 | __Stack] = __Stack0,
 [begin
   { var , name ( __1 ) }
  end | __Stack].

-compile({inline,'yeccpars2_18_<<'/1}).
-file("varp_parse.yrl", 91).
'yeccpars2_18_<<'(__Stack0) ->
 [__1 | __Stack] = __Stack0,
 [begin
   { var , name ( __1 ) }
  end | __Stack].

-compile({inline,'yeccpars2_18_<<<'/1}).
-file("varp_parse.yrl", 91).
'yeccpars2_18_<<<'(__Stack0) ->
 [__1 | __Stack] = __Stack0,
 [begin
   { var , name ( __1 ) }
  end | __Stack].

-compile({inline,'yeccpars2_18_<='/1}).
-file("varp_parse.yrl", 91).
'yeccpars2_18_<='(__Stack0) ->
 [__1 | __Stack] = __Stack0,
 [begin
   { var , name ( __1 ) }
  end | __Stack].

-compile({inline,'yeccpars2_18_=='/1}).
-file("varp_parse.yrl", 91).
'yeccpars2_18_=='(__Stack0) ->
 [__1 | __Stack] = __Stack0,
 [begin
   { var , name ( __1 ) }
  end | __Stack].

-compile({inline,'yeccpars2_18_>'/1}).
-file("varp_parse.yrl", 91).
'yeccpars2_18_>'(__Stack0) ->
 [__1 | __Stack] = __Stack0,
 [begin
   { var , name ( __1 ) }
  end | __Stack].

-compile({inline,'yeccpars2_18_>='/1}).
-file("varp_parse.yrl", 91).
'yeccpars2_18_>='(__Stack0) ->
 [__1 | __Stack] = __Stack0,
 [begin
   { var , name ( __1 ) }
  end | __Stack].

-compile({inline,'yeccpars2_18_>>'/1}).
-file("varp_parse.yrl", 91).
'yeccpars2_18_>>'(__Stack0) ->
 [__1 | __Stack] = __Stack0,
 [begin
   { var , name ( __1 ) }
  end | __Stack].

-compile({inline,'yeccpars2_18_>>>'/1}).
-file("varp_parse.yrl", 91).
'yeccpars2_18_>>>'(__Stack0) ->
 [__1 | __Stack] = __Stack0,
 [begin
   { var , name ( __1 ) }
  end | __Stack].

-compile({inline,yeccpars2_18_/1}).
-file("varp_parse.yrl", 155).
yeccpars2_18_(__Stack0) ->
 [__1 | __Stack] = __Stack0,
 [begin
   { var , name ( __1 ) }
  end | __Stack].

-compile({inline,yeccpars2_22_/1}).
-file("varp_parse.yrl", 90).
yeccpars2_22_(__Stack0) ->
 [__3,__2,__1 | __Stack] = __Stack0,
 [begin
   { S , N } = __3 , { S , N , name ( __1 ) }
  end | __Stack].

-compile({inline,yeccpars2_23_/1}).
-file("varp_parse.yrl", 97).
yeccpars2_23_(__Stack0) ->
 [__1 | __Stack] = __Stack0,
 [begin
   { uint , value ( __1 ) }
  end | __Stack].

-compile({inline,yeccpars2_25_/1}).
-file("varp_parse.yrl", 99).
yeccpars2_25_(__Stack0) ->
 [__1 | __Stack] = __Stack0,
 [begin
   { uint , name ( __1 ) }
  end | __Stack].

-compile({inline,yeccpars2_26_/1}).
-file("varp_parse.yrl", 98).
yeccpars2_26_(__Stack0) ->
 [__2,__1 | __Stack] = __Stack0,
 [begin
   { int , value ( __2 ) }
  end | __Stack].

-compile({inline,yeccpars2_27_/1}).
-file("varp_parse.yrl", 100).
yeccpars2_27_(__Stack0) ->
 [__2,__1 | __Stack] = __Stack0,
 [begin
   { int , name ( __2 ) }
  end | __Stack].

-compile({inline,yeccpars2_29_/1}).
-file("varp_parse.yrl", 106).
yeccpars2_29_(__Stack0) ->
 [__1 | __Stack] = __Stack0,
 [begin
   value ( __1 )
  end | __Stack].

-compile({inline,yeccpars2_31_/1}).
-file("varp_parse.yrl", 120).
yeccpars2_31_(__Stack0) ->
 [__1 | __Stack] = __Stack0,
 [begin
   [ __1 ]
  end | __Stack].

-compile({inline,yeccpars2_33_/1}).
-file("varp_parse.yrl", 156).
yeccpars2_33_(__Stack0) ->
 [__3,__2,__1 | __Stack] = __Stack0,
 [begin
   { var , name ( __1 ) }
  end | __Stack].

-compile({inline,yeccpars2_34_/1}).
-file("varp_parse.yrl", 105).
yeccpars2_34_(__Stack0) ->
 [__1 | __Stack] = __Stack0,
 [begin
   name ( __1 )
  end | __Stack].

-compile({inline,yeccpars2_39_/1}).
-file("varp_parse.yrl", 112).
yeccpars2_39_(__Stack0) ->
 [__2,__1 | __Stack] = __Stack0,
 [begin
   { call , factorial , [ __1 ] }
  end | __Stack].

-compile({inline,yeccpars2_49_/1}).
-file("varp_parse.yrl", 113).
yeccpars2_49_(__Stack0) ->
 [__3,__2,__1 | __Stack] = __Stack0,
 [begin
   { call , abs , [ __2 ] }
  end | __Stack].

-compile({inline,yeccpars2_50_/1}).
-file("varp_parse.yrl", 116).
yeccpars2_50_(__Stack0) ->
 [__3,__2,__1 | __Stack] = __Stack0,
 [begin
   { op ( __2 ) , __1 , __3 }
  end | __Stack].

-compile({inline,yeccpars2_51_/1}).
-file("varp_parse.yrl", 117).
yeccpars2_51_(__Stack0) ->
 [__3,__2,__1 | __Stack] = __Stack0,
 [begin
   { op ( __2 ) , __1 , __3 }
  end | __Stack].

-compile({inline,yeccpars2_54_/1}).
-file("varp_parse.yrl", 115).
yeccpars2_54_(__Stack0) ->
 [__4,__3,__2,__1 | __Stack] = __Stack0,
 [begin
   { call , name ( __1 ) , __3 }
  end | __Stack].

-compile({inline,yeccpars2_56_/1}).
-file("varp_parse.yrl", 114).
yeccpars2_56_(__Stack0) ->
 [__3,__2,__1 | __Stack] = __Stack0,
 [begin
   __2
  end | __Stack].

-compile({inline,yeccpars2_58_/1}).
-file("varp_parse.yrl", 121).
yeccpars2_58_(__Stack0) ->
 [__3,__2,__1 | __Stack] = __Stack0,
 [begin
   [ __1 | __3 ]
  end | __Stack].

-compile({inline,yeccpars2_59_/1}).
-file("varp_parse.yrl", 157).
yeccpars2_59_(__Stack0) ->
 [__4,__3,__2,__1 | __Stack] = __Stack0,
 [begin
   { var , list_to_tuple ( [ name ( __1 ) | __3 ] ) }
  end | __Stack].

-compile({inline,yeccpars2_60_/1}).
-file("varp_parse.yrl", 108).
yeccpars2_60_(__Stack0) ->
 [__2,__1 | __Stack] = __Stack0,
 [begin
   case op ( __1 ) of
    '-' when is_integer ( __2 ) -> - ( __2 ) ;
    Op -> { Op , __2 }
    end
  end | __Stack].

-compile({inline,'yeccpars2_63_!='/1}).
-file("varp_parse.yrl", 91).
'yeccpars2_63_!='(__Stack0) ->
 [__1 | __Stack] = __Stack0,
 [begin
   { var , name ( __1 ) }
  end | __Stack].

-compile({inline,'yeccpars2_63_%'/1}).
-file("varp_parse.yrl", 91).
'yeccpars2_63_%'(__Stack0) ->
 [__1 | __Stack] = __Stack0,
 [begin
   { var , name ( __1 ) }
  end | __Stack].

-compile({inline,'yeccpars2_63_*'/1}).
-file("varp_parse.yrl", 91).
'yeccpars2_63_*'(__Stack0) ->
 [__1 | __Stack] = __Stack0,
 [begin
   { var , name ( __1 ) }
  end | __Stack].

-compile({inline,'yeccpars2_63_+'/1}).
-file("varp_parse.yrl", 91).
'yeccpars2_63_+'(__Stack0) ->
 [__1 | __Stack] = __Stack0,
 [begin
   { var , name ( __1 ) }
  end | __Stack].

-compile({inline,'yeccpars2_63_-'/1}).
-file("varp_parse.yrl", 91).
'yeccpars2_63_-'(__Stack0) ->
 [__1 | __Stack] = __Stack0,
 [begin
   { var , name ( __1 ) }
  end | __Stack].

-compile({inline,'yeccpars2_63_/'/1}).
-file("varp_parse.yrl", 91).
'yeccpars2_63_/'(__Stack0) ->
 [__1 | __Stack] = __Stack0,
 [begin
   { var , name ( __1 ) }
  end | __Stack].

-compile({inline,'yeccpars2_63_<'/1}).
-file("varp_parse.yrl", 91).
'yeccpars2_63_<'(__Stack0) ->
 [__1 | __Stack] = __Stack0,
 [begin
   { var , name ( __1 ) }
  end | __Stack].

-compile({inline,'yeccpars2_63_<<'/1}).
-file("varp_parse.yrl", 91).
'yeccpars2_63_<<'(__Stack0) ->
 [__1 | __Stack] = __Stack0,
 [begin
   { var , name ( __1 ) }
  end | __Stack].

-compile({inline,'yeccpars2_63_<<<'/1}).
-file("varp_parse.yrl", 91).
'yeccpars2_63_<<<'(__Stack0) ->
 [__1 | __Stack] = __Stack0,
 [begin
   { var , name ( __1 ) }
  end | __Stack].

-compile({inline,'yeccpars2_63_<='/1}).
-file("varp_parse.yrl", 91).
'yeccpars2_63_<='(__Stack0) ->
 [__1 | __Stack] = __Stack0,
 [begin
   { var , name ( __1 ) }
  end | __Stack].

-compile({inline,'yeccpars2_63_=='/1}).
-file("varp_parse.yrl", 91).
'yeccpars2_63_=='(__Stack0) ->
 [__1 | __Stack] = __Stack0,
 [begin
   { var , name ( __1 ) }
  end | __Stack].

-compile({inline,'yeccpars2_63_>'/1}).
-file("varp_parse.yrl", 91).
'yeccpars2_63_>'(__Stack0) ->
 [__1 | __Stack] = __Stack0,
 [begin
   { var , name ( __1 ) }
  end | __Stack].

-compile({inline,'yeccpars2_63_>='/1}).
-file("varp_parse.yrl", 91).
'yeccpars2_63_>='(__Stack0) ->
 [__1 | __Stack] = __Stack0,
 [begin
   { var , name ( __1 ) }
  end | __Stack].

-compile({inline,'yeccpars2_63_>>'/1}).
-file("varp_parse.yrl", 91).
'yeccpars2_63_>>'(__Stack0) ->
 [__1 | __Stack] = __Stack0,
 [begin
   { var , name ( __1 ) }
  end | __Stack].

-compile({inline,'yeccpars2_63_>>>'/1}).
-file("varp_parse.yrl", 91).
'yeccpars2_63_>>>'(__Stack0) ->
 [__1 | __Stack] = __Stack0,
 [begin
   { var , name ( __1 ) }
  end | __Stack].

-compile({inline,'yeccpars2_63_&'/1}).
-file("varp_parse.yrl", 155).
'yeccpars2_63_&'(__Stack0) ->
 [__1 | __Stack] = __Stack0,
 [begin
   { var , name ( __1 ) }
  end | __Stack].

-compile({inline,'yeccpars2_63_&&'/1}).
-file("varp_parse.yrl", 155).
'yeccpars2_63_&&'(__Stack0) ->
 [__1 | __Stack] = __Stack0,
 [begin
   { var , name ( __1 ) }
  end | __Stack].

-compile({inline,'yeccpars2_63_)'/1}).
-file("varp_parse.yrl", 155).
'yeccpars2_63_)'(__Stack0) ->
 [__1 | __Stack] = __Stack0,
 [begin
   { var , name ( __1 ) }
  end | __Stack].

-compile({inline,'yeccpars2_63_,'/1}).
-file("varp_parse.yrl", 155).
'yeccpars2_63_,'(__Stack0) ->
 [__1 | __Stack] = __Stack0,
 [begin
   { var , name ( __1 ) }
  end | __Stack].

-compile({inline,'yeccpars2_63_->'/1}).
-file("varp_parse.yrl", 155).
'yeccpars2_63_->'(__Stack0) ->
 [__1 | __Stack] = __Stack0,
 [begin
   { var , name ( __1 ) }
  end | __Stack].

-compile({inline,'yeccpars2_63_<->'/1}).
-file("varp_parse.yrl", 155).
'yeccpars2_63_<->'(__Stack0) ->
 [__1 | __Stack] = __Stack0,
 [begin
   { var , name ( __1 ) }
  end | __Stack].

-compile({inline,'yeccpars2_63_='/1}).
-file("varp_parse.yrl", 155).
'yeccpars2_63_='(__Stack0) ->
 [__1 | __Stack] = __Stack0,
 [begin
   { var , name ( __1 ) }
  end | __Stack].

-compile({inline,'yeccpars2_63_['/1}).
-file("varp_parse.yrl", 155).
'yeccpars2_63_['(__Stack0) ->
 [__1 | __Stack] = __Stack0,
 [begin
   { var , name ( __1 ) }
  end | __Stack].

-compile({inline,'yeccpars2_63_^'/1}).
-file("varp_parse.yrl", 155).
'yeccpars2_63_^'(__Stack0) ->
 [__1 | __Stack] = __Stack0,
 [begin
   { var , name ( __1 ) }
  end | __Stack].

-compile({inline,yeccpars2_63_and/1}).
-file("varp_parse.yrl", 155).
yeccpars2_63_and(__Stack0) ->
 [__1 | __Stack] = __Stack0,
 [begin
   { var , name ( __1 ) }
  end | __Stack].

-compile({inline,yeccpars2_63_equ/1}).
-file("varp_parse.yrl", 155).
yeccpars2_63_equ(__Stack0) ->
 [__1 | __Stack] = __Stack0,
 [begin
   { var , name ( __1 ) }
  end | __Stack].

-compile({inline,yeccpars2_63_imp/1}).
-file("varp_parse.yrl", 155).
yeccpars2_63_imp(__Stack0) ->
 [__1 | __Stack] = __Stack0,
 [begin
   { var , name ( __1 ) }
  end | __Stack].

-compile({inline,yeccpars2_63_or/1}).
-file("varp_parse.yrl", 155).
yeccpars2_63_or(__Stack0) ->
 [__1 | __Stack] = __Stack0,
 [begin
   { var , name ( __1 ) }
  end | __Stack].

-compile({inline,yeccpars2_63_xor/1}).
-file("varp_parse.yrl", 155).
yeccpars2_63_xor(__Stack0) ->
 [__1 | __Stack] = __Stack0,
 [begin
   { var , name ( __1 ) }
  end | __Stack].

-compile({inline,'yeccpars2_63_|'/1}).
-file("varp_parse.yrl", 155).
'yeccpars2_63_|'(__Stack0) ->
 [__1 | __Stack] = __Stack0,
 [begin
   { var , name ( __1 ) }
  end | __Stack].

-compile({inline,'yeccpars2_63_||'/1}).
-file("varp_parse.yrl", 155).
'yeccpars2_63_||'(__Stack0) ->
 [__1 | __Stack] = __Stack0,
 [begin
   { var , name ( __1 ) }
  end | __Stack].

-compile({inline,yeccpars2_63_/1}).
-file("varp_parse.yrl", 131).
yeccpars2_63_(__Stack0) ->
 [__1 | __Stack] = __Stack0,
 [begin
   case __1 of
    { _ , _ , "E" } -> exists ;
    { _ , _ , "A" } -> forall
    end
  end | __Stack].

-compile({inline,yeccpars2_64_/1}).
-file("varp_parse.yrl", 127).
yeccpars2_64_(__Stack0) ->
 [__2,__1 | __Stack] = __Stack0,
 [begin
   case __1 of
    { _ , _ , "E" } -> one
    end
  end | __Stack].

-compile({inline,yeccpars2_71_/1}).
-file("varp_parse.yrl", 149).
yeccpars2_71_(__Stack0) ->
 [__3,__2,__1 | __Stack] = __Stack0,
 [begin
   __2
  end | __Stack].

-compile({inline,yeccpars2_85_/1}).
-file("varp_parse.yrl", 155).
yeccpars2_85_(__Stack0) ->
 [__1 | __Stack] = __Stack0,
 [begin
   { var , name ( __1 ) }
  end | __Stack].

-compile({inline,yeccpars2_88_/1}).
-file("varp_parse.yrl", 153).
yeccpars2_88_(__Stack0) ->
 [__6,__5,__4,__3,__2,__1 | __Stack] = __Stack0,
 [begin
   { subst , element ( 2 , __3 ) , element ( 2 , __5 ) , __1 }
  end | __Stack].

-compile({inline,yeccpars2_89_/1}).
-file("varp_parse.yrl", 144).
yeccpars2_89_(__Stack0) ->
 [__3,__2,__1 | __Stack] = __Stack0,
 [begin
   { op ( __2 ) , __1 , __3 }
  end | __Stack].

-compile({inline,yeccpars2_90_/1}).
-file("varp_parse.yrl", 147).
yeccpars2_90_(__Stack0) ->
 [__3,__2,__1 | __Stack] = __Stack0,
 [begin
   { op ( __2 ) , __1 , __3 }
  end | __Stack].

-compile({inline,yeccpars2_91_/1}).
-file("varp_parse.yrl", 146).
yeccpars2_91_(__Stack0) ->
 [__3,__2,__1 | __Stack] = __Stack0,
 [begin
   { op ( __2 ) , __1 , __3 }
  end | __Stack].

-compile({inline,yeccpars2_92_/1}).
-file("varp_parse.yrl", 145).
yeccpars2_92_(__Stack0) ->
 [__3,__2,__1 | __Stack] = __Stack0,
 [begin
   { op ( __2 ) , __1 , __3 }
  end | __Stack].

-compile({inline,yeccpars2_94_/1}).
-file("varp_parse.yrl", 139).
yeccpars2_94_(__Stack0) ->
 [__1 | __Stack] = __Stack0,
 [begin
   [ name ( __1 ) ]
  end | __Stack].

-compile({inline,yeccpars2_96_/1}).
-file("varp_parse.yrl", 140).
yeccpars2_96_(__Stack0) ->
 [__3,__2,__1 | __Stack] = __Stack0,
 [begin
   [ name ( __1 ) | __3 ]
  end | __Stack].

-compile({inline,yeccpars2_97_/1}).
-file("varp_parse.yrl", 136).
yeccpars2_97_(__Stack0) ->
 [__4,__3,__2,__1 | __Stack] = __Stack0,
 [begin
   { __2 , __3 , default }
  end | __Stack].

-compile({inline,yeccpars2_100_/1}).
-file("varp_parse.yrl", 83).
yeccpars2_100_(__Stack0) ->
 [__1 | __Stack] = __Stack0,
 [begin
   value ( __1 )
  end | __Stack].

-compile({inline,'yeccpars2_102_)'/1}).
-file("varp_parse.yrl", 76).
'yeccpars2_102_)'(__Stack0) ->
 [__1 | __Stack] = __Stack0,
 [begin
   name ( __1 )
  end | __Stack].

-compile({inline,'yeccpars2_102_*'/1}).
-file("varp_parse.yrl", 76).
'yeccpars2_102_*'(__Stack0) ->
 [__1 | __Stack] = __Stack0,
 [begin
   name ( __1 )
  end | __Stack].

-compile({inline,'yeccpars2_102_+'/1}).
-file("varp_parse.yrl", 76).
'yeccpars2_102_+'(__Stack0) ->
 [__1 | __Stack] = __Stack0,
 [begin
   name ( __1 )
  end | __Stack].

-compile({inline,'yeccpars2_102_-'/1}).
-file("varp_parse.yrl", 76).
'yeccpars2_102_-'(__Stack0) ->
 [__1 | __Stack] = __Stack0,
 [begin
   name ( __1 )
  end | __Stack].

-compile({inline,'yeccpars2_102_/'/1}).
-file("varp_parse.yrl", 76).
'yeccpars2_102_/'(__Stack0) ->
 [__1 | __Stack] = __Stack0,
 [begin
   name ( __1 )
  end | __Stack].

-compile({inline,yeccpars2_102_/1}).
-file("varp_parse.yrl", 84).
yeccpars2_102_(__Stack0) ->
 [__1 | __Stack] = __Stack0,
 [begin
   name ( __1 )
  end | __Stack].

-compile({inline,yeccpars2_103_/1}).
-file("varp_parse.yrl", 137).
yeccpars2_103_(__Stack0) ->
 [__6,__5,__4,__3,__2,__1 | __Stack] = __Stack0,
 [begin
   { __2 , __3 , __5 }
  end | __Stack].

-compile({inline,yeccpars2_108_/1}).
-file("varp_parse.yrl", 80).
yeccpars2_108_(__Stack0) ->
 [__3,__2,__1 | __Stack] = __Stack0,
 [begin
   { intersect , __1 , __3 }
  end | __Stack].

-compile({inline,yeccpars2_109_/1}).
-file("varp_parse.yrl", 79).
yeccpars2_109_(__Stack0) ->
 [__3,__2,__1 | __Stack] = __Stack0,
 [begin
   { subtract , __1 , __3 }
  end | __Stack].

-compile({inline,yeccpars2_110_/1}).
-file("varp_parse.yrl", 78).
yeccpars2_110_(__Stack0) ->
 [__3,__2,__1 | __Stack] = __Stack0,
 [begin
   { union , __1 , __3 }
  end | __Stack].

-compile({inline,yeccpars2_111_/1}).
-file("varp_parse.yrl", 81).
yeccpars2_111_(__Stack0) ->
 [__3,__2,__1 | __Stack] = __Stack0,
 [begin
   { product , __1 , __3 }
  end | __Stack].

-compile({inline,yeccpars2_113_/1}).
-file("varp_parse.yrl", 77).
yeccpars2_113_(__Stack0) ->
 [__3,__2,__1 | __Stack] = __Stack0,
 [begin
   { range , __1 , __3 }
  end | __Stack].

-compile({inline,yeccpars2_114_/1}).
-file("varp_parse.yrl", 84).
yeccpars2_114_(__Stack0) ->
 [__1 | __Stack] = __Stack0,
 [begin
   name ( __1 )
  end | __Stack].

-compile({inline,yeccpars2_124_/1}).
-file("varp_parse.yrl", 93).
yeccpars2_124_(__Stack0) ->
 [__3,__2,__1 | __Stack] = __Stack0,
 [begin
   { op ( __2 ) , __1 , __3 }
  end | __Stack].

-compile({inline,yeccpars2_125_/1}).
-file("varp_parse.yrl", 91).
yeccpars2_125_(__Stack0) ->
 [__1 | __Stack] = __Stack0,
 [begin
   { var , name ( __1 ) }
  end | __Stack].

-compile({inline,yeccpars2_126_/1}).
-file("varp_parse.yrl", 94).
yeccpars2_126_(__Stack0) ->
 [__3,__2,__1 | __Stack] = __Stack0,
 [begin
   { op ( __2 ) , __1 , __3 }
  end | __Stack].

-compile({inline,yeccpars2_127_/1}).
-file("varp_parse.yrl", 150).
yeccpars2_127_(__Stack0) ->
 [__3,__2,__1 | __Stack] = __Stack0,
 [begin
   { op ( __2 ) , __1 , __3 }
  end | __Stack].

-compile({inline,yeccpars2_129_/1}).
-file("varp_parse.yrl", 89).
yeccpars2_129_(__Stack0) ->
 [__3,__2,__1 | __Stack] = __Stack0,
 [begin
   { S , N } = __3 , { S , N , value ( __1 ) }
  end | __Stack].

-compile({inline,yeccpars2_130_/1}).
-file("varp_parse.yrl", 148).
yeccpars2_130_(__Stack0) ->
 [__2,__1 | __Stack] = __Stack0,
 [begin
   { op ( __1 ) , __2 }
  end | __Stack].

-compile({inline,yeccpars2_131_/1}).
-file("varp_parse.yrl", 95).
yeccpars2_131_(__Stack0) ->
 [__2,__1 | __Stack] = __Stack0,
 [begin
   { op ( __1 ) , __2 }
  end | __Stack].

-compile({inline,yeccpars2_132_/1}).
-file("varp_parse.yrl", 151).
yeccpars2_132_(__Stack0) ->
 [__2,__1 | __Stack] = __Stack0,
 [begin
   { __1 , __2 }
  end | __Stack].

-compile({inline,yeccpars2_137_/1}).
-file("varp_parse.yrl", 159).
yeccpars2_137_(__Stack0) ->
 [__3,__2,__1 | __Stack] = __Stack0,
 [begin
   [ __1 | __2 ]
  end | __Stack].

-compile({inline,yeccpars2_138_/1}).
-file("varp_parse.yrl", 160).
yeccpars2_138_(__Stack0) ->
 [__1 | __Stack] = __Stack0,
 [begin
   [ __1 ]
  end | __Stack].

-compile({inline,yeccpars2_139_/1}).
-file("varp_parse.yrl", 152).
yeccpars2_139_(__Stack0) ->
 [__4,__3,__2,__1 | __Stack] = __Stack0,
 [begin
   { __1 , __2 }
  end | __Stack].


-file("varp_parse.yrl", 177).
