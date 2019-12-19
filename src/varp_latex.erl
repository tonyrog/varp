%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2019, Tony Rogvall
%%% @doc
%%%    VARP latex plugin, format varp as latex
%%% @end
%%% Created : 12 Nov 2019 by Tony Rogvall <tony@rogvall.se>

-module(varp_latex).

-export([format_error/1]).
-export([parse_transform/2]).

format_error(Mesg) ->
    Mesg.

parse_transform(Form, _Options) ->
    io:format("FORM: ~p\n", [Form]),
    io:format("OPTIONS: ~p\n", [_Options]),
    TeX = form(Form),
    io:put_chars(TeX),
    Form.

form({'ALL',Fs}) ->
    ["\all", [form(F) || F <- Fs],  "}"];
form({'ANY',Fs}) ->
    ["\exists", [form(F) || F <- Fs],  "}"];
form({'NONE',Fs}) ->
    ["\none{", [form(F) || F <- Fs], "}"];
form({'ONE',Fs}) ->
    ["\exists!{", [form(F) || F <- Fs], "}"];
form(_F) ->
    "".
