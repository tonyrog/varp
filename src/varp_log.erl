-module(varp_log).

-export([debug/3]).
-export([info/3]).

-include("log.hrl").

debug(Opt, Fmt, As) ->
    log(Opt, ?DEBUG, Fmt, As).

info(Opt, Fmt, As) ->
    log(Opt, ?INFO, Fmt, As).

log(Opt, Level0, Fmt, As) ->
    Level = level(Level0),
    ?log(Opt,Level,Fmt,As).

level(debug)   -> ?DEBUG;
level(info)    -> ?INFO;
level(notice)  -> ?NOTICE;
level(warning) -> ?WARNING;
level(error)   -> ?ERROR;
level(critical) -> ?CRITICAL;
level(alert)    -> ?ALERT;
level(emergency) -> ?EMERGENCY;
level(none) -> ?LOG_NONE;
level(Level) when Level >= -1, Level =< 7 -> Level.
