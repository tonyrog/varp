-module(varp_log).

-export([debug/3]).
-export([info/3]).

-include("log.hrl").

debug(Opt, Fmt, As) ->
    log(Opt, ?LOG_LEVEL_DEBUG, Fmt, As).

info(Opt, Fmt, As) ->
    log(Opt, ?LOG_LEVEL_INFO, Fmt, As).

log(Opt, Level0, Fmt, As) ->
    Level = level(Level0),
    ?log(Opt,Level,Fmt,As).

level(debug)   -> ?LOG_LEVEL_DEBUG;
level(info)    -> ?LOG_LEVEL_INFO;
level(notice)  -> ?LOG_LEVEL_NOTICE;
level(warning) -> ?LOG_LEVEL_WARNING;
level(error)   -> ?LOG_LEVEL_ERROR;
level(critical) -> ?LOG_LEVEL_CRITICAL;
level(alert)    -> ?LOG_LEVEL_ALERT;
level(emergency) -> ?LOG_LEVEL_EMERGENCY;
level(none) -> ?LOG_LEVEL_NONE;
level(Level) when Level >= -1, Level =< 7 -> Level.
