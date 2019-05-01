-ifndef(__LOG_HRL__).
-define(__LOG_HRL__, true).

-define(LOG_LEVEL_NONE, -1).
-define(LOG_LEVEL_EMERGENCY, 0).
-define(LOG_LEVEL_ALERT,     1).
-define(LOG_LEVEL_CRITICAL,  2).
-define(LOG_LEVEL_ERROR,     3).
-define(LOG_LEVEL_WARNING,   4).
-define(LOG_LEVEL_NOTICE,    5).
-define(LOG_LEVEL_INFO,      6).
-define(LOG_LEVEL_DEBUG,     7).

-define(debug(Opt, Fmt, As), ?log(Opt,?LOG_LEVEL_DEBUG,Fmt,As)).
-define(warning(Opt, Fmt, As), ?log(Opt,?LOG_LEVEL_WARNING,Fmt,As)).
-define(info(Opt, Fmt, As), ?log(Opt,?LOG_LEVEL_INFO,Fmt,As)).
	
-define(log(OptMap, Level, Fmt, As),
	case Level =< maps:get(log,OptMap,?LOG_LEVEL_NONE) of
	    true ->
		io:format(Fmt, As);
	    false ->
		ok
	end).

-endif.

