-ifndef(__LOG_HRL__).
-define(__LOG_HRL__, true).

-define(LOG_NONE, -1).
-define(EMERGENCY, 0).
-define(ALERT,     1).
-define(CRITICAL,  2).
-define(ERROR,     3).
-define(WARNING,   4).
-define(NOTICE,    5).
-define(INFO,      6).
-define(DEBUG,     7).

-define(debug(Opt, Fmt, As), ?log(Opt,?DEBUG,Fmt,As)).
-define(warning(Opt, Fmt, As), ?log(Opt,?WARNING,Fmt,As)).
-define(info(Opt, Fmt, As), ?log(Opt,?INFO,Fmt,As)).
	
-define(log(OptMap, Level, Fmt, As),
	case Level =< maps:get(log,OptMap,?LOG_NONE) of
	    true ->
		io:format(Fmt, As);
	    false ->
		ok
	end).

-endif.

