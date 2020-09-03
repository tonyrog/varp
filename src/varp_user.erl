-module(varp_user).

-export([dist/2]).

dist(X, Y) ->
    trunc(math:sqrt(X*X + Y*Y)).
