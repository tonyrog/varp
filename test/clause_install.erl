%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2018, Tony Rogvall
%%% @doc
%%%    Check if eval trigg after install
%%% @end
%%% Created : 20 Apr 2018 by Tony Rogvall <tony@rogvall.se>

-module(clause_install).

-compile(export_all).

test() ->
    Vp = varc:new(),
    A = varc:add_variable(Vp),
    B = varc:add_variable(Vp),
    C = varc:add_variable(Vp),
    varc:put(Vp, B, -1),
    varc:put(Vp, C, -1),
    T = varc:add_clause(Vp, 'or', [1,A,B,C]),
    -1 = varc:get(Vp, B),
    -1 = varc:get(Vp, C),
    io:format("T = ~w, flags=~w\n", 
	      [varc:get_clause(Vp, T),
	       varc:get_clause_flags(Vp,T)]),
    true = varc:eval(Vp),
    1 = varc:get(Vp, A).

    
    
    

