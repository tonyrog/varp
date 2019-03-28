%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2019, Tony Rogvall
%%% @doc
%%%
%%% @end
%%% Created : 14 Mar 2019 by Tony Rogvall <tony@rogvall.se>

-ifndef(__VARP_HRL__).
-define(__VARP_HRL__, true).

-record(bs,
	{
	 option = #{} :: [#{}],  %% the options
	 vs :: map(),         %% map() model variables var <=> Vn
	 vp :: reference(),   %% varc instance
	 meta=[],            %% meta variable bindings during build
	 defs=[],            %% definitions [{{p,x,[v1,..vn]}, F(v1...vn)}]
	 decls=[],           %% declarations [{int,Sz,Pred},{uint,Sz,Pred}]
	 subst=[],           %% var/function substitution(s)
	 literals=[]         %% declared literals [atom()]
	}).

-endif.



