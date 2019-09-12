%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2019, Tony Rogvall
%%% @doc
%%%    varp plugin to validate a proof log
%%% @end
%%% Created : 18 Jun 2019 by Tony Rogvall <tony@rogvall.se>

-module(varp_validate).
-export([options/0, run/2]).

-include("varp.hrl").

options() ->
    [#{ long => "type",
	short => "t",
	key   => type,
	spec => {enum,
		 [{"none", none},
		  {"user", user},
		  {"undefined", undefined},
		  {"text", text},
		  {"binary", binary}]},
	default => undefined,
	description => "Proof type."
      },
     #{ long => "file",
	short => "f",
	key  => file,
	spec => string,
	default => "",
	description => "Proof log file."
      }
    ].

run(Bs, Param) ->
    T = case maps:get(type, Param) of
	    undefined -> varp_formula:getopt(Bs, proof_output);
	    Type -> Type
	end,
    F = case maps:get(file, Param) of
	    "" ->
		File = varp_formula:getopt(Bs, proof_file),
		Dir  = varp_formula:getopt(Bs, outdir),
		if Dir =:= "" -> File;
		   true -> filename:join(Dir, File)
		end;
	    File -> File
	end,

    close_proof_output(Bs), %% reopen later?

    case file:open(F, [read,binary,raw,read_ahead]) of
	{ok,Fd} ->
	    Res = validate_loop(Fd, T, Bs, 0),
	    file:close(Fd),
	    Res;
	{error,Reason} ->
	    io:format("error: file error ~p\n", [Reason]),
	    error
    end.

validate_loop(Fd,Type,Bs, I) ->
    I1 = I+1,
    if 	I1 rem 32000 =:= 0 ->
	    io:put_chars(".\n"); 
	I1 rem 1000 =:= 0 ->
	    io:put_chars(".");
	true ->
	    ok
    end,
    case read_clause(Fd,Type,Bs) of
	eof ->
	    io:format("VALIDATED\n"),
	    Bs;
	error ->
	    io:format("READ ERROR\n"),
	    error;
	Clause ->
	    %% io:format("check clause ~w\n", [Clause]),
	    varp_formula:set_level(Bs,1),
	    Res = eval_neg_literal_list(Bs, Clause),
	    varp_formula:undo_level(Bs,1),
	    case Res of
		false -> %% ok valid
		    varp_formula:set_level(Bs,0),
		    varp_formula:add_clause(Bs, Clause),
		    case varp_formula:eval(Bs) of
			false ->
			    case read_clause(Fd,Type,Bs) of
				[] ->
				    io:format("UNSATISFIABLE\n");
				EClause ->
				    io:format("UNSATISFIABLE, INVALID ~w\n",
					      [EClause])
			    end,
			    false;
			true ->
			    validate_loop(Fd,Type,Bs,I1)
		    end;
		true ->
		    io:format("INVALID\n"),
		    error
	    end
    end.

eval_neg_literal_list(Bs, [Li|Ls]) ->
    case varp_formula:bind(Bs,-Li) of
	false -> false;
	true -> eval_neg_literal_list(Bs, Ls)
    end;
eval_neg_literal_list(Bs, []) ->
    varp_formula:eval(Bs).


read_clause(_Fd, binary,_Bs) ->
    %% read compressed clause
    eof;
read_clause(Fd, _, Bs) ->  %% text/user
    read_text_clause(Fd, Bs, []).

read_text_clause(Fd, Bs, Acc) ->
    case file:read_line(Fd) of
	eof -> if Acc =:= [] -> eof;
		  true -> Acc
	       end;
	{ok,Line} ->
	    Ts = string:tokens(binary_to_list(Line), " \n"),
	    case add_literals(Ts, Bs, Acc) of
		{true, Clause} -> 
		    Clause;
		{false, Acc1} ->
		    read_text_clause(Fd, Bs, Acc1);
		error ->
		    error
	    end
    end.

add_literals([L|Ls], Bs, Acc) ->
    case list_to_integer(L) of
	0 ->
	    {true, lists:reverse(Acc)};
	Li -> 
	    add_literals(Ls, Bs, [dimacs_literal(Li,Bs)|Acc])
    end;
add_literals([], _Bs, Acc) ->
    {false, Acc}.

dimacs_literal(Li,Bs) when Li < 0 ->
    -variable({p,x,[-Li]},Bs);
dimacs_literal(Li,Bs) when Li > 0 ->
    variable({p,x,[Li]},Bs).

variable(V, Bs) ->
    I = maps:get(V, Bs#bs.vs),
    %% io:format("~w => ~w\n", [V,I]),
    I.

close_proof_output(Bs) ->
    case Bs#bs.proof_fd of
	undefined -> ok;
	user -> ok;
	Fd -> file:close(Fd)
    end.
