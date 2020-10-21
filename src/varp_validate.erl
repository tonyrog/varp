%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2019, Tony Rogvall
%%% @doc
%%%    varp plugin to validate a proof log
%%% @end
%%% Created : 18 Jun 2019 by Tony Rogvall <tony@rogvall.se>

-module(varp_validate).
-behaviour(varp_plugin).

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

run(Bs, Param) when is_record(Bs, bs), is_map(Param) ->
    %% io:format("Decls = ~p\n", [Bs#bs.decls]),
    %% io:format("Var = ~p\n", [Bs#bs.vs]),
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
	    {?ERROR, "file error", Bs}
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
	    io:format("\nVALIDATED\n"),
	    {?CONTINUE,[],Bs};
	error ->
	    io:format("\nREAD ERROR\n"),
	    {?ERROR,"read error",Bs};
	{a,Clause} ->
	    %% io:format("add clause ~w\n", [Clause]),
	    varp_nif:set_level(Bs#bs.vp,1),
	    Res = eval_neg_literal_list(Bs, Clause),
	    varp_nif:undo_level(Bs#bs.vp,1),
	    case Res of
		false -> %% ok valid
		    varp_nif:set_level(Bs#bs.vp,0),
		    case varp_nif:add_clause(Bs#bs.vp, Clause, gamma) of
			true -> ok;
			{true,_} -> ok
		    end,
		    case varp_nif:bcp(Bs#bs.vp) of
			false ->
			    case read_clause(Fd,Type,Bs) of
				{a,[]} ->
				    io:format("\nUNSATISFIABLE\n");
				EClause ->
				    io:format("\nUNSATISFIABLE, INVALID ~w\n",
					      [EClause])
			    end,
			    {?INCONSISTENT,[],Bs};
			true ->
			    validate_loop(Fd,Type,Bs,I1)
		    end;
		true ->
		    io:format("\nINVALID step=~w ~w\n", [I1,Clause]),
		    io:format("\nINVALID\n"),
		    {?ERROR,"invalid",Bs}
	    end;
	{d,Clause} ->
	    %% what tests must be done?
	    %% io:format("DELETE ~w\n", [Clause]),
	    CIX = varp_nif:find_clause(Bs#bs.vp, Clause),
	    %% io:format("  INDEX: ~w:~w\n", [(_CIX bsr 30),
	    %%            (CIX band 16#3fffffff)]),
	    ok = varp_nif:del_clause(Bs#bs.vp, CIX),
	    validate_loop(Fd,Type,Bs,I1);
	{c,_Comment} ->
	    validate_loop(Fd,Type,Bs,I1)
    end.

eval_neg_literal_list(Bs, [Li|Ls]) ->
    case varp_nif:bind(Bs#bs.vp,-Li) of
	false -> false;
	true -> eval_neg_literal_list(Bs, Ls)
    end;
eval_neg_literal_list(Bs, []) ->
    varp_nif:bcp(Bs#bs.vp).

read_clause(_Fd, binary,_Bs) ->
    %% read compressed clause
    eof;
read_clause(Fd, _, Bs) ->  %% text/user
    read_text_clause(Fd, Bs).

read_text_clause(Fd, Bs) ->
    case file:read_line(Fd) of
	eof -> eof;
	{ok,<<"c ",Text/binary>>} ->
	    {c, Text};
	{ok,Line} ->
	    %% io:format("~s", [Line]),
	    case varp_scan:string(binary_to_list(Line)) of
		{ok,[{identifier,_Ln,"d"}|Ts],Ln1} ->
		    text_clause(Fd, Bs, Ts, Ln1, [], d);
		{ok,[{identifier,_Ln,"a"}|Ts],Ln1} ->
		    text_clause(Fd, Bs, Ts, Ln1, [], a);
		{ok,Ts,Ln1} ->
		    text_clause(Fd, Bs, Ts, Ln1, [], a)
	    end
    end.

read_text_clause(Fd, Bs, Acc, Type) ->
    case file:read_line(Fd) of
	eof -> eof;
	{ok,Line} ->
	    case varp_scan:string(binary_to_list(Line)) of
		{ok,Ts,Ln1} ->
		    text_clause(Fd, Bs, Ts, Ln1, Acc, Type)
	    end
    end.

text_clause(Fd, Bs, Ts, Ln, Acc, Type) ->
    case varp_snf:parse(Ts++[{'.',Ln}]) of
	{ok,CL} ->
	    case lists:last(CL) of
		0 ->
		    {Type,snf_literals(CL--[0], Bs)};
		_ ->
		    read_text_clause(Fd, Bs, Acc+Ts, Type)
	    end;
	Error -> 
	    Error
    end.

%% translate SNF symbols
snf_literals(CL, Bs) ->
    snf_literals(CL, Bs, []).

snf_literals([Li|CL], Bs, Acc) when is_integer(Li) ->
    snf_literals(CL, Bs, [Li|Acc]);
snf_literals([{'not',X}|CL], Bs, Acc) ->
    snf_literals(CL, Bs, [-variable(eval_sym(X,Bs), Bs)|Acc]);
snf_literals([X|CL], Bs, Acc) ->
    snf_literals(CL, Bs, [variable(eval_sym(X,Bs), Bs)|Acc]);
snf_literals([], _Bs, Acc) ->
    lists:reverse(Acc).

eval_sym({p,S,Args},_Bs) ->
    {p,S,[eval_arg(A)||A<-Args]};
eval_sym({bit_index,Sym,Index},Bs) ->
    {p,Name,_Arg} = ESym = eval_sym(Sym,Bs),
    EIndex = eval_arg(Index),
    case maps:get(Name, Bs#bs.decls, undefined) of
	undefined ->
	    {bit_index,ESym,EIndex};
	{PType,_Arity,Size} ->
	    {PType,ESym,Size,EIndex}
    end.


eval_arg(V) when is_integer(V) -> V;
eval_arg({const,V}) -> V.

empty_vs(Bs) ->    
    (Bs#bs.vs =:= undefined) orelse  (maps:size(Bs#bs.vs) =:= 0).

variable(V, Bs) ->
    case empty_vs(Bs) of
	true ->
	    io:format("Error: Symbols are not present for ~p\n", [V]),
	    throw({error,{symbol, V}});
	false ->
	    maps:get(V, Bs#bs.vs)
    end.

close_proof_output(Bs) ->
    case Bs#bs.proof_fd of
	undefined -> ok;
	user -> ok;
	Fd -> file:close(Fd)
    end.
