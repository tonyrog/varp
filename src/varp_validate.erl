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

run(Bs, Param) when is_record(Bs, bs), is_map(Param) ->
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
	    io:format("add clause ~w\n", [Clause]),
	    varc:set_level(Bs#bs.vp,1),
	    Res = eval_neg_literal_list(Bs, Clause),
	    varc:undo_level(Bs#bs.vp,1),
	    case Res of
		false -> %% ok valid
		    varc:set_level(Bs#bs.vp,0),
		    varp_formula:add_clause(Bs, Clause),
		    case varc:bcp(Bs#bs.vp) of
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
		    io:format("\nINVALID\n"),
		    {?ERROR,"invalid",Bs}
	    end;
	{d,Clause} ->
	    %% what tests must be done?
	    io:format("delete clause ~w\n", [Clause]),
	    ok = varp_formula:del_clause(Bs, Clause),
	    validate_loop(Fd,Type,Bs,I1)	    
    end.

eval_neg_literal_list(Bs, [Li|Ls]) ->
    case varc:bind(Bs#bs.vp,-Li) of
	false -> false;
	true -> eval_neg_literal_list(Bs, Ls)
    end;
eval_neg_literal_list(Bs, []) ->
    varc:bcp(Bs#bs.vp).

read_clause(_Fd, binary,_Bs) ->
    %% read compressed clause
    eof;
read_clause(Fd, _, Bs) ->  %% text/user
    read_text_clause(Fd, Bs).

read_text_clause(Fd, Bs) ->
    case file:read_line(Fd) of
	eof -> eof;
	{ok,Line} ->
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
    case take_eol(Ts) of
	false -> 
	    read_text_clause(Fd, Bs, Acc++Ts, Type);
	{true, Ts1} ->
	    parse_clause(Bs, Acc++Ts1, Ln, Type)
    end.


take_eol(Ts) ->
    take_eol(Ts,[]).

take_eol([{decnum,_,"0"}],Acc) ->
    {true, lists:reverse(Acc)};
take_eol([T|Ts], Acc) ->
    take_eol(Ts, [T|Acc]);
take_eol([], _Acc) ->
    false.

parse_clause(Bs, Ts, Ln, Type) ->
    case scan_clause(Ts, Ln, Bs, []) of
	{ok, Clause} ->
	    {Type, Clause};
	error ->
	    error
    end.

scan_clause([], _Ln, _Bs, Acc) ->
    {ok, lists:reverse(Acc)};
scan_clause([{decnum,_Ln,Dec}|Ts], Ln, Bs, Acc) ->
    Li = list_to_integer(Dec),
    scan_clause(Ts, Ln, Bs, [dimacs_literal(Li,Bs)|Acc]);
scan_clause([{'-',_Ln0},{decnum,_Ln,Dec}|Ts], Ln, Bs, Acc) ->
    Li = -list_to_integer(Dec),
    scan_clause(Ts, Ln, Bs, [dimacs_literal(Li,Bs)|Acc]);
scan_clause(Ts, Ln, Bs, Acc) ->
    case varp_snf:parse(Ts++[{'.',Ln}]) of
	{ok, CL} ->
	    {ok, Acc ++ snf_literals(CL, Bs)};
	{error, _Reason} ->
	    error
    end.

%% translate SNF symbols and reverse list
snf_literals(CL, Bs) ->
    snf_literals(CL, Bs, []).

snf_literals([{'not',X}|CL], Bs, Acc) ->
    snf_literals(CL, Bs, [-variable(eval_sym(X), Bs)|Acc]);
snf_literals([X|CL], Bs, Acc) ->
    snf_literals(CL, Bs, [variable(eval_sym(X), Bs)|Acc]);
snf_literals([], _Bs, Acc) ->
    Acc.

eval_sym({p,S,Args}) ->
    {p,S,[eval_arg(A)||A<-Args]};
eval_sym({bit_index,Sym,Index}) ->
    {bit_index,eval_sym(Sym),eval_arg(Index)}.

eval_arg(V) when is_integer(V) -> V;
eval_arg(#cconst{base=B,value=V}) -> list_to_integer(V,B).

empty_vs(Bs) ->    
    (Bs#bs.vs =:= undefined) orelse  (maps:size(Bs#bs.vs) =:= 0).

dimacs_literal(Li,Bs) when Li < 0 ->
    case empty_vs(Bs) of
	true -> Li;
	false -> -variable({p,x,[-Li]},Bs)
    end;
dimacs_literal(Li,Bs) when Li > 0 ->
    case empty_vs(Bs) of
	true -> Li;
	false -> variable({p,x,[Li]},Bs)
    end.

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
