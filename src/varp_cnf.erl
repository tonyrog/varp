%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2019, Tony Rogvall
%%% @doc
%%%    cnf dump clause set plugin
%%% @end
%%% Created : 18 Jun 2019 by Tony Rogvall <tony@rogvall.se>

-module(varp_cnf).

-export([run/2]).
-export([options/0]).

-include("varp.hrl").

options() ->
    [ #{ long => "type",
	 short => "t",
	 key   => type,
	 spec => {enum,[{"cnf",cnf}, {"snf", snf}]},
	 default => cnf,
	 description => "Write cnf or symbolic snf format."
       },
      #{ long => "file",
	 short => "f",
	 key  => file,
	 spec => string,
	 default => "",
	 description => "Filename of file to write clauses to."
       },
      #{ long => "symbols",
	 short => "s",
	 key   => symbols,
	 spec => {enum,[?BOOL]},
	 default => false,
	 description => "Emit symbol comments."
       },
      #{ long => "raw",
	 short => "r",
	 key   => raw,
	 spec => {enum,[?BOOL,{"debug",debug}]},
	 default => false,
	 description => "Output 'raw' clauses."
       }
    ].

run(Bs, Opts) ->
    emit(Bs, Opts).

%% output cnf clauses
emit(Bs, Opts) when is_record(Bs,bs), is_map(Opts) ->
    Raw = maps:get(raw, Opts),
    Type = maps:get(type, Opts),
    Symbols = maps:get(symbols, Opts),
    case maps:get(file, Opts) of
	"" ->
	    emit_fd(user, Type, Symbols, Raw, Bs);
	File ->
	    case file:open(File, [write]) of
		{ok,Fd} ->
		    try emit_fd(Fd, Type, Symbols, Raw, Bs) of
			R -> R
		    after
			file:close(Fd)
		    end;
		{error,Reason} ->
		    io:format("cnf error: unable to open file ~s (~w)\n",
			      [File, Reason]),
		    {?ERROR,Reason,Bs}
	    end
    end.

emit_fd(Fd, Type, Symbols, Raw, Bs) ->
    {VarMap, NumClauses, NumVars} = renumerate_clauses(Bs, Raw),
    case Type of
	cnf ->
	    emit_symbols(Fd, Symbols, Bs, VarMap),
	    io:format(Fd, "p cnf ~w ~w\n", [NumVars, NumClauses]);
	snf ->
	    io:format(Fd, "p snf ~w ~w\n", [NumVars, NumClauses])
    end,
    cnf_(Fd, Type, Raw, varc:clause_first(Bs#bs.vp), VarMap, Bs).


cnf_(_Fd,_Type,_Raw,false,_VarMap,Bs) ->
    %% emit_edge_list(_Fd, Bs, _VarMap),
    {?CONTINUE,[],Bs};
cnf_(Fd,Type,Raw,I,VarMap,Bs) ->
    case varc:get_clause(Bs#bs.vp, I, undefined, Raw=/=false) of
	true ->
	    cnf_(Fd,Type,Raw,varc:clause_next(Bs#bs.vp,I),VarMap,Bs);
	[] ->
	    cnf_(Fd,Type,Raw,varc:clause_next(Bs#bs.vp,I),VarMap,Bs);
	CL ->
	    Fmt = case Type of
		      cnf -> format_cnf_clause(Bs,CL,Raw,VarMap); 
		      snf -> format_snf_clause(Bs,CL,Raw,VarMap)
		  end,
	    io:put_chars(Fd,[Fmt,"\n"]),
	    cnf_(Fd,Type,Raw,varc:clause_next(Bs#bs.vp,I),VarMap,Bs)
    end.

format_cnf_clause(_Bs,CL,_,VarMap) ->
    [lists:join(" ", [integer_to_list(translate_literal(L,VarMap))||L<-CL]),
     " 0"].

format_snf_clause(Bs,CL,debug,_VarMap) ->
    [lists:join(" ", [varp_formula:format_lit(Bs,L,true)||L<-CL]), "."];
format_snf_clause(Bs,CL,_,_VarMap) ->
    [lists:join(" ", [varp_formula:format_lit(Bs,L,false)||L<-CL]), "."].

%% emit symbols as comments
%% 'c' <symbol> is <literal-number>
%% ...
emit_symbols(_Fd, false, _Bs, _VarMap) ->
    ok;
emit_symbols(Fd, true, Bs, VarMap) ->
    maps:fold(
      fun (Key,_Value,Acc) when is_integer(Key) ->
	      Acc;
	  (Key,Value,_Acc) ->
	      case maps:find(Value, VarMap) of
		  {ok, Value1} ->
		      io:format(Fd, "c ~s is ~w\n", 
				[varp_formula:format_symbol(Key),Value1]);
		  error -> 
		      ok
	      end
      end, [], Bs#bs.vs).

-if(false).
%% emit edge list as comments
emit_edge_list(Fd, Bs,VarMap) ->
    maps:fold(
      fun(X, Y, _Acc) ->
	      case edge_list(Bs, X, VarMap) of
		  [] -> ok;
		  K -> io:format(Fd, "c ~w => ~s\n", [Y,fmt_list(K)])
	      end,
	      case edge_list(Bs, -X, VarMap) of
		  [] -> ok;
		  L -> io:format(Fd, "c ~w => ~s\n", [-Y,fmt_list(L)])
	      end
      end, ok, VarMap).

fmt_list(List) ->
    lists:concat(lists:join(' ', List)).

%% return translated and filtered edge list
edge_list(Bs, X, VarMap) ->
    L = varc:literal_info(Bs#bs.vp, X, edge),
    lists:foldl(
      fun(Xi, Acc) ->
	      case translate_literal(Xi,VarMap) of
		  error -> Acc;
		  Yi -> [Yi|Acc]
	      end
      end, [], L).
    
-endif.

%%
%% Count clause, and variabels. Also construct a
%% mapping into compact literal numbers
%%
renumerate_clauses(Bs, Raw) ->
    renumerate_clauses(Bs, Raw, #{}, 0).

renumerate_clauses(Bs, Raw, VarMap, NumClauses) ->
    renumerate_clauses(Bs, varc:clause_first(Bs#bs.vp),
		       Raw, VarMap, NumClauses).

renumerate_clauses(_Bs, false, _Raw, VarMap, NumClauses) ->
    {VarMap, NumClauses, maps:size(VarMap)};
renumerate_clauses(Bs, I, Raw, VarMap, NumClauses) ->
    I1 = varc:clause_next(Bs#bs.vp,I),
    case varc:get_clause(Bs#bs.vp, I, undefined, Raw) of
	true ->
	    renumerate_clauses(Bs,I1,Raw,VarMap,NumClauses);
	[] ->
	    renumerate_clauses(Bs,I1,Raw,VarMap,NumClauses);
	CL ->
	    VarMap1 = renumerate_clause(CL,VarMap),
	    renumerate_clauses(Bs,I1,Raw,VarMap1,NumClauses+1)
    end.

%% generate variabel mapping into a compact set of variables
renumerate_clause([L|Ls], VarMap) ->
    case translate_literal(L,VarMap) of 
	error ->
	    N = maps:size(VarMap),
	    renumerate_clause(Ls, maps:put(abs(L),N+1,VarMap));
	_M ->
	    renumerate_clause(Ls, VarMap)
    end;
renumerate_clause([], VarMap) ->
    VarMap.

translate_literal(?T, _VarMap) -> ?T;
translate_literal(?F, _VarMap) -> ?F;
translate_literal(L, VarMap) when L < 0 ->
    case maps:find(-L, VarMap) of
	error -> error;
	{ok, M} -> -M
    end;
translate_literal(L, VarMap) when L > 0 ->
    case maps:find(L, VarMap) of
	error -> error;
	{ok,M} -> M
    end.

-ifdef(unused).
%% count number of active clauses
count_number_of_clauses(Bs) ->
    count_number_of_clauses_(Bs, varc:clause_first(Bs#bs.vp), 0).

count_number_of_clauses_(_Bs, false, N) ->
    N;
count_number_of_clauses_(Bs, I, N) ->
    case varc:get_clause(Bs#bs.vp, I, undefined, false) of
	true -> 
	    count_number_of_clauses_(Bs, varc:clause_next(Bs#bs.vp,I),N);
	[] ->
	    count_number_of_clauses_(Bs, varc:clause_next(Bs#bs.vp,I),N);
	_CL ->    
	    count_number_of_clauses_(Bs, varc:clause_next(Bs#bs.vp,I),N+1)
    end.
-endif.
