%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2010, Tony Rogvall
%%% @doc
%%%    Prover interface
%%% @end
%%% Created :  5 Aug 2010 by Tony Rogvall <tony@rogvall.se>

-module(varp).

-export([main/1]).
-export([run/3]).
-export([run_formula/1, run_formula/2]).
-export([prove_formula/1, prove_formula/2]).
-export([parse/1, parse/2]).
-export([scan_file/1]).
-export([file/1, string/1, file_expand_cnf/2]).
-export([archive_path/1]).

-include_lib("stdlib/include/zip.hrl").

main(Args) ->
    application:start(varp),
    XArgs = case os:getenv("VARP_CORE") of
		false ->
		    ["-bcp", "1", "-clause", "1"];
		"varw" ->
		    ["-bcp", "1", "-clause", "1"];
		"varc" ->
		   ["-clause", "0"];
	       _ ->
		    ["-clause", "0"]
	    end,
    {Mode,Bound,Opts0,Files} = process_args0(Args, XArgs, satisfy),
    Opts = [{meta,Bound}|Opts0],
    io:format("Opts = ~p\n", [Opts]),
    {ReadIn,{Sections0,Formula0}} =
	case load_formulas(Opts, undefined, 'and') of
	    {ok,{S0,undefined}}-> {true,{S0,undefined}};
	    {ok,R0} -> {false,R0};
	    __Error -> halt(1)
	end,
    case Files of
	[] when Mode =:= help; Mode =:= version ->
	    run(Mode, undefined, Opts);
	[] when not ReadIn ->
	    Defs0 = maps:get(defs,Sections0),
	    run(Mode,Formula0,[{defs,Defs0}|Opts]);
	[] when ReadIn ->
	    case read_in() of
		{ok,<<>>} ->
		    Defs0 = maps:get(defs,Sections0),
		    run(Mode,Formula0,[{defs,Defs0}|Opts]);
		{ok,Data} ->
		    case parse("*stdin*", Data) of
			{ok,{Sections1,Formula}} ->
			    Formula1 = join_f('and',Formula0,Formula),
			    Sections = append_sections(Sections0,Sections1),
			    #{order:=Order,
			      decls:=Decls,
			      code:=Code,
			      literals:=Literals,
			      defs:=Defs} = Sections,
			    OrderOpts = order_decl(Order),
			    run(Mode,Formula1,
				OrderOpts++
				    [{defs,Defs},
				     {decls,Decls},
				     {code,Code},
				     {literals,Literals}|Opts]);
			_Error ->
			    halt(1)
		    end;
		_Error ->
		    halt(1)
	    end;
	[F] -> %% check if batch mode, run tar/zip over all formulas
	    case archive_type(F) of
		undefined ->
		    case load_files([F],Formula0,Sections0,'and',Opts) of
			{ok,{Sections1,Formula}} ->
			    Sections = append_sections(Sections0,Sections1),
			    #{order:=Order,
			      decls:=Decls,
			      code:=Code,
			      literals:=Literals,
			      defs:=Defs} = Sections,
			    OrderOpts = order_decl(Order),
			    run(Mode,Formula,
				OrderOpts++
				    [{defs,Defs},
				     {decls,Decls},
				     {code,Code},
				     {literals,Literals}|Opts]);
			_Error ->
			    halt(1)
		    end;
		Type ->
		    run_batch(Mode,Type,F,[{max,1}|Opts])
	    end;
	Fs ->
	    case load_files(Fs,Formula0,Sections0,'and',Opts) of
		{ok,{Sections1,Formula}} ->
		    Sections = append_sections(Sections0,Sections1),
		    #{order:=Order,
		      decls:=Decls,
		      code:=Code,
		      literals:=Literals,
		      defs:=Defs} = Sections,
		    OrderOpts = order_decl(Order),
		    run(Mode,Formula,
			OrderOpts++
			    [{defs,Defs},
			     {decls,Decls},
			     {code,Code},
			     {literals,Literals}|Opts]);
		_Error ->
		    halt(1)
	    end
    end,
    %% io:format("varp: arguments = ~p\n", [As]),
    halt(0).

run_batch(Mode,ArchiveType,ArchiveFile,Opts) ->
    {ok,Fs} = archive_file_list(ArchiveType,ArchiveFile),
    lists:foreach(
      fun(F) ->
	      AFile = filename:join(ArchiveFile,F),
	      case load_files([AFile],true,empty_sections(),'and',Opts) of
		  {ok,{Sections,Formula}} ->
		      #{order:=Order,
			decls:=Decls,
			code:=Code,
			literals:=Literals,
			defs:=Defs} = Sections,
		      OrderOpts = order_decl(Order),
		      run(Mode,Formula,
			  OrderOpts++
			      [{defs,Defs},
			       {decls,Decls},
			       {code,Code},
			       {literals,Literals}|Opts]);
		  Error ->
		      io:format("~s: error ~p\n", [F,Error]),
		      ok
	      end
      end, Fs).

run(satisfy, Formula, Opts) ->
    R = run_formula(Formula,Opts++[{value,true}]),
    result(R, satisfy);
run(falsify, Formula, Opts) ->
    R = run_formula(Formula,Opts++[{value,false}]),
    result(R, falsify);
run(prove, Formula, Opts) ->
    R = prove_formula(Formula,Opts),
    result(R, prove);
run(none, Formula, Opts) ->
    R = run_formula(Formula,Opts),
    result(R, none);
run(snf, Formula, Opts) ->
    %% generate dimacs snf from a formula
    Bs = proplists:get_value(env,Opts,[]),
    F = varp_expand:formula(Formula,Bs),
    %% Cs=clauses and Ls=literals eliminated
    {Cs,_Ls} = varp_cnf:clauses(F),
    Data = varp_cnf:format(Cs),
    case proplists:get_value(output,Opts,"") of
	"" ->
	    io:put_chars(Data);
	FileName ->
	    file:write_file(FileName, Data)
    end,
    ok;
run(cnf, Formula, Opts) ->
    %% generate dimacs cnf from a formula
    Bs = proplists:get_value(env,Opts,[]),
    F = varp_expand:formula(Formula,Bs),
    %% Cs=clauses and Ls=literals eliminated
    {Cs,_Ls} = varp_cnf:clauses(F),
    Data = varp_dimacs:format(Cs),
    case proplists:get_value(output,Opts,"") of
	"" ->
	    io:put_chars(Data);
	FileName ->
	    file:write_file(FileName, Data)
    end,
    ok;
run(help, _Formula, _Opts) ->
    varp_option:usage();
run(version, _Formula, _Opts) ->
    varp_option:version().

result(true,prove) ->       io:format("% TRUE\n", []);
result(false,prove) ->      io:format("% FALSE\n", []);
result(undefined,prove) ->  io:format("% UNKNOWN\n", []);
result(undefined,_) ->      io:format("\n", []);
result(N, _) when is_integer(N) -> io:format("% ~w\n", [N]);
result({N,_Mdls}, _) -> io:format("% ~w\n", [N]).

order_decl([]) -> [];
order_decl(Vs) -> order_decl(Vs,[]).

order_decl([Key1,Key2|Vs],Opts) when is_atom(Key1), is_atom(Key2) ->
    order_decl(Vs,[{order,[Key1,Key2]}|Opts]);
order_decl([Key1|Vs],Opts) when is_atom(Key1) ->
    order_decl(Vs,[{order,[Key1]}|Opts]);
order_decl([V|Vs],[{order_list,Ls}|Opts]) when is_tuple(V) ->
    order_decl(Vs, [{order_list,Ls++[V]}|Opts]);
order_decl([V|Vs],Opts) when is_tuple(V) ->
    order_decl(Vs, [{order_list,[V]}|Opts]);
order_decl([],Opts) ->
    case lists:reverse(Opts) of
	[{order_list,L1},{order,K},{order_list,L2}] ->
	    [{order,K},{order_first,L1},{order_last,L2}];
	[{order_list,L1},{order,K}] ->
	    [{order,K},{order_first,L1}];
	[{order,K},{order_list,L2}] ->
	    [{order,K},{order_last,L2}];
	[{order_list,L1}] ->
	    [{order_first,L1}];
	[{order,K}] ->
	    [{order,K}];
	[] ->
	    []
    end.

%% load files and form a conjunction over all files
load_files([F|Fs],Formula0,Sections,JoinOp,Opts) ->
    {ok, Data} = read_file(F),
    Ext = filename:extension(F),
    if Ext =:= ".cnf"; Ext =:= ".snf"; Ext =:= ".dimacs" ->
	    case varp_dimacs:parse(Data) of
		Error={error,Ln,Reason} ->
		    io:format("~s:~w error: ~p\n", [F,Ln,Reason]),
		    Error;
		Cnf = {cnf,{_NVars,_NClauses,Decls1,_Ls,_CLs}} ->
		    %% io:format("% loaded: ~p\n", [Cnf]),
		    Formula1 = join_f(JoinOp,Cnf,Formula0),
		    Decls = maps:get(decls,Sections) ++ Decls1,
		    load_files(Fs,Formula1,
			       Sections#{ decls=>Decls },
			       JoinOp,Opts);
		Snf = {snf,{_NVars,_NClauses,Decls1,_Ls,_CLs}} ->
		    %% io:format("% loaded: ~p\n", [Snf]),
		    Formula1 = join_f(JoinOp,Snf,Formula0),
		    Decls = maps:get(decls,Sections) ++ Decls1,
		    load_files(Fs,Formula1,
			       Sections#{ decls=>Decls },
			       JoinOp,Opts)
	    end;
       true ->
	    case parse(F, Data) of
		{ok,{Sections1,Formula}} ->
		    %% io:format("% loaded: ~s\n", [F]),
		    Formula1 = join_f(JoinOp,Formula,Formula0),
		    load_files(Fs,Formula1,
			       append_sections(Sections,Sections1),
			       JoinOp,Opts);
		Error ->
		    Error
	    end
    end;
load_files([],Formula,Sections,_JoinOp,_Opts) ->
    {ok,{Sections,Formula}}.

%% fixme analyze the path to see if there are 
%% archive tar/tar.gz/tgz/zip compoinents in the path
%% in such case open the archive and extract the file
%% as binary

-spec archive_path(FileName::string()) ->
			  {file,DirName::string(),FileName::string()} |
			  {archive,Type::gz|zip,Archive::string(),
			   File::string()} |
			  {error,term()}.

archive_path(FileName) ->
    case archive_path_(filename:split(FileName)) of
	{file,Ps1,F} ->
	    {file,fjoin(Ps1),F};
	{archive,Type,Ps1,Fs} ->
	    {archive,Type,fjoin(Ps1),fjoin(Fs)};
	{error,_}=Error -> Error
    end.
     
archive_path_([F]) ->
    {file,[],F};
archive_path_([D|Ds]) ->
    case filelib:is_dir(D) of
	true ->
	    archive_path_(Ds, D);
	false ->
	    case archive_type(D) of
		undefined ->
		    archive_path_(Ds, D);
		Type ->
		    {archive,Type,[D],Ds}
	    end
    end.

archive_path_(Ds, D) ->
    case archive_path_(Ds) of
	{archive,Type,Ds1,Fs} ->
	    {archive,Type,[D|Ds1],Fs};
	{file,Ds1,F} -> 
	    {file,[D|Ds1],F};
	Error={error,_} -> Error
    end.

archive_type(FileName) ->
    archive_type(FileName, [{".tar.gz", tgz},
			    {".tgz",    tgz},
			    {".tar",    tar},
			    {".zip",    zip}]).

archive_type(FileName, [{Sfx,Type}|L]) ->
    case lists:suffix(Sfx, FileName) of
	true -> Type;
	false -> archive_type(FileName, L)
    end;
archive_type(_FileName, []) ->
    undefined.

fjoin([]) -> "";
fjoin(Fs) -> filename:join(Fs).


%% load/parse formulas given on command line like -f "A && B"
load_formulas(Opts, A, JoinOp) ->
    case proplists:get_all_values(formula, Opts) of
	[] -> {ok,{empty_sections(),A}};
	Fs -> parse_formulas(Fs,A,empty_sections(),JoinOp)
    end.

parse_formulas([F|Fs], Formula, Sections0,JoinOp) ->
    case parse("*command-line*", F) of
	{ok,{Sections1,Formula1}} ->
	    parse_formulas(Fs, join_f(JoinOp, Formula, Formula1),
			   append_sections(Sections0, Sections1), JoinOp);
	Error ->
	    Error
    end;
parse_formulas([], Formula, Sections, _JoinOp) ->
    {ok,{Sections,Formula}}.

empty_sections() ->
    #{ decls=>[], code=>[], order=>[], literals=>[], defs=>[]}.    

append_sections(#{ decls:=D0, code:=C0, order:=O0, literals:=Ls0, defs:=Ds0},
		#{ decls:=D1, code:=C1, order:=O1, literals:=Ls1, defs:=Ds1}) ->
    #{ decls=>D0++D1, 
       code=>C0++C1, 
       order=>O0++O1, 
       literals=>Ls0++Ls1,
       defs=>Ds0++Ds1}.

join_f(_JoinOp,undefined,B) -> B;
join_f(_JoinOp,A,undefined) -> A;
join_f(JoinOp,A,B) -> {JoinOp,A,B}.

%% check "base" mode satisfy|falsify|prove
process_args0(["satisfy"|As], Bs, _Mode) ->
    varp_option:process_args(Bs++As, satisfy);
process_args0(["falsify"|As], Bs, _Mode) ->
    varp_option:process_args(Bs++As, falsify);
process_args0(["prove"|As], Bs, _Mode) ->
    varp_option:process_args(Bs++As, prove);
process_args0(["cnf"|As], Bs, _Mode) ->
    varp_option:process_args(Bs++As, cnf);
process_args0(["snf"|As], Bs, _Mode) ->
    varp_option:process_args(Bs++As, snf);
process_args0(["help"|As],Bs, _Mode) ->
    varp_option:process_args(Bs++As, help);
process_args0(["version"|As],Bs,_Mode) ->
    varp_option:process_args(Bs++As, version);
process_args0(["none"|As], Bs, _Mode) ->
    varp_option:process_args(Bs++As, nonde);
process_args0(As, Bs, Mode) ->
    varp_option:process_args(Bs++As, Mode).


read_in() ->
    collect_in([]).

collect_in(Acc) ->
    case io:get_line('') of
	eof -> 
	    {ok,list_to_binary(lists:reverse(Acc))};
	Line ->
	    collect_in([Line|Acc])
    end.

run_formula(Formula) ->
    run_formula(Formula,[]).
run_formula(Formula,Opts) ->
    varp_prover:run_formula(Formula, Opts).

prove_formula(Formula) ->
    prove_formula(Formula,[]).
prove_formula(Formula,Opts) ->
    varp_prover:prove_formula(Formula, [{max,2}|Opts]).

file(File) ->
    case read_file(File) of
	{ok,Binary} ->
	    parse(File,Binary);
	Error ->
	    Error
    end.

scan_file(File) ->
    case read_file(File) of
	{ok,Binary} ->    
	    tokens(binary_to_list(Binary));
	Error -> Error
    end.

%% Archive aware file:read
read_file(FileName) ->
    case archive_path(FileName) of
	{file,"",File} -> file:read_file(File);
	{file,Dir,File} -> file:read_file(filename:join(Dir,File));
	{archive,tgz,ArchiveFile,File} ->
	    case file:open(ArchiveFile,[read,compressed,raw,binary]) of
		{ok,Fd} ->
		    case erl_tar:extract({file,Fd},[{files,[File]},memory]) of
			{ok,[{File,Bin}]} ->
			    file:close(Fd),
			    {ok,Bin};
			Error ->
			    Error
		    end;
		Error -> Error
	    end;
	{archive,tar,ArchiveFile,File} ->
	    case file:open(ArchiveFile,[read,binary,raw]) of
		{ok,Fd} ->
		    case erl_tar:extract({file,Fd},[{files,[File]},memory]) of
			{ok,[{File,Bin}]} ->
			    file:close(Fd),
			    {ok,Bin};
			Error ->
			    Error
		    end;
		Error -> Error
	    end;
	{archive,zip,ArchiveFile,File} ->
	    case zip:extract(ArchiveFile,[{file_list,[File]},memory]) of
		{ok,[{File,Bin}]} ->
		    {ok,Bin};
		Error ->
		    Error
	    end
    end.

%% extract member names from archive file
archive_file_list(ArchiveType,ArchiveFile) ->
    case ArchiveType of
	tgz ->
	    case file:open(ArchiveFile,[read,binary,compressed,raw]) of
		{ok,Fd} ->
		    Res = erl_tar:table({file,Fd}),
		    file:close(Fd),
		    Res;
		Error -> Error
	    end;
	tar ->
	    case file:open(ArchiveFile,[read,binary,raw]) of
		{ok,Fd} ->
		    Res = erl_tar:table({file,Fd}),
		    file:close(Fd),
		    Res;
		Error -> Error
	    end;
	zip ->
	    case zip:table(ArchiveFile) of
		{ok,List} ->
		    {ok,zip_names(List)};
		Error ->
		    Error
	    end
    end.

zip_names([#zip_comment{}|L]) -> zip_names(L);
zip_names([#zip_file{name=Name}|L]) ->
    [Name|zip_names(L)];
zip_names([]) ->
    [].

parse(String) ->
    parse("*internal*", String).

parse(File, Binary) when is_binary(Binary) ->
    parse(File, binary_to_list(Binary));
parse(File, String) ->
    case tokens(String) of
	{ok,Ts} ->
	    case varp_parse:parse(Ts) of
		{ok,{Sections,Formula}} ->
		    SectionMap = split_sections(Sections),
		    {ok,{SectionMap,Formula}};
		Error={error,{Ln,Mod,Why}} when 
		      is_integer(Ln), is_atom(Mod) ->
		    Reason = Mod:format_error(Why),
		    io:format("~s:~w: ~s\n", [File,Ln,Reason]),
		    Error;
		Error ->
		    io:format("~s: Error: ~p\n", [File,Error]),
		    Error
	    end;
	Error ->
	    io:format("~s: Error: ~p\n", [File, Error]),
	    Error
    end.

split_sections(Sections) ->
    split_sections(Sections,empty_sections()).

split_sections([{declare,Decl}|Sections], Map=#{ decls:=Decl0 }) ->
    split_sections(Sections, Map#{ decls => Decl0++Decl });
split_sections([{code,Code}|Sections],Map=#{ code:=Code0 }) ->
    split_sections(Sections, Map#{ code => Code0++Code });
split_sections([{order,Order}|Sections],Map=#{ order:=Order0 }) ->
    split_sections(Sections, Map#{ order => Order0++Order });
split_sections([{literals,Ls}|Sections],Map=#{ literals:=Ls0 }) ->
    split_sections(Sections, Map#{ literals => Ls0++Ls });
split_sections([{define,P,Expr}|Sections], Map=#{ defs:=Defs0 }) ->
    split_sections(Sections, Map#{ defs => Defs0++[{P,Expr}] });
split_sections([], Map) ->
    Map.
    
string(Binary) when is_binary(Binary) ->
    string(binary_to_list(Binary));
string(String) when is_list(String) ->
    {ok,Ts} = tokens(String),
    varp_parse:parse(Ts).

tokens(String) ->
    case varp_scan:string(remove_comments(String)) of
	{ok,Ts,_Ln} -> 
	    %% io:format("tokens=~p\n", [Ts]),
	    {ok,Ts};
	Error -> Error
    end.

%% remove C-style comments from data
remove_comments([$/,$/|Cs]) -> remove_comments(remove_line(Cs));
remove_comments([$/,$*|Cs]) -> remove_comments(remove_block(Cs));
remove_comments([C|Cs]) -> [C|remove_comments(Cs)];
remove_comments([]) -> [].

%% remove until */ but keep all \n
remove_block([$*,$/|Cs]) -> Cs;
remove_block([$\n|Cs]) -> [$\n|remove_block(Cs)];
remove_block([_|Cs]) -> remove_block(Cs);
remove_block([]) -> [].

%% remove until end-of-line (but keep it)
remove_line(Cs=[$\n|_]) -> Cs;
remove_line([_|Cs]) -> remove_line(Cs);
remove_line([]) -> [].


%% special
file_expand_cnf(File, MetaBind) ->
    case file(File) of
	{ok,F} ->
	    F1 = varp_expand:formula(F,MetaBind),
	    {CLs,_Ls} = varp_cnf:clauses(F1),
	    CLs;
	Error ->
	    Error
    end.
