%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2026, Tony Rogvall
%%% @doc
%%%    Pentomino puzzles on epx: drag the pieces onto the figure, turn
%%%    them, and let varp fill in the rest.
%%%
%%%    erl -pa . -pa ../ebin -pa ~/erlang/epx/ebin -eval 'pento_epx:start()'
%%%
%%%    Mouse:  left drag      move a piece (tray <-> board)
%%%            right click    rotate the piece under the pointer
%%%            middle click   mirror it
%%%            wheel          rotate
%%%    Keys:   r / R          rotate the piece under the pointer (or held)
%%%            m              mirror it
%%%            n / p          next / previous puzzle
%%%            s solve, x stop, c clear solver pieces, w write formula, q quit
%%%
%%%    The pieces and the puzzles come from pento.config.  A puzzle is a
%%%    figure of cells, a set of pieces and, for the pento chess board,
%%%    the rule that the dark squares of a piece sit on dark squares.
%%%    The formula for a puzzle is generated here:
%%%
%%%      P(K,O,I,J)   piece K in orientation O with its top left corner
%%%                   at row I, column J (1 based), implies its L cells
%%%      L(K,I,J)     piece K covers cell (I,J); every cell exactly once
%%%
%%%    Solve asserts P(...) for every piece the user has placed and runs
%%%    the configured plugin chain in a separate process; its output is
%%%    captured through a group leader into the log pane, and the first
%%%    model's P(...) atoms put the remaining pieces on the board.
%%% @end

-module(pento_epx).
-behaviour(epxw).

-export([start/0, start/1, run/0, run/1]).
-export([init/1, draw/3, button_press/2, button_release/2, motion/2,
	 key_press/2, handle_info/2, close/1]).
%% pieces of the machinery, also for testing without a window
-export([load_config/1, parse_solve/1, run_varp/2, formula/2,
	 assumptions/1, placements/2, rotate/1, mirror/1, fits/4,
	 orientations/2, select_puzzle/2, layout/1]).

-define(BG,          {44,44,52}).
-define(SQUARE_S,    {118,118,130}).   %% dark square
-define(SQUARE_V,    {236,232,220}).   %% light square
-define(SQUARE,      {214,212,200}).   %% a plain figure's cell
-define(TRAY_BG,     {60,60,70}).
-define(DIM,         {84,84,94}).      %% a piece not in this puzzle
-define(BUTTON,      {90,100,130}).
-define(BUTTON_OFF,  {70,70,80}).
%% text colours carry alpha 0: the glyph supplies the coverage
-define(TEXT,        {0,230,230,230}).
-define(TEXT_DIM,    {0,150,150,160}).
-define(TEXT_DARK,   {0,20,20,20}).
-define(MARGIN,      16).
-define(TITLE_H,     22).
-define(TRAY_COLS,   3).
-define(TRAY_PAD,    6).
-define(BUTTON_H,    30).
-define(LOG_LINES,   8).
-define(TICK_MS,     500).

%% A piece.  cells are {Row,Col,s|v} with min row and col 0, the s/v
%% tag is the square the cell sits on in the chess puzzle.  pos is tray,
%% {board,R,C} (board cell of the cells' origin) or {drag,X,Y} (window
%% pixel of the origin cell's corner).  by says who put it there.
-record(piece, { id, name, color, cells, pos = tray, by = user }).

%% A puzzle: the figure as a set of {R,C} (0 based), the pieces in play
%% and whether each must be used (required) or may be (any).
-record(puzzle,
	{
	 name,
	 colored = false,
	 mode = required,     %% required | any
	 pieces = [],         %% piece ids in play
	 rows, cols,
	 region,              %% #{ {R,C} => true }
	 orient,              %% #{ Id => [{O,Cells}] }
	 formula              %% cached text, undefined until needed
	}).

-record(st,
	{
	 dir,                 %% directory of the config file
	 solve,               %% plugin chain, a string
	 cell0,               %% configured cell size
	 board_px,            %% the square the board is fitted into
	 puzzles = [],        %% [#puzzle{}]
	 pz = 1,              %% index of the current puzzle
	 cell,                %% cell size of the current board
	 tcell,               %% tray cell size
	 board_x, board_y,    %% top left of the current board
	 area_x, area_y,      %% top left of the board area
	 tray_x, tray_y, slot,
	 buttons = [],        %% [{Name,Label,{X,Y,W,H}}]
	 log_y, log_h,
	 width, height,
	 pieces = #{},        %% Id => #piece{}
	 order = [],          %% draw order, last on top
	 slots = [],          %% tray slots, the config order, fixed
	 drag,                %% undefined | {Id,DX,DY}
	 selected,            %% last touched piece
	 pointer,             %% last known pointer position {X,Y}
	 font, small,
	 solver,              %% undefined | {Pid,Mon,Ref,Io,T0}
	 log = [],            %% last lines, newest first
	 status = ""
	}).

%%%===================================================================
%%% API
%%%===================================================================

start() -> start([]).

%% Opts: [{config, File}]
start(Opts) ->
    application:ensure_all_started(epx),
    application:ensure_all_started(varp),
    Config = proplists:get_value(config, Opts, default_config()),
    St0 = load_config(Config),
    St = select_puzzle(1, layout(St0)),
    epxw:start(?MODULE, [{state,St}],
	       [{title,"Pento"},
		{screen_color, ?BG},
		%% the status bar (18) sits below the content; the view
		%% is exactly the content, so no scroll bars appear
		{width, St#st.width}, {height, St#st.height + 18},
		{view_width, St#st.width}, {view_height, St#st.height}]).

%% from the command line: wait for the window and halt
run() -> run([]).
run(Opts) ->
    case start(Opts) of
	{ok,Pid} ->
	    Mon = erlang:monitor(process, Pid),
	    receive {'DOWN',Mon,process,Pid,_} -> halt(0) end;
	Error ->
	    io:format("pento_epx: ~p\n", [Error]),
	    halt(1)
    end.

default_config() ->
    Dir = case code:which(?MODULE) of
	      Beam when is_list(Beam) ->
		  filename:dirname(Beam);
	      _ -> "."
	  end,
    filename:join(Dir, "pento.config").

%%%===================================================================
%%% Configuration
%%%===================================================================

load_config(File) ->
    case file:consult(File) of
	{ok,Terms} ->
	    Dir = filename:dirname(filename:absname(File)),
	    Cell = case lists:keyfind(cell, 1, Terms) of
		       {cell,Sz} -> Sz;
		       false -> 44
		   end,
	    BoardPx = case lists:keyfind(board_px, 1, Terms) of
			  {board_px,Px} -> Px;
			  false -> 10*Cell
		      end,
	    Solve = case lists:keyfind(solve, 1, Terms) of
			{solve,S} -> S;
			false -> "sat bj --timeout=60"
		    end,
	    Ps = [#piece{ id = Id, name = Name, color = Color,
			  cells = shape_cells(Shape) }
		  || {piece,Id,Name,Color,Shape} <- Terms],
	    Ps =/= [] orelse erlang:error({config, File, no_pieces}),
	    Pieces = maps:from_list([{P#piece.id,P} || P <- Ps]),
	    Puzzles = [puzzle(Name, Opts, Rows, Ps)
		       || {puzzle,Name,Opts,Rows} <- Terms],
	    Puzzles =/= [] orelse erlang:error({config, File, no_puzzles}),
	    #st{ dir = Dir, solve = Solve, cell0 = Cell, board_px = BoardPx,
		 pieces = Pieces, order = [P#piece.id || P <- Ps],
		 slots = [P#piece.id || P <- Ps], puzzles = Puzzles };
	{error,Reason} ->
	    erlang:error({config, File, Reason})
    end.

%% ["VS","SV"] -> [{0,0,v},{0,1,s},{1,0,s},{1,1,v}]
shape_cells(Rows) ->
    normalize(
      lists:append(
	[[{R,C,tag(Ch)} || {C,Ch} <- enumerate(Row), Ch =/= $.]
	 || {R,Row} <- enumerate(Rows)])).

tag($S) -> s;
tag($V) -> v;
tag($s) -> s;
tag($v) -> v.

enumerate(L) -> lists:zip(lists:seq(0, length(L)-1), L).

puzzle(Name, Opts, Rows, Ps) ->
    Colored = lists:member(colored, Opts),
    All = [P#piece.id || P <- Ps],
    ByName = fun(Names) ->
		     [P#piece.id || N <- Names, P <- Ps, P#piece.name =:= N]
	     end,
    {Mode,Ids} =
	case proplists:get_value(pieces, Opts, all) of
	    all -> {required, All};
	    any -> {any, All};
	    {except,Names} -> {required, All -- ByName(Names)};
	    Names when is_list(Names) -> {required, ByName(Names)}
	end,
    Region = maps:from_list(
	       [{{R,C},true} || {R,Row} <- enumerate(Rows),
				{C,Ch} <- enumerate(Row), Ch =:= $#]),
    Orient = maps:from_list(
	       [{P#piece.id, orientations(P#piece.cells, Colored)}
		|| P <- Ps, lists:member(P#piece.id, Ids)]),
    #puzzle{ name = Name, colored = Colored, mode = Mode, pieces = Ids,
	     rows = length(Rows), cols = lists:max([length(R) || R <- Rows]),
	     region = Region, orient = Orient }.

current(St) -> lists:nth(St#st.pz, St#st.puzzles).

%%%===================================================================
%%% Geometry of pieces
%%%===================================================================

normalize(Cells) ->
    R0 = lists:min([R || {R,_,_} <- Cells]),
    C0 = lists:min([C || {_,C,_} <- Cells]),
    lists:sort([{R-R0,C-C0,T} || {R,C,T} <- Cells]).

%% a quarter turn clockwise: (r,c) -> (c,-r)
rotate(Cells) -> normalize([{C,-R,T} || {R,C,T} <- Cells]).

mirror(Cells) -> normalize([{R,-C,T} || {R,C,T} <- Cells]).

%% the square at board cell (R,C), 0 based: dark at the top left
parity_tag(R, C) when (R+C) rem 2 =:= 0 -> s;
parity_tag(_, _) -> v.

%% The distinct orientations of a piece, numbered from 1: the eight
%% transforms, less the duplicates.  On the chess board two shapes
%% with the colours swapped are different orientations, elsewhere
%% only the geometry counts.
orientations(Cells, Colored) ->
    R = fun rotate/1, M = fun mirror/1,
    Ts = [Cells, R(Cells), R(R(Cells)), R(R(R(Cells))),
	  M(Cells), R(M(Cells)), R(R(M(Cells))), R(R(R(M(Cells))))],
    {Os,_} = lists:foldl(
	       fun(Cs, {Acc,Seen}) ->
		       Key = orient_key(Cs, Colored),
		       case maps:is_key(Key, Seen) of
			   true -> {Acc,Seen};
			   false -> {[{length(Acc)+1,Cs}|Acc], Seen#{ Key => true }}
		       end
	       end, {[],#{}}, Ts),
    lists:reverse(Os).

orient_key(Cells, true) -> Cells;
orient_key(Cells, false) -> [{R,C} || {R,C,_} <- Cells].

%% can Cells sit with their origin at board cell (R,C)?  Inside the
%% figure, on squares of the right colour when that matters, and free
%% of other pieces.
fits(Cells, {R,C}, Occupied, St) ->
    Pz = current(St),
    lists:all(
      fun({Dr,Dc,T}) ->
	      Br = R+Dr, Bc = C+Dc,
	      maps:is_key({Br,Bc}, Pz#puzzle.region) andalso
	      (not Pz#puzzle.colored orelse parity_tag(Br, Bc) =:= T) andalso
	      not maps:is_key({Br,Bc}, Occupied)
      end, Cells).

%% board cell -> piece id, for every piece on the board but Except
occupied(St, Except) ->
    maps:fold(
      fun(Id, #piece{pos={board,R,C},cells=Cells}, Acc) when Id =/= Except ->
	      lists:foldl(fun({Dr,Dc,_}, A) -> A#{ {R+Dr,C+Dc} => Id } end,
			  Acc, Cells);
	 (_, _, Acc) -> Acc
      end, #{}, St#st.pieces).

in_play(Id, St) ->
    lists:member(Id, (current(St))#puzzle.pieces).

%%%===================================================================
%%% The formula of a puzzle
%%%===================================================================

%% every way to put piece K on the figure: {K,O,I,J,[{I1,J1}]} with
%% I,J 1 based like the formula
placements_of(K, Pz) ->
    Os = maps:get(K, Pz#puzzle.orient),
    [{K,O,I+1,J+1,[{I+Dr+1,J+Dc+1} || {Dr,Dc,_} <- Cells]}
     || {O,Cells} <- Os,
	I <- lists:seq(0, Pz#puzzle.rows-1),
	J <- lists:seq(0, Pz#puzzle.cols-1),
	lists:all(fun({Dr,Dc,T}) ->
			  maps:is_key({I+Dr,J+Dc}, Pz#puzzle.region) andalso
			      (not Pz#puzzle.colored orelse
			       parity_tag(I+Dr, J+Dc) =:= T)
		  end, Cells)].

%% The formula as text.  Colours never appear: a placement that puts a
%% dark cell on a light square is simply not generated.
formula(Pz, _St) ->
    Ks = Pz#puzzle.pieces,
    Pls = lists:append([placements_of(K, Pz) || K <- Ks]),
    P = fun({K,O,I,J,_}) -> io_lib:format("P(~w,~w,~w,~w)", [K,O,I,J]) end,
    L = fun(K, {I,J}) -> io_lib:format("L(~w,~w,~w)", [K,I,J]) end,
    %% a placement covers its cells
    Covers = [["(", P(Pl), " -> (", lists:join(" && ", [L(K, C) || C <- Cs]),
	       ")) &&\n"] || Pl={K,_,_,_,Cs} <- Pls],
    %% each piece once, or at most once (a counting quantifier over a
    %% single argument is written as the argument: varp's bld_args
    %% does not take one)
    Once = [case {[P(Pl) || Pl={K1,_,_,_,_} <- Pls, K1 =:= K], Pz#puzzle.mode} of
		{[],required} -> "false &&\n";
		{[],any} -> "";
		{[One],required} -> [One, " &&\n"];
		{[_],any} -> "";
		{Ps,required} -> ["[ONE](", lists:join(",", Ps), ") &&\n"];
		{Ps,any} -> ["[LTE 1](", lists:join(",", Ps), ") &&\n"]
	    end || K <- Ks],
    %% a covered cell comes from one of the placements covering it
    ByCell = lists:foldl(
	       fun(Pl={K,_,_,_,Cs}, Acc) ->
		       lists:foldl(fun(C, A) ->
					   maps:update_with({K,C}, fun(L0) -> [Pl|L0] end,
							    [Pl], A)
				   end, Acc, Cs)
	       end, #{}, Pls),
    %% (and a cell no placement of K reaches is never K's)
    Cells = lists:sort([{R+1,C+1} || {R,C} <- maps:keys(Pz#puzzle.region)]),
    Reasons = [case maps:get({K,C}, ByCell, []) of
		   [] -> ["!", L(K, C), " &&\n"];
		   Pls1 -> ["(", L(K, C), " -> ", any_of([P(Pl) || Pl <- Pls1]), ") &&\n"]
	       end || K <- Ks, C <- Cells],
    %% every cell of the figure is covered exactly once
    Exact = [case [L(K, Cell) || K <- Ks] of
		 [One] -> [One, " &&\n"];
		 Ls -> ["[ONE](", lists:join(",", Ls), ") &&\n"]
	     end || Cell <- Cells],
    lists:flatten([Covers, Once, Reasons, Exact, "true\n"]).

any_of([One]) -> One;
any_of(Ps) -> ["[ANY](", lists:join(",", Ps), ")"].

%% the formula of the current puzzle, generated once
puzzle_formula(St) ->
    Pz = current(St),
    case Pz#puzzle.formula of
	undefined ->
	    F = formula(Pz, St),
	    Pz1 = Pz#puzzle{ formula = F },
	    Puzzles = lists:sublist(St#st.puzzles, St#st.pz-1) ++ [Pz1] ++
		lists:nthtail(St#st.pz, St#st.puzzles),
	    {F, St#st{ puzzles = Puzzles }};
	F ->
	    {F, St}
    end.

%% key w: the formula of the current puzzle on disk, for the varp CLI
write_formula(St) ->
    {F, St1} = puzzle_formula(St),
    Pz = current(St1),
    Name = [case Ch of $\s -> $_; _ -> Ch end || Ch <- Pz#puzzle.name],
    File = filename:join(St1#st.dir, "puzzle_" ++ Name ++ ".varp"),
    case file:write_file(File, F) of
	ok -> log(["wrote ", File], St1);
	{error,E} -> log(io_lib:format("cannot write ~s: ~p", [File, E]), St1)
    end.

%%%===================================================================
%%% The solver side
%%%===================================================================

%% "P(1,2,7,7) && P(3,8,7,1)" for the pieces the user placed, or "true"
assumptions(St) ->
    As = lists:append(
	   [case orientation_of(P, St) of
		{ok,O} ->
		    [io_lib:format("P(~w,~w,~w,~w)", [Id,O,R+1,C+1])];
		error ->
		    []
	    end
	    || #piece{id=Id,pos={board,R,C},by=user}=P
		   <- maps:values(St#st.pieces)]),
    case As of
	[] -> "true";
	_ -> lists:flatten(lists:join(" && ", lists:sort(As)))
    end.

orientation_of(#piece{id=Id,cells=Cells}, St) ->
    Pz = current(St),
    Key = orient_key(Cells, Pz#puzzle.colored),
    Os = maps:get(Id, Pz#puzzle.orient, []),
    case [O || {O,Cs} <- Os, orient_key(Cs, Pz#puzzle.colored) =:= Key] of
	[O|_] -> {ok,O};
	[] -> error
    end.

%% the plugin chain on command line form, parsed with the plugins'
%% own option specs: "sat saturate -k=1 bj --timeout=60"
parse_solve(Str) ->
    Plugins = varp:load_plugins(),
    parse_solve_(string:lexemes(Str, " \t\n"), Plugins, []).

parse_solve_([], _Plugins, Acc) ->
    lists:reverse(Acc);
parse_solve_([Tok|Toks], Plugins, Acc) ->
    case maps:get(Tok, Plugins, undefined) of
	undefined ->
	    erlang:error({unknown_plugin, Tok});
	Mod ->
	    Infos = Mod:options(),
	    Spec = maps:put('$plugin', Mod, varp_option:options_spec(Infos)),
	    Opts = varp_option:default_opts(Infos),
	    {Toks1,Opts1,_} = varp_option:process_args(Toks, Spec, Opts, []),
	    parse_solve_(Toks1, Plugins, [{Mod,Opts1}|Acc])
    end.

%% runs in the solver process
run_varp(Sources, Solve) ->
    GOpts0 = varp:load_option_list([{print,false},{undeclared,none},
				    {log,info}]),
    GOpts = GOpts0#{ meta => #{} },
    case varp:load(Sources, GOpts) of
	{ok,Assignments,Formula,GOpts1} ->
	    Do = parse_solve(Solve),
	    case varp:do_run(Do, Assignments, Formula, GOpts1) of
		{R,Models,_Bs} when is_list(Models) -> {done,R,Models};
		{R,_,_} -> {done,R,[]};
		Other -> {done,Other,[]}
	    end;
	Error ->
	    {error,Error}
    end.

%% the model's P(K,O,I,J) atoms as {Id,{board,R,C},Cells}
placements(Model, St) ->
    Pz = current(St),
    [{K, {board,I-1,J-1}, Cells}
     || {{p,<<"P">>,[K,O,I,J]},true} <- Model,
	{O1,Cells} <- maps:get(K, Pz#puzzle.orient, []), O1 =:= O].

start_solver(St) when St#st.solver =/= undefined ->
    St;
start_solver(St0) ->
    Self = self(),
    Ref = make_ref(),
    {Formula, St} = puzzle_formula(St0),
    Assume = assumptions(St),
    Sources = [{text,Assume},{text,Formula}],
    Solve = St#st.solve,
    Io = spawn(fun() -> io_server(Self, Ref) end),
    Pid = spawn(fun() ->
			group_leader(Io, self()),
			Res = try run_varp(Sources, Solve)
			      catch Class:Reason:Stack ->
				      {crash,Class,Reason,Stack}
			      end,
			Self ! {solver,Ref,Res}
		end),
    Mon = erlang:monitor(process, Pid),
    erlang:send_after(?TICK_MS, Self, {tick,Ref}),
    Fixed = [P || #piece{pos={board,_,_},by=user}=P <- maps:values(St#st.pieces)],
    Unmatched = [P#piece.name || P <- Fixed, orientation_of(P, St) =:= error],
    St1 = case Unmatched of
	      [] -> St;
	      _ -> log(io_lib:format("no orientation in the formula for ~s, not fixed",
				     [lists:join(", ", Unmatched)]), St)
	  end,
    St2 = log(io_lib:format("solve ~s: ~w piece(s) fixed",
			    [(current(St))#puzzle.name,
			     length(Fixed) - length(Unmatched)]),
	      log(["assume: ", Assume], St1)),
    set_status(St2#st{ solver = {Pid,Mon,Ref,Io,erlang:monotonic_time()} }).

stop_solver(St=#st{ solver = undefined }) ->
    St;
stop_solver(St=#st{ solver = {Pid,Mon,_Ref,Io,_T0} }) ->
    erlang:demonitor(Mon, [flush]),
    exit(Pid, kill),
    Io ! stop,
    set_status(log("solver stopped", St#st{ solver = undefined })).

solver_done(Res, St=#st{ solver = {_Pid,Mon,_Ref,Io,T0} }) ->
    erlang:demonitor(Mon, [flush]),
    Io ! stop,
    Secs = (erlang:monotonic_time() - T0) / erlang:convert_time_unit(1, second, native),
    St1 = St#st{ solver = undefined },
    St2 = case Res of
	      {done,_R,[Model|_]} ->
		  place_model(Model,
			      log(io_lib:format("SAT in ~.1f s", [Secs]), St1));
	      {done,inconsistent,[]} ->
		  log(io_lib:format("UNSAT after ~.1f s: no solution with these pieces", [Secs]), St1);
	      {done,{abort,timeout},[]} ->
		  log(io_lib:format("timeout after ~.1f s", [Secs]), St1);
	      {done,R,[]} ->
		  log(io_lib:format("no model (~p) after ~.1f s", [R,Secs]), St1);
	      {error,E} ->
		  log(io_lib:format("load error: ~p", [E]), St1);
	      {crash,C,R,_Stack} ->
		  log(io_lib:format("solver crashed: ~p:~p", [C,R]), St1);
	      {'DOWN',Reason} ->
		  log(io_lib:format("solver died: ~p", [Reason]), St1)
	  end,
    set_status(St2).

%% solver pieces from the model; user pieces stay as they are, pieces
%% the model leaves out (mode any) go back to the tray
place_model(Model, St) ->
    Ps = placements(Model, St),
    Placed = maps:from_list([{Id,{Pos,Cells}} || {Id,Pos,Cells} <- Ps]),
    Pieces =
	maps:map(
	  fun(_, P=#piece{pos={board,_,_},by=user}) -> P;
	     (Id, P) ->
		  case maps:find(Id, Placed) of
		      {ok,{Pos,Cells}} ->
			  P#piece{ pos = Pos, cells = Cells, by = solver };
		      error ->
			  P#piece{ pos = tray, by = user }
		  end
	  end, St#st.pieces),
    St#st{ pieces = Pieces }.

%% a group leader that turns the solver's output into log lines
io_server(Owner, Ref) ->
    io_loop(Owner, Ref, []).

io_loop(Owner, Ref, Acc) ->
    receive
	{io_request,From,ReplyAs,Req} ->
	    {Reply,Acc1} = io_request(Req, Acc, Owner, Ref),
	    From ! {io_reply,ReplyAs,Reply},
	    io_loop(Owner, Ref, Acc1);
	stop ->
	    case Acc of
		[] -> ok;
		_ -> Owner ! {solver_log,Ref,lists:reverse(Acc)}
	    end
    end.

io_request({put_chars,_Enc,Chars}, Acc, Owner, Ref) ->
    {ok, emit(Chars, Acc, Owner, Ref)};
io_request({put_chars,_Enc,M,F,A}, Acc, Owner, Ref) ->
    {ok, emit(safe_apply(M,F,A), Acc, Owner, Ref)};
io_request({put_chars,Chars}, Acc, Owner, Ref) ->
    {ok, emit(Chars, Acc, Owner, Ref)};
io_request({put_chars,M,F,A}, Acc, Owner, Ref) ->
    {ok, emit(safe_apply(M,F,A), Acc, Owner, Ref)};
io_request({requests,Reqs}, Acc, Owner, Ref) ->
    lists:foldl(fun(R, {_,A}) -> io_request(R, A, Owner, Ref) end,
		{ok,Acc}, Reqs);
io_request({get_geometry,_}, Acc, _Owner, _Ref) ->
    {{error,enotsup}, Acc};
io_request(_, Acc, _Owner, _Ref) ->
    {{error,request}, Acc}.

safe_apply(M, F, A) ->
    try apply(M, F, A)
    catch _:Reason -> io_lib:format("~p", [Reason])
    end.

%% Acc holds the current line reversed
emit(Chars, Acc, Owner, Ref) ->
    Text = case unicode:characters_to_list(Chars) of
	       L when is_list(L) -> L;
	       _ -> lists:flatten(io_lib:format("~p", [Chars]))
	   end,
    lists:foldl(
      fun($\n, A) -> Owner ! {solver_log,Ref,lists:reverse(A)}, [];
	 (Ch, A) -> [Ch|A]
      end, Acc, Text).

%%%===================================================================
%%% epxw callbacks
%%%===================================================================

init(Opts) ->
    St0 = proplists:get_value(state, Opts),
    {ok,Font} = epx_font:match([{name,"Arial"},{size,14},{slant,roman}]),
    {ok,Small} = epx_font:match([{name,"Arial"},{size,10},{slant,roman}]),
    St = St0#st{ font = Font, small = Small },
    %% motion is always on: the keys act on the piece under the pointer
    epxw:enable_motion(),
    {ok, set_status(St)}.

close(St) ->
    stop_solver(St),
    {stop,normal,St}.

%% window geometry: a square board area, the tray to the right of it
layout(St=#st{ cell0 = Cell0, board_px = BoardPx }) ->
    M = ?MARGIN,
    AreaX = M, AreaY = M + ?TITLE_H,
    TCell = max(12, Cell0 div 2),
    Slot = 5*TCell + 2*?TRAY_PAD,
    TrayX = AreaX + BoardPx + M,
    TrayY = AreaY,
    NPieces = maps:size(St#st.pieces),
    TrayRows = (NPieces + ?TRAY_COLS - 1) div ?TRAY_COLS,
    TrayH = TrayRows*Slot,
    ButtonY = AreaY + BoardPx + 12,
    Gap = 6,
    Specs = [{prev,"<",30},{solve,"Solve",64},{stop,"Stop",64},
	     {clear,"Clear",64},{reset,"Reset",64},{next,">",30}],
    {Buttons,_} = lists:mapfoldl(
		    fun({Name,Label,W}, X) ->
			    {{Name,Label,{X,ButtonY,W,?BUTTON_H}}, X+W+Gap}
		    end, AreaX, Specs),
    LogY = ButtonY + ?BUTTON_H + 12,
    LogH = ?LOG_LINES*16 + 8,
    Width = TrayX + ?TRAY_COLS*Slot + M,
    Height = max(LogY + LogH, TrayY + TrayH) + M,
    St#st{ tcell = TCell, area_x = AreaX, area_y = AreaY,
	   tray_x = TrayX, tray_y = TrayY, slot = Slot,
	   buttons = Buttons, log_y = LogY, log_h = LogH,
	   width = Width, height = Height }.

%% make puzzle N the current one: every piece back in the tray, the
%% board fitted into the board area
select_puzzle(N, St0) ->
    St = stop_solver(St0),
    Pz = lists:nth(N, St#st.puzzles),
    Cell = lists:min([St#st.cell0, St#st.board_px div Pz#puzzle.cols,
		      St#st.board_px div Pz#puzzle.rows]),
    BoardX = St#st.area_x + (St#st.board_px - Pz#puzzle.cols*Cell) div 2,
    BoardY = St#st.area_y + (St#st.board_px - Pz#puzzle.rows*Cell) div 2,
    Pieces = maps:map(fun(_, P) -> P#piece{ pos = tray, by = user } end,
		      St#st.pieces),
    St1 = St#st{ pz = N, cell = Cell, board_x = BoardX, board_y = BoardY,
		 pieces = Pieces, drag = undefined, selected = undefined },
    case St1#st.font of
	undefined -> St1;      %% before the window exists
	_ -> epxw:invalidate(), set_status(St1)
    end.

draw(Pixels, _Dirty, St) ->
    epx_gc:set_fill_style(solid),
    draw_title(Pixels, St),
    draw_board(Pixels, St),
    draw_tray(Pixels, St),
    lists:foreach(fun(Id) -> draw_piece(Pixels, maps:get(Id, St#st.pieces), St) end,
		  St#st.order),
    draw_buttons(Pixels, St),
    draw_log(Pixels, St),
    St.

draw_title(Pixels, St) ->
    Pz = current(St),
    N = length(St#st.puzzles),
    Title = io_lib:format("~w/~w  ~s   (~s~s)",
			  [St#st.pz, N, Pz#puzzle.name,
			   case Pz#puzzle.mode of
			       required -> io_lib:format("~w pieces", [length(Pz#puzzle.pieces)]);
			       any -> "any pieces"
			   end,
			   if Pz#puzzle.colored -> ", colours match"; true -> "" end]),
    text(Pixels, St#st.font, St#st.area_x, ?MARGIN, Title, ?TEXT).

draw_board(Pixels, St=#st{ cell = Cell }) ->
    Pz = current(St),
    X0 = St#st.board_x, Y0 = St#st.board_y,
    fill(Pixels, X0-2, Y0-2, Pz#puzzle.cols*Cell+4, Pz#puzzle.rows*Cell+4, {20,20,24}),
    lists:foreach(
      fun({R,C}) ->
	      Color = case Pz#puzzle.colored of
			  true -> case parity_tag(R, C) of s -> ?SQUARE_S; v -> ?SQUARE_V end;
			  false -> ?SQUARE
		      end,
	      fill(Pixels, X0+C*Cell+1, Y0+R*Cell+1, Cell-1, Cell-1, Color)
      end, maps:keys(Pz#puzzle.region)).

draw_tray(Pixels, St=#st{ slot = Slot }) ->
    N = length(St#st.slots),
    [begin
	 {X,Y} = slot_xy(I, St),
	 fill(Pixels, X+1, Y+1, Slot-2, Slot-2, ?TRAY_BG)
     end || I <- lists:seq(0, N-1)],
    ok.

slot_xy(I, St=#st{ slot = Slot }) ->
    {St#st.tray_x + (I rem ?TRAY_COLS)*Slot,
     St#st.tray_y + (I div ?TRAY_COLS)*Slot}.

%% where a piece is drawn: {X,Y,CellSize}
piece_xy(#piece{pos=tray,id=Id}, St) ->
    I = index_of(Id, St#st.slots),
    {X,Y} = slot_xy(I, St),
    {X+?TRAY_PAD, Y+?TRAY_PAD, St#st.tcell};
piece_xy(#piece{pos={board,R,C}}, St) ->
    {St#st.board_x + C*St#st.cell, St#st.board_y + R*St#st.cell, St#st.cell};
piece_xy(#piece{pos={drag,X,Y}}, St) ->
    {X, Y, St#st.cell}.

index_of(X, L) -> index_of(X, L, 0).
index_of(X, [X|_], I) -> I;
index_of(X, [_|T], I) -> index_of(X, T, I+1).

draw_piece(Pixels, P=#piece{id=Id,cells=Cells,color=Color,by=By}, St) ->
    {X0,Y0,Sz} = piece_xy(P, St),
    Pz = current(St),
    InPlay = in_play(Id, St),
    Base = if not InPlay -> ?DIM;
	      By =:= solver -> lighten(Color);
	      true -> Color
	   end,
    lists:foreach(
      fun({R,C,T}) ->
	      Col = case {InPlay andalso Pz#puzzle.colored, T} of
			{true,s} -> darken(Base);
			_ -> Base
		    end,
	      fill(Pixels, X0+C*Sz+1, Y0+R*Sz+1, Sz-2, Sz-2, Col)
      end, Cells),
    %% the name on the first cell
    {R1,C1,_} = hd(Cells),
    Font = if Sz >= 30 -> St#st.font; true -> St#st.small end,
    text(Pixels, Font, X0+C1*Sz+4, Y0+R1*Sz+2, P#piece.name,
	 if InPlay -> ?TEXT_DARK; true -> ?TEXT_DIM end),
    ok.

draw_buttons(Pixels, St) ->
    Solving = St#st.solver =/= undefined,
    lists:foreach(
      fun({Name,Label,{X,Y,W,H}}) ->
	      Active = case Name of
			   solve -> not Solving;
			   stop -> Solving;
			   _ -> true
		       end,
	      fill(Pixels, X, Y, W, H, if Active -> ?BUTTON; true -> ?BUTTON_OFF end),
	      {TW,_} = epx_font:dimension(St#st.font, Label),
	      text(Pixels, St#st.font, X + (W-TW) div 2, Y+6, Label,
		   if Active -> ?TEXT; true -> ?TEXT_DIM end)
      end, St#st.buttons).

draw_log(Pixels, St) ->
    X = St#st.area_x, Y = St#st.log_y,
    W = St#st.board_px,
    fill(Pixels, X, Y, W, St#st.log_h, {30,30,36}),
    Lines = lists:reverse(lists:sublist(St#st.log, ?LOG_LINES)),
    lists:foldl(
      fun(Line, Ly) ->
	      text(Pixels, St#st.small, X+4, Ly, Line, ?TEXT),
	      Ly + 16
      end, Y+4, Lines),
    ok.

fill(Pixels, X, Y, W, H, Color) ->
    epx_gc:set_fill_color(Color),
    epx:draw_rectangle(Pixels, X, Y, W, H).

text(Pixels, Font, X, Y, Text, Color) ->
    epx_gc:set_font(Font),
    epx_gc:set_foreground_color(Color),
    Ascent = epx:font_info(Font, ascent),
    epx_gc:set_fill_style(none),
    epx:draw_string(Pixels, X, Y+Ascent, lists:flatten(Text)),
    epx_gc:set_fill_style(solid).

darken({R,G,B}) -> {R*3 div 4, G*3 div 4, B*3 div 4}.
lighten({R,G,B}) -> {(R+255) div 2, (G+255) div 2, (B+255) div 2}.

%%% ---- input ----------------------------------------------------

%% epxw gives the button as a list, {button_press,[left],Pos}
button_press({button_press,B,Pos}, St) ->
    press(button(B), Pos, St);
button_press(_, St) ->
    St.

button([B|_]) -> B;
button(B) -> B.

press(left, Pos, St) ->
    {X,Y} = xy(Pos),
    case button_at(X, Y, St) of
	{ok,Name} -> command(Name, St);
	error ->
	    case piece_at(X, Y, St) of
		{ok,Id} -> grab(Id, X, Y, St);
		error -> St
	    end
    end;
press(right, Pos, St) ->
    turn(fun rotate/1, Pos, St);
press(middle, Pos, St) ->
    turn(fun mirror/1, Pos, St);
press(wheel_up, Pos, St) ->
    turn(fun rotate/1, Pos, St);
press(wheel_down, Pos, St) ->
    turn(fun(Cs) -> rotate(rotate(rotate(Cs))) end, Pos, St);
press(_, _Pos, St) ->
    St.

button_release({button_release,B,Pos}, St=#st{ drag = {Id,_,_} }) ->
    case button(B) of
	left ->
	    {X,Y} = xy(Pos),
	    drop(Id, X, Y, St);
	_ ->
	    St
    end;
button_release(_, St) ->
    St.

motion({motion,_Buttons,Pos}, St=#st{ drag = {Id,DX,DY} }) ->
    {X,Y} = xy(Pos),
    P = maps:get(Id, St#st.pieces),
    St1 = St#st{ pieces = (St#st.pieces)#{ Id => P#piece{ pos = {drag,X-DX,Y-DY} } },
		 pointer = {X,Y} },
    epxw:invalidate(),
    St1;
motion({motion,_Buttons,Pos}, St) ->
    St#st{ pointer = xy(Pos) };
motion(_, St) ->
    St.

key_press({key_press,Sym,_Mods,_Code}, St) ->
    case Sym of
	$r -> turn_selected(fun rotate/1, St);
	$R -> turn_selected(fun(Cs) -> rotate(rotate(rotate(Cs))) end, St);
	$m -> turn_selected(fun mirror/1, St);
	$n -> command(next, St);
	$p -> command(prev, St);
	$s -> command(solve, St);
	$x -> command(stop, St);
	$c -> command(clear, St);
	$w -> write_formula(St);
	$q -> stop_solver(St), exit(normal);
	_ -> St
    end;
key_press(_, St) ->
    St.

xy(Pos) -> {trunc(element(1, Pos)), trunc(element(2, Pos))}.

button_at(X, Y, St) ->
    case [Name || {Name,_,{Bx,By,Bw,Bh}} <- St#st.buttons,
		  X >= Bx, X < Bx+Bw, Y >= By, Y < By+Bh] of
	[Name|_] -> {ok,Name};
	[] -> error
    end.

%% the topmost piece of this puzzle under the pointer
piece_at(X, Y, St) ->
    Hits = [Id || Id <- lists:reverse(St#st.order),
		  in_play(Id, St),
		  hit(maps:get(Id, St#st.pieces), X, Y, St)],
    case Hits of
	[Id|_] -> {ok,Id};
	[] -> error
    end.

hit(P=#piece{cells=Cells}, X, Y, St) ->
    {X0,Y0,Sz} = piece_xy(P, St),
    lists:any(fun({R,C,_}) ->
		      X >= X0+C*Sz andalso X < X0+(C+1)*Sz andalso
		      Y >= Y0+R*Sz andalso Y < Y0+(R+1)*Sz
	      end, Cells).

%% pick a piece up: it follows the pointer at board scale
grab(Id, X, Y, St) ->
    P = maps:get(Id, St#st.pieces),
    Cell = St#st.cell,
    {X0,Y0} =
	case P#piece.pos of
	    {board,_,_} ->
		{Px,Py,_} = piece_xy(P, St),
		{Px,Py};
	    _ ->
		%% from the tray: the pointer lands on the first cell
		{R1,C1,_} = hd(P#piece.cells),
		{X - C1*Cell - Cell div 2, Y - R1*Cell - Cell div 2}
	end,
    P1 = P#piece{ pos = {drag,X0,Y0}, by = user },
    epxw:invalidate(),
    St#st{ pieces = (St#st.pieces)#{ Id => P1 },
	   order = (St#st.order -- [Id]) ++ [Id],
	   drag = {Id,X-X0,Y-Y0}, selected = Id }.

%% let go: onto the board if it fits there, else back to the tray
drop(Id, X, Y, St=#st{ drag = {Id,DX,DY}, cell = Cell }) ->
    P = maps:get(Id, St#st.pieces),
    Pz = current(St),
    Ox = X-DX, Oy = Y-DY,
    C = round((Ox - St#st.board_x) / Cell),
    R = round((Oy - St#st.board_y) / Cell),
    Occupied = occupied(St, Id),
    {Pos,St1} =
	case fits(P#piece.cells, {R,C}, Occupied, St) of
	    true -> {{board,R,C}, St};
	    false ->
		OnBoard = Ox > St#st.board_x - Cell andalso
		    Ox < St#st.board_x + Pz#puzzle.cols*Cell andalso
		    Oy > St#st.board_y - Cell andalso
		    Oy < St#st.board_y + Pz#puzzle.rows*Cell,
		{tray, if OnBoard -> log(why_not(P#piece.cells, {R,C}, Occupied, St), St);
			  true -> St
		       end}
	end,
    epxw:invalidate(),
    set_status(St1#st{ pieces = (St1#st.pieces)#{ Id => P#piece{ pos = Pos } },
		       drag = undefined }).

%% the reason a piece does not fit, for the log
why_not(Cells, {R,C}, Occupied, St) ->
    Pz = current(St),
    Outside = [1 || {Dr,Dc,_} <- Cells,
		    not maps:is_key({R+Dr,C+Dc}, Pz#puzzle.region)],
    Taken = [1 || {Dr,Dc,_} <- Cells, maps:is_key({R+Dr,C+Dc}, Occupied)],
    if Outside =/= [] -> "does not fit: outside the figure";
       Taken =/= [] -> "does not fit: on another piece";
       true -> "does not fit: a dark cell on a light square, or the reverse"
    end.

%% turn the piece under the pointer
turn(Fun, Pos, St) ->
    {X,Y} = xy(Pos),
    case St#st.drag of
	{Id,_,_} -> turn_piece(Fun, Id, St);
	undefined ->
	    case piece_at(X, Y, St) of
		{ok,Id} -> turn_piece(Fun, Id, St#st{ selected = Id });
		error -> St
	    end
    end.

%% a key turns the held piece, else the one under the pointer, else
%% the last one touched
turn_selected(Fun, St) ->
    case St#st.drag of
	{Id,_,_} -> turn_piece(Fun, Id, St);
	undefined ->
	    Under = case St#st.pointer of
			{X,Y} -> piece_at(X, Y, St);
			undefined -> error
		    end,
	    case Under of
		{ok,Id} -> turn_piece(Fun, Id, St#st{ selected = Id });
		error ->
		    case St#st.selected of
			undefined -> St;
			Id -> turn_piece(Fun, Id, St)
		    end
	    end
    end.

%% A piece on the board turns in place when the result fits; on the
%% chess board a turn often moves every cell to the other colour (a
%% piece of even width mirrored, of even height rotated), so the
%% neighbouring cells are tried as well before giving up.
turn_piece(Fun, Id, St) ->
    P = maps:get(Id, St#st.pieces),
    Cells = Fun(P#piece.cells),
    case P#piece.pos of
	{board,R,C} ->
	    Occupied = occupied(St, Id),
	    Shifts = [{0,0},{0,1},{0,-1},{1,0},{-1,0},{1,1},{1,-1},{-1,1},{-1,-1}],
	    case [{R+Dr,C+Dc} || {Dr,Dc} <- Shifts,
				 fits(Cells, {R+Dr,C+Dc}, Occupied, St)] of
		[{R1,C1}|_] ->
		    set_piece(P#piece{ cells = Cells, pos = {board,R1,C1},
				       by = user }, St);
		[] ->
		    log("cannot turn it there", St)
	    end;
	_ ->
	    set_piece(P#piece{ cells = Cells }, St)
    end.

set_piece(P, St) ->
    epxw:invalidate(),
    St#st{ pieces = (St#st.pieces)#{ P#piece.id => P } }.

command(solve, St) ->
    start_solver(St);
command(stop, St) ->
    stop_solver(St);
command(clear, St) ->
    %% solver pieces back to the tray
    Pieces = maps:map(fun(_, P=#piece{by=solver}) -> P#piece{ pos = tray, by = user };
			 (_, P) -> P
		      end, St#st.pieces),
    epxw:invalidate(),
    set_status(St#st{ pieces = Pieces });
command(reset, St) ->
    Pieces = maps:map(fun(_, P) -> P#piece{ pos = tray, by = user } end,
		      St#st.pieces),
    epxw:invalidate(),
    set_status(St#st{ pieces = Pieces, drag = undefined });
command(next, St) ->
    N = length(St#st.puzzles),
    select_puzzle(St#st.pz rem N + 1, St);
command(prev, St) ->
    N = length(St#st.puzzles),
    select_puzzle((St#st.pz + N - 2) rem N + 1, St).

%%% ---- messages from the solver -----------------------------------

handle_info({solver_log,Ref,Line}, St=#st{ solver = {_,_,Ref,_,_} }) ->
    {noreply, log(Line, St)};
handle_info({solver_log,_Ref,Line}, St) ->
    %% a late line from a stopped run
    {noreply, log(Line, St)};
handle_info({solver,Ref,Res}, St=#st{ solver = {_,_,Ref,_,_} }) ->
    {noreply, solver_done(Res, St)};
handle_info({'DOWN',Mon,process,_Pid,Reason}, St=#st{ solver = {_,Mon,_,_,_} }) ->
    {noreply, solver_done({'DOWN',Reason}, St)};
handle_info({tick,Ref}, St=#st{ solver = {_,_,Ref,_,_} }) ->
    erlang:send_after(?TICK_MS, self(), {tick,Ref}),
    epxw:invalidate(),
    {noreply, set_status(St)};
handle_info(_Info, St) ->
    {noreply, St}.

%%% ---- status and log ---------------------------------------------

log(Line, St) ->
    Text = lists:flatten(Line),
    epxw:invalidate(),
    St#st{ log = [Text | lists:sublist(St#st.log, 100)] }.

set_status(St) ->
    OnBoard = [P || P=#piece{pos={board,_,_}} <- maps:values(St#st.pieces)],
    NUser = length([1 || #piece{by=user} <- OnBoard]),
    NSolver = length(OnBoard) - NUser,
    NTray = length((current(St))#puzzle.pieces) - length(OnBoard),
    Text =
	case St#st.solver of
	    {_,_,_,_,T0} ->
		Secs = (erlang:monotonic_time() - T0) /
		    erlang:convert_time_unit(1, second, native),
		io_lib:format("solving... ~.1f s  (~w fixed)", [Secs, NUser]);
	    undefined ->
		io_lib:format("~w placed, ~w by solver, ~w in tray   "
			      "r rotate, m mirror, n/p puzzle, s solve",
			      [NUser, NSolver, NTray])
	end,
    epxw:set_status_text(lists:flatten(Text)),
    St#st{ status = Text }.
