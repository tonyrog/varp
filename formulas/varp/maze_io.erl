-module(maze_io).
-export([file/1, file/2]).
%% -export([input/2]).
-export([output/2]).

-define(WALL_LEFT,  16#01).
-define(WALL_ABOVE, 16#02).
-define(WALL_RIGHT, 16#04).
-define(WALL_BELOW, 16#08).
-define(START,      16#10).
-define(STOP,       16#20).
-define(SOLID,      16#40).

-define(IS_WALL_LEFT(Z),  (((Z) band ?WALL_LEFT) =:= ?WALL_LEFT)).
-define(IS_WALL_RIGHT(Z), (((Z) band ?WALL_RIGHT) =:= ?WALL_RIGHT)).
-define(IS_WALL_ABOVE(Z), (((Z) band ?WALL_ABOVE) =:= ?WALL_ABOVE)).
-define(IS_WALL_BELOW(Z), (((Z) band ?WALL_BELOW) =:= ?WALL_BELOW)).
-define(IS_SOLID(Z),      (((Z) band ?SOLID) =:= ?SOLID)).

-define(NO_WALL_LEFT(Z),  (((Z) band ?WALL_LEFT) =:= 0)).
-define(NO_WALL_RIGHT(Z), (((Z) band ?WALL_RIGHT) =:= 0)).
-define(NO_WALL_ABOVE(Z), (((Z) band ?WALL_ABOVE) =:= 0)).
-define(NO_WALL_BELOW(Z), (((Z) band ?WALL_BELOW) =:= 0)).

-define(IS_FOOD_SMALL(Z), (((Z) band ?FOOD_SMALL) =:= ?FOOD_SMALL)).
-define(IS_FOOD_BIG(Z),   (((Z) band ?FOOD_BIG) =:= ?FOOD_BIG)).

-define(ITE(Cond,Then,Else), if (Cond) -> (Then); true -> (Else) end).

-define(FLAG(Code,Bit,Pred), if (Code) band Bit =:= Bit -> Pred;
				true -> {'not', Pred}
			     end).

-record(out,
	{
	 maze = #{},  %% {integer(),integer()} -> char()
	 start,       %% {integer(),integer()}
	 stop,        %% {integer(),integer()}
	 pos = #{} :: #{ integer() => {integer(),integer()}},
	 dir = #{} :: #{ integer() => 'Left'|'Right'|'Up'|'Down' }
	}).
	 
output(_Fd, Model) ->
    Out = lists:foldl(
	     fun({{p,'Wall',[I,J]},true}, Out) ->
		     Out#out { maze = maps:put({I,J}, $X, Out#out.maze) };
		({{p,'Wall',[I,J]},false}, Out) ->
		     Out#out { maze = maps:put({I,J}, $\s, Out#out.maze) };
		({{p,'Pos',[S,I,J]},true}, Out) ->
		     io:format("~w => (~w,~w)\n", [S,I,J]),
		     Out#out { pos = maps:put(S, {I,J}, Out#out.pos) };
		({{p,'Left',[S]}, true}, Out) ->
		     %% io:format("Left(~w)\n", [S]),
		     Out#out { dir = maps:put(S, 'Left', Out#out.dir) };
		({{p,'Right',[S]}, true}, Out) ->
		     %% io:format("Right(~w)\n", [S]),
		     Out#out { dir = maps:put(S, 'Right', Out#out.dir) };
		({{p,'Up',[S]}, true}, Out) ->
		     %% io:format("Up(~w)\n", [S]),
		     Out#out { dir = maps:put(S, 'Up', Out#out.dir) };
		({{p,'Down',[S]}, true}, Out) ->
		     %% io:format("Down(~w)\n", [S]),
		     Out#out { dir = maps:put(S, 'Down', Out#out.dir) };
		(_, Mi) ->
		     Mi
	     end, #out{}, Model),
    %% io:format("Maze = ~p\n", [Maze]),
    N = lists:max([I || {{p,'Wall',[I,_J]},_} <- Model]),
    M = lists:max([J || {{p,'Wall',[_I,J]},_} <- Model]),
    K = maps:size(Out#out.pos)-1,
    Maze = maps:fold(
	     fun(S, Pos, Mi) ->
		     Char = if S =:= 0 -> $@;
			       S =:= K -> $#;
			       true -> $.
			    end,
		     %% io:format("~w => ~w\n", [S, Pos]),
		     %% Char = if S > 9 -> $A+(S-10);
		     %% true -> S+$0
		     %% end,
		     maps:put(Pos, Char, Mi)
	     end, Out#out.maze, Out#out.pos),

    lists:foreach(
      fun(I) ->
	      lists:foreach(
		fun(J) ->
			io:put_chars([maps:get({I,J},Maze)])
		end, lists:seq(1, M)),
	      io:put_chars("\n")
      end, lists:seq(1, N)),
    ok.

%% Convert ascii maze into bit flag version 
ascii_to_data(Rs=[Xs,Ys,Zs|_]) ->
    ascii_to_data(Xs,Ys,Zs,Rs,[],[]).

ascii_to_data([_,_],[_,_],[_,_],[_|Rs=[Xs,Ys,Zs|_]],RAcc,Acc) ->
    ascii_to_data(Xs,Ys,Zs,Rs,[],[RAcc|Acc]);
ascii_to_data([_,_],[_,_],[_,_],[_,_,_],RAcc,Acc) ->
    lists:reverse([RAcc|Acc]);
ascii_to_data([_X1|Xs=[X2,_X3|_]],
	      [Y1|Ys=[Y2,Y3|_]],
	      [_Z1|Zs=[Z2,_Z3|_]],Rs,RAcc,Acc) ->
    Walls =
	?ITE(X2 =:= $X orelse X2 =:= $O,?WALL_ABOVE,0) bor
	?ITE(Y1 =:= $X orelse Y1 =:= $O,?WALL_LEFT,0)  bor
	?ITE(Y3 =:= $X orelse Y3 =:= $O,?WALL_RIGHT,0) bor
	?ITE(Z2 =:= $X orelse Z2 =:= $O,?WALL_BELOW,0),
    Code = case Y2 of
	       $O -> 0;
	       $X -> ?SOLID;
	       $\s -> Walls;
	       $@  -> Walls bor ?START;
	       $&  -> Walls bor ?STOP
	   end,
    ascii_to_data(Xs,Ys,Zs,Rs,[Code|RAcc],Acc).

%% pacman maze style
maze1([R|Rs]) ->
    maze1(R, Rs, 1, 1, []).

maze1([Code|Ds], Rs, I, J, Acc) ->
    Acc1 = [{'ALL',[
		    ?FLAG(Code, ?WALL_LEFT,  {p,'L',[I,J]}),
		    ?FLAG(Code, ?WALL_ABOVE, {p,'U',[I,J]}),
		    ?FLAG(Code, ?WALL_RIGHT, {p,'R',[I,J]}),
		    ?FLAG(Code, ?WALL_BELOW, {p,'D',[I,J]})]} | Acc],
    Acc2 = if Code band ?START =:= ?START ->
		   [{p, 'Pos', [0,I,J]} | Acc1];
	      Code band ?STOP =:= ?STOP ->
		   [{p, 'Pos', ['k',I,J]} | Acc1];
	      true ->
		   Acc1
	   end,
    maze1(Ds, Rs, I, J+1, Acc2); 
maze1([], [R|Rs], I, _J, Acc) ->
    maze1(R, Rs, I+1, 1, Acc);
maze1([], [], _I, _J, Acc) ->
    {'ALL', Acc}.

%% simple binary maze style
maze2([R|Rs]) ->
    maze2(R, Rs, 1, 1, []).

pos(S,I,J) ->
    {p,'Pos',[S,I,J]}.

wall(I,J) ->
    {p,'Wall',[I,J]}.

passage(I,J) ->
    {'not',wall(I,J)}.

maze2([$X|Ds], Rs,  I, J, Acc) ->
    maze2(Ds, Rs, I, J+1, [wall(I,J)|Acc]);
maze2([$\s|Ds], Rs,  I, J, Acc) ->
    maze2(Ds, Rs, I, J+1, [passage(I,J)|Acc]);
maze2([$@|Ds], Rs,  I, J, Acc) ->
    %% io:format("START = Pos(0,~w,~w)\n", [I,J]),
    maze2(Ds, Rs, I, J+1, [pos(0,I,J),passage(I,J)|Acc]);
maze2([$&|Ds], Rs,  I, J, Acc) ->
    %% io:format("STOP = Pos(k,~w,~w)\n", [I,J]),
    maze2(Ds, Rs, I, J+1, [pos('k',I,J),passage(I,J)|Acc]);
maze2([], [R|Rs], I, _J, Acc) ->
    maze2(R, Rs, I+1, 1, Acc);
maze2([], [], _I, _J, Acc) ->
    {'ALL', Acc}.

file(File) ->
    file(File,[]).
file(File,_Meta) ->
    case file:open(File, [read,binary]) of
	{ok,Fd} ->
	    try load_lines(Fd, []) of
		Lines ->
		    %% io:format("Lines=~w\n", [Lines]),
		    %% Data = ascii1_to_data(Lines),
		    %% io:format("Data=~w\n", [Data]),
		    %% N = length(Lines)-2,
		    %% M = length(hd(Lines))-2,
		    %% MazeFormula = maze1(Data),
		    MazeFormula = maze2(Lines),
		    %% io:format("Maze=~w\n", [MazeFormula]),
		    N = length(Lines),
		    M = length(hd(Lines)),
		    {ok,[{"n",N},{"m",M}],MazeFormula}
	    after
		file:close(Fd)
	    end;
	Error ->
	    Error
    end.

load_lines(Fd, Acc) ->
    case file:read_line(Fd) of
	{ok,LineNL} ->
	    LineSize = byte_size(LineNL)-1,
	    Line = case LineNL of
		       <<L:LineSize/binary,$\n>> -> L;
		       _ -> LineNL
		   end,
	    load_lines(Fd, [binary_to_list(Line)|Acc]);
	eof ->
	    lists:reverse(Acc)
    end.
