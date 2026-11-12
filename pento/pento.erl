%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2026, Tony Rogvall
%%% @doc
%%%    Pento chess
%%% @end
%%% Created : 17 Oct 2026 by Tony Rogvall <tony@rogvall.se>

-module(pento).

-compile(export_all).

-define(S, $1).
-define(V, $2).
-define(B, $0).

piece(1) -> %% A (Empty)
    [[?V, ?S, ?B, ?B, ?B],
     [?S, ?V, ?B, ?B, ?B],
     [?B, ?B, ?B, ?B, ?B],
     [?B, ?B, ?B, ?B, ?B],
     [?B, ?B, ?B, ?B, ?B]];
piece(2) -> %% B  V(9)
    [[?B, ?V, ?B, ?B, ?B],
     [?V, ?S, ?V, ?B, ?B],
     [?B, ?V, ?B, ?B, ?B],
     [?B, ?B, ?B, ?B, ?B],
     [?B, ?B, ?B, ?B, ?B]];
piece(3) -> %% C V(B)
    [[?S, ?V, ?B, ?B, ?B],
     [?V, ?B, ?B, ?B, ?B],
     [?S, ?B, ?B, ?B, ?B],
     [?V, ?B, ?B, ?B, ?B],
     [?B, ?B, ?B, ?B, ?B]];
piece(4) -> %% D V(3)
    [[?S, ?B, ?B, ?B, ?B],
     [?V, ?B, ?B, ?B, ?B],
     [?S, ?B, ?B, ?B, ?B],
     [?V, ?B, ?B, ?B, ?B],
     [?S, ?B, ?B, ?B, ?B]];
piece(5) -> %% E V(1)
    [[?V, ?S, ?B, ?B, ?B],
     [?S, ?B, ?B, ?B, ?B],
     [?V, ?S, ?B, ?B, ?B],
     [?B, ?B, ?B, ?B, ?B],
     [?B, ?B, ?B, ?B, ?B]];
piece(6) -> %% F V(7)
    [[?V, ?B, ?B, ?B, ?B],
     [?S, ?V, ?B, ?B, ?B],
     [?V, ?B, ?B, ?B, ?B],
     [?S, ?B, ?B, ?B, ?B],
     [?B, ?B, ?B, ?B, ?B]];
piece(7) -> %% G V(5)
    [[?S, ?V, ?S, ?B, ?B],
     [?B, ?S, ?B, ?B, ?B],
     [?B, ?V, ?B, ?B, ?B],
     [?B, ?B, ?B, ?B, ?B],
     [?B, ?B, ?B, ?B, ?B]];
piece(8) -> %% H V(6)
    [[?S, ?B, ?B, ?B, ?B],
     [?V, ?S, ?B, ?B, ?B],
     [?B, ?V, ?B, ?B, ?B],
     [?B, ?S, ?B, ?B, ?B],
     [?B, ?B, ?B, ?B, ?B]];
piece(9) -> %% I V(2)
    [[?B, ?S, ?V, ?B, ?B],
     [?B, ?V, ?B, ?B, ?B],
     [?V, ?S, ?B, ?B, ?B],
     [?B, ?B, ?B, ?B, ?B],
     [?B, ?B, ?B, ?B, ?B]];
piece(10) -> %% J V(C)
    [[?V, ?B, ?B, ?B, ?B],
     [?S, ?B, ?B, ?B, ?B],
     [?V, ?S, ?V, ?B, ?B],
     [?B, ?B, ?B, ?B, ?B],
     [?B, ?B, ?B, ?B, ?B]];
piece(11) -> %% K V(8)
    [[?S, ?B, ?B, ?B, ?B],
     [?V, ?S, ?B, ?B, ?B],
     [?B, ?V, ?S, ?B, ?B],
     [?B, ?B, ?B, ?B, ?B],
     [?B, ?B, ?B, ?B, ?B]];
piece(12) -> %% L V(4)
    [[?V, ?S, ?B, ?B, ?B],
     [?S, ?V, ?B, ?B, ?B],
     [?B, ?S, ?B, ?B, ?B],
     [?B, ?B, ?B, ?B, ?B],
     [?B, ?B, ?B, ?B, ?B]];
piece(13) -> %% M V(A)
    [[?B, ?S, ?V, ?B, ?B],
     [?S, ?V, ?B, ?B, ?B],
     [?B, ?S, ?B, ?B, ?B],
     [?B, ?B, ?B, ?B, ?B],
     [?B, ?B, ?B, ?B, ?B]].

%% verify that initial pieces have 5 positions (and 1 has 4 positions)
%% the poistions are connected. is aligne in upper left corner
verify() ->
    (piece_size(piece(1)) == 4) andalso
	lists:all(fun(I) -> piece_size(piece(I)) == 5 end, lists:seq(2, 13))
	andalso
	(length(lists:usort([encode(piece(I)) || I <- lists:seq(1,13)])) == 13).

piece_size(P) ->
    length(lists:flatten(P) -- lists:duplicate(25, ?B)).

%% generate all pieces with all transformations
generate() ->
    generate(1, #{}).

generate(14, Set) -> Set;
generate(I, Set) ->
    Set1 = add_transforms(piece(I), I, Set),
    generate(I+1, Set1).

add_transforms(P, I, Set) ->
    P1 = align(P),
    Set2 = add(align(mirror(P1)), I, add(P1, I, Set)),

    P2 = align(align(rotate(P1))),
    Set3 = add(align(mirror(P2)), I, add(P2, I, Set2)),

    P3 = align(align(rotate(P2))),
    Set4 = add(align(mirror(P3)), I, add(P3, I, Set3)),

    P4 = align(align(rotate(P3))),
    Set5 = add(align(mirror(P4)), I, add(P4, I, Set4)),

    Set5.


add(P, I, Set) ->
    Set#{ encode(P) => I }.

%% encode 5x5 piece as a number i base 3
encode(P) ->
    list_to_integer(lists:flatten(P), 3).

%% decode integer in base 3 as 5x5
decode(Pi) ->
    Ds0 = integer_to_list(Pi, 3),
    Pad = 25 - length(Ds0),
    Ds  = lists:duplicate(Pad, $0) ++ Ds0,
    [A,B,C,D,E,
     F,G,H,I,J,
     K,L,M,N,O,
     P,Q,R,S,T,
     U,V,W,X,Y] = Ds,
    [[A,B,C,D,E],
     [F,G,H,I,J],
     [K,L,M,N,O],
     [P,Q,R,S,T],
     [U,V,W,X,Y]].

print_all(Set) ->
    print_all(Set, false).

print_all(Set, Crop) ->
    maps:foreach(
      fun(Pi,I) ->
	      io:format("~w:\n", [I]),
	      P = decode(Pi),
	      Pa = align(P),
	      Pb = if Crop -> crop(Pa); true -> Pa end,
	      print(Pb),
	      io:put_chars("\n")
      end, Set).

print_info(Set) ->
    CSet = lists:foldl(
      fun({_Pi, I}, Count) ->
	      N = maps:get(I, Count, 0),
	      maps:put(I, N+1, Count)
      end, #{}, maps:to_list(Set)),
    Histo = lists:sort(maps:to_list(CSet)),
    {lists:sum([ Count || {_I, Count} <- Histo]), Histo}.

print(P) ->
    print_border(P),
    _ = [print_row(Row) || Row <- P],
    print_border(P).

print_border(P) ->
    N = length(hd(P)),
    lists:foreach(fun(_) -> io:put_chars("+---") end, lists:seq(1, N)),
    io:put_chars("+\n").

print_row(Row) ->
    _ = [begin io:put_chars("|"),print_char(Char) end || Char <- Row],
    io:put_chars("|\n").

print_char(?B) -> io:put_chars("   ");
print_char(?S) -> io:put_chars(" S ");
print_char(?V) -> io:put_chars(" V ").

save_formula(Filename) ->
    case file:open(Filename, [write]) of
	{ok, Fd} ->
	    try print_formula(Fd) of
		ok ->
		    io:format(Fd, "~s\n", ["true"])
	    after
		file:close(Fd)
	    end;
	Error ->
	    Error
    end.

print_formula() ->
    print_formula(user).

print_formula(Fd) ->
    Set = generate(),
    FMap = maps:fold(
	    fun(Pi,I,Map) ->
		    P = decode(Pi),
		    Pa = align(P),
		    Pb = crop(Pa),
		    Os = maps:get(I, Map, []),
		    J = length(Os)+1,
		    maps:put(I, [{J,Pb}|Os], Map)
	    end, #{}, Set),
    lists:foreach(
      fun(Pi) ->
	      Os = lists:sort(maps:get(Pi, FMap)),
	      lists:foreach(
		fun({Oj,P}) ->
			print_loc_formula(Fd,P,Pi,Oj)
		end, Os),
	      print_one_formula(Fd,Os,Pi)
      end, lists:seq(1,13)),
    lists:foreach(  %% each row
      fun(I) ->
	      lists:foreach(  %% each column
		fun(J) ->
			if ((I+J) band 1 =:= 0) ->
				io:format(Fd, "S(~w,~w) && !V(~w,~w) &&\n", 
					  [I, J, I, J]);
			   true ->
				io:format(Fd, "V(~w,~w) && !S(~w,~w) &&\n", 
					  [I, J, I, J])
			end
		end, lists:seq(1, 8))
      end, lists:seq(1, 8)),
    %% Only one brick on one location
    lists:foreach(  %% each row
      fun(I) ->
	      lists:foreach(  %% each column
		fun(J) ->
			Ls = [io_lib:format("L(~w,~w,~w)", [K,I,J]) ||
				 K <- lists:seq(1,13)],
			io:format(Fd, "[ONE](~s) && \n", 
				  [lists:join(",", Ls)])
		end, lists:seq(1, 8))
      end, lists:seq(1, 8)).    

print_loc_formula(Fd,P,Pi,Oj) ->
    H = length(P),
    W = length(hd(P)),
    Rows = (8-H)+1,
    Cols = (8-W)+1,
    lists:foreach( %% each row
      fun(I) ->
	      lists:foreach(  %% each column
		fun(J) ->
			io:format(Fd, "(P(~w,~w,~w,~w) -> (", [Pi,Oj,I,J]),
			Ls = loc_formula_rows(P, Pi, Oj, I, J),
			SVs = sv_formula_rows(P, I, J),
			io:format(Fd, "~s)) && \n",
				  [lists:join(" && ", Ls++SVs)])
		end, lists:seq(1, Cols))
      end, lists:seq(1, Rows)).

print_one_formula(Fd,Os,Pi) ->
    PsList =
	[ begin
	      H = length(P),
	      W = length(hd(P)),
	      Rows = (8-H)+1,
	      Cols = (8-W)+1,
	      [ [io_lib:format("P(~w,~w,~w,~w)", [Pi,Oj,I,J]) ||
		    J <- lists:seq(1, Cols)] || I <- lists:seq(1, Rows)]
	  end || {Oj,P} <- Os],
    Ps1 = lists:append(lists:append(PsList)),
    io:format(Fd, "[ONE](~s) && \n", [lists:join(",", Ps1)]).

%% print location formula shape Pj (1..13), orientation Oj (1..8)
%% for row I column J
loc_formula_rows([Row|P],Pi,Oj,I,J) ->
    Fs = loc_formula_row(Row,Pi,Oj,I,J),
    Fs ++ loc_formula_rows(P,Pi,Oj,I+1,J);
loc_formula_rows([],_Pi,_Oj,_I,_J) ->
    [].

loc_formula_row([?B|Row],Pi,Oj,I,J) ->
    loc_formula_row(Row,Pi,Oj,I,J+1);
loc_formula_row([?S|Row],Pi,Oj,I,J) ->
    [io_lib:format("L(~w,~w,~w)", [Pi,I,J]) |
     loc_formula_row(Row,Pi,Oj,I,J+1)];
loc_formula_row([?V|Row],Pi,Oj,I,J) ->
    [io_lib:format("L(~w,~w,~w)", [Pi,I,J]) |
     loc_formula_row(Row,Pi,Oj,I,J+1)];
loc_formula_row([],_Pi,_Oj,_I,_J) ->
    [].


%% print color S/V formula for row I column J
sv_formula_rows([Row|P],I,J) ->
    Fs = sv_formula_row(Row,I,J),
    Fs ++ sv_formula_rows(P,I+1,J);
sv_formula_rows([],_I,_J) ->
    [].

sv_formula_row([?B|Row],I,J) ->
    sv_formula_row(Row,I,J+1);
sv_formula_row([?S|Row],I,J) ->
    [io_lib:format("S(~w,~w)", [I,J]) |
     sv_formula_row(Row,I,J+1)];
sv_formula_row([?V|Row],I,J) ->
    [io_lib:format("V(~w,~w)", [I,J]) |
     sv_formula_row(Row,I,J+1)];
sv_formula_row([],_I,_J) ->
    [].

%% check if top row is blank
is_blank_top([Row|_]) ->
    lists:all(fun(X) -> X end, [(R == ?B) || R <- Row]).

%% check if bottom row is blank 
is_blank_bot(Rows) -> 
    Row = lists:last(Rows),
    lists:all(fun(X) -> X end, [(R == ?B) || R <- Row]).

%% check if left column is blank
is_blank_left(Rows) ->
    lists:all(fun(X) -> X end, [(hd(Row) == ?B) || Row <- Rows]).    

%% check if right column is blank
is_blank_right(Rows) ->
    lists:all(fun(X) -> X end, [(lists:last(R) == ?B) || R <- Rows]).

%% mirror (assume 5x5 format)
mirror(P) ->
    [ mirror_row(R) || R <- P ].

mirror_row([A,B,C,D,E]) ->
    [E,D,C,B,A].

%% rotate right (assume 5x5 format)
rotate([[A,B,C,D,E],
	[F,G,H,I,J],
	[K,L,M,N,O],
	[P,Q,R,S,T],
	[U,V,W,X,Y]]) ->
    [[U,P,K,F,A],
     [V,Q,L,G,B],
     [W,R,M,H,C],
     [X,S,N,I,D],
     [Y,T,O,J,E]].

%% move up, left to align transformed piece
align(P) ->
    align_left(align_up(P)).

align_up(P) ->
    case is_blank_top(P) of
	true -> align_up(move_up(P));
	false -> P
    end.

align_left(P) ->
    case is_blank_left(P) of
	true -> align_left(move_left(P));
	false -> P
    end.

%% remove blank rows at bottom and right (after align)
crop(P) ->
    crop_right(crop_bot(P)).

crop_bot(P) ->
    case is_blank_bot(P) of
	true -> crop_bot(remove_bot(P));
	false -> P
    end.

crop_right(P) ->
    case is_blank_right(P) of
	true -> crop_right(remove_right(P));
	false -> P
    end.

%% remove top row and add a blank row at the bottom
move_up([Top|Rows]) ->
    N = length(Top),
    Rows ++ [lists:duplicate(N, ?B)].

%% remove left column and add a blank right column 
move_left(Rows) ->
    [tl(Row) ++ [?B] || Row <- Rows].

%% remove bottom row
remove_bot(Rows) ->
    [_|Rows1] = lists:reverse(Rows),
    lists:reverse(Rows1).

%% remove right column
remove_right([R|Rs]) ->
    [_|R1] = lists:reverse(R),
    [lists:reverse(R1)|remove_right(Rs)];
remove_right([]) ->
    [].

    
