-module(sudoku_io).
-export([file/1, file/2]).
-export([input/2]).
-export([output/2]).

input(Line, _Acc) ->
    Ns = [(I-$0) || I <- lists:sublist(Line,81)],
    Ss = [{p,'S',[I,J]} || I <- lists:seq(1,9), J <- lists:seq(1,9)],
    NsSs = lists:zip(Ss, Ns),
    %% remove all zeros and inject indices
    {true,{'ALL',[{p,'S',[I,J,K]} || {{p,'S',[I,J]},K} <- NsSs, K =/= 0]}}.

%% fixme: display a sudoku grid 
output(Fd, Model) ->
    io:format(Fd, "~p\n", [Model]).

input_loop(Fd, RecNo, Acc) ->
    case file:read_line(Fd) of
	{ok,_} when RecNo > 1 ->
	    input_loop(Fd, RecNo-1, Acc);
	{ok,LineNL} ->
	    LineSize = byte_size(LineNL)-1,
	    Line = case LineNL of
		       <<L:LineSize/binary,$\n>> -> L;
		       _ -> LineNL
		   end,
	    case input(binary_to_list(Line), Acc) of
		{true,Acc1} ->
		    {ok,Acc1};
		{false,_Acc1} ->
		    {error, input}
	    end;
	eof ->
	    Acc;
	Error = {error,_} -> Error
    end.

file(File) ->	    
    file(File,[]).
file(File,Meta) ->
    case file:open(File, [read,binary]) of
	{ok,Fd} ->
	    RecNo = case proplists:lookup("recno", Meta) of
			none -> 1;
			{"recno",Rn} when is_integer(Rn), Rn>0 -> Rn
		    end,
	    try input_loop(Fd, RecNo, []) of
		Result -> Result
	    after
		file:close(Fd)
	    end;
	Error={error,_} ->
	    Error
    end.
