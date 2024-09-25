-module(sudoku_io).
-export([file/1, file/2]).
-export([input/2]).
-export([output/3]).

input(Line, _Acc) ->
    Translate = fun($.) -> 0;
		   (X) when X >= $0, X =< $9 -> (X-$0)
		end,
    Ns = [Translate(I) || I <- lists:sublist(Line,81)],
    Ss = [{p,<<"S">>,[I,J]} || I <- lists:seq(1,9), J <- lists:seq(1,9)],
    NsSs = lists:zip(Ss, Ns),
    %% remove all zeros and inject indices
    {true,{'ALL',[{p,<<"S">>,[I,J,K]} || {{p,<<"S">>,[I,J]},K} <- NsSs, K =/= 0]}}.

output(Fd, _Partial, Model) ->
    %% io:format(Fd, "~p\n", [Model]).
    io:format(Fd,"+-+-+--+--+-+--+--+-+--+\n", []),
    lists:foreach(
      fun(I) ->
	      io:format(Fd,"|~s|~s|~s | ~s|~s|~s | ~s|~s|~s |\n",
			[s(I,J,Model) || J <- lists:seq(1,9)])
      end, lists:seq(1,3)),
    io:format(Fd, "+=+=+==+==+=+==+==+=+==+\n", []),
    lists:foreach(
      fun(I) ->
	      io:format(Fd,"|~s|~s|~s | ~s|~s|~s | ~s|~s|~s |\n",
			[s(I,J,Model) || J <- lists:seq(1,9)])
      end, lists:seq(4,6)),
    io:format(Fd,"+=+=+==+==+=+==+==+=+==+\n",[]),
    lists:foreach(
	  fun(I) ->
		  io:format(Fd,"|~s|~s|~s | ~s|~s|~s | ~s|~s|~s |\n",
			    [s(I,J,Model) || J <- lists:seq(1,9)])
	  end, lists:seq(7,9)),
    io:format(Fd,"+-+-+--+--+-+--+--+-+--+\n",[]),
    ok.

s(I,J, [{{p,<<"S">>,[I,J,K]},true}|_Ms]) ->
    integer_to_list(K);
s(I,J, [_|Ms]) -> 
    s(I,J,Ms);
s(_I, _J, []) -> %% allow for partial models
    " ".

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
	    RecNo = case maps:find("recno", Meta) of
			error -> 1;
			{ok,Rn} when is_integer(Rn), Rn>0 -> Rn
		    end,
	    try input_loop(Fd, RecNo, []) of
		Result -> Result
	    after
		file:close(Fd)
	    end;
	Error={error,_} ->
	    Error
    end.
