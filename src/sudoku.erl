%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2012, Tony Rogvall
%%% @doc
%%%    Logic formulation(s) of sudoku
%%% @end
%%% Created : 13 Oct 2012 by Tony Rogvall <tony@rogvall.se>

-module(sudoku).
-compile(export_all).
-import(lists, [foreach/2]).

sudoku(S) ->
    sudoku(S,fun(I) -> I end).

sudokux(S) ->
    sudoku(S,fun(I) -> {f,x,[I]} end).

sudoku(S,F) ->
    {all,
     [
      %% every position must have a uniq value!
      %%  (FORALL i=1..9)(FORALL j=1..9) (EXISTS! k=1,..9) S(i,j,k)
      {{all,[{'=',i,{range,1,9}}]},
       {{all,[{'=',j,{range,1,9}}]},
	{{eqk,[1,{'=',k,{range,1,9}}]}, {p,S,[i,j,F(k)]}}
       }
      },

      %% for every row every column must be uniq
      %%  (FORALL i=1..9 (FORALL k=1..9) (EXISTS! j=1...9) S(i,j,k)
      {{all,[{'=',i,{range,1,9}}]},
       {{all,[{'=',k,{range,1,9}}]},
	{{eqk,[1,{'=',j,{range,1,9}}]}, {p,S,[i,j,F(k)]}}
       }
      },
      
      %% for every column every row must be uniq
      %%  (A j=1..9) (A k=1..9) (E! i=1...9) S(i,j,k)
      {{all,[{'=',j,{range,1,9}}]},
       {{all,[{'=',k,{range,1,9}}]},
	{{eqk,[1,{'=',i,{range,1,9}}]},{p,S,[i,j,F(k)]} }
       }
      },

      %% for every box every position must be uniq
      %%  (A s=0..2)(A t=0..2)(A k=1..9)
      %%    (E! i=1..3,j=1..3) S(3*s+i,3*t+j,k)
      {{all,[{'=',s,{range,0,2}}]},
       {{all,[{'=',t,{range,0,2}}]},
	{{all,[{'=',k,{range,1,9}}]},
	 {{eqk,[1,{'=',i,{range,0,8}}]},
	  {p,S,[{'+',{'+',{'*',3,s},{'/',i,3}},1},
		{'+',{'+',{'*',3,t},{'%',i,3}},1},F(k)]}}
	}
       }
      }
     ]}.

sudoku0(X) ->
    %% every position must have a uniq value!
    %%  (A i=1..9)(A j=1..9) (E! k=0,..9) X(i,j,k)
    {{all,[{'=',i,{range,1,9}}]},
     {{all,[{'=',j,{range,1,9}}]},
      {{eqk,[1,{'=',k,{range,0,9}}]},{p,X,[i,j,k]}}
     }}.

inst(X,Matrix) ->
    instr(X,1,Matrix,[]).

instr(X,I,[R|Rs],Acc) ->
    Acc1 = instc(X,I,1,R,Acc),
    instr(X,I+1,Rs,Acc1);
instr(_X,_I,[],Acc) ->
    {all,lists:reverse(Acc)}.

instc(X,I,J,[x|Ks],Acc) ->
    instc(X,I,J+1,Ks,Acc);
instc(X,I,J,[K|Ks],Acc) ->
    instc(X,I,J+1,Ks,[{p,X,[I,J,K]}|Acc]);
instc(_X,_I,_J,[],Acc) ->
    Acc.

install(X,[{{p,X,[_I,_J,0]},true} |Rs],D) -> 
    %% skip A(I,J,0) is a place holder - check me!
    install(X,Rs,D);
install(X,[{{p,X,[I,J,K]},true}|Rs],D) ->
    D1 = dict:store({I,J}, K, D),
    install(X,Rs,D1);
install(X,[_|Rs],D) ->
    install(X,Rs,D);
install(_X,[],D) ->
    D.

fpos(I,J,D) ->
    case dict:find({I,J}, D) of
	error ->  [$\s,$x,$\s];
	{ok,C} -> [$\s,C+$0,$\s]
    end.

frow(I,D) ->
    "|"++ 
	[fpos(I,J,D) || J <- lists:seq(1,3)] ++ "|" ++
	[fpos(I,J,D) || J <- lists:seq(4,6)] ++ "|" ++
	[fpos(I,J,D) || J <- lists:seq(7,9)] ++ "|".

print(X, Model) ->
    D = install(X, Model, dict:new()),
    io:format("+---------+---------+---------+\n",[]),
    foreach(fun(I) -> io:format("~s\n", [frow(I,D)]) end, lists:seq(1,3)),
    io:format("+---------+---------+---------+\n",[]),
    foreach(fun(I) -> io:format("~s\n", [frow(I,D)]) end, lists:seq(4,6)),
    io:format("+---------+---------+---------+\n",[]),
    foreach(fun(I) -> io:format("~s\n", [frow(I,D)]) end, lists:seq(7,9)),
    io:format("+---------+---------+---------+\n",[]),
    io:format("\n\n").

puzzle_sudoku17(I) ->
    case file:open(filename:join(code:priv_dir(varp),"sudoku17.txt"),[read]) of
	{ok,Fd} ->
	    case file:pread(Fd, I*82, 81) of
		{ok,Data} ->
		    Res = convert_puzzle(Data),
		    file:close(Fd),
		    Res;
		Error ->
		    Error
	    end;
	Error ->
	    Error
    end.
%%
%% convert a sudoku board on the form [0-9]{81} to 
%% a matrix form where 'x' represent the empty place
%%
convert_puzzle(Data) ->
    Data1 = lists:map(fun($0) -> x;
			 (C) -> C-$0 end, Data),
    split_parts(Data1,9,[]).

split_parts([],_N,Acc) ->
    lists:reverse(Acc);
split_parts(List,N,Acc) ->
    Len = length(List),
    if Len =< N ->
	    split_parts([],N,[List|Acc]);
       true ->
	    {R,List1} = lists:split(N, List),
	    split_parts(List1,N,[R|Acc])
    end.

%% DN svår 2012-10-13
puzzle1() ->
    [[x,x,x,x,1,3,x,9,x],
     [6,4,5,x,2,x,x,x,x],
     [x,x,x,x,x,5,x,6,x],
     [x,1,x,x,9,2,x,x,4],
     [x,5,x,x,x,1,x,x,7],
     [7,x,x,x,x,x,x,x,x],
     [x,6,x,3,x,x,x,1,x],
     [x,x,4,x,x,x,x,x,x],
     [x,9,x,x,x,x,6,x,x]].

%% SVD generator extra svår.
puzzle2() ->
    [[3,x,2,4,8,x,6,x,x],
     [9,x,x,1,x,x,7,x,x],
     [x,x,6,x,x,x,2,x,x],
     [x,8,x,x,5,x,x,7,x],
     [1,x,x,x,7,2,x,x,x],
     [x,x,x,x,x,x,x,x,x],
     [8,x,4,6,x,x,x,x,x],
     [x,x,x,x,x,7,x,x,x],
     [x,x,x,x,x,x,x,9,5]].

%% SM 2004 1-4
%% http://gfx.svd-cdn.se/multimedia/archive/00251/Sudoku_1-4_fr_n_Sud_251935a.pdf
puzzle_sm_2005_1() ->
    [[6,7,x,x,x,1,x,x,x],
     [3,x,x,x,x,9,x,8,6],
     [x,x,x,x,8,x,x,x,x],
     [x,x,7,1,x,x,9,x,3],
     [x,x,x,x,4,x,x,x,x],
     [8,x,5,x,x,6,4,x,x],
     [x,x,x,x,6,x,x,x,x],
     [9,4,x,2,x,x,x,x,7],
     [x,x,x,7,x,x,x,4,1]].

puzzle_sm_2005_2() ->
    [[x,x,x,9,1,x,x,3,x],
     [x,6,x,x,x,2,7,x,9],
     [x,x,x,x,x,x,x,x,x],
     [4,x,7,5,x,x,x,1,x],
     [x,x,x,x,x,x,x,x,x],
     [x,9,x,x,x,3,8,x,2],
     [x,x,x,x,x,x,x,x,x],
     [9,x,3,8,x,x,x,2,x],
     [x,5,x,x,4,6,x,x,x]].

puzzle_sm_2005_3() ->    
    [[x,x,x,7,x,x,x,x,5],
     [x,1,x,x,x,x,4,x,x],
     [x,x,6,x,8,x,x,x,x],
     [x,x,x,6,x,x,2,x,7],
     [x,9,x,x,x,x,x,8,x],
     [3,x,5,x,x,4,x,x,x],
     [x,x,x,x,2,x,1,x,x],
     [x,x,4,x,x,x,x,3,x],
     [7,x,x,x,x,9,x,x,x]].

puzzle_sm_2005_4() ->
    [[x,x,9,4,x,x,3,x,x],
     [x,2,x,x,x,x,x,1,x],
     [4,x,8,x,x,x,7,x,5],
     [x,5,x,x,7,6,x,x,x],
     [x,x,x,3,x,9,x,x,x],
     [x,x,x,2,8,x,x,7,x],
     [7,x,1,x,x,x,2,x,8],
     [x,8,x,x,x,x,x,5,x],
     [x,x,6,x,x,3,1,x,x]].

%% VM : http://www.aftonbladet.se/nyheter/article15054343.ab
puzzle_vm() ->
    [[8,x,x,x,x,x,x,x,x],
     [x,x,3,6,x,x,x,x,x],
     [x,7,x,x,9,x,2,x,x],
     [x,5,x,x,x,7,x,x,x],
     [x,x,x,x,4,5,7,x,x],
     [x,x,x,1,x,x,x,3,x],
     [x,x,1,x,x,x,x,6,8],
     [x,x,8,5,x,x,x,1,x],
     [x,9,x,x,x,x,4,x,x]].


puzzle_bt(P) ->
    B = sudoku(a1),
    I = inst(a1,P),
    case prover:satisfy_formula({'and',B,I}, [{print,model},{max,2},
					      {method,collect}]) of
	false ->
	    false;
	{_N,Models} ->
	    lists:foreach(
	      fun(M) -> print(a1,M) end, Models),
	    Models
    end.

puzzle_sat1(P) ->
    puzzle_satk(1,P).

puzzle_sat2(P) ->
    puzzle_satk(2,P).

puzzle_satk(K,P) ->
    puzzle_satk(K,P,true).

puzzle_satk(K,P,Backtrack) ->
    B1 = sudoku(a1),
    I = inst(a1,P),
    case prover:saturate_formula(K, {'and',B1,I}, 
				 [{value,true},
				  {max,2},
				  {log,info},
				  {order, depth},
				  {bcp, false},
				  {method,collect}]) of
	false ->
	    false;
	Bs ->
	    NV = formula:number_of_variables(Bs),
	    NB = formula:number_of_bound(Bs),
	    io:format("NV=~w, NB=~w\n", [NV, NB]),
	    if NV =:= NB ->
		    M = formula:model(Bs),
		    print(a1,M),
		    true;
	       Backtrack ->
		    io:format("Backtrack:\n", []),
		    case prover:backtrack_bs(Bs) of
			{0,[]} -> 
			    false;
			{1,[M]} ->
			    print(a1,M),
			    true;
			{_N,Models} ->
			    lists:foreach(
			      fun(M) -> print(a1,M) end, Models),
			    error
		    end;
	       true ->
		    false
	    end
    end.

%%
%% Pre solutions
%%
puzzle_pre() ->
    [[1,2,3,4,5,6,7,8,9],
     [4,x,x,x,x,x,x,x,x],
     [5,x,x,x,x,x,x,x,x],
     [6,x,x,x,x,x,x,x,x],
     [7,x,x,x,x,x,x,x,x],
     [8,x,x,x,x,x,x,x,x],
     [9,x,x,x,x,x,x,x,x],
     [2,x,x,x,x,x,x,x,x],
     [3,x,x,x,x,x,x,x,x]].

%%
%% Test if all 17 pzzles are 1-easy
%%
puzzle_test17() ->
    puzzle_test17_(1, 49152).

puzzle_test17_(I, N) when I < N ->
    B = sudoku('S'),
    P = puzzle_sudoku17(I),
    A = inst('S',P),
    case prover:run_formula({'and',B,A}, 
			    [{value,true},{saturate,1},
			     {backtrack,false},{method,count}]) of
	false -> io:format("~w: NOT easy!\n", [I]),
		 error({not_easy,I});
	1 -> io:format("~w: OK\n", [I])
    end,
    puzzle_test17_(I+1,N);
puzzle_test17_(N,N) ->
    ok.

%% 
%% Puzzle finder
%%
puzzle_find() ->
    puzzle_find(1, 49151).

puzzle_find(K,L) ->
    A0 = sudoku0(a0),
    A1 = sudoku(a1),
    %% load solutions already found
    Cs = lists:map(
	   fun(I) -> 
		   P = puzzle_sudoku17(I),
		   S = inst(a0,P),
		   {'not',S}
	   end, lists:seq(0, L)),
    N = 17,
    F = 
	{'all',
	 [ A0, A1,
	   %% N = size of the partial solution (81-N = 0)
	   {{eqk,[81-N,{'=',i,{range,1,9}},{'=',j,{range,1,9}}]},
	    {p,a0,[i,j,0]}},

	   {{forall,[{'=',i,{range,1,9}}]},
	    {{forall,[{'=',j,{range,1,9}}]},
	     {{forall,[{'=',k,{range,1,9}}]},
	      {'->',{p,a0,[i,j,k]},{p,a1,[i,j,k]} }}}}
	 ] ++ Cs },

    case prover:saturate_formula(K, F,
				 [{value,true},
				  {max,2},
				  {log,info},
				  {order, [occure,reverse]},
				  {bcp, false},
				  {method,collect}]) of
	false ->
	    false;
	Bs ->
	    NV = formula:number_of_variables(Bs),
	    NB = formula:number_of_bound(Bs),
	    io:format("NV=~w, NB=~w\n", [NV,NB]),
	    if NV =:= NB ->
		    M = formula:model(Bs),
		    print(a0,M),
		    print(a1,M);
	       true ->
		    io:format("Backtrack:\n", []),
		    case prover:backtrack_bs(Bs) of
			{0,[]} -> false;
			{_N,Models} ->
			    lists:foreach(
			      fun(M) -> 
				      print(a0,M),
				      print(a1,M)
			      end, Models),
			    Models
		    end
	    end
    end.

puzzle17_loop() ->
    puzzle17_loop(1).

puzzle17_loop(K) ->
    Is = shuffle:list(lists:seq(0, 49151)),
    puzzle17_loop(K, Is).

puzzle17_par(K) ->
    N = erlang:system_info(schedulers_online),
    puzzle17_par(K, N).
    
puzzle17_par(K, N) ->
    IsL = split_parts(lists:seq(0, 49151),49152 div N,[]),
    lists:foreach(
      fun(Is) ->
	      spawn(fun() ->
			    io:format("loop: ~w started\n", [self()]),
			    puzzle17_loop(K, Is),
			    io:format("loop: ~w stopped\n", [self()])
		    end)
      end, IsL).

puzzle17_loop(K, [I|Is]) ->
    io:format("~w: I:~w\n", [self(),I]),
    case puzzle17_instance(I, K) of
	true -> 
	    ok;
	false ->
	    puzzle17_loop(K, Is)
    end;
puzzle17_loop(_K, []) ->
    ok.

puzzle17_instance(I, K) ->
    P = puzzle_sudoku17(I),
    A = sudoku(a1),
    {all,P0} = inst(a1,P),
    %% find16_random(K, P0, A)
    find16_loop(K, P0, [], A).

find16_random(K, P0, A) ->
    {Ps0,[Pi|Ps1]} = lists:split(random:uniform(16), P0),
    P16 = Ps0++Ps1,
    case puzzle16_prove(K,Pi,P16,A) of
	true ->
	    io:format("~w: SOLUTION: ~p\n", [self(),P16]),
	    {true, P16};
	false ->
	    false
    end.

find16_loop(K,[Pi|Ps0],Ps1,A) ->
    P16 = Ps0++Ps1,
    case puzzle16_prove(K,Pi,P16,A) of
	true ->
	    io:format("~w: SOLUTION: ~p\n", [self(),P16]),
	    {true,P16};
	false ->
	    find16_loop(K,Ps0,[Pi|Ps1],A)
    end;
find16_loop(_K, [], _Ps1, _A) ->
    false.

puzzle16_prove(K,Pi,P16,A) ->
    F = {'->', {'and',A,{all,P16}},Pi},
    io:format("Pi:~p\n", [Pi]),
    case prover:saturate_formula(K, F,
				 [{value,false},
				  {max,1},
				  {log,info},
				  {bcp, false},
				  {method,collect}]) of
	false ->
	    true;
	Bs ->
	    NV = formula:number_of_variables(Bs),
	    NB = formula:number_of_bound(Bs),
	    %% io:format("NV=~w, NB=~w\n", [NV, NB]),
	    if NV =:= NB ->
		    %% M = formula:model(Bs),
		    %% print(a1,M),
		    false;
	       true ->
		    %% io:format("Backtrack:\n", []),
		    case prover:backtrack_bs(Bs) of
			{0,[]} ->
			    true;
			{_N,_Models} ->
			    %% lists:foreach(
			    %% fun(M) -> print(a1,M) end, Models),
			    %% Models,
			    false
		    end
	    end    
    end.
    
    


    
