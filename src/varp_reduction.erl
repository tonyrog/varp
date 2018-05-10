%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2018, Tony Rogvall
%%% @doc
%%%    Given a SNF/CNF generate 
%%%    a model reduction defintion 
%%% @end
%%% Created : 25 Apr 2018 by Tony Rogvall <tony@rogvall.se>

-module(varp_reduction).
-compile(export_all).

-include("varp_bic.hrl").


file(Input,Output) ->
    SNF = varp_dimacs:load(Input),
    save_snf_to_red(SNF, Output).

save_snf_to_red(SNF, Output) ->
    T = transform(SNF),
    file:write_file(Output,format_defs(T)).

save_snf_to_red_plus_clauses(SNF={snf,{_Nv,_Nc,_Decls,_Ls0,CLs}}, Output) ->
    {Decls,Ls,Defs} = transform(SNF),
    Fs = format_cnf(CLs),
    file:write_file(Output, [format_decls(Decls),Fs," &&\n",
			     format_defs({[],Ls,Defs})]).

save_snf_to_clauses({snf,{_Nv,_Nc,_Decls,_Ls0,CLs}}, Output) ->
    Fs = format_cnf(CLs),
    file:write_file(Output, Fs).


load(File) ->
    varp_dimacs:load(File).

transform({snf,{_Nv,_Nc,Decls,Ls0,CLs0}}) ->
    {CLs,Ls1} = pp_clauses(CLs0,Ls0),
    Vars = snf_vars(CLs),
    Defs = sets:fold(
	     fun(V,Acc) ->
		     [def(V, CLs), def({'not',V},CLs) | Acc]
	     end, [], Vars),
    {Decls,Ls1,Defs}.

format_defs({Decls,Ls,Defs}) ->
    [format_decls(Decls),
     [[format_literal(L)," &&\n"] || L<-Ls],
     concat([ ["(",format_literal(L)," <-> (", format_dnf(D),")",")"] ||
		{L,D} <- Defs], " &&\n")].

format_decls(Ds) ->
    [["declare ",format_decl(D),";\n"] || D <- Ds].

format_decl({Var,uint,Size}) ->
    [varp_cnf:format_symbol(Var),":",integer_to_list(Size),
     "/unsigned"];
format_decl({Var,int,Size}) ->
    [varp_cnf:format_symbol(Var),":",integer_to_list(Size),
     "/signed"].

format_cnf(CLs) ->
    concat([format_cnf_clause(CL) || CL <- CLs], " &&\n").

format_dnf(CLs) ->
    concat([format_dnf_clause(CL) || CL <- CLs], " || ").

format_cnf_clause([L]) ->
    format_literal(L);
format_cnf_clause(CL) ->
    ["(",concat([format_literal(L) || L <- CL], " || "),")"].

format_dnf_clause([L]) ->
    format_literal(L);
format_dnf_clause(CL) ->
    ["(",concat([format_literal(L) || L <- CL], " && "),")"].



format_literal({'not',V}) ->
    ["!",varp_cnf:format_symbol(V)];
format_literal(V) ->
    varp_cnf:format_symbol(V).

%% Def generates and clauses
def(L, CLs) ->
    {L,def(L, CLs, [])}.

def(L, [CL|CLs], Acc) ->
    case CL -- [L] of
	CL -> def(L, CLs, Acc);
	CL1 -> def(L, CLs, [[neg(M)||M<-CL1]|Acc])
    end;
def(_L, [], Acc) ->
    Acc.

neg({'not',V}) -> V;
neg(V) -> {'not',V}.

snf_vars(CLs) -> 
    snf_vars(CLs,sets:new()).
snf_vars([C|CLs],VSet) ->
    VSet1 = lists:foldl(
	      fun({'not',V}, Si) -> add_var(V,Si);
		 (V,Si) -> add_var(V,Si)
	      end, VSet, C),
    snf_vars(CLs, VSet1);
snf_vars([],VSet) ->
    VSet.

%% preprocess clauses and literls
pp_clauses(CLs,Ls) ->
    pp_clauses(CLs,[],Ls).

pp_clauses([[L]|CLs],Acc,Ls) ->
    pp_clauses(CLs,Acc,[[L]|Ls]);
pp_clauses([CL|CLs],Acc,Ls) ->
    pp_clauses(CLs,[pp_clause(CL)|Acc],Ls);
pp_clauses([],Acc,Ls) ->
    {Acc,Ls}.

pp_clause(CL) ->
    [pp_literal(L) || L <- CL].

pp_literal({'not',V}) -> {'not',pp_var(V)};
pp_literal(V) -> pp_var(V).

pp_var({bit_index,Var,I}) -> 
    {bit_index,pp_pred(Var),pp_expr(I)};
pp_var({uint,Var,Size,N}) -> 
    {uint,pp_pred(Var),pp_expr(Size),pp_expr(N)};
pp_var({int,Var,Size,N}) -> 
    {int,pp_pred(Var),pp_expr(Size),pp_expr(N)};
pp_var(true) -> true;
pp_var(false) -> false;
pp_var(Var) -> pp_pred(Var).

pp_pred({p,Var,I}) when is_integer(I) -> {p,Var,I};
pp_pred({p,Var,Es}) -> {p,Var,[pp_expr(E)||E<-Es]}.

pp_expr(#cconst{value=List,base=Base}) ->
    list_to_integer(List,Base);
pp_expr(E) when is_integer(E) -> 
    E.

add_var(true,VSet) -> VSet;
add_var(false,VSet) -> VSet;
add_var(V,VSet) -> sets:add_element(V,VSet).

concat([], _) -> [];
concat([H],_) -> [H];
concat([H|T],S) -> [H,S | concat(T,S)].
