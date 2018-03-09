%% -*- erlang -*-
%%
%%
Terminals
	symbol identifier hexnum binnum octnum decnum flonum chrnum
        true false
	'A' 'E'
        '&' '|' '^' '!' '~'
	'+' '-' '*' '/' '%' '>>>' '>>' '<<<' '<<'
	'<=' '>=' '!=' '<' '>' '=' '=='
	',' '(' ')' '.' '[' ']'
	.

Nonterminals
        bor_op band_op bxor_op bnot_op
	rel_op add_op mul_op prefix_op 
        constant expr exprs psymbol pexpr
        literal snf.

Rootsymbol snf.

Left 501 bor_op.
Left 601 band_op.
Unary 751 bnot_op.
Left 700 rel_op.
Left 800 add_op.
Left 900 mul_op.
Unary 1000 prefix_op.

snf -> literal snf : ['$1' | '$2'].
snf -> '.' : [].

literal -> '!' pexpr : {'not','$2'}.
literal -> true  : true.
literal -> false : false.
literal -> pexpr : '$1'.

bor_op  -> '|' : '$1'.
band_op -> '&' : '$1'.
bxor_op -> '^' : '$1'.
bnot_op -> '~' : '$1'.

add_op  -> '+' : '$1'.
add_op  -> '-' : '$1'.
mul_op -> '*' : '$1'.
mul_op -> '/' : '$1'.
mul_op -> '%' : '$1'.
mul_op -> '<<'  : '$1'.
mul_op -> '>>'  : '$1'.
mul_op -> '<<<' : '$1'.
mul_op -> '>>>' : '$1'.

prefix_op -> '+' : '$1'.
prefix_op -> '-' : '$1'.

rel_op -> '<'  : '$1'.
rel_op -> '<=' : '$1'.
rel_op -> '>'  : '$1'.
rel_op -> '>=' : '$1'.
rel_op -> '==' : '$1'.
rel_op -> '!=' : '$1'.

constant -> hexnum : hex('$1').
constant -> octnum : oct('$1').
constant -> decnum : dec('$1').
constant -> binnum : bin('$1').
constant -> flonum : flo('$1').
constant -> chrnum : chr('$1').

%%
%% Arithmetic expression function expression
%%
expr -> identifier        : id('$1').
expr -> symbol            : id('$1').
expr -> constant          : '$1'.
expr -> bnot_op expr      : 
	    #cunary {line=line('$1'),op=op('$1'),arg='$2'}.
expr -> prefix_op expr : 
	    case op('$1') of
	       '-' when is_integer('$2') -> -('$2');
	 	_ ->
		    #cunary {line=line('$1'),op=op('$1'),arg='$2'}
	    end.
expr -> '(' expr ')' : '$2'.
expr -> identifier '(' exprs ')' : 
	    #ccall{ line=line('$2'), func='$1', args='$3'}.
expr -> expr add_op expr   :
	    #cbinary{ line=line('$2'), op=op('$2'),arg1='$1',arg2='$3'}.
expr -> expr mul_op expr   :
	    #cbinary{ line=line('$2'), op=op('$2'),arg1='$1',arg2='$3'}.
expr -> expr rel_op expr   :
	    #cbinary{ line=line('$2'), op=op('$2'),arg1='$1',arg2='$3'}.
expr -> expr band_op expr  :
	    #cbinary{ line=line('$2'), op=op('$2'),arg1='$1',arg2='$3'}.
expr -> expr bor_op  expr  :
	    #cbinary{ line=line('$2'), op=op('$2'),arg1='$1',arg2='$3'}.
expr -> expr bxor_op expr  :
	    #cbinary{ line=line('$2'), op=op('$2'),arg1='$1',arg2='$3'}.
expr -> identifier '=' expr  :
	    #cassign{ line=line('$2'), op=op('$2'), lhs='$1',rhs='$3'}.

%% list of expr
exprs -> expr : ['$1'].
exprs -> expr ',' exprs : ['$1' | '$3'].

pexpr -> psymbol                    : { p, '$1', []}.
pexpr -> psymbol '(' ')'            : { p, '$1', []}.
pexpr -> psymbol '(' exprs ')'      : { p, '$1', '$3'}.
pexpr -> pexpr '[' expr ']' : {bit_index,'$1','$3'}.

psymbol -> 'A' : 'A'.
psymbol -> 'E' : 'E'.
psymbol -> symbol : name('$1').

Erlang code.

-include("varp_bic.hrl").

op({Op,_Ln}) -> Op.

line([H|_]) -> line(H);
line({_,Ln}) -> Ln.

name({symbol,_,Name})       -> list_to_atom(Name);
name({identifier,_,Name})   -> list_to_atom(Name).

id({identifier,Line,Name}) -> #cid { line=Line, name=Name};
id({symbol,Line,Name})     -> #cid { line=Line, name=Name}.

bin({binnum,Line,Val}) ->
    #cconst { line=Line, base=2, value=Val}.
    
oct({octnum,Line,Val}) ->
    #cconst { line=Line, base=8, value=Val}.

hex({hexnum,Line,Val}) ->
    #cconst { line=Line, base=16, value=Val}.

dec({decnum,Line,Val}) ->
    #cconst { line=Line, base=10, value=Val}.

chr({chrnum,Line,Val}) ->
    #cconst { line=Line, base=char, value=Val}.

flo({flonum,Line,Val}) ->
    #cconst { line=Line, base=float, value=Val}.
