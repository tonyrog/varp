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

literal -> '!' pexpr : {lop,'not','$2'}.
literal -> true  : true.
literal -> false : false.
literal -> pexpr : '$1'.
literal -> decnum : to_integer('$1').
literal -> '-' decnum : -to_integer('$2').

bor_op  -> '|' : 'bor'.
band_op -> '&' : 'band'.
bxor_op -> '^' : 'bxor'.
bnot_op -> '~' : 'bnor'.

add_op  -> '+' : 'add'.
add_op  -> '-' : 'sub'.
mul_op -> '*' : 'mul'.
mul_op -> '/' : 'div'.
mul_op -> '%' : 'rem'.
mul_op -> '<<'  : 'shl'.
mul_op -> '>>'  : 'shr'.
mul_op -> '<<<' : 'rol'.
mul_op -> '>>>' : 'ror'.

prefix_op -> '+' : 'pos'.
prefix_op -> '-' : 'neg'.

rel_op -> '<'  : 'lt'.
rel_op -> '<=' : 'lte'.
rel_op -> '>'  : 'gt'.
rel_op -> '>=' : 'gte'.
rel_op -> '==' : 'eq'.
rel_op -> '!=' : 'neq'.

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
expr -> bnot_op expr      : {lop,'bnot','$2'}.
expr -> prefix_op expr : 
	    case op('$1') of
	       '-' when is_integer('$2') -> -('$2');
	 	_ ->
		    {op,op('$1'),'$2'}
	    end.
expr -> '(' expr ')' : '$2'.
expr -> identifier '(' exprs ')' : 
	    {call, '$1', '$3'}.
expr -> expr add_op expr   :
	    {op, op('$2'), '$1', '$3'}.
expr -> expr mul_op expr   :
	    {op, op('$2'), '$1', '$3'}.
expr -> expr rel_op expr   :
	    {op, op=op('$2'),'$1','$3'}.
expr -> expr band_op expr  :
	    {op, op('$2'), '$1', '$3'}.
expr -> expr bor_op  expr  :
	    {op, op('$2'), '$1', '$3'}.
expr -> expr bxor_op expr  :
	    {op, op('$2'), '$1', '$3'}.
expr -> identifier '=' expr  :
	    {lop, '=', '$1', '$3'}.

%% list of expr
exprs -> expr : ['$1'].
exprs -> expr ',' exprs : ['$1' | '$3'].

pexpr -> psymbol                    : { p, '$1', []}.
pexpr -> psymbol '(' ')'            : { p, '$1', []}.
pexpr -> psymbol '(' exprs ')'      : { p, '$1', '$3'}.
pexpr -> pexpr   '[' expr ']'       : {bitindex,'$1','$3'}.

psymbol -> 'A' : <<"A">>.
psymbol -> 'E' : <<"E">>.
psymbol -> symbol : name('$1').

Erlang code.

-include("varp.hrl").

op({Op,_Ln}) -> Op.

name({symbol,_,Name})       -> Name;
name({identifier,_,Name})   -> Name.

id({identifier,_Line,Name}) -> {id,Name};
id({symbol,_Line,Name})     -> {id,Name}.

bin({binnum,_Line,"0b"++Val}) -> {const,list_to_integer(Val,2)}.
oct({octnum,_Line,Val}) -> {const,list_to_integer(Val,8)}.
hex({hexnum,_Line,"0x"++Val}) -> {const,list_to_integer(Val,16)};
hex({hexnum,_Line,"0X"++Val}) -> {const,list_to_integer(Val,16)}.
dec({decnum,_Line,Val}) -> {const,list_to_integer(Val)}.
chr({chrnum,_Line,Val}) ->  {const,Val}.
flo({flonum,_Line,Val}) ->  {const,list_to_float(Val)}.

to_integer({binnum,_,List}) -> list_to_integer(List,2);
to_integer({octnum,_,List}) -> list_to_integer(List,8);
to_integer({decnum,_,List}) -> list_to_integer(List,10);
to_integer({hexnum,_,List}) -> list_to_integer(List,16).
