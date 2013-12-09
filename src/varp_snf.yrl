%% -*- erlang -*-
%%
%%
Terminals
	symbol variable hexnum binnum octnum decnum
        true false
	'A' 'E'
        '&' '|' '^' '!' '~'
	'+' '-' '*' '/' '%' '>>>' '>>' '<<<' '<<'
	'<=' '>=' '!=' '<' '>' '=' '=='
	',' '(' ')' '.'
	.

Nonterminals
        bor_op band_op bxor_op bnot_op
	rel_op add_op mul_op prefix_op 
        integer expr exprs psymbol pexpr
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

integer -> binnum : '$1'.
integer -> octnum : '$1'.
integer -> decnum : '$1'.
integer -> hexnum : '$1'.


%%
%% Arithmetic expression function expression
%%
expr -> variable          : name('$1').
expr -> integer           : value('$1').
expr -> bnot_op expr      : {op('$1'), '$2' }.
expr -> prefix_op expr : 
	    case op('$1') of
	       '-' when is_integer('$2') -> -('$2');
	       Op -> {Op,'$2'}
	    end.
expr -> '(' expr ')' : '$2'.
expr -> variable '(' exprs ')' : { f, name('$1'), '$3'}.
expr -> expr add_op expr   : { op('$2'), '$1', '$3' }.
expr -> expr mul_op expr   : { op('$2'), '$1', '$3' }.
expr -> expr rel_op expr   : { op('$2'), '$1', '$3' }.
expr -> expr band_op expr  : {op('$2'), '$1', '$3' }.
expr -> expr bor_op  expr  : {op('$2'), '$1', '$3' }.
expr -> expr bxor_op expr  : {op('$2'), '$1', '$3' }.
expr -> variable '=' expr  : { '=', name('$1'), '$3' }.

%% list of expr
exprs -> expr : ['$1'].
exprs -> expr ',' exprs : ['$1' | '$3'].

pexpr -> psymbol                    : { p, '$1', []}.
pexpr -> psymbol '(' ')'            : { p, '$1', []}.
pexpr -> psymbol '(' exprs ')'      : { p, '$1', '$3'}.

psymbol -> 'A' : 'A'.
psymbol -> 'E' : 'E'.
psymbol -> symbol : name('$1').


Erlang code.

op({Op,_Ln}) -> Op.

name({symbol,_,Name})       -> list_to_atom(Name);
name({variable,_,Name})     -> list_to_atom(Name).

value({decnum,_,Num})       -> list_to_integer(Num,10);
value({octnum,_,Num})       -> list_to_integer(Num,8);
value({hexnum,_,"0x"++Num}) -> list_to_integer(Num,16);
value({binnum,_,"0b"++Num}) -> list_to_integer(Num,2).
