%% -*- erlang -*-
%%
%%
Terminals
	symbol variable hexnum binnum octnum decnum
        signed unsigned true false forall exists 
        eqk neqk gtk gtek ltk ltek all any none one
	'and' 'or' 'xor' 'not' imp equ 'A' 'E'
        '&' '&&' '|' '||' '^' '!' '~'  '->' '<->'
	'+' '-' '*' '/' '%' '>>>' '>>' '<<<' '<<'
	'<=' '>=' '!=' '<' '>' '=' '=='
	'{' '}' ',' ':' '(' ')' '[' ']' '..' 
	.

%% '.' ';' 

Nonterminals
	equ_op imp_op or_op and_op not_op
        bor_op band_op bxor_op bnot_op
	rel_op add_op mul_op prefix_op 
        range_op 
        integer expr exprs vexpr vexprs nexpr
        qtype quantifier psymbol pexpr lexpr lexprs
        formula .

Rootsymbol formula.

Left 300 equ_op.
Left 400 imp_op.
Left 500 or_op.
Left 501 bor_op.
Left 600 and_op.
Left 601 band_op.
Unary 750 not_op.
Unary 751 bnot_op.
Left 700 rel_op.
Left 750 range_op.
Left 800 add_op.
Left 900 mul_op.
Unary 1000 prefix_op.
Unary 1100 quantifier.

%% equ_op -> '='     : '$1'.
equ_op -> '<->'   : '$1'.
equ_op -> 'equ'   : '$1'.
equ_op -> 'xor'   : '$1'.
imp_op -> '->'    : '$1'.
imp_op -> 'imp'   : '$1'.
or_op  -> 'or'    : '$1'.
or_op  -> '||'    : '$1'.
and_op -> 'and'   : '$1'.
and_op -> '&&'    : '$1'.
not_op -> 'not'   : '$1'.
not_op -> '!'     : '$1'.

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

range_op -> '..' : range.

integer -> binnum : '$1'.
integer -> octnum : '$1'.
integer -> decnum : '$1'.
integer -> hexnum : '$1'.
    
formula  -> lexpr  : '$1'.

%%
%% Bit vector expressions
%% X:32  bit vector of 32 variables
%% I:32  bit constant of 32
%%
%% vexpr -> '(' vexpr ')'         : '$2'.
vexpr -> integer ':' nexpr     : {S,N} = '$3',{S,N,value('$1')}.
vexpr -> psymbol  ':' nexpr     : {S,N} = '$3',{S,N,'$1'}.
%% vexpr -> integer               : value('$1').
vexpr -> vexpr band_op vexpr   : {op('$2'), '$1', '$3' }.
vexpr -> vexpr bor_op vexpr    : {op('$2'), '$1', '$3' }.
vexpr -> vexpr bxor_op vexpr   : {op('$2'), '$1', '$3' }.
vexpr -> bnot_op vexpr         : {op('$1'), '$2' }.
vexpr -> vexpr add_op vexpr    : {op('$2'), '$1', '$3'}.
vexpr -> vexpr mul_op vexpr    : {op('$2'), '$1', '$3'}.
vexpr -> prefix_op vexpr       : {op('$1'), '$2'}.
vexpr -> '{' vexprs '}'        : '$2'.

vexprs -> lexpr : ['$1'].
vexprs -> lexpr ',' vexprs : ['$1' | '$3'].

%% nexpr -> expr              : {uint,'$1'}.
%% nexpr -> expr '/' signed   : {int,'$1'}.
%% nexpr -> expr '/' unsigned : {uint,'$1'}.
nexpr -> integer              : {uint,value('$1')}.
nexpr -> integer '/' signed   : {int, value('$1')}.
nexpr -> integer '/' unsigned : {uint,value('$1')}.

nexpr -> variable              : {uint,name('$1')}.
nexpr -> variable '/' signed   : {int, name('$1')}.
nexpr -> variable '/' unsigned : {uint,name('$1')}.
%% nexpr -> '-' variable : {int,name('$2')}.


    
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
expr -> expr range_op expr : { '$2', '$1', '$3' }.
%% dexpr -> dexpr '|' dexpr : { union,   '$1', '$3' }.
%% dexpr -> dexpr '*' dexpr : { product, '$1', '$3' }.
expr -> variable '=' expr  : { '=', name('$1'), '$3' }.

%% list of expr
exprs -> expr : ['$1'].
exprs -> expr ',' exprs : ['$1' | '$3'].
    
%%
%% Formulas
%%
qtype -> 'E' '!' : one.
qtype -> 'E'     : any.
qtype -> 'A'     : all.
qtype -> exists  '!' : one.
qtype -> exists  : any.
qtype -> forall  : all.
qtype -> all     : all.
qtype -> any     : any.
qtype -> one     : one.
qtype -> none    : none.
qtype -> eqk     : eqk.
qtype -> neqk    : neqk.
qtype -> gtk     : gtk.
qtype -> gtek    : gtek.
qtype -> ltk     : ltk.
qtype -> ltek    : ltek.

quantifier -> '[' all ']'     : all.
quantifier -> '[' any ']'     : any.
quantifier -> '[' none ']'    : none.
quantifier -> '[' one  ']'    : one.
quantifier -> '[' 'E' ']'     : any.
quantifier -> '[' 'E' '!' ']' : one.
quantifier -> '[' 'A' ']'     : all.
quantifier -> '[' qtype exprs ']' : {'$2','$3'}.

%% Logic expression
lexpr -> true                      : true.
lexpr -> false                     : true.
lexpr -> pexpr                     : '$1'.
lexpr -> lexpr and_op lexpr        : { op('$2'), '$1', '$3' }.
lexpr -> lexpr or_op lexpr         : { op('$2'), '$1', '$3' }.
lexpr -> lexpr imp_op lexpr        : { op('$2'), '$1', '$3' }.
lexpr -> lexpr equ_op lexpr        : { op('$2'), '$1', '$3' }.
lexpr -> not_op lexpr              : { op('$1'), '$2' }.
lexpr -> '(' lexpr ')'             : '$2'.
lexpr -> vexpr rel_op vexpr        : { op('$2'), '$1', '$3' }.
lexpr -> quantifier '(' lexprs ')' : {'$1','$3'}.
lexpr -> quantifier lexpr          : {'$1','$2'}.
lexpr -> quantifier vexpr          : {'$1','$2'}.
%% lexpr -> lexpr '[' pexpr '/' pexpr ']' : {subst,'$3','$5','$1'}.

pexpr -> psymbol                    : { p, '$1', []}.
%% pexpr -> symbol '(' ')'            : { p, name('$1'), []}.
pexpr -> psymbol '(' exprs ')'      : { p, '$1', '$3'}.

psymbol -> 'A' : 'A'.
psymbol -> 'E' : 'E'.
psymbol -> symbol : name('$1').
    
    
lexprs -> lexpr ',' lexprs : ['$1' | '$3'].
lexprs -> lexpr : ['$1'].
    
Erlang code.

op({Op,_Ln}) -> Op.

name({symbol,_,Name})       -> list_to_atom(Name);
name({variable,_,Name})     -> list_to_atom(Name).

value({decnum,_,Num})       -> list_to_integer(Num,10);
value({octnum,_,Num})       -> list_to_integer(Num,8);
value({hexnum,_,"0x"++Num}) -> list_to_integer(Num,16);
value({binnum,_,"0b"++Num}) -> list_to_integer(Num,2).
