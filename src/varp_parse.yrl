%% -*- erlang -*-
%%
%%
Terminals
	symbol variable hexnum binnum octnum decnum
        signed unsigned 
	'and' 'or' 'xor' 'not' imp equ
        '&' '&&' '|' '||' '^' '!' '~'  '->' '<->'
	'+' '-' '*' '/' '%' '>>>' '>>' '<<<' '<<'
	'<=' '>=' '!=' '<' '>' '=' '=='
	';' '{' '}' ',' ':' '(' ')' '[' ']' '..' '.'
	.

Nonterminals
	equ_op imp_op or_op and_op not_op
	rel_op add_op mul_op prefix_op 
        integer expr exprs dexpr rexpr aexpr nexpr vars
        qtype quantifier pexpr lexpr lexprs formula .

Rootsymbol formula.

Left 300 equ_op.
Left 400 imp_op.
Left 500 or_op.
Left 600 and_op.
Unary 750 not_op.
Left 700 rel_op.
Left 800 add_op.
Left 900 mul_op.
Unary 1000 prefix_op.
Unary 1100 quantifier.

equ_op -> '='     : '$1'.
equ_op -> '<->'   : '$1'.
equ_op -> 'equ'   : '$1'.
equ_op -> '^'   : '$1'.
equ_op -> 'xor'   : '$1'.
imp_op -> '->'   : '$1'.
imp_op -> 'imp'   : '$1'.
or_op  -> 'or'    : '$1'.
or_op  -> '|'     : '$1'.
or_op  -> '||'    : '$1'.
and_op -> 'and'   : '$1'.
and_op -> '&'   : '$1'.
and_op -> '&&'   : '$1'.
not_op -> 'not'   : '$1'.
not_op -> '!'  : '$1'.
not_op -> '~'  : '$1'.

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
    
formula  -> lexpr  : '$1'.

%%
%% domain expressions
%%
dexpr -> variable : name('$1').
dexpr -> rexpr '..' rexpr : { range, '$1', '$3' }.
dexpr -> dexpr '+' dexpr  : { union, '$1', '$3'}.
dexpr -> dexpr '-' dexpr  : { subtract, '$1', '$3'}.
dexpr -> dexpr '/' dexpr  : { intersect, '$1', '$3'}.
dexpr -> dexpr '*' dexpr  : { product, '$1', '$3'}.

rexpr -> integer : value('$1').
rexpr -> variable : name('$1').

%%
%% Arithmentic expressions
%%
aexpr -> integer ':' nexpr : {S,N} = '$3',{S,N,value('$1')}.
aexpr -> symbol  ':' nexpr : {S,N} = '$3',{S,N,name('$1')}.
aexpr -> symbol              : {var,name('$1')}.
aexpr -> integer             : value('$1').
aexpr -> aexpr add_op aexpr  : {op('$2'), '$1', '$3'}.
aexpr -> aexpr mul_op aexpr  : {op('$2'), '$1', '$3'}.
aexpr -> prefix_op aexpr     : {op('$1'), '$2'}.

nexpr -> integer      : {uint,value('$1')}.
nexpr -> '-' integer  : {int, value('$2')}.
nexpr -> variable     : {uint,name('$1')}.
nexpr -> '-' variable : {int,name('$2')}.
    
%%
%% arithmetic expression
%%
expr -> variable                   :   name('$1').
expr -> integer                    :   value('$1').
expr -> prefix_op expr : 
	    case op('$1') of
	       '-' when is_integer('$2') -> -('$2');
	       Op -> {Op,'$2'}
	    end.
expr -> expr '!'     : {call, factorial, ['$1']}.
expr -> '|' expr '|' : {call, abs, ['$2']}.
expr -> '(' expr ')' : '$2'.
expr -> variable '(' exprs ')' : { call, name('$1'), '$3'}.
expr -> expr add_op expr : { op('$2'), '$1', '$3' }.
expr -> expr mul_op expr : { op('$2'), '$1', '$3' }.

%% list of expr
exprs -> expr		: ['$1'].
exprs -> expr ',' exprs : ['$1' | '$3'].

%%
%% Formulas
%%
qtype -> symbol '!' :
	 case '$1' of
	    {_,_,"E"} -> one
	 end.
qtype -> symbol :
	 case '$1' of
	     {_,_,"E"} -> exists;
	     {_,_,"A"} -> forall
	 end.

quantifier -> '(' qtype vars ')' : {'$2', '$3', default }.
quantifier -> '(' qtype vars '=' dexpr ')' : {'$2','$3','$5'}.

vars -> variable : [name('$1')].
vars -> variable ',' vars : [name('$1')|'$3'].

%% Logic expression
lexpr -> pexpr                     : '$1'.
lexpr -> lexpr and_op lexpr        : { op('$2'), '$1', '$3' }.
lexpr -> lexpr or_op lexpr         : { op('$2'), '$1', '$3' }.
lexpr -> lexpr imp_op lexpr        : { op('$2'), '$1', '$3' }.
lexpr -> lexpr equ_op lexpr        : { op('$2'), '$1', '$3' }.
lexpr -> not_op lexpr              : { op('$1'), '$2' }.
lexpr -> '(' lexpr ')'             : '$2'.
lexpr -> aexpr rel_op aexpr        : { op('$2'), '$1', '$3' }.
lexpr -> quantifier lexpr          : {'$1','$2'}.
lexpr -> quantifier '(' lexprs ')' : {'$1','$2'}.
lexpr -> lexpr '[' pexpr '/' pexpr ']' : {subst,element(2,'$3'),element(2,'$5'),'$1'}.

pexpr -> symbol                    : { var, name('$1')}.
pexpr -> symbol '(' ')'            : { var, name('$1')}.
pexpr -> symbol '(' exprs ')'      : { var, list_to_tuple([name('$1')|'$3']) }.
    
lexprs -> lexpr ',' lexprs : ['$1' | '$2'].
lexprs -> lexpr : ['$1'].
    
Erlang code.

op({Op,_Ln}) -> Op.

name({symbol,_,Name}) -> list_to_atom(Name);
name({variable,_,Name}) -> list_to_atom(Name).

value({decnum,_,Num}) -> list_to_integer(Num,10);
value({octnum,_,Num}) -> list_to_integer(Num,8);
value({hexnum,_,"0x"++Num}) -> list_to_integer(Num,16);
value({binnum,_,"0b"++Num}) -> list_to_integer(Num,2).
