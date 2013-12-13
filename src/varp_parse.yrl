%% -*- erlang -*-
%%
%%
Terminals
	symbol variable hexnum binnum octnum decnum
        signed unsigned true false 
        eqk neqk gtk gtek ltk ltek all any none one
	'and' 'or' 'xor' 'not' imp equ 'A' 'E'
        '&' '&&' '|' '||' '^' '!' '~'  '->' '<->'
	'+' '-' '*' '/' '%' '>>>' '>>' '<<<' '<<'
	'<=' '>=' '!=' '<' '>' '=' '==' ':='
	'{' '}' ',' ':' ';' '(' ')' '[' ']' '..'  '#'
	.

%% '.'

Nonterminals
        prefix_op sign
        integer expr exprs sexpr
        qtype quantifier psymbol pexpr lexpr lexprs
        file definition definitions.

Rootsymbol file.

Left 300 '<->' 'equ' 'xor'.
Left 301 '^'.
Left 400 '->'.
Left 400 'imp'.

Left 500  'or' '||'.
Left 501  '|'.
Left 600 'and' '&&'.
Left 601 '&'.
Unary 750 '!' 'not'.
Unary 751 '~'.
Left 700 '<' '<=' '>' '>=' '==' '!='.
Left 750 '..'.
Left 800 '+' '-'.
Left 900 '*' '<<' '>>' '<<<' '>>>'.
Left 910 ':'.
Left 920 '/' '%'.


Unary 1000 prefix_op.
Unary 1100 quantifier.
Right 100 ':='.

prefix_op -> '+' : '$1'.
prefix_op -> '-' : '$1'.

integer -> binnum : '$1'.
integer -> octnum : '$1'.
integer -> decnum : '$1'.
integer -> hexnum : '$1'.
    

definitions -> '$empty' : [].
definitions -> definition ';' definitions : ['$1'|'$3'].

definition -> '#' pexpr ':=' lexpr : {'$2','$4'}.

file  -> definitions : {'$1',undefined}.
file  -> definitions lexpr  : {'$1','$2'}.


%%
%% Arithmetic expression function expression
%%
expr -> variable     : name('$1').
expr -> integer      : value('$1').
expr -> '~' expr     : {op('$1'), '$2' }.
expr -> prefix_op expr : 
	    if element(1,'$1') =:= '-',is_integer('$2') ->
		    -'$2'; 
	       true -> {'-','$2'}
	    end.
expr -> '(' expr ')' : '$2'.
expr -> variable '(' exprs ')' : { f, name('$1'), '$3'}.
expr -> expr '+' expr   : { op('$2'), '$1', '$3' }.
expr -> expr '-' expr   : { op('$2'), '$1', '$3' }.
expr -> expr '*' expr   : {op('$2'), '$1', '$3'}.
expr -> expr '/' expr   : {op('$2'), '$1', '$3'}.
expr -> expr '%' expr   : {op('$2'), '$1', '$3'}.
expr -> expr '<<' expr  : {op('$2'), '$1', '$3'}.
expr -> expr '>>' expr  : {op('$2'), '$1', '$3'}.
expr -> expr '<' expr   : { op('$2'), '$1', '$3' }.
expr -> expr '<=' expr  : { op('$2'), '$1', '$3' }.
expr -> expr '>' expr   : { op('$2'), '$1', '$3' }.
expr -> expr '>=' expr   : { op('$2'), '$1', '$3' }.
expr -> expr '==' expr  : { op('$2'), '$1', '$3' }.
expr -> expr '!=' expr  : { op('$2'), '$1', '$3' }.
expr -> expr '&' expr  : {op('$2'), '$1', '$3' }.
expr -> expr '|' expr  : {op('$2'), '$1', '$3' }.
expr -> expr '^' expr  : {op('$2'), '$1', '$3' }.
expr -> expr '..' expr : { range, '$1', '$3' }.
expr -> variable '=' expr  : { '=', name('$1'), '$3' }.

%% list of expr
exprs -> expr : ['$1'].
exprs -> expr ',' exprs : ['$1' | '$3'].

%% dexpr -> dexpr '|' dexpr : { union,   '$1', '$3' }.
%% dexpr -> dexpr '*' dexpr : { product, '$1', '$3' }.
    
%%
%% Formulas
%%
qtype -> 'E' '!' : one.
qtype -> 'E'     : any.
qtype -> 'A'     : all.
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
lexpr -> true                     : true.
lexpr -> false                    : false.
lexpr -> integer                  : constant(value('$1')).
lexpr -> variable                 : {var,name('$1')}.
lexpr -> '-' lexpr                : {'-', '$2'}.

lexpr -> pexpr                    : '$1'.
lexpr -> lexpr ':' sexpr '/' signed   : {int,'$3','$1'}.
lexpr -> lexpr ':' sexpr '/' unsigned : {uint,'$3','$1'}.
lexpr -> lexpr ':' sexpr              : {uint,'$3','$1'}.

lexpr -> lexpr '+' lexpr          : { op('$2'), '$1', '$3' }.
lexpr -> lexpr '-' lexpr          : { op('$2'), '$1', '$3' }.
lexpr -> lexpr '*' lexpr          : { op('$2'), '$1', '$3'}.
lexpr -> lexpr '/' lexpr          : { op('$2'), '$1', '$3'}.
lexpr -> lexpr '%' lexpr          : { op('$2'), '$1', '$3'}.
lexpr -> lexpr '<<' lexpr         : { op('$2'), '$1', '$3'}.
lexpr -> lexpr '>>' lexpr         : { op('$2'), '$1', '$3'}.
lexpr -> lexpr '<<<' lexpr        : { op('$2'), '$1', '$3'}.
lexpr -> lexpr '>>>' lexpr        : { op('$2'), '$1', '$3'}.
lexpr -> lexpr 'and' lexpr        : { op('$2'), '$1', '$3' }.
lexpr -> lexpr '&&'  lexpr        : { op('$2'), '$1', '$3' }.
lexpr -> lexpr '&'   lexpr        : { op('$2'), '$1', '$3' }.
lexpr -> lexpr 'or'  lexpr        : { op('$2'), '$1', '$3' }.
lexpr -> lexpr '||'  lexpr        : { op('$2'), '$1', '$3' }.
lexpr -> lexpr '|'   lexpr        : { op('$2'), '$1', '$3' }.
lexpr -> lexpr '->'  lexpr        : { op('$2'), '$1', '$3' }.
lexpr -> lexpr 'imp' lexpr        : { op('$2'), '$1', '$3' }.
lexpr -> lexpr 'xor' lexpr        : { op('$2'), '$1', '$3' }.
lexpr -> lexpr '^'   lexpr        : { op('$2'), '$1', '$3' }.
lexpr -> lexpr 'equ' lexpr        : { op('$2'), '$1', '$3' }.
lexpr -> lexpr '<->' lexpr        : { op('$2'), '$1', '$3' }.

lexpr -> 'not' lexpr              : { op('$1'), '$2' }.
lexpr -> '!' lexpr                : { op('$1'), '$2' }.
lexpr -> '~' lexpr                : { op('$1'), '$2' }.
lexpr -> '(' lexpr ')'            : '$2'.
lexpr -> variable '(' lexprs ')'  : { name('$1'), '$3'}.
    
lexpr -> lexpr '<'  lexpr          : { op('$2'), '$1', '$3' }.
lexpr -> lexpr '<=' lexpr          : { op('$2'), '$1', '$3' }.
lexpr -> lexpr '>'  lexpr          : { op('$2'), '$1', '$3' }.
lexpr -> lexpr '>=' lexpr          : { op('$2'), '$1', '$3' }.
lexpr -> lexpr '==' lexpr          : { op('$2'), '$1', '$3' }.
lexpr -> lexpr '!=' lexpr          : { op('$2'), '$1', '$3' }.
lexpr -> quantifier '(' lexprs ')' : {'$1','$3'}.
lexpr -> quantifier lexpr          : {'$1','$2'}.
lexpr -> '{' lexprs '}'            : {vec,'$2'}.
%% fixme?
%% lexpr -> lexpr '[' pexpr '/' pexpr ']' : {subst,'$3','$5','$1'}.

lexprs -> lexpr ',' lexprs : ['$1' | '$3'].
lexprs -> lexpr : ['$1'].

sign -> signed   : int.
sign -> unsigned : uint.

%% sexpr -> '-' sexpr : {'-','$2'}.
%% sexpr -> sexpr '*' sexpr : {'*','$1','$3'}.
%% sexpr -> sexpr '+' sexpr : {'+','$1','$3'}.
%% sexpr -> sexpr '-' sexpr : {'-','$1','$3'}.
sexpr -> '(' expr ')' : '$2'.
sexpr -> integer  : value('$1').
sexpr -> variable : name('$1').
     

pexpr -> psymbol                    : { p, '$1', []}.
pexpr -> psymbol '(' ')'            : { p, '$1', []}.
pexpr -> psymbol '(' exprs ')'      : { p, '$1', '$3'}.

psymbol -> 'A' : 'A'.
psymbol -> 'E' : 'E'.
psymbol -> symbol : name('$1').
    

Erlang code.

constant(N) when N >= 0   -> {uint,varp_math:integer_size(N),N};
constant(N) when N < 0   -> {int,varp_math:integer_size(N),N}.

op({Op,_Ln}) -> Op.

name({symbol,_,Name})       -> list_to_atom(Name);
name({variable,_,Name})     -> list_to_atom(Name).

value({decnum,_,Num})       -> list_to_integer(Num,10);
value({octnum,_,Num})       -> list_to_integer(Num,8);
value({hexnum,_,"0x"++Num}) -> list_to_integer(Num,16);
value({binnum,_,"0b"++Num}) -> list_to_integer(Num,2).
