%% -*- erlang -*-

Terminals
	symbol true false define declare literals
        order depth occur random identity
        'EQ' 'NEQ' 'GT' 'GTE' 'LT' 'LTE' 'NONE' 'ONE'
	'and' 'or' 'xor' 'not' 'imp' 'equ' 'A' 'E' 'ALL' 'ANY'
        'SUM' 'PROD'
        '<->' '>>>' '<<<' '$' '..'
        hexnum octnum binnum decnum flonum chrnum identifier
	'->' '<<' '>>' '<' '>' '>=' '<=' '==' '!=' ':='
	'&&' '||'
	'(' ')' '[' ']' '{' '}' ',' '.' '&' '*' '+' '-' '~' '!'
	'/' '%' '^' '|' ':' '?' '=' ';'
	'char' 'short' 'int' 'long' 'signed' 'unsigned' 
%%      'float' 'double'
	.

Nonterminals
        cidentifier
	primary_expr postfix_expr argument_expr_list
	unary_expr unary_operator
	multiplicative_expr additive_expr shift_expr
	relational_expr equality_expr and_expr exclusive_or_expr
	inclusive_or_expr logical_and_expr logical_or_expr
	conditional_expr assignment_expr assignment_operator
	expr constant
	file 
        integer sexpr
        qtype quantifier psymbol pexpr oexpr odecl odecls ldecl ldecls
        lexpr_prim
        lexpr0 lexpr1 lexpr2 lexpr3 lexpr4 lexpr40 lexpr43 lexpr45 lexpr47 
        lexpr5 lexpr6 lexpr7 lexpr8 lexpr9
        lexpr lexprs
        definition definitions
        pdecl pdecls
        .

Rootsymbol file.

file  -> definitions : {'$1',undefined}.
file  -> definitions lexpr  : {'$1','$2'}.
file  -> lexpr : {[], '$1'}.

definitions -> definition : ['$1'].
definitions -> definitions definition : '$1'++['$2'].

definition -> 'define' pexpr lexpr ';' : {define,'$2','$3'}.
definition -> 'declare' pdecls ';'     : {declare,'$2'}.
definition -> 'literals' ldecls ';'    : {literals,'$2'}.
definition -> 'order' odecls ';'       : {order,'$2'}.
    
primary_expr -> cidentifier  : '$1'.
primary_expr -> constant     : '$1'.
primary_expr -> '(' expr ')' : '$2'.
primary_expr -> '{' expr '}' : {vec,comma_list('$2')}.
    
     
postfix_expr -> primary_expr : '$1'.
postfix_expr -> postfix_expr '[' expr ']' : 
		    #cbinary {line=line('$1'),op='[]',arg1='$1',arg2='$3'}.
postfix_expr -> postfix_expr '(' ')' : 
		    #ccall {line=line('$1'),func='$1',args=[]}.
postfix_expr -> postfix_expr '(' argument_expr_list ')' :
		    #ccall {line=line('$1'),func='$1',args='$3'}.
postfix_expr -> postfix_expr '.' cidentifier :
		    #cbinary {line=line('$1'),op='.',arg1='$1',arg2='$3' }.
postfix_expr -> postfix_expr '->' cidentifier : 
		    #cbinary {line=line('$1'),op='->',arg1='$1',arg2='$3'}.

argument_expr_list -> assignment_expr : ['$1'].
argument_expr_list -> argument_expr_list ',' assignment_expr : '$1'++['$3'].

unary_expr -> postfix_expr : '$1'.
unary_expr -> unary_operator unary_expr : 
		  #cunary {line=line('$1'),op=op('$1'),arg='$2'}.

unary_operator -> '+' : '$1'.
unary_operator -> '-' : '$1'.
unary_operator -> '~' : '$1'.
unary_operator -> '!' : '$1'.

multiplicative_expr -> unary_expr : '$1'.
multiplicative_expr -> multiplicative_expr '*' unary_expr : 
		   #cbinary { line=line('$2'), op='*',arg1='$1',arg2='$3'}.
multiplicative_expr -> multiplicative_expr '/' unary_expr :
		   #cbinary { line=line('$2'), op='/',arg1='$1',arg2='$3'}.
multiplicative_expr -> multiplicative_expr '%' unary_expr :
		   #cbinary { line=line('$2'), op='%',arg1='$1',arg2='$3'}.

additive_expr -> multiplicative_expr : '$1'.
additive_expr -> additive_expr '+' multiplicative_expr :
		   #cbinary { line=line('$2'), op='+',arg1='$1',arg2='$3'}.
additive_expr -> additive_expr '-' multiplicative_expr :
		   #cbinary { line=line('$2'), op='-',arg1='$1',arg2='$3'}.

shift_expr -> additive_expr : '$1'.
shift_expr -> shift_expr '<<' additive_expr :
		   #cbinary { line=line('$2'),op='<<',arg1='$1',arg2='$3'}.
shift_expr -> shift_expr '>>' additive_expr :
		  #cbinary { line=line('$2'),op='>>',arg1='$1',arg2='$3'}.

relational_expr -> shift_expr : '$1'.
relational_expr -> relational_expr '<' shift_expr :
		  #cbinary { line=line('$2'),op='<',arg1='$1',arg2='$3'}.
relational_expr -> relational_expr '>' shift_expr :
		  #cbinary { line=line('$2'),op='>',arg1='$1',arg2='$3'}.
relational_expr -> relational_expr '<=' shift_expr :
		  #cbinary { line=line('$2'),op='<=',arg1='$1',arg2='$3'}.
relational_expr -> relational_expr '>=' shift_expr :
		  #cbinary { line=line('$2'),op='>=',arg1='$1',arg2='$3'}.

equality_expr -> relational_expr : '$1'.
equality_expr -> equality_expr '==' relational_expr :
		  #cbinary { line=line('$2'),op='==',arg1='$1',arg2='$3'}.
equality_expr -> equality_expr '!=' relational_expr :
		  #cbinary { line=line('$2'),op='!=',arg1='$1',arg2='$3'}.

and_expr -> equality_expr : '$1'.
and_expr -> and_expr '&' equality_expr :
		  #cbinary { line=line('$2'),op='&',arg1='$1',arg2='$3'}.

exclusive_or_expr -> and_expr : '$1'.
exclusive_or_expr -> exclusive_or_expr '^' and_expr :
		  #cbinary { line=line('$2'),op='^',arg1='$1',arg2='$3'}.

inclusive_or_expr -> exclusive_or_expr : '$1'.
inclusive_or_expr -> inclusive_or_expr '|' exclusive_or_expr :
		  #cbinary { line=line('$2'),op='|',arg1='$1',arg2='$3'}.

logical_and_expr -> inclusive_or_expr : '$1'.
logical_and_expr -> logical_and_expr '&&' inclusive_or_expr :
		  #cbinary { line=line('$2'),op='&&',arg1='$1',arg2='$3'}.

logical_or_expr -> logical_and_expr : '$1'.
logical_or_expr -> logical_or_expr '||' logical_and_expr :
		  #cbinary { line=line('$2'),op='||',arg1='$1',arg2='$3'}.

conditional_expr -> logical_or_expr : '$1'.
conditional_expr -> logical_or_expr '?' logical_or_expr ':' conditional_expr :
		  #cifexpr { line=line('$2'),test='$1',then='$3',else='$5'}.

assignment_expr -> conditional_expr : '$1'.
assignment_expr -> conditional_expr '..' conditional_expr :
		       #crange { line=line('$2'), from='$1', to='$3' }.
assignment_expr -> unary_expr assignment_operator assignment_expr :
		       #cassign {line=line('$2'),op=op('$2'),lhs='$1',rhs='$3'}.

assignment_operator -> '=' : '$1'.

expr -> assignment_expr : '$1'.
expr -> expr ',' assignment_expr : 
     	#cbinary { line=line('$2'), op=',',arg1='$1',arg2='$3'}.

constant -> hexnum : hex('$1').
constant -> octnum : oct('$1').
constant -> decnum : dec('$1').
constant -> binnum : bin('$1').
constant -> flonum : flo('$1').
constant -> chrnum : chr('$1').

cidentifier -> identifier : id('$1').
cidentifier -> symbol     : id('$1').
cidentifier -> true       : id('$1').
cidentifier -> false      : id('$1').
cidentifier -> 'E'        : id('$1').
cidentifier -> 'A'        : id('$1').
%%  'A' 'E' 
%% FIXME symbols below as cidentifiers!
%% 'EQ' 'NEQ' 'GT' 'GTE' 'LT' 'LTE' 'NONE' 'ONE'
%% 'and' 'or' 'xor' 'not' imp equ 'ALL' 'ANY' 'true' 'false'

%%
%% Logical stuff
%%

integer -> binnum : '$1'.
integer -> octnum : '$1'.
integer -> decnum : '$1'.
integer -> hexnum : '$1'.

%%
%% Formulas
%%
qtype -> 'E' '!' : 'ONE'.
qtype -> 'E'     : 'ANY'.
qtype -> 'A'     : 'ALL'.
qtype -> 'ALL'   : op('$1').
qtype -> 'ANY'   : op('$1').
qtype -> 'ONE'   : op('$1').
qtype -> 'NONE'  : op('$1').
qtype -> 'EQ'    : op('$1').
qtype -> 'NEQ'   : op('$1').
qtype -> 'GT'    : op('$1').
qtype -> 'GTE'   : op('$1').
qtype -> 'LT'    : op('$1').
qtype -> 'LTE'   : op('$1').
qtype -> 'SUM'   : op('$1').
qtype -> 'PROD'  : op('$1').
    
quantifier -> '[' 'ALL' ']'   : op('$2').
quantifier -> '[' 'ANY' ']'   : op('$2').
quantifier -> '[' 'NONE' ']'  : op('$2').
quantifier -> '[' 'ONE'  ']'  : op('$2').
quantifier -> '[' 'SUM' ']'   : op('$2').
quantifier -> '[' 'PROD' ']'  : op('$2').
quantifier -> '[' 'E' ']'     : 'ANY'.
quantifier -> '[' 'E' '!' ']' : 'ONE'.
quantifier -> '[' 'A' ']'     : 'ALL'.
quantifier -> '[' qtype expr ']' : {'$2',comma_list('$3')}.

%%
%% Declaration of boolean and integer "predicates"
%%
pdecl -> pexpr ':' sexpr '/' 'signed'   : {'$1',int,'$3'}.
pdecl -> pexpr ':' sexpr '/' 'unsigned' : {'$1',uint,'$3'}.
pdecl -> pexpr ':' sexpr                : {'$1',uint,'$3'}.

pdecls -> pdecl : ['$1'].
pdecls -> pdecls ',' pdecl : '$1'++['$3'].

ldecls -> ldecl : ['$1'].
ldecls -> ldecls ',' ldecl : '$1'++['$3'].

ldecl -> identifier : name('$1').

odecls -> odecl : ['$1'].
odecls -> odecls ',' odecl : '$1'++['$3'].

odecl -> depth      : '+depth'.
odecl -> '+' depth  : '+depth'.
odecl -> '-' depth  : '-depth'.
odecl -> occur      : '+occur'.
odecl -> '+' occur  : '+occur'.
odecl -> '-' occur  : '-occur'.
odecl -> random     : '$1'.
odecl -> identity   : '$1'.
odecl -> oexpr      : '$1'.
    
%% bit collection
oexpr -> pexpr                          : '$1'.
oexpr -> pexpr '[' expr ']'             : {bit_index,'$1','$3'}.
oexpr -> pexpr '[' expr ':' expr ']'    : {bit_range, '$1', '$3', '$5', 1}.
oexpr -> pexpr '[' expr ':' expr ':' expr ']'  : 
	     { bit_range, '$1', '$3', '$5', '$7'}.
oexpr -> pexpr ':' sexpr '/' 'signed'   : {int,'$3','$1'}.
oexpr -> pexpr ':' sexpr '/' 'unsigned' : {uint,'$3','$1'}.
oexpr -> '!' pexpr                      : {'!', '$2'}.

%%
%% Logic expression
%%
lexpr_prim -> integer               : constant(value('$1')).
lexpr_prim -> pexpr                 : '$1'.
lexpr_prim -> identifier            : name('$1').  %% meta/env variable
lexpr_prim -> '$' '(' expr ')'      : {'expr','$3'}.

lexpr0 -> lexpr_prim                : '$1'.
lexpr0 -> true                      : true.
lexpr0 -> false                     : false.
lexpr0 -> '-' lexpr0                : {'-', '$2'}.
lexpr0 -> 'not' lexpr0              : { op('$1'), '$2' }.
lexpr0 -> '!' lexpr0                : { op('$1'), '$2' }.
lexpr0 -> '~' lexpr0                : { op('$1'), '$2' }.
lexpr0 -> '(' lexpr ')'             : '$2'.
lexpr0 -> '{' lexprs '}'            : {vec,'$2'}.
lexpr0 -> identifier '(' lexprs ')' : { name('$1'), '$3'}. %% meta function
lexpr0 -> quantifier '(' lexprs ')' : {'$1','$3'}.
lexpr0 -> quantifier lexpr0         : {'$1','$2'}.

lexpr0 -> lexpr_prim ':' sexpr '/' 'signed'   : {int,'$3','$1'}.
lexpr0 -> lexpr_prim ':' sexpr '/' 'unsigned' : {uint,'$3','$1'}.
lexpr0 -> lexpr_prim ':' sexpr                : {uint,'$3','$1'}.
lexpr0 -> lexpr0 '[' expr ']'           : { bit_index, '$1', '$3'}.
lexpr0 -> lexpr0 '[' expr ':' expr ']'  : { bit_range,'$1','$3','$5', 1}.
lexpr0 -> lexpr0 '[' expr ':' expr ':' expr ']' :
	      { bit_range,'$1','$3','$5','$7'}.

lexpr1 -> lexpr0                  : '$1'.
lexpr1 -> lexpr1 '*' lexpr0       : { op('$2'), '$1', '$3'}.
lexpr1 -> lexpr1 '/' lexpr0       : { op('$2'), '$1', '$3'}.
lexpr1 -> lexpr1 '%' lexpr0       : { op('$2'), '$1', '$3'}.

lexpr2 -> lexpr1                  : '$1'.
lexpr2 -> lexpr2 '+' lexpr1       : { op('$2'), '$1', '$3' }.
lexpr2 -> lexpr2 '-' lexpr1       : { op('$2'), '$1', '$3' }.

lexpr3 -> lexpr2                  : '$1'.
lexpr3 -> lexpr3 '<<' lexpr2      : { op('$2'), '$1', '$3'}.
lexpr3 -> lexpr3 '>>' lexpr2      : { op('$2'), '$1', '$3'}.
lexpr3 -> lexpr3 '<<<' lexpr2     : { op('$2'), '$1', '$3'}.
lexpr3 -> lexpr3 '>>>' lexpr2     : { op('$2'), '$1', '$3'}.

lexpr4 -> lexpr3                  : '$1'.
lexpr4 -> lexpr4 '<'  lexpr3      : { op('$2'), '$1', '$3' }.
lexpr4 -> lexpr4 '<=' lexpr3      : { op('$2'), '$1', '$3' }.
lexpr4 -> lexpr4 '>'  lexpr3      : { op('$2'), '$1', '$3' }.
lexpr4 -> lexpr4 '>=' lexpr3      : { op('$2'), '$1', '$3' }.

lexpr40 -> lexpr4                 : '$1'.
lexpr40 -> lexpr40 '==' lexpr4    : { op('$2'), '$1', '$3' }.
lexpr40 -> lexpr40 ':=' lexpr4    : { op('$2'), '$1', '$3' }.
lexpr40 -> lexpr40 '!=' lexpr4    : { op('$2'), '$1', '$3' }.

lexpr43 -> lexpr40                : '$1'.
lexpr43 -> lexpr43 '&' lexpr40    : { op('$2'), '$1', '$3' }.   

lexpr45 -> lexpr43                : '$1'.
lexpr45 -> lexpr45 '^' lexpr43    : { op('$2'), '$1', '$3' }.

lexpr47 -> lexpr45                : '$1'.
lexpr47 -> lexpr47 '|' lexpr45    : { op('$2'), '$1', '$3' }.

lexpr5 -> lexpr47                 : '$1'.
lexpr5 -> lexpr5 'and' lexpr47    : { op('$2'), '$1', '$3' }.
lexpr5 -> lexpr5 '&&'  lexpr47    : { op('$2'), '$1', '$3' }.

lexpr6 -> lexpr5                  : '$1'.
lexpr6 -> lexpr6 'xor' lexpr5     : { op('$2'), '$1', '$3' }.

lexpr7 -> lexpr6                  : '$1'.
lexpr7 -> lexpr7 'or'  lexpr6     : { op('$2'), '$1', '$3' }.
lexpr7 -> lexpr7 '||'  lexpr6     : { op('$2'), '$1', '$3' }.

lexpr8 -> lexpr7                  : '$1'.
lexpr8 -> lexpr8 '->'  lexpr7     : { op('$2'), '$1', '$3' }.
lexpr8 -> lexpr8 'imp' lexpr7     : { op('$2'), '$1', '$3' }.

lexpr9 -> lexpr8                  : '$1'.
lexpr9 -> lexpr9 'equ' lexpr8     : { op('$2'), '$1', '$3' }.
lexpr9 -> lexpr9 '<->' lexpr8     : { op('$2'), '$1', '$3' }.

lexpr -> lexpr9                   : '$1'.

%% fixme?
%% lexpr -> lexpr '[' pexpr '/' pexpr ']' : {subst,'$3','$5','$1'}.

lexprs -> lexpr ',' lexprs : ['$1' | '$3'].
lexprs -> lexpr : ['$1'].

%% sign -> signed   : int.
%% sign -> unsigned : uint.

%% sexpr -> '-' sexpr : {'-','$2'}.
%% sexpr -> sexpr '*' sexpr : {'*','$1','$3'}.
%% sexpr -> sexpr '+' sexpr : {'+','$1','$3'}.
%% sexpr -> sexpr '-' sexpr : {'-','$1','$3'}.
sexpr -> '(' expr ')' : '$2'.
sexpr -> integer  : value('$1').
sexpr -> 'char' : machine_sizeof(char).
sexpr -> 'short' : machine_sizeof(short).
sexpr -> 'long' : machine_sizeof(long).
sexpr -> 'int' : machine_sizeof(int).
sexpr -> identifier : name('$1').

pexpr -> psymbol               : { p, '$1', []}.
pexpr -> psymbol '(' ')'       : { p, '$1', []}.
pexpr -> psymbol '(' expr ')'  : { p, '$1', comma_list('$3')}.

psymbol -> 'A' : 'A'.
psymbol -> 'E' : 'E'.
psymbol -> symbol : name('$1').

Erlang code.

-include("varp.hrl").
-import(lists, [map/2, member/2]).
-export([init/0]).

init() ->
    ok.

id({identifier,Line,Name}) -> #cid { line=Line, name=Name};
id({symbol,Line,Name})     -> #cid { line=Line, name=Name};
id({true,Line})            -> #cid { line=Line, name="true"};
id({false,Line})           -> #cid { line=Line, name="false"};
id({'E',Line})             -> #cid { line=Line, name="E"};
id({'A',Line})             -> #cid { line=Line, name="A"}.

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

op({Op,_Ln})     -> Op.

line([H|_]) -> line(H);
line(T) when is_tuple(T) -> element(2,T).

constant(N) when N >= 0   -> {uint,varp_math:integer_size(N),N};
constant(N) when N < 0   -> {int,varp_math:integer_size(N),N}.

name({symbol,_,Name})       -> list_to_atom(Name);
name({identifier,_,Name})   -> list_to_atom(Name).

value({decnum,_,Num})       -> list_to_integer(Num,10);
value({octnum,_,Num})       -> list_to_integer(Num,8);
value({hexnum,_,"0x"++Num}) -> list_to_integer(Num,16);
value({binnum,_,"0b"++Num}) -> list_to_integer(Num,2).

comma_list(#cbinary{op=',',arg1=A1,arg2=A2}) ->
    comma_list(A1) ++ comma_list(A2);
comma_list(A) ->
    [A].

%% fixme make this flexible
machine_sizeof(char)  ->
    application:get_env(varp, sizeof_char, 8);
machine_sizeof(short) ->
    application:get_env(varp, sizeof_short, 16);
machine_sizeof(int)   ->
    application:get_env(varp, sizeof_int, 32);
machine_sizeof(long)  ->
    application:get_env(varp, sizeof_long, 64).

%% machine_endian() ->
%%    application:get_enc(varp, endian, little).
