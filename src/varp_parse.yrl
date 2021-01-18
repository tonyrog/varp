%% -*- erlang -*-

Terminals
	symbol true false define declare literals assert input output
        order rank degree random identity user
        'EQ' 'NEQ' 'GT' 'GTE' 'LT' 'LTE' 'NONE' 'ONE'
	'and' 'or' 'xor' 'not' 'imp' 'equ' 'A' 'E' 'ALL' 'ANY' 'PARITY'
        'ODD' 'EVEN'
        'SUM' 'PROD' 'implies' 'equivalent'
        '<->' '>>>' '<<<' '..'
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
	conditional_expr assignment_expr
	expr constant
	file 
        integer sexpr
        qtype quantifier psymbol pexpr pcexpr oexpr odecl odecls ldecl ldecls
        lexpr_const lexpr_var
        lexpr0 lexpr10 lexpr20 lexpr30 lexpr40 lexpr41 lexpr43 lexpr45 lexpr47 
        lexpr50 lexpr60 lexpr70 lexpr80 lexpr90
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
definition -> 'assert' expr ';'        : {assert,'$2'}.
definition -> 'input' cidentifier ';'  : {input,'$2'}.
definition -> 'output' cidentifier ';' : {output,'$2'}.
    
primary_expr -> cidentifier  : '$1'.
primary_expr -> constant     : '$1'.
primary_expr -> '(' expr ')' : '$2'.
primary_expr -> '{' expr '}' : {vec,comma_list('$2')}.
    
     
postfix_expr -> primary_expr : '$1'.
postfix_expr -> postfix_expr '[' expr ']' : {'index','$1','$3'}.
postfix_expr -> postfix_expr '(' ')' : {'call','$1',[]}.
postfix_expr -> postfix_expr '(' argument_expr_list ')' : {'call','$1','$3'}.
postfix_expr -> postfix_expr '.' cidentifier : {'field','$1','$3'}.
postfix_expr -> postfix_expr '->' cidentifier :  {'pointer','$1','$3'}.

argument_expr_list -> assignment_expr : ['$1'].
argument_expr_list -> argument_expr_list ',' assignment_expr : '$1'++['$3'].

unary_expr -> postfix_expr : '$1'.
unary_expr -> unary_operator unary_expr : {'$1', '$2'}.

unary_operator -> '+' : 'pos'.
unary_operator -> '-' : 'neg'.
unary_operator -> '~' : 'bnot'.
unary_operator -> '!' : 'not'.

multiplicative_expr -> unary_expr : '$1'.
multiplicative_expr -> multiplicative_expr '*' unary_expr : {'mul','$1','$3'}.
multiplicative_expr -> multiplicative_expr '/' unary_expr : {'div','$1','$3'}.
multiplicative_expr -> multiplicative_expr '%' unary_expr : {'rem','$1','$3'}.

additive_expr -> multiplicative_expr : '$1'.
additive_expr -> additive_expr '+' multiplicative_expr : {'add','$1','$3'}.
additive_expr -> additive_expr '-' multiplicative_expr : {'sub','$1','$3'}.

shift_expr -> additive_expr : '$1'.
shift_expr -> shift_expr '<<' additive_expr : {'shl','$1','$3'}.
shift_expr -> shift_expr '>>' additive_expr : {'shr','$1','$3'}.

relational_expr -> shift_expr : '$1'.
relational_expr -> relational_expr '<' shift_expr : {'lt','$1','$3'}.
relational_expr -> relational_expr '>' shift_expr : {'gt','$1','$3'}.
relational_expr -> relational_expr '<=' shift_expr : {'lte','$1','$3'}.
relational_expr -> relational_expr '>=' shift_expr : {'gte','$1','$3'}.

equality_expr -> relational_expr : '$1'.
equality_expr -> equality_expr '==' relational_expr : {'eq','$1','$3'}.
equality_expr -> equality_expr '!=' relational_expr : {'neq','$1','$3'}.

and_expr -> equality_expr : '$1'.
and_expr -> and_expr '&' equality_expr : {'band','$1','$3'}.

exclusive_or_expr -> and_expr : '$1'.
exclusive_or_expr -> exclusive_or_expr '^' and_expr : {'bxor','$1','$3'}.

inclusive_or_expr -> exclusive_or_expr : '$1'.
inclusive_or_expr -> inclusive_or_expr '|' exclusive_or_expr :
			 {'bor','$1','$3'}.

logical_and_expr -> inclusive_or_expr : '$1'.
logical_and_expr -> logical_and_expr '&&' inclusive_or_expr : {'and','$1','$3'}.

logical_or_expr -> logical_and_expr : '$1'.
logical_or_expr -> logical_or_expr '||' logical_and_expr : {'or','$1','$3'}.

conditional_expr -> logical_or_expr : '$1'.
conditional_expr -> logical_or_expr '?' logical_or_expr ':' conditional_expr :
			{'ite', '$1', '$3', '$5'}.

assignment_expr -> conditional_expr : '$1'.
assignment_expr -> conditional_expr '..' conditional_expr :
		       {'range', '$1', '$3'}.
assignment_expr -> unary_expr '=' assignment_expr :
		       {'assign', '$1', '$3'}.

expr -> assignment_expr : '$1'.
expr -> expr ',' assignment_expr : {',', '$1', '$3'}. %% fixme? list?

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
qtype -> 'E' '!'  : 'ONE'.
qtype -> 'E'      : 'ANY'.
qtype -> 'A'      : 'ALL'.
qtype -> 'ALL'    : op('$1').
qtype -> 'ANY'    : op('$1').
qtype -> 'ONE'    : op('$1').
qtype -> 'NONE'   : op('$1').
qtype -> 'EQ'     : op('$1').
qtype -> 'NEQ'    : op('$1').
qtype -> 'GT'     : op('$1').
qtype -> 'GTE'    : op('$1').
qtype -> 'LT'     : op('$1').
qtype -> 'LTE'    : op('$1').
qtype -> 'SUM'    : op('$1').
qtype -> 'PROD'   : op('$1').
qtype -> 'PARITY' : op('$1').
qtype -> 'ODD'    : op('$1').
qtype -> 'EVEN'   : op('$1').
    
quantifier -> '[' 'ALL' ']'    : op('$2').
quantifier -> '[' 'ANY' ']'    : op('$2').
quantifier -> '[' 'NONE' ']'   : op('$2').
quantifier -> '[' 'ONE'  ']'   : op('$2').
quantifier -> '[' 'SUM' ']'    : op('$2').
quantifier -> '[' 'PROD' ']'   : op('$2').
quantifier -> '[' 'PARITY' ']' : op('$2').
quantifier -> '[' 'ODD' ']'    : op('$2').
quantifier -> '[' 'EVEN' ']'   : op('$2').
quantifier -> '[' 'E' ']'     : 'ANY'.
quantifier -> '[' 'E' '!' ']' : 'ONE'.
quantifier -> '[' 'A' ']'     : 'ALL'.
quantifier -> '[' qtype expr ']' : {'$2',comma_list('$3')}.

%%
%% Declaration of integers (can be extended)
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

odecl -> rank       : 'rank'.
odecl -> '+' rank   : '+rank'.
odecl -> '-' rank   : '-rank'.
odecl -> degree     : 'degree'.
odecl -> '+' degree : '+degree'.
odecl -> '-' degree : '-degree'.

odecl -> random         : 'random'.
odecl -> '+' random     : '+random'.
odecl -> '-' random     : '-random'.

odecl -> identity       : 'identity'.
odecl -> '+' identity   : '+identity'.
odecl -> '-' identity   : '-identity'.

odecl -> user           : 'user'.
odecl -> '+' user       : '+user'.
odecl -> '-' user       : '-user'.

odecl -> oexpr      : '$1'.
    
%% bit collection
oexpr -> pexpr                          : '$1'.
oexpr -> pexpr '[' expr ']'             : {bitindex,'$1','$3'}.
oexpr -> pexpr '[' expr ':' expr ']'    : {bitrange, '$1', '$3', '$5', 1}.
oexpr -> pexpr '[' expr ':' expr ':' expr ']'  : 
	     { bitrange, '$1', '$3', '$5', '$7'}.
oexpr -> pexpr ':' sexpr '/' 'signed'   : {int,'$3','$1'}.
oexpr -> pexpr ':' sexpr '/' 'unsigned' : {uint,'$3','$1'}.
oexpr -> '!' pexpr                      : {'!', '$2'}.

%%
%% Logic expression
%%
lexpr_var -> pexpr                           : '$1'.
lexpr_var -> pcexpr ':' sexpr '/' 'signed'   : {int,'$3','$1'}.
lexpr_var -> pcexpr ':' sexpr '/' 'unsigned' : {uint,'$3','$1'}.
lexpr_var -> pcexpr ':' sexpr                : {uint,'$3','$1'}.

lexpr_const -> integer               : constant(value('$1')).
lexpr_const -> identifier            : id('$1').  %% meta/env variable
%%lexpr_prim -> '$' '(' expr ')'      : {'expr','$3'}.

lexpr0 -> true                      : true.
lexpr0 -> false                     : false.
lexpr0 -> lexpr_var                 : '$1'.
lexpr0 -> lexpr_const               : '$1'.
%% lexpr0 -> lexpr_var '=' lexpr       : { op('$2'), '$1', '$3' }.
lexpr0 -> '-' lexpr0                : {'neg', '$2'}.
lexpr0 -> 'not' lexpr0              : {'not', '$2' }.
lexpr0 -> '!' lexpr0                : {'not', '$2' }.
lexpr0 -> '~' lexpr0                : {'bnot', '$2' }.
lexpr0 -> '(' lexpr ')'             : '$2'.
lexpr0 -> '{' lexprs '}'            : {vec,'$2'}.
lexpr0 -> identifier '(' lexprs ')' : { name('$1'), '$3'}. %% meta function
lexpr0 -> quantifier '(' lexprs ')' : {'$1','$3'}.
lexpr0 -> quantifier lexpr0         : {'$1','$2'}.
lexpr0 -> lexpr0 '[' expr ']'           : { bitindex, '$1', '$3'}.
lexpr0 -> lexpr0 '[' expr ':' expr ']'  : { bitrange,'$1','$3','$5', 1}.
lexpr0 -> lexpr0 '[' expr ':' expr ':' expr ']' :
	      { bit_range,'$1','$3','$5','$7'}.

lexpr10 -> lexpr0                 : '$1'.
lexpr10 -> lexpr10 '*' lexpr0     : { 'mul', '$1', '$3'}.
lexpr10 -> lexpr10 '/' lexpr0     : { 'div', '$1', '$3'}.
lexpr10 -> lexpr10 '%' lexpr0     : { 'rem', '$1', '$3'}.

lexpr20 -> lexpr10                : '$1'.
lexpr20 -> lexpr20 '+' lexpr10    : { 'add', '$1', '$3' }.
lexpr20 -> lexpr20 '-' lexpr10    : { 'sub', '$1', '$3' }.

lexpr30 -> lexpr20                : '$1'.
lexpr30 -> lexpr30 '<<' lexpr20   : { 'shl', '$1', '$3'}.
lexpr30 -> lexpr30 '>>' lexpr20   : { 'shr', '$1', '$3'}.
lexpr30 -> lexpr30 '<<<' lexpr20  : { 'rol', '$1', '$3'}.
lexpr30 -> lexpr30 '>>>' lexpr20  : { 'ror', '$1', '$3'}.

lexpr40 -> lexpr30                : '$1'.
lexpr40 -> lexpr40 '<'  lexpr30   : { 'lt', '$1', '$3' }.
lexpr40 -> lexpr40 '<=' lexpr30   : { 'lte', '$1', '$3' }.
lexpr40 -> lexpr40 '>'  lexpr30   : { 'gt', '$1', '$3' }.
lexpr40 -> lexpr40 '>=' lexpr30   : { 'gte', '$1', '$3' }.

lexpr41 -> lexpr40                : '$1'.
lexpr41 -> lexpr41 '==' lexpr40   : { 'eq', '$1', '$3' }.
lexpr41 -> lexpr41 ':=' lexpr40   : { 'alias', '$1', '$3' }.
lexpr41 -> lexpr41 '!=' lexpr40   : { 'neq', '$1', '$3' }.

lexpr43 -> lexpr41                : '$1'.
lexpr43 -> lexpr43 '&' lexpr41    : { 'band', '$1', '$3' }.   

lexpr45 -> lexpr43                : '$1'.
lexpr45 -> lexpr45 '^' lexpr43    : { 'bxor', '$1', '$3' }.

lexpr47 -> lexpr45                : '$1'.
lexpr47 -> lexpr47 '|' lexpr45    : { 'bor', '$1', '$3' }.

lexpr50 -> lexpr47                : '$1'.
lexpr50 -> lexpr50 'and' lexpr47  : { 'and', '$1', '$3' }.
lexpr50 -> lexpr50 '&&'  lexpr47  : { 'and', '$1', '$3' }.

lexpr60 -> lexpr50                  : '$1'.
lexpr60 -> lexpr60 'xor' lexpr50    : { op('$2'), '$1', '$3' }.

lexpr70 -> lexpr60                  : '$1'.
lexpr70 -> lexpr70 'or'  lexpr60    : { 'or', '$1', '$3' }.
lexpr70 -> lexpr70 '||'  lexpr60    : { 'and', '$1', '$3' }.

lexpr80 -> lexpr70                  : '$1'.
lexpr80 -> lexpr80 '->'  lexpr70    : { 'imp', '$1', '$3' }.
lexpr80 -> lexpr80 'imp' lexpr70    : { 'imp', '$1', '$3' }.
lexpr80 -> lexpr80 'implies' lexpr70 : { 'imp', '$1', '$3' }.

lexpr90 -> lexpr80                  : '$1'.
lexpr90 -> lexpr90 'equ' lexpr80    : { 'equ', '$1', '$3' }.
lexpr90 -> lexpr90 'equivalent' lexpr80 : { 'equ', '$1', '$3' }.
lexpr90 -> lexpr90 '<->' lexpr80    : { 'equ', '$1', '$3' }.

lexpr -> lexpr90                    : '$1'.

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

pcexpr -> pexpr : '$1'.
pcexpr -> integer : value('$1').
pcexpr -> identifier : name('$1').

psymbol -> 'A' : 'A'.
psymbol -> 'E' : 'E'.
psymbol -> symbol : name('$1').

Erlang code.

-include("varp.hrl").
-import(lists, [map/2, member/2]).
-export([init/0]).

init() ->
    ok.

id({identifier,_Line,Name}) -> {id,Name};
id({symbol,_Line,Name})     -> {id,Name};
id({true,_Line})            -> {id,"true"};
id({false,_Line})           -> {id,"false"};
id({'E',_Line})             -> {id,"E"};
id({'A',_Line})             -> {id,"A"}.

bin({binnum,_Line,"0b"++Val}) -> {const,list_to_integer(Val,2)}.
oct({octnum,_Line,Val}) -> {const,list_to_integer(Val,8)}.
hex({hexnum,_Line,"0x"++Val}) -> {const,list_to_integer(Val,16)};
hex({hexnum,_Line,"0X"++Val}) -> {const,list_to_integer(Val,16)}.
dec({decnum,_Line,Val}) -> {const,list_to_integer(Val)}.
chr({chrnum,_Line,Val}) ->  {const,Val}.
flo({flonum,_Line,Val}) ->  {const,list_to_float(Val)}.


op({Op,_Ln})     -> Op.

constant(N) when N >= 0   -> {uint,varp_math:unsigned_size(N),N};
constant(N) when N < 0   -> {int,varp_math:signed_size(N),N}.

name({symbol,_,Name})       -> list_to_atom(Name);
name({identifier,_,Name})   -> list_to_atom(Name).

value({decnum,_,Num})       -> list_to_integer(Num,10);
value({octnum,_,Num})       -> list_to_integer(Num,8);
value({hexnum,_,"0x"++Num}) -> list_to_integer(Num,16);
value({binnum,_,"0b"++Num}) -> list_to_integer(Num,2).

comma_list({',',A1,A2}) ->
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
