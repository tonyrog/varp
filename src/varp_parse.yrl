%% -*- erlang -*-

Terminals
	symbol cname true false define declare literals assert input output
        order rank degree random identity 
        'EQ' 'NEQ' 'GT' 'GTE' 'LT' 'LTE' 'NONE' 'ONE'
	'and' 'or' 'xor' 'not' 'imp' 'equ' 'A' 'E' 'ALL' 'ANY' 'PARITY'
        'ODD' 'EVEN'
        'SUM' 'PROD' 'implies' 'equivalent'
        '<->' '>>>' '<<<' '..'
        hexnum octnum binnum decnum flonum chrnum
	'->' '<<' '>>' '<' '>' '>=' '<=' '==' '!=' ':='
	'&&' '||'
	'(' ')' '[' ']' '{' '}' ',' '.' '&' '*' '+' '-' '~' '!'
	'/' '%' '^' '|' ':' '?' '=' ';'
	'bool' 'char' 'short' 'int' 'long' 'signed' 'unsigned' 
        'float' 'double'
        'circuit' 'in' 'out' 'return'
        'min' 'max' 'abs'
	.

Nonterminals
        init file 
	primary_expr postfix_expr argument_expr_list
	unary_expr unary_operator
	multiplicative_expr additive_expr shift_expr
	relational_expr equality_expr and_expr exclusive_or_expr
	inclusive_or_expr logical_and_expr logical_or_expr
	conditional_expr assignment_expr
	expr constant 
        integer sexpr
        qtype quantifier sym pexpr oexpr odecl odecls ldecl ldecls
        lexpr0 lexpr10 lexpr20 lexpr30 lexpr40 lexpr41 lexpr43 lexpr45 lexpr47 
        lexpr50 lexpr60 lexpr70 lexpr80 lexpr90 lexpr92 
        lexpr lexprs
        definition definition_list
        pdecl pdecls
        assignment_defs assignment_def
        circuit_params circuit_param_decls circuit_param_decl
        circuit_defs circuit_def arg_list arg 
        cpdecls cpdecl 
        .

Rootsymbol file.

file  -> init definition_list assignment_defs lexpr  : {'$2','$3','$4'}.
file  -> init definition_list assignment_defs : {'$2','$3',true}.
file  -> init definition_list lexpr  : {'$2',[],'$3'}.
file  -> init definition_list : {'$2',[],undefined}.
file  -> init assignment_defs lexpr  : {[],'$2','$3'}.
file  -> init assignment_defs : {[],'$2',true}.
file  -> init lexpr : {[],[],'$2'}.

init -> '$empty' : init().

assignment_defs -> assignment_def : ['$1'].
assignment_defs -> assignment_defs assignment_def : '$1'++['$2'].

assignment_def -> oexpr '=' lexpr ';' : {lop,'=','$1','$3'}.
assignment_def -> cname '(' arg_list ')' ';'  : { cop, str('$1'), '$3'}.

definition_list -> definition : ['$1'].
definition_list -> definition_list definition : '$1'++['$2'].

definition -> 'define' pexpr lexpr ';' : {define,'$2','$3'}.
definition -> 'declare' pdecls ';'     : {declare,'$2'}.
definition -> 'literals' ldecls ';'    : {literals,'$2'}.
definition -> 'order' odecls ';'       : {order,'$2'}.
definition -> 'assert' expr ';'        : {assert,'$2'}.
definition -> 'input' sym ';'  : {input,'$2'}.
definition -> 'output' sym ';' : {output,'$2'}.
definition -> 'circuit' sym circuit_params '{'  circuit_defs '}' :
		  varp_formula:add_circuit_def({circuit, '$2', '$3', '$5'}).

circuit_params -> '(' ')' : [].
circuit_params -> '(' circuit_param_decls ')' : '$2'.

circuit_param_decls -> circuit_param_decl : '$1'.
circuit_param_decls -> circuit_param_decls ';' circuit_param_decl : '$1' ++ '$3'.
    
circuit_param_decl -> cpdecls : [{in,'$1'}].
circuit_param_decl -> 'in' cpdecls : [{in,'$2'}].
circuit_param_decl -> 'out' cpdecls : [{out,'$2'}].
circuit_param_decl -> 'return' cpdecl : [{return,'$2'}].

cpdecls -> cpdecl : ['$1'].
cpdecls -> cpdecl '=' lexpr : [{'=','$1','$3'}].
cpdecls -> cpdecls ',' cpdecl : '$1'++['$3'].
cpdecls -> cpdecls ',' cpdecl '=' lexpr : '$1'++[{'=','$3','$5'}].

cpdecl -> pexpr ':' sexpr '/' 'signed'   : {'$1',int,'$3'}.
cpdecl -> pexpr ':' sexpr '/' 'unsigned' : {'$1',uint,'$3'}.
cpdecl -> pexpr ':' sexpr                : {'$1',uint,'$3'}.
cpdecl -> pexpr                          : '$1'.

circuit_defs -> circuit_def : ['$1'].
circuit_defs -> circuit_defs circuit_def : '$1' ++ ['$2'].

%% oexpr must be output args, lexpr may contain both in and out id's
circuit_def -> 'declare' pdecls ';' : {declare,'$2'}.
circuit_def -> 'circuit' sym circuit_params '{'  circuit_defs '}' :
		   varp_formula:add_circuit_def({circuit, '$2', '$3', '$5'}).
circuit_def -> oexpr '=' lexpr ';' : {lop,'=','$1','$3'}.
    
primary_expr -> 'min': <<"min">>.
primary_expr -> 'max': <<"max">>.
primary_expr -> 'abs': <<"abs">>.
primary_expr -> sym  : '$1'.
primary_expr -> constant     : '$1'.
primary_expr -> '(' expr ')' : '$2'.
primary_expr -> '{' expr '}' : {vec,comma_list('$2')}.
    
postfix_expr -> primary_expr : '$1'.
postfix_expr -> postfix_expr '[' expr ']' : {'index','$1','$3'}.
postfix_expr -> postfix_expr '(' ')' : {'call','$1',[]}.
postfix_expr -> postfix_expr '(' argument_expr_list ')' : {'call','$1','$3'}.
postfix_expr -> postfix_expr '.' sym : {'field','$1','$3'}.
postfix_expr -> postfix_expr '->' sym :  {'pointer','$1','$3'}.

argument_expr_list -> assignment_expr : ['$1'].
argument_expr_list -> argument_expr_list ',' assignment_expr : '$1'++['$3'].

unary_expr -> postfix_expr : '$1'.
unary_expr -> unary_operator unary_expr : {op,'$1','$2'}.

unary_operator -> '+' : 'pos'.
unary_operator -> '-' : 'neg'.
unary_operator -> '~' : 'bnot'.
unary_operator -> '!' : 'not'.

multiplicative_expr -> unary_expr : '$1'.
multiplicative_expr -> multiplicative_expr '*' unary_expr : {op,'mul','$1','$3'}.
multiplicative_expr -> multiplicative_expr '/' unary_expr : {op,'div','$1','$3'}.
multiplicative_expr -> multiplicative_expr '%' unary_expr : {op,'rem','$1','$3'}.

additive_expr -> multiplicative_expr : '$1'.
additive_expr -> additive_expr '+' multiplicative_expr : {op,'add','$1','$3'}.
additive_expr -> additive_expr '-' multiplicative_expr : {op,'sub','$1','$3'}.

shift_expr -> additive_expr : '$1'.
shift_expr -> shift_expr '<<' additive_expr : {op,'shl','$1','$3'}.
shift_expr -> shift_expr '>>' additive_expr : {op,'shr','$1','$3'}.

relational_expr -> shift_expr : '$1'.
relational_expr -> relational_expr '<' shift_expr : {op,'lt','$1','$3'}.
relational_expr -> relational_expr '>' shift_expr : {op,'gt','$1','$3'}.
relational_expr -> relational_expr '<=' shift_expr : {op,'lte','$1','$3'}.
relational_expr -> relational_expr '>=' shift_expr : {op,'gte','$1','$3'}.

equality_expr -> relational_expr : '$1'.
equality_expr -> equality_expr '==' relational_expr : {op,'eq','$1','$3'}.
equality_expr -> equality_expr '!=' relational_expr : {op,'neq','$1','$3'}.

and_expr -> equality_expr : '$1'.
and_expr -> and_expr '&' equality_expr : {op,'band','$1','$3'}.

exclusive_or_expr -> and_expr : '$1'.
exclusive_or_expr -> exclusive_or_expr '^' and_expr : {op,'bxor','$1','$3'}.

inclusive_or_expr -> exclusive_or_expr : '$1'.
inclusive_or_expr -> inclusive_or_expr '|' exclusive_or_expr :{op,'bor','$1','$3'}.

logical_and_expr -> inclusive_or_expr : '$1'.
logical_and_expr -> logical_and_expr '&&' inclusive_or_expr : {op,'and','$1','$3'}.

logical_or_expr -> logical_and_expr : '$1'.
logical_or_expr -> logical_or_expr '||' logical_and_expr : {op,'or','$1','$3'}.

conditional_expr -> logical_or_expr : '$1'.
conditional_expr -> logical_or_expr '?' logical_or_expr ':' conditional_expr :
			{op,'ite','$1','$3','$5'}.

assignment_expr -> conditional_expr : '$1'.
assignment_expr -> conditional_expr '..' conditional_expr :
		       {'range', '$1', '$3'}.
assignment_expr -> unary_expr '=' assignment_expr : {op,'=','$1','$3'}.

expr -> assignment_expr : '$1'.
expr -> expr ',' assignment_expr : {op,',', '$1', '$3'}.

constant -> hexnum : hex('$1').
constant -> octnum : oct('$1').
constant -> decnum : dec('$1').
constant -> binnum : bin('$1').
constant -> flonum : flo('$1').
constant -> chrnum : chr('$1').


%%  'A' 'E' 
%% FIXME symbols below as ids!
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

%% Declaration of symbols
pdecl -> pexpr ':' sexpr '/' 'signed'   : {'$1',int,'$3'}.
pdecl -> pexpr ':' sexpr '/' 'unsigned' : {'$1',uint,'$3'}.
pdecl -> pexpr ':' sexpr                : {'$1',uint,'$3'}.
pdecl -> pexpr                          : '$1'.

pdecls -> pdecl : ['$1'].
pdecls -> pdecls ',' pdecl : '$1'++['$3'].

ldecls -> ldecl : ['$1'].
ldecls -> ldecls ',' ldecl : '$1'++['$3'].

ldecl -> sym : '$1'.

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

lexpr0 -> integer                   : constant(value('$1')).
lexpr0 -> true                      : true.
lexpr0 -> false                     : false.
lexpr0 -> '-' lexpr0                : {lop,'neg', '$2'}.
lexpr0 -> 'not' lexpr0              : {lop,'not', '$2' }.
lexpr0 -> '!' lexpr0                : {lop,'not', '$2' }.
lexpr0 -> '~' lexpr0                : {lop,'bnot', '$2' }.
lexpr0 -> '(' lexpr ')'             : '$2'.
lexpr0 -> '{' lexprs '}'            : {vec,'$2'}.
lexpr0 -> 'min' '(' lexpr ',' lexpr ')' : {p,<<"min">>,['$3','$5']}.
lexpr0 -> 'max' '(' lexpr ',' lexpr ')' : {p,<<"max">>,['$3','$5']}.
lexpr0 -> 'abs' '(' lexpr ')' : {p,<<"abs">>,['$3']}.
lexpr0 -> pexpr : '$1'.
lexpr0 -> quantifier '(' lexprs ')' : {'$1','$3'}.
lexpr0 -> quantifier lexpr0         : {'$1','$2'}.
lexpr0 -> lexpr0 '[' expr ']'           : { bitindex, '$1', '$3'}.
lexpr0 -> lexpr0 '[' expr ':' expr ']'  : { bitrange,'$1','$3','$5', 1}.
lexpr0 -> lexpr0 '[' expr ':' expr ':' expr ']' :
	      { bit_range,'$1','$3','$5','$7'}.

lexpr10 -> lexpr0                 : '$1'.
lexpr10 -> lexpr10 '*' lexpr0     : {lop, 'mul', '$1', '$3'}.
lexpr10 -> lexpr10 '/' lexpr0     : {lop, 'div', '$1', '$3'}.
lexpr10 -> lexpr10 '%' lexpr0     : {lop, 'rem', '$1', '$3'}.

lexpr20 -> lexpr10                : '$1'.
lexpr20 -> lexpr20 '+' lexpr10    : {lop, 'add', '$1', '$3' }.
lexpr20 -> lexpr20 '-' lexpr10    : {lop, 'sub', '$1', '$3' }.

lexpr30 -> lexpr20                : '$1'.
lexpr30 -> lexpr30 '<<' lexpr20   : {lop, 'shl', '$1', '$3'}.
lexpr30 -> lexpr30 '>>' lexpr20   : {lop, 'shr', '$1', '$3'}.
lexpr30 -> lexpr30 '<<<' lexpr20  : {lop, 'rol', '$1', '$3'}.
lexpr30 -> lexpr30 '>>>' lexpr20  : {lop, 'ror', '$1', '$3'}.

lexpr40 -> lexpr30                : '$1'.
lexpr40 -> lexpr40 '<'  lexpr30   : {lop, 'lt', '$1', '$3' }.
lexpr40 -> lexpr40 '<=' lexpr30   : {lop, 'lte', '$1', '$3' }.
lexpr40 -> lexpr40 '>'  lexpr30   : {lop, 'gt', '$1', '$3' }.
lexpr40 -> lexpr40 '>=' lexpr30   : {lop, 'gte', '$1', '$3' }.

lexpr41 -> lexpr40                : '$1'.
lexpr41 -> lexpr41 '==' lexpr40   : {lop, 'eq', '$1', '$3' }.
lexpr41 -> lexpr41 ':=' lexpr40   : {lop, 'alias', '$1', '$3' }.
lexpr41 -> lexpr41 '!=' lexpr40   : {lop, 'neq', '$1', '$3' }.

lexpr43 -> lexpr41                : '$1'.
lexpr43 -> lexpr43 '&' lexpr41    : {lop, 'band', '$1', '$3' }.   

lexpr45 -> lexpr43                : '$1'.
lexpr45 -> lexpr45 '^' lexpr43    : {lop, 'bxor', '$1', '$3' }.

lexpr47 -> lexpr45                : '$1'.
lexpr47 -> lexpr47 '|' lexpr45    : {lop, 'bor', '$1', '$3' }.

lexpr50 -> lexpr47                : '$1'.
lexpr50 -> lexpr50 'and' lexpr47  : {lop, 'and', '$1', '$3' }.
lexpr50 -> lexpr50 '&&'  lexpr47  : {lop, 'and', '$1', '$3' }.

lexpr60 -> lexpr50                  : '$1'.
lexpr60 -> lexpr60 'xor' lexpr50    : {lop, 'xor', '$1', '$3' }.

lexpr70 -> lexpr60                  : '$1'.
lexpr70 -> lexpr70 'or'  lexpr60    : {lop, 'or', '$1', '$3' }.
lexpr70 -> lexpr70 '||'  lexpr60    : {lop, 'or', '$1', '$3' }.

lexpr80 -> lexpr70                  : '$1'.
lexpr80 -> lexpr80 '->'  lexpr70    : {lop, 'imp', '$1', '$3' }.
lexpr80 -> lexpr80 'imp' lexpr70    : {lop, 'imp', '$1', '$3' }.
lexpr80 -> lexpr80 'implies' lexpr70 : {lop, 'imp', '$1', '$3' }.

lexpr90 -> lexpr80                  : '$1'.
lexpr90 -> lexpr90 'equ' lexpr80    : {lop, 'equ', '$1', '$3' }.
lexpr90 -> lexpr90 'equivalent' lexpr80 : {lop, 'equ', '$1', '$3' }.
lexpr90 -> lexpr90 '<->' lexpr80    : {lop, 'equ', '$1', '$3' }.

lexpr92 -> lexpr90 : '$1'.
lexpr92 -> lexpr90 '?' lexpr90 ':' lexpr90 : {lop,'ite','$1','$3','$5'}.

lexpr -> lexpr92                    : '$1'.

lexprs -> lexpr ',' lexprs : ['$1' | '$3'].
lexprs -> lexpr : ['$1'].

sexpr -> '(' expr ')' : '$2'.
sexpr -> integer  : value('$1').
sexpr -> 'bool' : 1.
sexpr -> 'char' : machine_sizeof(char).
sexpr -> 'short' : machine_sizeof(short).
sexpr -> 'long' : machine_sizeof(long).
sexpr -> 'int' : machine_sizeof(int).
sexpr -> 'float' : machine_sizeof(float).
sexpr -> 'double' : machine_sizeof(double).
sexpr -> sym : '$1'.

pexpr -> sym               : { p, '$1', []}.
pexpr -> sym '(' ')'       : { p, '$1', []}.
pexpr -> sym '(' expr ')'  : { p, '$1', comma_list('$3')}.
pexpr -> cname '(' arg_list ')'  : { cop, str('$1'), '$3'}.

arg_list -> '$empty' : [].
arg_list -> arg : ['$1'].
arg_list -> arg_list ',' arg : '$1'++['$3'].

arg -> lexpr : '$1'.
arg -> sym '=' lexpr : {'=','$1','$3'}.

sym -> 'A'        : <<"A">>.
sym -> 'E'        : <<"E">>.
sym -> symbol     : str('$1').

Erlang code.

-include("varp.hrl").
-import(lists, [map/2, member/2]).

bin({binnum,_Line,"0b"++Val}) -> {const,list_to_integer(Val,2)}.
oct({octnum,_Line,Val}) -> {const,list_to_integer(Val,8)}.
hex({hexnum,_Line,"0x"++Val}) -> {const,list_to_integer(Val,16)};
hex({hexnum,_Line,"0X"++Val}) -> {const,list_to_integer(Val,16)}.
dec({decnum,_Line,Val}) -> {const,list_to_integer(Val)}.
chr({chrnum,_Line,Val}) ->  {const,Val}.
flo({flonum,_Line,Val}) ->  {const,list_to_float(Val)}.

str({symbol,_Ln,Name}) -> Name;
str({cname,_Ln,Name}) -> Name.

op({Op,_Ln})     -> Op.

constant(N) when N >= 0   -> {uint,varp_math:unsigned_size(N),N};
constant(N) when N < 0   -> {int,varp_math:signed_size(N),N}.

value({decnum,_,Num})       -> list_to_integer(Num,10);
value({octnum,_,Num})       -> list_to_integer(Num,8);
value({hexnum,_,"0x"++Num}) -> list_to_integer(Num,16);
value({binnum,_,"0b"++Num}) -> list_to_integer(Num,2).

comma_list({lop,',',A1,A2}) ->
    comma_list(A1) ++ comma_list(A2);
comma_list({op,',',A1,A2}) ->
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
    application:get_env(varp, sizeof_long, 64);
machine_sizeof(float)  ->
    application:get_env(varp, sizeof_float, 32);
machine_sizeof(double)  ->
    application:get_env(varp, sizeof_double, 64).

%% machine_endian() ->
%%    application:get_enc(varp, endian, little).
init() ->
    %% io:format("INIT\n"),
    varp_formula:init_circuit_def(),
    ok.

