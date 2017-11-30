%% -*- erlang -*-
%%
%%
%%

Terminals
	symbol true false define declare code type
        'EQ' 'NEQ' 'GT' 'GTE' 'LT' 'LTE' 'NONE' 'ONE'
	'and' 'or' 'xor' 'not' 'imp' 'equ' 'A' 'E' 'ALL' 'ANY'
        '<->' '>>>' '<<<' ':=' '$' '..'
        hexnum octnum binnum decnum flonum chrnum
	identifier string sizeof
	'->' '++' '--' '<<' '>>' '<' '>' '>=' '<=' '==' '!='
	'&&' '||' '*=' '/=' '%=' '+='
	'-=' '<<=' '>>=' '&=' '^=' '|=' 
	'(' ')' '[' ']' '{' '}' ',' '.' '&' '*' '+' '-' '~' '!'
	'/' '%' '^' '|' ':' '?' '=' ';'
        'typedef' 'extern' 'static' 'auto' 'register'
	'char' 'short' 'int' 'long' 'signed' 'unsigned' 'float' 'double' 
	'const' 'volatile' 'void'
	'struct' 'union' 'enum' '...'
	'case' 'default' 'if' 'else' 'switch' 'while' 'do' 
	'for' 'goto' 'continue' 'break' 'return'
	.

%% '.'

Nonterminals
        cidentifier
	primary_expr postfix_expr argument_expr_list
	unary_expr unary_operator cast_expr
	multiplicative_expr additive_expr shift_expr
	relational_expr equality_expr and_expr exclusive_or_expr
	inclusive_or_expr logical_and_expr logical_or_expr
	conditional_expr assignment_expr assignment_operator
	expr constant constant_expr declaration declaration_specifiers
	init_declarator_list init_declarator
	storage_class_specifier type_specifier type_name
	struct_or_union_specifier struct_or_union
	struct_declaration_list struct_declaration
	struct_declarator_list struct_declarator
	enum_specifier enumerator_list enumerator
	declarator declarator2 pointer type_specifier_list
	parameter_identifier_list identifier_list
	parameter_type_list parameter_list
	parameter_declaration abstract_declarator
	abstract_declarator2 initializer
	initializer_list statement labeled_statement
	compound_statement declaration_list
	statement_list expression_statement 
	selection_statement iteration_statement jump_statement 
	file external_definition function_definition
	function_body
        integer sexpr
        qtype quantifier psymbol pexpr
        lexpr_prim
        lexpr0 lexpr1 lexpr2 lexpr3 lexpr4 lexpr40 lexpr43 lexpr45 lexpr47 
        lexpr5 lexpr6 lexpr7 lexpr8 lexpr9
        lexpr lexprs
        definition definitions
        cfile 
        pdecl pdecls
        .

Rootsymbol file.

file  -> definitions : {'$1',undefined}.
file  -> definitions lexpr  : {'$1','$2'}.
file  -> lexpr : {[], '$1'}.

definitions -> definition : ['$1'].
definitions -> definitions definition : '$1'++['$2'].

definition -> 'define' pexpr ':=' lexpr ';' : {'$2','$4'}.
definition -> 'declare' pdecls ';'          : {declare,'$2'}.
definition -> 'code' '{' cfile '}'          : {code, '$3'}.

primary_expr -> cidentifier : '$1'.
primary_expr -> constant : '$1'.
primary_expr -> string : str('$1').
primary_expr -> '(' expr ')' : '$2'.

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
postfix_expr -> postfix_expr '++' : 
		    #cunary {line=line('$1'),op='++',arg='$1'}.
postfix_expr -> postfix_expr '--' : 
		    #cunary {line=line('$1'),op='--',arg='$1'}.

argument_expr_list -> assignment_expr : ['$1'].
argument_expr_list -> argument_expr_list ',' assignment_expr : '$1'++['$3'].

unary_expr -> postfix_expr : '$1'.
unary_expr -> '++' unary_expr :
		  #cunary {line=line('$1'),op='+++',arg='$2'}.
unary_expr -> '--' unary_expr : 
		  #cunary {line=line('$1'),op='---',arg='$2'}.
unary_expr -> unary_operator cast_expr : 
		  #cunary {line=line('$1'),op=op('$1'),arg='$2'}.
unary_expr -> 'sizeof' unary_expr : 
		  #cunary {line=line('$1'),op='sizeof',arg='$2'}.
unary_expr -> 'sizeof' '(' type_name ')' : 
		  #cunary {line=line('$1'),op='sizeof',arg='$3'}.

unary_operator -> '&' : '$1'.
unary_operator -> '*' : '$1'.
unary_operator -> '+' : '$1'.
unary_operator -> '-' : '$1'.
unary_operator -> '~' : '$1'.
unary_operator -> '!' : '$1'.

cast_expr -> unary_expr : '$1'.
cast_expr -> '(' type_name ')' cast_expr :
		 #cbinary {line=line('$1'),op=cast,arg1='$2',arg2='$4'}.

multiplicative_expr -> cast_expr : '$1'.
multiplicative_expr -> multiplicative_expr '*' cast_expr : 
		   #cbinary { line=line('$2'), op='*',arg1='$1',arg2='$3'}.
multiplicative_expr -> multiplicative_expr '/' cast_expr :
		   #cbinary { line=line('$2'), op='/',arg1='$1',arg2='$3'}.
multiplicative_expr -> multiplicative_expr '%' cast_expr :
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
assignment_operator -> '*=' : '$1'.
assignment_operator -> '/=' : '$1'.
assignment_operator -> '%=' : '$1'.
assignment_operator -> '+=' : '$1'.
assignment_operator -> '-=' : '$1'.
assignment_operator -> '<<=' : '$1'.
assignment_operator -> '>>=' : '$1'.
assignment_operator -> '&=' : '$1'.
assignment_operator -> '^=' : '$1'.
assignment_operator -> '|=' : '$1'.

expr -> assignment_expr : '$1'.
expr -> expr ',' assignment_expr : 
     	#cbinary { line=line('$1'), op=',',arg1='$1',arg2='$3'}.

constant_expr -> conditional_expr : '$1'.

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
%% FIXME symbols below as cidentifiers!
%% 'EQ' 'NEQ' 'GT' 'GTE' 'LT' 'LTE' 'NONE' 'ONE'
%% 'and' 'or' 'xor' 'not' imp equ 'A' 'E' 'ALL' 'ANY' 'true' 'false'

declaration -> declaration_specifiers ';' : 
		 [#cdecl { type='$1'}].
declaration -> declaration_specifiers init_declarator_list ';' :
	       map(fun(D) when is_record(D,cdecl) ->
			   D#cdecl { type='$1'++D#cdecl.type };
		      (T) when is_record(T,ctypedef) ->
			   Type = ('$1'--[typedef]) ++ T#ctypedef.type,
			   T#ctypedef { type=Type }
		   end, '$2').

declaration_specifiers -> storage_class_specifier : 
		['$1'].
declaration_specifiers -> storage_class_specifier declaration_specifiers :
		['$1' | '$2'].
declaration_specifiers -> type_specifier : 
		['$1'].
declaration_specifiers -> type_specifier declaration_specifiers :
		['$1'|'$2'].

init_declarator_list -> init_declarator : 
		['$1'].
init_declarator_list -> init_declarator_list ',' init_declarator : 
		'$1'++['$3'].

%% Extension - allow bit size construct for normal variables

init_declarator -> declarator : 
		decl('$1').
init_declarator -> declarator ':' constant_expr : 
		decl('$1'#cdecl { size ='$3'}).
init_declarator -> declarator '=' initializer : 
		decl('$1'#cdecl { value = '$3'}).
init_declarator -> declarator ':' constant_expr '=' initializer : 
		decl('$1'#cdecl { size = '$3', value = '$5'}).


storage_class_specifier -> 'extern'   : op('$1').
storage_class_specifier -> 'static'   : op('$1').
storage_class_specifier -> 'auto'     : op('$1').
storage_class_specifier -> 'register' : op('$1').
storage_class_specifier -> 'typedef'  : put(bic_is_typedef, true), op('$1').

type_specifier -> 'char' : op('$1').
type_specifier -> 'short' : op('$1').
type_specifier -> 'int' : op('$1').
type_specifier -> 'long' : op('$1').
type_specifier -> 'signed' : op('$1').
type_specifier -> 'unsigned' : op('$1').
type_specifier -> 'float' : op('$1').
type_specifier -> 'double' : op('$1').
type_specifier -> 'const' : op('$1').
type_specifier -> 'volatile' : op('$1').
type_specifier -> 'void' : op('$1').
type_specifier -> struct_or_union_specifier : '$1'.
type_specifier -> enum_specifier : '$1'.
type_specifier -> type : typeid('$1').

struct_or_union_specifier -> struct_or_union cidentifier '{' struct_declaration_list '}' : 
	case op('$1') of
	     struct -> #cstruct {line=line('$1'),
				    name='$2'#cid.name, elems='$4'};
	     union ->  #cunion  {line=line('$1'),
				    name='$2'#cid.name, elems='$4'}
	end.
		     
struct_or_union_specifier -> struct_or_union '{' struct_declaration_list '}' :
	case op('$1') of
	     struct -> #cstruct {line=line('$1'),elems='$3'};
	     union ->  #cunion  {line=line('$1'),elems='$3'}
	end.

struct_or_union_specifier -> struct_or_union cidentifier :
	case op('$1') of
	     struct -> #cstruct {line=line('$1'),name='$2'#cid.name};
	     union ->  #cunion  {line=line('$1'),name='$2'#cid.name}
	end.

struct_or_union -> 'struct' : '$1'.
struct_or_union -> 'union' : '$1'.

struct_declaration_list -> struct_declaration : '$1'.
struct_declaration_list -> struct_declaration_list struct_declaration :
			'$1'++'$2'.

struct_declaration -> type_specifier_list struct_declarator_list ';' :
		 map(fun(D) -> D#cdecl { type='$1'++D#cdecl.type} end,
		     '$2').

struct_declarator_list -> struct_declarator : ['$1'].
struct_declarator_list -> struct_declarator_list ',' struct_declarator :
		       '$1'++['$3'].

struct_declarator -> declarator : 
		   '$1'.
struct_declarator -> ':' constant_expr : 
		   #cdecl { line=line('$1'), size ='$2'} .
struct_declarator -> declarator ':' constant_expr : 
		   '$1'#cdecl { size ='$3'}.

enum_specifier -> 'enum' '{' enumerator_list '}' : 
	       #cenum {line=line('$1'),elems='$3'}.
enum_specifier -> 'enum' cidentifier '{' enumerator_list '}' :
	       #cenum {line=line('$1'),name='$2'#cid.name,elems='$4'}.
enum_specifier -> 'enum' cidentifier :
	       #cenum {line=line('$1'),name='$2'#cid.name}.

enumerator_list -> enumerator : ['$1'].
enumerator_list -> enumerator_list ',' enumerator : '$1'++['$3'].

enumerator -> cidentifier :
		  { '$1'#cid.name, '$1'#cid.line, undefined }.
enumerator -> cidentifier '=' constant_expr : 
		  {'$1'#cid.name,'$1'#cid.line,'$3'}.

declarator -> declarator2 : '$1'.
declarator -> pointer declarator2 : 
		  '$2'#cdecl { type=add_decl('$1','$2'#cdecl.type) }.

declarator2 -> cidentifier : 
		   #cdecl { line='$1'#cid.line, name='$1'#cid.name }.
declarator2 -> '(' declarator ')' : 
		   '$2'.
declarator2 -> declarator2 '[' ']' : 
           '$1'#cdecl { type=[{array,[]}|'$1'#cdecl.type]}.
declarator2 -> declarator2 '[' constant_expr ']' : 
           '$1'#cdecl { type=[{array,'$3'}|'$1'#cdecl.type]}.
declarator2 -> declarator2 '(' ')' : 
           '$1'#cdecl { type=[{fn,[]}|'$1'#cdecl.type]}.
declarator2 -> declarator2 '(' parameter_type_list ')' :
           '$1'#cdecl { type=[{fn,'$3'}|'$1'#cdecl.type]}.
declarator2 -> declarator2 '(' parameter_identifier_list ')' :
           '$1'#cdecl { type=[{fn,'$3'}|'$1'#cdecl.type]}.

pointer -> '*' : [{pointer,['*'],[]}].
pointer -> '*' type_specifier_list : [{pointer,['*'],'$2'}].
pointer -> '*' pointer : add_pointer('$2').
pointer -> '*' type_specifier_list pointer : [{pointer,['*'],'$2'++['$3']}].

type_specifier_list -> type_specifier : ['$1'].
type_specifier_list -> type_specifier_list type_specifier : '$1'++['$2'].

parameter_identifier_list -> identifier_list : '$1'.
parameter_identifier_list -> identifier_list ',' '...' : '$1'++['$3'].

identifier_list -> cidentifier : ['$1'].
identifier_list -> identifier_list ',' cidentifier : '$1'++['$3'].

parameter_type_list -> parameter_list : '$1'.
parameter_type_list -> parameter_list ',' '...' : '$1' ++ ['$3'].

parameter_list -> parameter_declaration : ['$1'].
parameter_list -> parameter_list ',' parameter_declaration : '$1'++['$3'].

parameter_declaration -> type_specifier_list declarator :
		'$2'#cdecl { type='$1'++'$2'#cdecl.type}.
parameter_declaration -> type_name : 
		#cdecl { type='$1'}.

type_name -> type_specifier_list : '$1'.
type_name -> type_specifier_list abstract_declarator : '$1'++'$2'.

abstract_declarator -> pointer : '$1'.
abstract_declarator -> abstract_declarator2 : '$1'.
abstract_declarator -> pointer abstract_declarator2 : add_decl('$1','$2').

abstract_declarator2 -> '(' abstract_declarator ')' : 
		     '$2'.
abstract_declarator2 -> '[' ']' :
		     [{array,[]}].
abstract_declarator2 -> '[' constant_expr ']' : 
		     [{array,'$2'}].
abstract_declarator2 -> abstract_declarator2 '[' ']' : 
		     '$1'++[{array,[]}].
abstract_declarator2 -> abstract_declarator2 '[' constant_expr ']' : 
		     '$1'++[{array,'$3'}].
abstract_declarator2 -> '(' ')' : 
		     [{params,[]}].
abstract_declarator2 -> '(' parameter_type_list ')' : 
		     [{params,'$2'}].
abstract_declarator2 -> abstract_declarator2 '(' ')' : 
		     '$1'++[{params,[]}].
abstract_declarator2 -> abstract_declarator2 '(' parameter_type_list ')' :
		     '$1'++[{params,'$3'}].

initializer -> assignment_expr : '$1'.
initializer -> '{' initializer_list '}' : '$2'.
initializer -> '{' initializer_list ',' '}' : '$2'.

initializer_list -> initializer : ['$1'].
initializer_list -> initializer_list ',' initializer : '$1'++['$3'].

statement -> labeled_statement : '$1'.
statement -> compound_statement : '$1'.
statement -> expression_statement : '$1'.
statement -> selection_statement : '$1'.
statement -> iteration_statement : '$1'.
statement -> jump_statement : '$1'.

labeled_statement -> cidentifier ':' statement : 
			 #clabel { line='$1'#cid.line,name='$1'#cid.name,code='$3'}.
labeled_statement -> 'case' constant_expr ':' statement : 
			 #ccase { line=line('$1'),expr='$2',code='$4'}.
labeled_statement -> 'default' ':' statement : 
			 #cdefault {line=line('$1'),code='$3'}.

compound_statement -> '{' '}' : [].
compound_statement -> '{' statement_list '}' : '$2'.
compound_statement -> '{' declaration_list '}' : '$2'.
compound_statement -> '{' declaration_list statement_list '}' : '$2'++'$3'.

declaration_list -> declaration : '$1'.
declaration_list -> declaration_list declaration : '$1'++'$2'.

statement_list -> statement : ['$1'].
statement_list -> statement_list statement : '$1' ++ ['$2'].

expression_statement -> ';' : #cempty{line=line('$1')}.
expression_statement -> expr ';' : '$1'.

selection_statement -> 'if' '(' expr ')' statement :
	    #cif {line=line('$1'),test='$3',then='$5'}.
selection_statement -> 'if' '(' expr ')' statement 'else' statement :
	    #cif {line=line('$1'),test='$3',then='$5',else='$7'}.
selection_statement -> 'switch' '(' expr ')' statement :
	    #cswitch { line=line('$1'),expr='$3',body='$5'}.

iteration_statement -> 'while' '(' expr ')' statement :
	    #cwhile { line=line('$1'),test='$3',body='$5'}.
iteration_statement -> 'do' statement 'while' '(' expr ')' ';' :
	    #cdo { line=line('$1'),body='$2',test='$5'}.
iteration_statement -> 'for' '(' ';' ';' ')' statement :
	    #cfor {line=line('$1'),body='$6'}.
iteration_statement -> 'for' '(' ';' ';' expr ')' statement :
	    #cfor {line=line('$1'),update='$5',body='$7'}.
iteration_statement -> 'for' '(' ';' expr ';' ')' statement :
	    #cfor {line=line('$1'),test='$4',body='$7'}.
iteration_statement -> 'for' '(' ';' expr ';' expr ')' statement :
	    #cfor {line=line('$1'),test='$4',update='$6',body='$8'}.
iteration_statement -> 'for' '(' expr ';' ';' ')' statement :
	    #cfor {line=line('$1'),init='$3',body='$7'}.
iteration_statement -> 'for' '(' expr ';' ';' expr ')' statement :
	    #cfor {line=line('$1'),init='$3',update='$6',body='$8'}.
iteration_statement -> 'for' '(' expr ';' expr ';' ')' statement :
	    #cfor {line=line('$1'),init='$3',test='$5',body='$8'}.
iteration_statement -> 'for' '(' expr ';' expr ';' expr ')' statement :
	    #cfor {line=line('$1'),init='$3',test='$5',update='$7',body='$9'}.

jump_statement -> 'goto' cidentifier ';' : 
	    #cgoto {line=line('$1'),label='$2'#cid.name}.
jump_statement -> 'continue' ';' : 
	    #ccontinue {line=line('$1')}.
jump_statement -> 'break' ';' : 
	    #cbreak {line=line('$1')}.
jump_statement -> 'return' ';' : 
	    #creturn {line=line('$1')}.
jump_statement -> 'return' expr ';' : 
	   #creturn {line=line('$1'),expr='$2'}.

cfile -> external_definition : '$1'.
cfile -> cfile external_definition : '$1'++'$2'.

external_definition -> function_definition : ['$1'].
external_definition -> declaration_list statement_list : '$1'++'$2'.

function_definition -> declarator function_body : 
		   {OldDecl,Body} = '$2',
		    #cfunction { line='$1'#cdecl.line,
				  name='$1'#cdecl.name,
				  type='$1'#cdecl.type,
				  params=OldDecl,
				  body=Body}.
function_definition -> declaration_specifiers declarator function_body :
		   {OldDecl,Body} = '$3',
		    #cfunction { line='$2'#cdecl.line,
				  name='$2'#cdecl.name,
				  storage='$1',
				  type='$2'#cdecl.type,
				  params=OldDecl,
				  body=Body}.

function_body -> compound_statement : {[],'$1'}.
function_body -> declaration_list compound_statement : {'$1','$2'}.

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

quantifier -> '[' 'ALL' ']'   : op('$2').
quantifier -> '[' 'ANY' ']'   : op('$2').
quantifier -> '[' 'NONE' ']'  : op('$2').
quantifier -> '[' 'ONE'  ']'  : op('$2').
quantifier -> '[' 'E' ']'     : 'ANY'.
quantifier -> '[' 'E' '!' ']' : 'ONE'.
quantifier -> '[' 'A' ']'     : 'ALL'.
quantifier -> '[' qtype expr ']' : {'$2',comma_list('$3')}.

%%
%% Declaration of boolean and integer "predicates"
%%
pdecl -> pexpr ':' sexpr '/' 'signed'   : {int,'$3','$1'}.
pdecl -> pexpr ':' sexpr '/' 'unsigned' : {uint,'$3','$1'}.
pdecl -> pexpr ':' sexpr                : {uint,'$3','$1'}.

pdecls -> pdecl : ['$1'].
pdecls -> pdecls ',' pdecl : '$1'++['$3'].

%%
%% Logic expression
%%
lexpr_prim -> integer               : constant(value('$1')).
lexpr_prim -> pexpr                 : '$1'.
lexpr_prim -> identifier            : name('$1').
lexpr_prim -> '$' '(' expr ')'      : {'expr','$3'}.

lexpr0 -> lexpr_prim                : '$1'.
lexpr0 -> true                      : true.
lexpr0 -> false                     : false.
lexpr0 -> '-' lexpr                 : {'-', '$2'}.
lexpr0 -> 'not' lexpr               : { op('$1'), '$2' }.
lexpr0 -> '!' lexpr                 : { op('$1'), '$2' }.
lexpr0 -> '~' lexpr                 : { op('$1'), '$2' }.
lexpr0 -> '(' lexpr ')'             : '$2'.
lexpr0 -> '{' lexprs '}'            : {vec,'$2'}.
lexpr0 -> identifier '(' lexprs ')' : { name('$1'), '$3'}.
lexpr0 -> quantifier '(' lexprs ')' : {'$1','$3'}.
lexpr0 -> quantifier lexpr          : {'$1','$2'}.

lexpr0 -> lexpr_prim ':' sexpr '/' 'signed'   : {int,'$3','$1'}.
lexpr0 -> lexpr_prim ':' sexpr '/' 'unsigned' : {uint,'$3','$1'}.
lexpr0 -> lexpr_prim ':' sexpr              : {uint,'$3','$1'}.
lexpr0 -> lexpr0 '[' expr ']'           : { bit_index, '$1', '$3'}.
lexpr0 -> lexpr0 '[' expr ':' expr ']'  : { bit_range, '$1', '$3', '$5'}.

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
sexpr -> identifier : name('$1').

pexpr -> psymbol               : { p, '$1', []}.
pexpr -> psymbol '(' ')'       : { p, '$1', []}.
pexpr -> psymbol '(' expr ')'  : { p, '$1', comma_list('$3')}.

psymbol -> 'A' : 'A'.
psymbol -> 'E' : 'E'.
psymbol -> symbol : name('$1').
    

Erlang code.

-include("varp_bic.hrl").
-import(lists, [map/2, member/2]).
-export([init/0]).

init() ->
    %% erase dictionay use
    erase(bic_is_typedef),
    lists:foreach(
      fun
	  ({{bic_type,T},_}) -> erase({bic_type,T});
	  (_) -> ok
      end, get()).


add_pointer([{pointer,Ptr,Spec}]) ->
    [{pointer,['*'|Ptr],Spec}].

add_decl([{pointer,Ptr,Spec}], Decl) ->
    [{pointer,Ptr,Spec++Decl}].

id({identifier,Line,Name}) -> #cid { line=Line, name=Name};
id({symbol,Line,Name})     -> #cid { line=Line, name=Name};
id({true,Line})            -> #cid { line=Line, name="true"};
id({false,Line})           -> #cid { line=Line, name="false"}.


typeid({type,Line,Name}) ->
    #ctypeid { line=Line, name=Name}.

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

str({string,Line,Val}) ->
    #cconst { line=Line, base=string, value=Val}.

%% Handle typedef declaration (very) special
decl(D) ->
	case get(bic_is_typedef) of
	    true ->
		put({bic_type,D#cdecl.name}, true),
		put(bic_is_typedef, false),
		#cdecl { line=L, name=N, type=T, size=S, value=V } = D,
		#ctypedef { line=L, name=N, type=T, value=V, size=S };
	    _ ->
		D
	end.

op({Type,_Line})     -> Type.

line([H|_]) -> line(H);
line(T) when is_atom(element(1,T)),
	     is_integer(element(2,T)) ->
    element(2,T).

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

machine_type(Type) ->
    machine_type(int,Type).

machine_type(Sign,Type) -> {Sign, machine_sizeof(Type)}.

%% fixme make this flexible
machine_sizeof(char) -> 8;
machine_sizeof(short) -> 16;
machine_sizeof(int) -> 32;
machine_sizeof(long) -> 64.

machine_endian() -> little.
