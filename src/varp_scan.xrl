%% -*- erlang -*-
%% VARP scanner
%%

Definitions.

B	= [0-1]
D	= [0-9]
L       = [a-zA-Z_\$]
A       = ({L}|{U})
H	= [a-fA-F0-9]
E	= [Ee][+-]?{D}+
FS	= (f|F|l|L)
IS	= (u|U|l|L)*
WS      = [\000-\s]

Rules.

%% C keywords
char		: {token,{char,TokenLine}}.
double		: {token,{double,TokenLine}}.
float		: {token,{float,TokenLine}}.
int		: {token,{int,TokenLine}}.
long		: {token,{long,TokenLine}}.
short		: {token,{short,TokenLine}}.
signed		: {token,{signed,TokenLine}}.
sizeof		: {token,{sizeof,TokenLine}}.
unsigned	: {token,{unsigned,TokenLine}}.

%% varp keywords
assert              : {token,{'assert',TokenLine}}.
input               : {token,{'input',TokenLine}}.
output              : {token,{'output',TokenLine}}.
declare             : {token,{'declare',TokenLine}}.
literals            : {token,{'literals',TokenLine}}.
define              : {token,{'define',TokenLine}}.
order               : {token,{'order',TokenLine}}.
rank                : {token,{'rank',TokenLine}}.
degree              : {token,{'degree',TokenLine}}.
random              : {token,{'random',TokenLine}}.
identity            : {token,{'identity',TokenLine}}.
true                : {token,{'true',TokenLine}}.
false               : {token,{'false',TokenLine}}.
and                 : {token,{'and',TokenLine}}.
or                  : {token,{'or',TokenLine}}.
xor                 : {token,{'xor',TokenLine}}.
not                 : {token,{'not',TokenLine}}.
imp                 : {token,{imp,TokenLine}}.
imp                 : {token,{implies,TokenLine}}.
equ                 : {token,{equ,TokenLine}}.
equivalent          : {token,{equivalent,TokenLine}}.
A                   : {token,{'A',TokenLine}}.
E                   : {token,{'E',TokenLine}}.
ALL                 : {token,{'ALL',TokenLine}}.
ANY                 : {token,{'ANY',TokenLine}}.
ONE                 : {token,{'ONE',TokenLine}}.
NONE                : {token,{'NONE',TokenLine}}.
EQ                  : {token,{'EQ',TokenLine}}.
NEQ                 : {token,{'NEQ',TokenLine}}.
GT                  : {token,{'GT',TokenLine}}.
GTE                 : {token,{'GTE',TokenLine}}.
LT                  : {token,{'LT',TokenLine}}.
LTE                 : {token,{'LTE',TokenLine}}.
SUM                 : {token,{'SUM',TokenLine}}.
PROD                : {token,{'PROD',TokenLine}}.

"(\^.|\.|[^\"])*"   : begin
			  S = lists:sublist(TokenChars,2,TokenLen-2),
			{token,{string, TokenLine, S}}
		      end.

%% C identifier (varp tokens are added in the grammar)

{L}({L}|{D})*	    :	case TokenChars of
			    [C|_] when C >= $A, C =< $Z; C =:= $_; C =:= $$ ->
				{token,{symbol,TokenLine,TokenChars}};
			    _ ->
				{token,{identifier,TokenLine,
					TokenChars}}
			end.

0[xX]{H}+{IS}?      : {token,{hexnum,TokenLine,TokenChars}}.
0[b]{B}+{IS}?       : {token,{binnum,TokenLine,TokenChars}}.
0{D}+{IS}?          : {token,{octnum,TokenLine,TokenChars}}.
{D}+{IS}?           : {token,{decnum,TokenLine,TokenChars}}.

'(.|[^\'])+'	    : {token,{chrnum,TokenLine,TokenChars}}.

%% floating point not yet supported!
%% {D}+{E}{FS}?	      : {token,{flonum,TokenLine,TokenChars}}.
%% {D}*\.{D}+({E})?{FS}? : {token,{flonum,TokenLine,TokenChars}}.
%% {D}+\.{D}*({E})?{FS}? : {token,{flonum,TokenLine,TokenChars}}.

%% Varp operators
<->                 : {token,{'<->',TokenLine}}.
>>>		    : {token,{'>>>',TokenLine}}.
<<<		    : {token,{'<<<',TokenLine}}.
>>		    : {token,{'>>',TokenLine}}.
<<		    : {token,{'<<',TokenLine}}.
->		    : {token,{'->',TokenLine}}.
&&		    : {token,{'&&',TokenLine}}.
\|\|		    : {token,{'||',TokenLine}}.
<=		    : {token,{'<=',TokenLine}}.
>=		    : {token,{'>=',TokenLine}}.
==		    : {token,{'==',TokenLine}}.
!=		    : {token,{'!=',TokenLine}}.
:=		    : {token,{':=',TokenLine}}.
;		    : {token,{';',TokenLine}}.
\{		    : {token,{'{',TokenLine}}.
\}		    : {token,{'}',TokenLine}}.
,		    : {token,{',',TokenLine}}.
:		    : {token,{':',TokenLine}}.
=		    : {token,{'=',TokenLine}}.
\(		    : {token,{'(',TokenLine}}.
\)		    : {token,{')',TokenLine}}.
\[		    : {token,{'[',TokenLine}}.
\]		    : {token,{']',TokenLine}}.
\.\.		    : {token,{'..',TokenLine}}.
\.		    : {token,{'.',TokenLine}}.
&		    : {token,{'&',TokenLine}}.
!		    : {token,{'!',TokenLine}}.
~		    : {token,{'~',TokenLine}}.
-		    : {token,{'-',TokenLine}}.
\+		    : {token,{'+',TokenLine}}.
\*		    : {token,{'*',TokenLine}}.
/		    : {token,{'/',TokenLine}}.
\%		    : {token,{'%',TokenLine}}.
<		    : {token,{'<',TokenLine}}.
>		    : {token,{'>',TokenLine}}.
\^		    : {token,{'^',TokenLine}}.
\|		    : {token,{'|',TokenLine}}.
\?		    : {token,{'?',TokenLine}}.
{WS}+		    : skip_token .

Erlang code.

