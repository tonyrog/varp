%% -*- erlang -*-
%% VARP scanner
%%

Definitions.

B	= [0-1]
D	= [0-9]
L       = [a-z]
U       = [A-Z]
A       = ({L}|{U})
H	= [a-fA-F0-9]
E	= [Ee][+-]?{D}+
FS	= (f|F|l|L)
WS      = [\000-\s]

Rules.

"(\^.|\.|[^\"])*"   : begin
			  S = lists:sublist(TokenChars,2,TokenLen-2),
			{token,{string, TokenLine, S}}
		      end.

0[xX]{H}+           : {token,{hexnum,TokenLine,TokenChars}}.
0[b]{B}+            : {token,{binnum,TokenLine,TokenChars}}.
0{D}+	            : {token,{octnum,TokenLine,TokenChars}}.
{D}+                : {token,{decnum,TokenLine,TokenChars}}.

'(.|[^\'])+'	    : {token,{chrnum,TokenLine,TokenChars}}.

%% {D}+{E}             : {token,{flonum,TokenLine,TokenChars}}.
%% {D}*\.{D}+({E})?    : {token,{flonum,TokenLine,TokenChars}}.
%% {D}+\.{D}*({E})?    : {token,{flonum,TokenLine,TokenChars}}.

%% words
unsigned            : {token,{'unsigned',TokenLine}}.
signed              : {token,{'signed',TokenLine}}.

true                : {token,{'true',TokenLine}}.
false               : {token,{'false',TokenLine}}.

%% key words
A                   : {token,{'A',TokenLine}}.
E                   : {token,{'E',TokenLine}}.
FORALL              : {token,{'forall',TokenLine}}.
EXISTS              : {token,{'exists',TokenLine}}.
ALL                 : {token,{'all',TokenLine}}.
ANY                 : {token,{'any',TokenLine}}.
ONE                 : {token,{'one',TokenLine}}.
NONE                : {token,{'none',TokenLine}}.
EQ                  : {token,{'eqk',TokenLine}}.
NEQ                 : {token,{'neqk',TokenLine}}.
GT                  : {token,{'gtk',TokenLine}}.
GTE                 : {token,{'gtek',TokenLine}}.
LT                  : {token,{'ltk',TokenLine}}.
LTE                 : {token,{'ltek',TokenLine}}.

%% logic operators

AND                 : {token,{'and',TokenLine}}.
and                 : {token,{'and',TokenLine}}.
&&                  : {token,{'&&',TokenLine}}.
&                   : {token,{'&',TokenLine}}.
OR                  : {token,{'or',TokenLine}}.
or                  : {token,{'or',TokenLine}}.
\|\|		    : {token,{'||',TokenLine}}.
\|                  : {token,{'|',TokenLine}}.
XOR                 : {token,{'xor',TokenLine}}.
xor                 : {token,{'xor',TokenLine}}.
\^                  : {token,{'^',TokenLine}}.
NOT                 : {token,{'not',TokenLine}}.
not                 : {token,{'not',TokenLine}}.
!                   : {token,{'!',TokenLine}}.
~                   : {token,{'~',TokenLine}}.
IMP                 : {token,{imp,TokenLine}}.
imp                 : {token,{imp,TokenLine}}.
->                  : {token,{'->',TokenLine}}.
EQU                 : {token,{equ,TokenLine}}.
equ                 : {token,{equ,TokenLine}}.
<->                 : {token,{'<->',TokenLine}}.
==                  : {token,{'==',TokenLine}}.
=		    : {token,{'=',TokenLine}}.

%% arithmetic operators    

>>>		: {token,{'>>>',TokenLine}}.
<<<		: {token,{'<<<',TokenLine}}.
>>		: {token,{'>>',TokenLine}}.
<<		: {token,{'<<',TokenLine}}.
\+		: {token,{'+',TokenLine}}.
-		: {token,{'-',TokenLine}}.
\*		: {token,{'*',TokenLine}}.
/		: {token,{'/',TokenLine}}.
\%		: {token,{'%',TokenLine}}.

%% relations
<=		: {token,{'<=',TokenLine}}.
>=		: {token,{'>=',TokenLine}}.
!=		: {token,{'!=',TokenLine}}.
<		: {token,{'<',TokenLine}}.
>		: {token,{'>',TokenLine}}.

%% separators
;		: {token,{';',TokenLine}}.
{		: {token,{'{',TokenLine}}.
}		: {token,{'}',TokenLine}}.
,		: {token,{',',TokenLine}}.
:		: {token,{':',TokenLine}}.
\(		: {token,{'(',TokenLine}}.
\)		: {token,{')',TokenLine}}.
\[		: {token,{'[',TokenLine}}.
\]		: {token,{']',TokenLine}}.
\.\.		: {token,{'..',TokenLine}}.
\.		: {token,{'.',TokenLine}}.

{L}({A}|{D}|_)*     : {token,{variable,TokenLine,TokenChars}}.
{U}({A}|{D}|_)*     : {token,{symbol,TokenLine,TokenChars}}.

{WS}+		: skip_token .

Erlang code.

