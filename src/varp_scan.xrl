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

%% type keywords
bool		: {token,{bool,TokenLine}}.
char		: {token,{char,TokenLine}}.
double		: {token,{double,TokenLine}}.
float		: {token,{float,TokenLine}}.
int		: {token,{int,TokenLine}}.
long		: {token,{long,TokenLine}}.
short		: {token,{short,TokenLine}}.
signed		: {token,{signed,TokenLine}}.
sizeof		: {token,{sizeof,TokenLine}}.
unsigned	: {token,{unsigned,TokenLine}}.

%% keywords
assert              : {token,{'assert',TokenLine}}.
circuit             : {token,{'circuit',TokenLine}}.
input               : {token,{'input',TokenLine}}.
in                  : {token,{'in',TokenLine}}.
output              : {token,{'output',TokenLine}}.
out                 : {token,{'out',TokenLine}}.
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
implies             : {token,{implies,TokenLine}}.
equ                 : {token,{equ,TokenLine}}.
equivalent          : {token,{equivalent,TokenLine}}.
return              : {token,{return,TokenLine}}.
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
PARITY              : {token,{'PARITY',TokenLine}}.
ODD                 : {token,{'ODD',TokenLine}}.
EVEN                : {token,{'EVEN',TokenLine}}.
%% builtin "logic" functions
abs                 : {token,{'abs',TokenLine}}.
min                 : {token,{'min',TokenLine}}.
max                 : {token,{'max',TokenLine}}.

"(\^.|\.|[^\"])*"   : begin
			  S = lists:sublist(TokenChars,2,TokenLen-2),
			{token,{string, TokenLine, S}}
		      end.

{L}({L}|{D})*	    : 
  Name = list_to_binary(TokenChars),  %% utf8?
  case varp_formula:is_circuit_def(Name, false) of
      false -> {token,{symbol,TokenLine,Name}};
      true -> {token,{cname,TokenLine,Name}}
  end.


0[xX]{H}+{IS}?      : {token,{hexnum,TokenLine,TokenChars}}.
0[b]{B}+{IS}?       : {token,{binnum,TokenLine,TokenChars}}.
0{D}+{IS}?          : {token,{octnum,TokenLine,TokenChars}}.
{D}+{IS}?           : {token,{decnum,TokenLine,TokenChars}}.

'(\^.|\.|[^\'])+'	    : {token,{chrnum,TokenLine,TokenChars}}.

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

-export([init/1, one_token/0, all_tokens/0, all_tokens/1]).

-define(CONT, varp_scan_cont).
-define(LOC, varp_scan_loc).
-define(BUF, varp_scan_buf).

init(Chars) ->
    put(?CONT, []),
    put(?LOC,  1),
    put(?BUF, Chars++" ").

%% ulgy stuff !!! why not continuation between yecc/leex ...why why why
one_token() ->
    case token(get(?CONT), get(?BUF), get(?LOC)) of
	{more, Cont} -> %% check end of file...
	    %% here we should add a blank at end of buf and try again!
	    put(?CONT, Cont),  %% only used if we read more chars!
	    {eof, get(?LOC)};
	{done, {ok, Token, EndLoc}, Chars1} ->
	    put(?LOC, EndLoc),
	    put(?BUF, Chars1),
	    {ok, [Token], EndLoc};
	{done, {eof, EndLoc}, Chars1} ->
	    put(?LOC, EndLoc),
	    put(?BUF, Chars1),
	    {eof, EndLoc};
	{done, Error = {error,_,_}, Chars1} ->
	    put(?BUF, Chars1),
	    Error
    end.

all_tokens(Chars) ->
    init(Chars),
    all_tokens().

all_tokens() -> 
    all_tokens_([]).
all_tokens_(Acc) ->
    case one_token() of
	{ok,[T],_EndLoc} ->
	    all_tokens_([T|Acc]);
	{eof, Loc} ->
	    {ok, lists:reverse(Acc), Loc};
	Error ->
	    Error
    end.
