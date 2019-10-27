
# propositional variables

A propositional variables always start with a big letter
like A,B,C, Foo ... A propositional variable name can also include a 
list of arguments like A(1,2) B(3) an empty list like D() is equivalent with D.
This can also be viewed as instances of predicates.

A propositional variable argument can be an integer, declared literal,
an ordered set of integers or a function application ( f(1,2) )
where the function name must start with a small letter.

syntax

  propvar = <name> [ '(' [ <arg> [',' <arg>]* ] ')' ]
  arg     = <integer> | <literal> | setof(<integer>) | <func>
  func    = <name> '(' [ <arg> [',' <arg>]* ] ')'
  
# Boolean connectives

Boolean connectives in priority order are

	not  !
	and  &&
	xor
	or   ||	
    imp  implies ->
    equ  equivalent <->

# Integers

Integer are represented in two complement form and integer variables
may be signed or unsigned. A integer variable X of bit size N is 
entered as X:N. The default sign is unsigned. To enter a signed
variable the notation X:N/signed is used. 
Integer variables may also be declared like:

    declare X:n/signed;
    declare Y:m/unsigned;

Integer variables are infact boolean variable vectors and integer values
are boolean constant vectors and may be used as such.

# Integer operators

	*    integer multiplication
	/    integer division
	%    integer reminder
	+    addition
	-    subtraction
	
# Comparison operators

    <    less than
	<=   less than or equal
	>    greater than
	>=   greater than or equal
	==   equal to
	!=   not equal to
	
# Vectors

Boolean vectors can be entered as {A,B,C} and is handled like
unsigned integer when it comes to integer operators.

# Bitwise operators

Bitwise operators work on Integers, Vectors and Propositional
variables. The Propositional variables are handled as 
vectors of length 1.

    ~    bitwise not
    &    bitwise and
	^    bitwise exclusive or
	|    bitwise or
	<<   left shift by constant
	>>   right shift by constant
	<<<  left circular shift by constant
	>>>  right circular shift by constant

# Quantifiers

    '['<quatifiers> [<expr>] (<domain>|<condition>)* ']' <formula>
    '['<quatifiers> [<expr>] (<domain>|<condition>)* ']' <formula-args>

    <domain> = <var> '=' <set> 
    <domain> = '{' <var1> ...<varn> '}' '=' <set>
	<condition> is a boolean meta expression
	<set> = a..b integer set of all integers including a to b
	<set> = 
	
The quantifiers are:

    A  | ALL        all quantification
	E  | ANY        existence quantification
	E! | ONE        exist one quantification
	NONE            exist none
	PARITY          odd number of true
	ODD             odd number of true
	EVEN            even number of true
	EQ n            exactly n true
	NEQ n           exactly n false
	GT n            more than n true
	GTE n           more than or equal to n true
	LT n            less than n true
	LTE n           less than or equal to n true

## Meta expression used in predicate arguments and quatifier expressions

    arithmetic unary operators
	   +, -
	arithmetic binary operators
	   +, -, *, /, %
	comparison operators
	   <, <=, >, >=, ==, !=
	logical unary operators
       !
	logical binary operators
       &&, ||
	bitwise binary operators
	   &, |, ^, <<, >>
	bitwise unary operators
	   ~
    a..b -> Sequence (a,a+1..b)

    builin meta function
	
	  factorial(Integer A) -> Integer
	  binom(Integer A, Integer B) -> Integer
	  sqrt(Number A) -> Float
	  isqrt(Integer A) -> Integer
	  sqr(Number A) -> Float
	  nroot(Number A, Integer N) -> Float
	  ln(Number A) -> Float
	  log(Number A) -> Float
	  log2(Number A) -> Float
	  log10(Number A) -> Float
	  ilog2(Integer A) -> Integer
	  isize(Integer A) -> Integer
	  usize(Integer A) -> Integer
	  pi() -> Float
	  e() -> Float
	  pow(Integer A, Integer B) -> Integer
	  pow(Number A, Number B)  -> Float
	  sin(Number A) -> Float
	  cos(Number A) -> Float
	  trunc(Number A) -> Integer
	  round(Number A) -> Integer
	  abs(Number A) -> Number
	  max(Number A, Number B) -> Number
	  min(Number A, Number B) -> Number
	  sum(Number X1,...Numner Xn) -> Number
	  union(OrdSet A, OrdSet B) -> OrdSet
	  subtract(OrdSet A, OrdSet B) -> OrdSet
	  intersect(OrdSet A, OrdSet B) -> OrdSet
	  product(OrdSet A, OrdSet B) -> Sequence(Ai,Bj)
	  subsets(Set A) -> Sequence(Set)
      subsets(Integer K,Set A) -> Sequence(Set) of size K
	  permutation(Sequence A) -> Set(Sequence)
	  zip(Sequence A,Sequence B) -> Sequence(Ai,Bi)


## Examples of quantifier use


    [ALL i=1..5] P(i)
    [ANY j=2..7] Q(i)
    [ONE x=1..6,y=x+1..10,x+y<15] R(x,y)
    [EQ 1,a=1..10] S(a)
    [EQ 2,a=1..10] S(a)
    [GT 2,b=1..10] T(b)
	[PARITY i=1..5] Q(i)

# Integer quantifiers

    [SUM i=1..5] X(i)
    [PROD j=1..5] Y(i)

# Bit selection

From a Integer X or a bit vector V a single bit may be selected by
using index.

    X[i] 
	V[i]
	
A range of bits my be selected by by specifing the start bit and
the stop bit.

	X[1:5]
	V[3:8]
