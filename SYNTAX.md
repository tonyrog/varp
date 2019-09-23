
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
    imp  ->       implication	
    equ  <->      equivalence

# Integers

Integer are represented in two complement form and integer variables
may be signed or unsigned. A integer variable X of bit size N is 
entered as X:N. The default sign is unsigned. To alter the sign of
a variable X:N/signed is used. Integer variables may also be declared
like

    declare X:n/signed;
    declare Y:m/unsigned;

Integer variables are infact boolean variable vectors and integer values
are boolean constant vectors and are handled as such internally.

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

[<quatifiers> var=domain...] <formula>

[ALL i=1..5] P(i)
[ANY j=2..7] Q(i)
[ONE x=1..6,y=x+1..10,x+y<15] R(x,y)
[EQ 1,a=1..10] S(a)
[EQ 2,a=1..10] S(a)
[GT 2,b=1..10] T(b)

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
