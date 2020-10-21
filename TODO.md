- fix STACK OVERFLOW

Running some large formulas the qtype=recursive can recurse to
deep on the runtime stack. bcp1 is called over and over.
This can partly be improved by checking for short cut instead of
doing a recursion. (work around use qype=lifo|fifo)


- add predicate info

  add_predicate(Vp, "Name", [{arity,N},{type,bool|int|uint|bits}])
  
  del_predicate(Vp, "Name")

  predicate_info(Vp, "Name", arity) -> integer()
  predicate_info(Vp, "Name", type) -> bool|int|uint|bits

  symbol_first(Vp, "Name") -> symbol() | false
  symbol_next(Vp, "Name", Sym) -> symbol() | false

  add_symbol(Vp, {"Name",[A1,..An]}) ->

  add_symbol(Vp, "Name") ==
    		 (maybe add_predicate(Vp,"Name",[{airty,0},{type,bool}]) )
  		 add_symbol(Vp, {"Name",[]})
  
  add_predicate(Vp, "Name") == add_predicate(Vp,"Name",[{arity,0},{type,bool}])

- semantic quantified expressions

semantics best decribed with an example!

[E! x=1..3][E! x=1..3]P(x,y)

   ONE(
      ONE(P(1,1),P(1,2),P(1,3)),
      ONE(P(2,1),P(2,2),P(2,3)),
      ONE(P(3,1),P(3,2),P(3,3)))

[E! x=1..3,x=1..3]P(x,y)

   ONE(
      P(1,1),P(1,2),P(1,3),
      P(2,1),P(2,2),P(2,3),
      P(3,1),P(3,2),P(3,3))
   

- determine a symbol encoding

  P        boolean variable
  P()      same as above but in a predicate style
  P(1,2)   predicate instance, normal
  P(a)     predictae instance, literal atom
  P(f(a))  predicate instance, function application
  P(a+b) = P(add(a,b)) predicate instance operator application

  A(1,1):4   integer/bitvector indexed variable
  A(1,1)[2]  integer/bitvector bit access

  Either variable P(a+b) is stored as string "P(add(a,b))"
  or if structure needs to be handle or matched then symbol
  name is stored as structure {"P",[{"add",["a","b"]}]}
  (in python as  ("P",[("add",["a","b"])])


  formalize internal atomic formula structure
  #define ARG_TYPE_INT  0
  #define ARG_TYPE_ATM  1
  #define ARG_TYPE_APP  2

  ARG(i) == INT() | APP() | ATM()
  APP -> [INT(n),ATM(name),ARG(1),...ARG(n)]
  

  a) store bits together as aliases?

     symbol "A(1,1)" has a list of bits as value
     symbol "P(1,2)" has one bit as value

     when looking up A(1,1)[3] then symbol "A(1,1)" is first looked
     up then the fourth bit (0 based) is retrived if available.


  b) new add symbol / add bitvector access

     (first,last) = add_variables(vp, 5 [,is_atom])

     add_symbol(vp, 5, "X(1,2)")
     add_symbol(vp, 5, "Y(2,2)")
     add_symbol(vp, [5,3,2] "Z(1)")
     
        variable 5 is both X(1,2), Y(2,2) and Z(1)[0]

     set_symbol(vp, 1, 7, "Z(1)")

        update symbol Z(1) to [5,7,2]

     set_symbol(vp, 0, 13, "X(1,2)") == set_symbol(vp, 13, "X(1,2)")
     		    

     set_symbol(vp, 3, [1,2,3], "Z(1)")

        update symbol Z(1) to [5,3,2,1,2,3]

     set_symbol(vp, 5, [12], "Z(1)")

        update symbol Z(1) to [5,3,2,F,F,12]

     find symbol return either a variable or a list
     of variables

     variable_info symbol should also keep the index/0 for
     symbols to find position for each alias

     
- allow for multiple clausesets  D1...Dn

  each clause set should be able to set properties
  like hash/xref

- add trigger list, a list with only one watch point.
  When the watch point reach start/end of list, then all variables
  are assign a value and will trigger.


- test saturate over clauses!

given a clause [A,B,C]
try saturate over [A,B,C]


- turbo bcp(Vp, [L1,..Ln], TryAllTurbo=false)

  P/1
	( P ... C1 )
	( P ... C2 )
	...
	( p ... Cn )

  if C1,C2...Cn are all true then
     ( for Backjump add clause ( ~P ~C1 ~C2 ... ~Cn ) )
     generate contradiction (return atom turbo)

  for Overdrive then set ~C1,..~Cn and see if it holds
  
  Using turbo in backtrack
  
  set_level(Level=1),
  Turbo = get_param(turbo),
  true = bind(Vp, P)  -- set P=1
  case bcp(Vp, Turbo) of
     true ->
	   Bs1 = get_bindings(Vp,Level),
	   undo_level(Vp,Level),
   	   true = bind(Vp, -P),
	   case bcp(Vp, Turbo) of
     		true ->
		      Bs0 = get_bindings(Vp,Level),
		      undo_level(Vp,Level),
		      install(intersect(P, Bs0, Bs1));
		_FalseOrTurbo ->
		      undo_level(Vp,Level),
		      install(Bs1)
	   end;
     TurboOrFalse ->
     	   undo_level(Vp,Level),
	   true = bind(Vp, -P),
	   case bcp(Vp, TurboOrFalse==false) of
     		true ->
		      Bs0 = get_bindings(Vp,Level);
		_FalseOrTurbo ->		      
		      undo_level(Vp,Level),
		      false
	   end
    end	  

Run 

- multiple bcp strategies (used when twl can not be used)

  bcp_xref (clause,i)
    - bitmap (max 64 literals) |BFM|BTM|Size | X1 ... Xn |
	 Propagate Xi=FALSE:
	   BTF |= (1 << i)
	   if only one bit remain unbound set and propagte Xi
	 Propagate Xi=TRUE
 	   BitsTrue |= (1 << i)
	   kill clause (level=0)

    - swap (clause,i)
	 |Size|#unbound| X1..Xm Y1..Yn |

	 Y1 .. Ym are bound while X1..Xm are unbound

	 Propagate Xi=FALSE:
	   swap (Xref.pos, Xm) set unbound--
	   unbound=1 => propagate X1
	 Propagate Xi=TRUE
 	   swap (Xref.pos, Xm) set unbound--


- decide/bind next_unbound now returns variable, decide/bind will
 control the sign, this allow for using the previous saved value.

- various bump variants (OK)
  
- Check variables with degree = 1 (may be set = TRUE?) (included in turbo)

- Handle declaration of integers and sizes in snf and cnf formats also
 add variables that where bound "X[1] is t"

- Save CNF from varp_wx, {satisfy, [saturate], cnf -f <file> } (OK)

- Generate proof files (check box in varp_wx) file.prf

- Validate proofs read file.prf {validate -f <file> }

- What if TWL opt for literals that are already watched in
    other clauses?

  - use a flag that mark if a literal is already watched in some
    clause.
  - 

- Fix/verify pair substitution

  - Level/Bound feedback (for fun)

- More flexibel "order" syntax (Prepared)

old syntax: [+|-]<name>[','[+|-]<name>]

  <x          +x    x ascending
   x>         -x    x descending

  <x|<y       +x,+y
  <x|y>       +x,-y
  x>|<y       -x,+y
  x>|y>       -x,-y

  x>||y>      sort on x if x equal then then y then fold

  x>y == x>|<y  -x,+y


- turbo eval (OK)  nbcp + undo

  nbcp
    bcp n steps until contradiction or model
    return
  	  true       - model exist
	  false      - contradiction found

  undo
       undo and flip decision, if already flipped then
       undo to next level.

    return
       false  - no more variables to flip = no models = inconsistent
       true   - backtracked may call nbcp again

- Seoul

  - Xref on/off (get_clauses) (OK)


- Shanghai

  - only allow one predicate symbol to be used for one
    arity. P(x) and P(x,y) is then not allowed. Neither is
    X:6 and X:5 ony one size per symbol may be declared. OK
  - Fixed sorting bug, keep variable order better

- Beijing

  - Fix cancel bug (Ok)
  - Fix substitution bug (Ok)

- Ulanbaatar

  - Explicit short cuts to all menu items, did not work automatically under
   windows. (OK)

  - Multiple clause set 0(delta), 1(gamma), 2(alpha?), 3(beta?) (30 bit index)
    (OK)
    
  - Multiple models with backjump (OK)

  - PARITY function (OK)
  - ODD/EVEN (OK)

  - select error line on parse error (OK)
    
- Bajkal release

  fix satisfy/falsify/cancel (OK)
  
  check gauge glow under windows, looks like running (NOT POSSIBLE).
  
  update final statistics (OK)
  
  update clauses/dead-clauses while running time update (OK)

  check content changed ! maybe use modified? (OK)

  new - create new window? or clear (OK)

  save to file (OK)

  open ( save before )  (OK)
  
  save as (overwrite/rename dialog) (OK)


- move varc wrapper api into varp module!

+ map TRUE and FALSE (FIXED using atoms t and f in erlang)

  map TRUE to   (1 bsl 27)  =  0x8000000
  and FALSE to -(1 bsl 27)  = -0x8000000
  UNDEF is still = 0
  
  and use 1 for variables.

  This makes dimacs process possible without mapping
  of variables!

- push/pop

  create clause stack/heap

  push (create clauses and variables ) pop ( variables and clauses are removed)


- 2-clause implication list

  2-clauses are only represented as " implication list"
  clause (A,B), (B,C),

  install triggers
	A:
	   !A -> [B]
        B:
	   !B -> [A,C]
	C:
	   !C -> [B]

  if during eval B=0 then the list for !B is executed and
  A=1, C=1 are set.

  A cantor pair enumeration map must be install for this to
  work, first to check for duplicates and then to generate
  clause indices.

  normal clause index is return as (cix << 1) while
  a 2-clause index is return as ((cantor_pair(A,B) << 1)+1)
	   

- cantor pair enumeration map for all 2-clauses, marking
  2_clauses already installed.

  given (A,B) then mark

  (!A -> B)  (!B -> A)

  set bit number cantor_pair(!A,B)
  and cantor_pair(!B,A)

  before install of 2-clause check the cantor map


- satdis (plugin)

 Lägg till (alla) Ci v Di vid dilemma intersection

- sym (plugin)

 Givet två klausuler som är lite lika skapa en
 permutation P och kolla om de klausuler som ej
 finns i delta följer av delta. Då lägger
 man in  V <= P(V) eller V = P(V) om en model

 Spara P till konflikt klausuler.
 
- size (atoms ?)

+ order occure + clause length

  occure A =  1/N1 + ... + 1/Nk

  om A förekommer i (A ... Pn1) (A ... Pn2) + ... + (A + Pnk)

- order activity

  activity score initialized update each variable
  in an conflict (possibly not decision variables) with
  1. sort according to score

- continue with backtrack after backjump
  as alternative to install all models while
  backjumping.
  Only install the first model as blocked clause
  (negate literals) and continue with backtracking
  keep install conflict clauses...

+ add input conversion

input(Line,Acc) ->
  {true,Form,Acc1}
| {false,Acc1}

+ add assertion,

  assert(is_odd(n) && (n > 1))

+ Options per backend

  new option syntax and new control file format

  plugin1 [options] plugin2 [options] ...

  file format allows for nested options when possible:

  %% erlang format?

  plugin/backends
  ---------------

    General options

    --seed <unsigned>		set random seed
    --compress <bool>		compress clauses
    --max <unsigned>		max number of models
    --method=collect|count
    --print true|false|model|umodel|literal|erlang
    --clause <bool>
    --starexec <boolean>
    --timeout <seconds>|'infinity'    
    
    satisfy
	-- no options, set formula value = 1, if possible
    prove
	-- no options, set formula value = 0, if possible
    
    saturate
	-s <k>
	--pair <bool>
	--timeout <seconds>|'infinity'
	--threshold <unsigned>
	--laps <unsigned>|'infinity'
	
    backjump
    	--timeout <seconds>|'infinity'
	--minimize <bool>
	--max-learned
	--max-learned-factor
	--keep-factor
	--min-keep-clauses
	--restart-counter
	--restart-interval
	--iorder
	--max-conflicts
	--num-conflicts
	--stumble
	--olle
	--stumble-olle
	
    backtrack
	--timeout <seconds>|'infinity'
	
    reduction
    	--timeout <seconds>|'infinity'
	--reduction <unsigned>|'all'
	--reduction-type=pos|neg|both|min

    rat
    	--timeout <seconds>|'infinity'
	--rat <unsigned>|'all'
      	--rat-type=pos|neg|both|min

    cnf
	--file <filename>




 {do [,otions], [
    {plugin1, [option..]},
    {plugin2, [option..]},
    ...
    ]}

  some general options are 'timeout' and 'order' ... etc

- simulator gui backjump

  Design GUI to track simple examples ~30-40 clauses
  and conflict clauses and assignments levels

+ Statistcs

  histogram over conflict clause lengths added

  histogram over number conflicts analysed generated per conflict

  histogram over eval implication chain lengths?

  historgram over backjump/backstumble distance.
  

+ Add max conflict clause length i-order learning.

+ Add relevance bounded learning, example lru learning.

+ Back stumble j diff between last levels

- Prove F => x1=x2= .. =xn
 use models ex x1=x3=x7=1 x2=x4=x8=0 to construct
 F => x1=x3=x7
 etc

- Strategy olle/stumble messure conflict clauses distances... something
  to tune olle and stumble jump lengths.

+ add --seed to random generator

+ stumble_olle  stumbel AND olle (now it is OR)


1. Test backtrack over multi value variables.

Example x1...x8

Bind pairwise

     x1=x2
        x3=x4
            x5=x6
                x7=x8
                    x2=x4
                        x6=x8
                            x4=x8
			    x4!=x8
			x6!=x8

2. Test multiple backtrack & run them in parallell

   Create N instances of the problem, all with different
   settings and variable order etc.

   Now multitask over the instances.


3. Saturate over multivalue variable vector

   saturate {x1,x2,x3} like

   ~x1, ~x2, ~x3  => b000
   ~x1, ~x2, x3   => b001
   ~x1, x2, ~x3   => b010
   ~x1, x2,  x3   => b011
    x1, ~x2,~x3   => b100
    x1, ~x2, x3   => b101
    x1, x2, ~x3   => b110
    x1, x2,  x3   => b111

    Variable vectors like
      {uint,X,n,i}
      {int,X,n,i}
      {bit,X,n,i}


4. Introduce CODE block, reason about sequential code

code {
   int x = 1;
   int y = 2;
   if (x < y)
      x++;
   else
      y++;
}

C-types:
	char   = signed char
	short  = signed short
	int    = signed int
	long   = signed long
	unsigned char
	unsigned short
	unsigned int
	unsigned long
	unsigned = unsigned int
	signed = signed int?
stdint
	int8_t, int16_t, int32_t, int64_t
	uint8_t, uint16_t, uint32_t, uint64_t

code generation
     L0 : int x = 1  => X[0]:32 = 1
     L1 : int y = 2  => Y[0]:32 = 2
     L2 : if (x < y) => C1 == (X[0]:32 < Y[0]:32);
     L3:      x++;    => X[1]:32 = X[0]:32 + 1
          else
     L4:      y++     => Y[1]:32 = Y[0]:32 + 1

     X[2]:32 = ITE(C1, X[1]:32, X[0]:32)
     Y[2]:32 = ITE(C1, Y[0]:32, Y[1]:32)
     L0 = true
     L1 = true
     L2 = true
     L3 = C1;
     L4 = ~C1


Models are presented with some of:
- output state
- all instances
- all instances and flow positions (maybe line numbers)

input variables must be accessible
