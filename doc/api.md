
# varp python API documentation 

## Instance functions

``` python
varpy.new(options)
```
Create a new varp instance from a dict of options

* {'size': size}
  Initial variable table size 
* {'qtype': 'lifo'|'fifo'|'recursive'}
  use lifo/fifo strategy in bcp
* {'xref': x}
  use cross references if x is True
* {'hash': x}
  use hash table for clauses if x is True
* {'edge': x}
  use edge tables for 2-clauses if x is True

``` python
varpy.clone(vp, options)
```

Clone the varp instance using setting options from varpy.new with the
follow additions:

* {'level': l}
  clone bindings up until level __l__
* {'set':  __clauseset__ | [__clauseset__]}
  clone clauseset DELTA, GAMMA, BETA and/or ALPHA
* {'queue', x}
  clone bcp queue only if x is True.

where __clauseset__ = 'delta'|'gamma'|'beta'|'alpha'

``` python
varpy.info(vp,  item)
```

Get varp information 

* version
* 'bcp\_counter'
* 'conflict\_counter'
* 'max\_conflicting'
* 'num\_conflicting'
* 'number\_of\_variables'
* 'number\_of\_clauses'
* 'number\_of\_edges'
* 'number\_of\_dead_clauses'
* 'number\_of\_dead_edges'
* 'number\_of\_learnt_clauses'
* 'number\_of\_bound_variables'
* 'number\_of\_subst_variables'
* 'number\_of\_unbound_variables'
* 'clause\_n\_counter'
* 'clause\_2\_counter'
* 'clause\_3\_counter'
* 'clause\_d\_counter'
* 'edge\_2\_counter'
* 'edge\_d\_counter'
* 'size'
* 'qtype'
* 'max\_level'
* 'min\_level'
* 'max\_bound'
* 'literal\_size'
* 'literal\_integer'
* 'value\_packing'
* 'edge'
* 'xref'
* 'hash'
* 'init\_phase'
* 'use\_phase'


``` python
varpy.config(vp, item, value)
```

Set configurable items in varp

* 'max\_conflicting'
 set max number of conflicts during bcp (<= MAX_CONFLICTING=1024)
*  'xref'
 turn on (True) or off (False) cross reference handling
* 'hash'
 turn on (True) or off (False) hash table handling		
* 'qtype'
 set style of literal queueing in bcp
 where value is one of 
 'lifo' | 'fifo' | 'recursive'
	

``` python
varpy.add_variable(vp [,is_atom])
```

Create a new variable. The variable is return as an index to the
next available variable in the variable table. Mark the new variable
as atom if is_atom is __True__. The atom status may later be queried with
variable info. is\_atom defaults to __True__.

``` python
varpy.add_variables(vp, num, [,is_atom])
```

Create __num__ new variables. The variables are return as a tuple
(__firstindex__, __lastindex__). If is_atom is __True__ then the variables
are marked as atom.


``` python
varpy.value(vp, x)
```

Return __True__ | __False__ | __None__,
Value, None is return if variables undefined.


``` python
varpy.bind(vp, x, [,l])
```

Bind variable x to True. If level __l__ is given then that level 
is used to the variable is bound on that level else the
variable is bound on the current level as set with varpy.set\_level.

``` python
varpy.decide(vp, x [,l])
```

Bind variable x to True and mark x as a decision variable.
If level __l__ is given then that level 
is used to the variable is bound on that level else the
variable is bound on the current level as set with varpy.set\_level.

``` python
varpy.subst(vp, x, y)
```

Substitute one literal for an other. Apply the substitution [__x__/__y__]
that is, all instances of __y__ are replaced by __x__ in all clauses.
The literal __y__ is then linked to __x__ so it will keep the
same status and value as that of __x__.
__NOTE__ that cross references must be enabled before varpy.subst can be
used, that is a call to varpy.config(vp, 'xref', True) must have been made
prior a call to varpy.subst.

``` python
varpy.implication_clause(vp, x)
```

Return the clause index for the clause where literal __x__ became a unit.

``` python
varpy.implication_level(vp, x)
```

Return the bind level for variable __x__, where it was assigned during bcp.

``` python
varpy.implication_pos(vp, x)
```

Return the position where literal __x__ is found in the implication clause.

``` python
varpy.conflicting_clause(vp, i)
```

Return the i'th conflicting clause found during the last bcp. The number
of conflicting clauses that can be returned is 'num_conflicting'.

``` python
varpy.is_variable(vp, x)
```

Return __True__ if literal __x__ is unbound. Return __False__ otherwise

``` python
varpy.is_bound(vp, x)
```

Return __True__ if literal __x__ is bound, through substition, 
to an other variable. Return __False__ otherwise.

``` python
varpy.is_equal(vp, x, y)
```

Check if literal __x__ and literal __y__ are the equal, that is bound to the
same variable or are bound to the same constant.


``` python
varpy.set_level(vp, l)
```

Set current level to __l__. Note that level 0 is treated
as constant level. So be careful when setting level to 0.


``` python
varpy.keep_level(vp, l)
```

Keep all bindings on level __l__ by removing the undo information.

``` python
varpy.move_level(vp, src, dst)
```

Move bindings from level __src__ to level __dst__.

``` python
varpy.undo_level(vp, l)
```

Undo all bindings on level __l__.

``` python
varpy.undo(vp)
```

Undo bindings typically after an nbind. Undo will undo all bindings
until a decision and flip the variable if not already flipped.


``` python
varpy.bcp(vp [,[x1,..,xn] [,all]])
```

Run value propagation. Return __True__ if no
contradiction is found, __False__ otherwise.

__[EXPERIMENTAL]__

If literals __x1__..__xn__ are given they are checked for
"turbo" rule, that is, if all clauses that xi
is a part of are true regardless of the value of xi.
If 'all' is true then all xi's must be true for the
rule to hold. If turbo rule is successful then 
varpy.__turbo__ is returned.

__[EXPERIMENTAL]__


``` python
varpy.nbcp(vp)
```

decide and bind next unbound variables until either
no more variables to bind, return True,
or a contradicion is reached, then return False.
nbcp can be use with undo to implement a tight loop
for simple backtracking.

``` python
    def bt(vp):
        while not varpy.nbcp(vp):
          if varpy.undo(vp) == False:
            return False # contradiction
        return True # model
```


``` python
varpy.add_clause(vp, [x1,...,xn] [,clause_set])
```

Create a new clause, given as a literal list and return the
new clause index. All varables indices must already have been
created by calling add_variable. The clause create is installed
in one of four clause sets: 'delta', 'gamma', 'alpha', 'beta'.
The 'delta' clauseset is use to store the "problem" formula
clauses while 'gamma' is used for storing learnt clauses. 
However the conflict clause(s) created by varpy.conflict are created in 
'alpha' and may then, by user, moved into 'gamma'.


``` python
varpy.get_clause(vp, cix [, skip | varpy.undefined [, raw]] )
```

Retrieve a clause as list given the clause index __cix__.
If literal __x__ is given then literal __x__ is removed 
from the clause list returned. if __raw__ is __True__ then literals 
bound on level=0 are also return as normal, otherwise they are
removed. If __False__ or the clause is dead and empty list is
returned (fixme). 


``` python
varpy.find_clause(vp, [x1,...,xn])
```

Check if the clause [__x1__,...,__xn__] exist among the clausesets.
return clause index if found, return __False__ otherwise.

``` python
varpy.compress_clause(vp,  cix | [x1,...,xn])
```

Return a compressed version of the clause [__x1__,...,__xn__], 
or the clause given by the clause index cix.
It writes a utf8 like code with 0x80 bit for continuation bit and 
7-bits per byte for integer value. The LSB is coded as the literal sign.

-1000 is translated to unsigned by 

    2*1000 + 1 = 0xb11111010001
	
which is divided in groups of 7 bits starting from LSB

    (1)1010001,(0)0001111
	
while 1000 is translated to 

	2*1000 = 0xb11111010000

which is divided in groups of 7 bits starting from LSB

    (1)1010000,(0)0001111

Then sequence of coded literals are then terminated with a zero.


``` python
varpy.clause_info(vp, cix, item)
```

Get information about clause given by clause index cix

* 'length'
* 'jump'
* 'status'
* 'watch0'
* 'watch1'
* 'watch'


``` python
varpy.variable_info(vp, x, item)
```

Get information about variable x

* 'implication'
* 'implication\_clause'
* 'implication\_pos'
* 'level'
* 'phase'
* 'is\_atom'
* 'degree'
* 'symbol'
	
``` python
varpy.literal_info(vp, x, item)
```

Get information about literal x

* 'degree'
* 'user'
* 'edge'
* 'symbol'

``` python
varpy.del_clause(vp, cix | [x1,...,xn])
```

Delete clause __cix__ or [__x1__,...,__xn__] from clausesets.
__NOTE__: When deleting clauses by giving it as a list, 
then hashing may be enable (varpy.config(vp, 'hash', True) ) 
to gain reasonable speed.

``` python
varpy.clean_clause(vp, cix)
```

Cleanup clause by removing all false literals on level 0.
if clause is contradictory then exception is raised


``` python
varpy.clean_edges(vp, x)
```

Remove __x__ edges, that is clauses on form [-x,y] where y
is constant.


``` python
varpy.get_clauses(vp, cix, skip, raw)
```

Return a list of literals given by clause index __cix__.
Remove the literal __skip__ from the returned list.
Also remove literals on level 0 if __raw__ is __False__.


``` python
varpy.get_decision(vp, l)
```

Get literal on decision level __l__.

``` python
varpy.get_undo_state(vp, l)
```

__DEBUG__

Return the undo state on level __l__

* varpy.__set__
* varpy.__toggle__
* varpy.__done__
* varpy.__undef__

``` python
varpy.get_bindings(vp, l, clauseinfo, as_trail, as_tuple)
```

Return all bindings on level __l__. Return them in order of when
binding where made if __as_trail__ is __True__ otherwise the bidnings
are returned as latest binding first. if __as_tuple__ is __True__ then
bindings are returned as a tuple otherwise a list is returned.

if clauseinfo is __True__ then a list of
tuples (literal, pos, implication\_clause) are returned otherwise
a list of literals are returned. A negative literal means that the
variable is bound to __False__ a positive literal means that the
variable is bound to __True__.

``` python
varpy.get_nbindings(vp, count, clauseinfo)
```

Return a maximum of __count__ bindings with the latest binding first.

if clauseinfo is __True__ then a list of
tuples (literal, pos, implication\_clause) are returned otherwise
a list of literals are returned. A negative literal means that the
variable is bound to __False__ a positive literal means that the
variable is bound to __True__.

``` python
varpy.get_number_of_bindings(vp, l)
```

Return number of bindings on level __l__.

``` python
varpy.order_sort(vp, key1, key2, arg)
```

Order variables according to __key1__ and then __key2__, an optional
__arg__ may be supplied when needed by sorting.

The sort keys available are:
* 'identity'
 Sort according to when the variable number, this mostly corresponds 
to when the variable was created.
* 'random'
 Sort variables using a uniform distribution, an integer
seed may be given as __arg__.
* 'degree'
 Sort literals according to the number of time they occur in the clauses.
* 'rank'
 Sort literals according to the sum of ranks for all occurences in
all clauses. The rank for literal x is defined as the
sum of 1/|ci| for all clauses ci where x is a member.
* 'user'
 Sort literals according to a user value, that can be set by
using the varpy.__set\_user\_cunt__(vp, x, unsigned)

If the sort key is prefixed with a '+' then sorting is
ascending. If prefix is '-' then the sort is descending, wich
is also the default.

``` python
varpy.order_first(vp, [x1,..,xn])
```

Update current sort order so that literals __x1__..__xn__
are placed first.


``` python
varpy.order_last(vp, [x1,..,xn])
```

Update current sort order so that literals __x1__..__xn__
are placed last.

``` python
varpy.next_unbound(varp [, previous])
```

Return the next unbound literal in the current variable order.
If __previous__ is given then start looking for unbound literals
from that point.

``` python
varpy.queue_first(varp)
```

__DEBUG__ Return the first literal on the bcp queue.

``` python
varpy.queue_next(vp, x)
```

__DEBUG__ Return the next literal on the bcp queue, following literal __x__,
that must previously being returned from varpy.queue\_first of varpy.queue\_next.

``` python
varpy.queue_clear(varp)
```

Remove all literals enqueued on the bcp queue by calls to 
varpy.bind or varpy.decide.

``` python
varpy.add_symbol(vp, x|xs, string|term)
```

Associate a term or string to to a variable __x__ or variables __xs__,
for example the name of the variable. 
The term or string must not be assoicated with
other variables or an exception will occur.
If the variable part is a list __xs__ then the symbol refer to a
list of variables, integer encoding or bit vector.
Integer encoding should store least significant bit first (at index 0)

``` python
varpy.del_symbol(vp, string|term)
```

Remove the symbol from the symbol table.

``` python
varpy.find_symbol(vp, string|term)
```

Given a string or term return the variable assoicated.
If no assoication is found __False__ is returned.


``` python
varpy.use_clause(vp, cix)
```

Update the clause __cix__ timestamp to the current bcp\_counter,
the number of bcp's that has been run since __vp__ instance was created.

``` python
varpy.bump(vp, x, n)
```

"bump" a variable __x__ to move it in the dynamic variable order.
Either bump value __n__ is one of 
* 'next',  move variable to the top position, next variable to be assigned
* 'log2',  bump value is calculated to log2(__'number-of-variables'__)
* 'log10', bump value is calculated to log10(__'number-of-variables'__)
* 'rank',  bump value is set to the length of the implication clause.

Or the __n__ is a floating point ration between zero and one that will
give the the number of steps to move, 0.1 means move 10% in number of
variables.
Or the value is an integer that gives an absolute number of steps to move.

``` python
varpy.subscribe(vp, flag|[flag])
```

Flags

* 'variable'
* 'atom'
* 'number\_of\_variables'
* 'number\_of\_bound_variables'
* 'number\_of\_subst_variables'
* 'number\_of\_clauses'
* 'number\_of\_dead_clauses'
* 'max\_level'
* 'max\_bound'
* 'min\_level'

``` python
varpy.clauseset_size(vp, s)
```

Where __s__ is one of 'delta', 'gamma', 'alpha', 'beta'

``` python
varpy.clauseset_offset(vp, s)
```

Get offset where __s__ is one of 'delta', 'gamma', 'alpha', 'beta'

``` python
varpy.clauseset_offset(vp, s, offset)
```

Set offset where __s__ is one of 'delta', 'gamma', 'alpha', 'beta'

``` python
varpy.clauseset_sort(vp, s)
```

Sort clauses in the clause set __s__, where __s__ is one of 
'delta', 'gamma', 'alpha', 'beta'. The clauses are sorted
according to the internal use counter set by varpy.use\_clause.

``` python
varpy.clauseset_first(vp, s)
```

get clause index of first clause in clauseset __s__

``` python
varpy.clauseset_next(vp, s)
```

get clause index to the next clause in clauseset __s__

``` python
varpy.set_user_count(vp, x, count)
```

Set user value for literal __x__ to __count__.

``` python
varpy.conflict(vp, level, bump, i)
```

Do conflict analysis, called with level where the conflict i was found
and the __bump__ factor that is applied to variables involved in the conflict.
Return value is a clause index in clauseset 'alpha'. This
clause may then be minimized and later moved to 'gamma'.


``` python
varpy.minimize(vp, cix)
```

Minimize clause, may be called after varpy.conflict and requires
that literals and levels are set like after the conflict.


``` python
varpy.move_clause(vp, cix, set)
```

Move clause __cix__ to clauseset __set__.
__NOTE__ that this function is currently limited to clause in 'alpha'
and set must be 'gamma'

``` python
varpy.unmark(vp)
```

Clear all marks

``` python
varpy.mark(vp, l | [x1,...,xn] | (x1,...,xn), [clear])
```

Mark variables __x1__..__xn__ or all bindind on level __l__.
Optionally if __clear__ is __False__ then marks are concatinated to the 
previous marks, otherwise the marks are cleared before adding new ones.

``` python
varpy.intersect_marks(vp, l | [x1,...,xn] | (x1,...,xn))
```

Keep all marks that are present in bindings on level __l__ or
the literals __x1__...__xn__. Clear the other marks.


``` python
varpy.intersect_var(vp, x, l | [x1,...,xn]|(x1,...,xn), as_tuple)
```

Return all marks that are present in bindings on level __l__ or
the literals __x1__..__xn__. Return the marks in a list if
__as_tuple_ if __False__ or as a tuple if __as_tuple__ is __True__.

``` python
varpy.get_marked(vp, as_tuple)
```

Return the marks in a list if
__as_tuple_ if __False__ or as a tuple if __as_tuple__ is __True__.
