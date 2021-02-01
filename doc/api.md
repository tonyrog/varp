
# varp python API documentation 

## Instance functions

``` python
varpy.new(options)
```
Create a new varp instance from a dict of options

* {'size': size | 'default'}
  Initial variable table size  ( default 1024 )
* {'qtype': 'lifo'|'fifo'|'recursive'}  ( default = __recursive__ )
  Use lifo/fifo strategy in bcp
* {'xref': x}  ( default = __False__ )
  Use cross references if x is __True__
* {'vsids': x}  ( default = __True__ )
  Use variable decaying sum variable selection ifg x is __True__
* {'init\_phase': x}  ( default = __True__ )
  The initial phase to start with, x is boolean. Set to __None__ if
  random value is requested.
* {'use\_phase': x}  ( default = __False__ )
  Use saved phase in decide iff x is __True__
* {'all\_used': x}  ( default = __False__ )
  All variables are "used" if 'all\_used' is __True__,
  that is all variables created are backtracked
  and turn up in calls to next_unbound. If all_\used is __False__ then
  varpy.isused and literal degree controls when variabels are used.
* {'hash': x} ( default = __False__ )
  use hash table for clauses iff x is __True__
* {'seed': x}  ( default = 0 )
  random seed used (64-bit unsigned number). Use seed = 0 when a, 
  kind of non deterministc, number is wanted as seed.

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
* 'level'
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
* 'seed'

``` python
varpy.config(vp, item, value)
```

Set configurable items in varp

* 'max\_conflicting'
 set max number of conflicts during bcp (<= MAX_CONFLICTING=1024)
*  'xref'
 turn on (__True__) or off (__False__) cross reference handling
* 'vsids'
 enable (__True__) or disable (__False__) the use of VSIDS,
 variable decaying sum variable selection.
* 'hash'
 turn on (__True__) or off (__False__) hash table handling		
* 'qtype'
 set style of literal queueing in bcp
 where value is one of 
 'lifo' | 'fifo' | 'recursive'
* 'seed'
  random seed used (64-bit unsigned number). Use seed = 0 when a, 
  kind of non deterministc, number is wanted as seed.

``` python
varpy.add_variable(vp)
varpy.add_variable(vp, is_atom)
varpy.add_variable(vp, is_atom, is_used)
```

Create a new variable. The variable is return as an index to the
next available variable in the variable table. Mark the new variable
as atom if is_atom is __True__. The atom status may later be queried with
variable info. is\_atom defaults to __True__.

exception: system_limit (too many variables)


``` python
varpy.add_variables(vp, num)
varpy.add_variables(vp, num, is_atom)
varpy.add_variables(vp, num, is_atom, is_used)
```

Create __num__ new variables. The variables are return as a tuple
(__firstindex__, __lastindex__). If is_atom is __True__ then the variables
are marked as atom.

exception: system_limit (too many variables)

``` python
varpy.level(vp)
```

Return current binding level.

``` python
varpy.value(vp, x)
```

Return __True__ | __False__ | __None__,
Value, None is return if variables undefined.

exception: literal (x is not a literal)

``` python
varpy.bound(vp, x)
```

Return __True__ | __False__ | __None__ | literal

None is return if variable x is unbound,
if x is bound to literal y then y is returned.

exception: literal (x is not a literal)

``` python
varpy.bind(vp, x)
```

Bind variable x to True.

``` python
varpy.decide(vp, x)
```

Use the decision parameters to decide and bind variable x 
also mark x as a decision variable.
The value used for x is initially the value of 'init\_phase' as
setup in varpy.new. If 'use\_phase' is true the last propagated
value is used as next initial decision value.


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

exception: literal (if x or y are not literals)
exception: level (when level != 0)
exception: xref  (when xref is not turned on)

``` python
varpy.implication_clause(vp, x)
```

Return the clause index for the clause where literal __x__ became a unit.

exception: variable (x is not a variable)

``` python
varpy.implication_level(vp, x)
```

Return the bind level for variable __x__, where it was assigned during bcp.

exception: variable (x is not a variable)

``` python
varpy.conflicting_clause(vp, i)
```

Return the i'th conflicting clause found during the last bcp. The number
of conflicting clauses that can be returned is 'num_conflicting'.

``` python
varpy.is_variable(vp, x)
```

Return __True__ if literal __x__ is unbound. Return __False__ otherwise

exception: variable (x is not a variable)

``` python
varpy.is_bound(vp, x)
```

Return __True__ if literal __x__ is bound, through substition, 
to an other variable. Return __False__ otherwise.

exception: variable (x is not a variable)

``` python
varpy.is_equal(vp, x, y)
```

Check if literal __x__ and literal __y__ are the equal, that is bound to the
same variable or are bound to the same constant.

exception: literal (x or y are not literals)

``` python
varpy.isused(vp, x)
varpy.isused(vp, x, value)
```

Check if literal __x__ is used in any clause or is forced to be
in use by a previous setting of value. This makes "free" variables
be included in fist and next\_unbound calls.

exception: variable (x is not a variable)

``` python
varpy.isatom(vp, x)
varpy.isatom(vp, x value)
```

Check if literal __x__ is an __atom__, that is
marked as atomic formula when adding new variables
or set using is\_atom(vp, x, True)

exception: variable (x is not a variable)

``` python
varpy.push(vp)
```

Push binding level stack and move on to the next,
return the level number before the push.

``` python
varpy.pop(vp)
```

Undo all bindings on current level and move to the
previous level. Return the level number after pop.


``` python
varpy.pop(vp, l)
```

Undo and pop all bindings until level l, but NOT including level l.

``` python
varpy.undo(vp)
```

Undo bindings typically after an nbind. Undo will undo all bindings
until a decision and flip the variable if not already flipped.

``` python
varpy.bcp(vp)

varpy.bcp(vp [x1,..,xn])
varpy.bcp(vp [x1,..,xn], all)
```

Run value propagation. Return __True__ if no
contradiction is found, __False__ otherwise.

__[EXPERIMENTAL]__

If literals __x1__..__xn__ are given they are checked for
"turbo" rule, that is, if all clauses that xi
is a part of are true regardless of the value of xi.
If 'all' is __True__ then all xi's must be true for the
rule to hold. If turbo rule is successful then 
'turbo' is returned.

__[EXPERIMENTAL]__



``` python
varpy.nbcp(vp)
```

Repeatedly decide/bind next unbound variable, on a new level and
run bcp until there are no more variables to bind or a contradiction 
is found. If a contraduction is readed them return __False__
otherwise there is a model, and __True__ is returned.
__nbcp__ can be use together with undo to implement
simple backtracking using a tight loop:


``` python
    def bt(vp):
        while not varpy.nbcp(vp):
          if varpy.undo(vp) == False:
            return False # contradiction
        return True # model
```

``` python
varpy.vbcp(vp, [x1,...,xn])
varpy.vbcp(vp, [x1,...,xn], single_level)
```

Vector bcp.

If __single_level__ is __false__ (default) then each
literal xi in x1...xn xi is used as decision followed
by a bcp. if bcp generates a conflict then __false__ is returned,
If xj in xi+1...xn is inconsistent then (j,xj) is returned.
else if xi is not last then the level is pushed and xi+1 is
processed.

If __single_level__ is __true__ then all literals xi in x1...xn,
are assigned, followed by a bcp. if assignment of xi is inconsistent 
then (i, xi) is returned, otherwise the return value of bcp is returned.


``` python
varpy.add_clause(vp, [x1,...,xn])
varpy.add_clause(vp, (x1,...,xn))
varpy.add_clause(vp, [x1,...,xn], clause_set)
varpy.add_clause(vp, (x1,...,xn), clause_set)
```

Create a new clause, given as a literal list and return the
new clause index. All varables indices must already have been
created by calling add_variable. The clause create is installed
in one of four clause sets: 'delta', 'gamma', 'alpha', 'beta'
given by __clause\_set__
The 'delta' clauseset is use to store the "problem" formula
clauses while 'gamma' is used for storing learnt clauses. 
However the conflict clause(s) created by varpy.conflict are created in 
'alpha' and may then, by user, moved into 'gamma'.


``` python
varpy.find_clause(vp, [x1,...,xn])
varpy.find_clause(vp, (x1,...,xn))
```

Check if the clause [__x1__,...,__xn__] exist among the clausesets.
return clause index if found, return __False__ otherwise.

``` python
varpy.compress_clause(vp,  cix)
varpy.compress_clause(vp,  [x1,...,xn])
```

Return a compressed version of the clause [__x1__,...,__xn__], 
or the clause given by the clause index cix.
It writes a utf8 like code with 0x80 bit for continuation bit and 
7-bits per byte for integer value. The LSB is coded as the literal sign.
Note that when argument is given as an integer list the elements
do not need to created as variables/literals.

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
* 'level'
* 'phase'
* 'is\_atom'
* 'is\_used'
* 'degree'
* 'symbol'

exception: variable (x is not a variable)

``` python
varpy.literal_info(vp, x, item)
```

Get information about literal x

* 'degree'
* 'mark'
* 'xref'
* 'symbol'

``` python
varpy.del_clause(vp, cix)
varpy.del_clause(vp, [x1,...,xn])
varpy.del_clause(vp, (x1,...,xn))
```

Delete clause __cix__ or [__x1__,...,__xn__] from clausesets.
__NOTE__: When deleting clauses by giving it as a list, 
then hashing may be enable (varpy.config(vp, 'hash', True) ) 
to gain reasonable speed.

exception: level (level != 0)

``` python
varpy.clean_clause(vp, cix)
```

Cleanup clause by removing all false literals on level 0.
if clause is contradictory then exception is raised

exception: level (level != 0)

``` python
varpy.clean_edges(vp, x)
```

Remove __x__ edges, that is clauses on form [-x,y] where y
is constant.

exception: literal (x is not a literal)

``` python
varpy.get_clause(vp, cix)
varpy.get_clause(vp, cix, skip)
varpy.get_clause(vp, cix, skip, raw)
varpy.get_clause(vp, cix, skip, raw, as_tuple)
```

Return a list of literals given by clause index __cix__.
Remove the literal __skip__ from the returned list.
Also remove literals on level 0 if __raw__ is __False__.


``` python
varpy.get_decision(vp, l)
```

Get decision literal on level __l__.

``` python
varpy.get_undo_state(vp, l)
```

__DEBUG__

Return the undo state on level __l__

* 'set'
* 'toggle'
* 'done'
* 'undef'

``` python
varpy.get_bindings(vp)
varpy.get_bindings(vp, l)
varpy.get_bindings(vp, l, as_trail)
varpy.get_bindings(vp, l, as_trail, as_tuple)
```

Return all bindings on level __l__. Return them in order of when
binding where made if __as_trail__ is __True__ otherwise the bidnings
are returned as latest binding first (default). 
if __as_tuple__ is __True__ (default) then bindings are returned 
as a tuple otherwise a list is returned.

A list of literals are returned. A negative literal means that the
variable is bound to __False__ a positive literal means that the
variable is bound to __True__.

``` python
varpy.get_nbindings(vp, count)
varpy.get_nbindings(vp, count, as_trail)
varpy.get_nbindings(vp, count, as_trail, as_tuple)
```

Return a maximum of __count__ bindings.
Return them in order of when binding where made, if __as_trail__ 
is __True__, otherwise the bidnings are returned as latest binding first.
if __as_tuple__ is __True__ (default) then bindings are returned as a tuple 
otherwise a list is returned.

A list of literals are returned. A negative literal means that the
variable is bound to __False__ a positive literal means that the
variable is bound to __True__.

``` python
varpy.get_number_of_bindings(vp, l)
```

Return number of bindings on binding level __l__.

``` python
varpy.order_sort(vp, key)
varpy.order_sort(vp, key, arg)
varpy.order_sort(vp, key1, key2)
varpy.order_sort(vp, key1, key2, arg)
```

Order variables according to __key1__ and then __key2__, an optional 
unsigned integer __arg__ may be supplied when needed by sorting.
In the case of 'random' sort the __arg__ is the random seed 
(use __arg__ = 0 to set an arbitrary seed )

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

If the sort key is prefixed with a '+' then sorting is
ascending. If prefix is '-' then the sort is descending, wich
is also the default.

exception: level (when level != 0)

``` python
varpy.order_first(vp, [x1,..,xn])
```

Update current sort order so that literals __x1__..__xn__
are placed first.

exception: level (when level != 0)

``` python
varpy.order_last(vp, [x1,..,xn])
```

Update current sort order so that literals __x1__..__xn__
are placed last.

exception: level (when level != 0)

``` python
varpy.next_unbound(varp)
varpy.next_unbound(varp, previous)
```

Return the next unbound literal in the current variable order.
If __previous__ is given then start looking for unbound literals
from that point.

exception: variable (previous is not a variable)

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
varpy.add_symbol(vp, x, string)
varpy.add_symbol(vp, x, term)
varpy.add_symbol(vp, xs, string)
varpy.add_symbol(vp, xs, term)
```

Associate a term or string to to a variable __x__ or variables __xs__,
for example the name of the variable. 
The term or string must not be assoicated with
other variables or an exception will occur.
If the variable part is a list __xs__ then the symbol refer to a
list of variables, integer encoding or bit vector.
Integer encoding should store least significant bit first (at index 0)

``` python
varpy.del_symbol(vp, string)
varpy.del_symbol(vp, term)
```

Remove the symbol from the symbol table.

``` python
varpy.find_symbol(vp, symbol)
```

Given a symbol return the variable assoicated with it.
If no assoication is found __False__ is returned.

``` python
varpy.first_symbol(vp)
```

Find first symbol in the symbol table. Return __False__ if 
not found. Try not use __False__ as a symbol.


``` python
varpy.next_symbol(vp, symbol)
```

Given a symbol in the symbol table (must be present),
find next symbol in the symbol table. Return __False__ if 
not found. Try not use __False__ as a symbol.
If symbol table is updated while calling next\_symbol then
the behaviour is undefined.

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

if __n__ is a floating point value between 0 and 1 then the
bump value will be computed to the relative to the number of variables.
For example a value of, 0.1 means move 10% in number of variables.
If __n__ is an integer then x is moved that exact number of steps.

``` python
varpy.subscribe(vp, flag)
varpy.subscribe(vp, [flag])
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
varpy.conflict(vp, bump, cix)
varpy.conflict(vp, bump, cix, xi)
varpy.conflict(vp, bump, [x1..xn])
varpy.conflict(vp, bump, [x1..xn], xi)
```

Do conflict analysis on the conflict clause cix or
explict clause [x1,...,xn], the unit literal xi must
be supplied or __false__ (default)

The __bump__ factor is applied to variables involved in the conflict.
Returned value is a clause index in clauseset 'alpha'. This
clause may then be minimized and later moved to 'gamma'.
if __None__ is returned then the conflict clause was a copy of an
existing clause.


``` python
varpy.minimize(vp, cix)
varpy.minimize(vp, cix, 'local'|'global'|'recursive')
```

Minimize clause, may be called after varpy.conflict and requires
that literals and levels are set like after the conflict.
Return updated length of clause if successful, or __None__
if clause, after minimization, already exists.


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
