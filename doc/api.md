
# varp python API documentation 

## Instance functions

``` python
varpy.new(options)
```
Create a new varp instance from a dict of options

* {varpy.__size__: size}
  Initial variable table size 
* {varpy.__qtype__: varpy.lifo|varpy.fifo|varpy.recursive}
  use lifo/fifo strategy in bcp
* {varpy.__xref__: x}
  use cross references if x is True
* {varpy.__hash__: x}
  use hash table for clauses if x is True
* {varpy.__edge__: x}
  use edge tables for 2-clauses if x is True

``` python
varpy.clone(vp, options)
```

Clone the varp instance using setting options from new with the
follow additions.

* {varpy.__level__: l}
  clone bindings up until level l
* {varpy.__set__ :  varpy.__delta__+varpy.__gamma__+varpy.__beta__+varpy.__alpha__}
  clone clauseset DELTA, GAMMA, BETA, ALPHA
* {varpy.__queue__, x}
  clone bcp queue if x is True

``` python
varpy.info(vp,  item)
```

Get varp information 

* varpy.__bcp\_counter__
* varpy.__conflict\_counter__
* varpy.__max\_conflicting__
* varpy.__num\_conflicting__
* varpy.__number\_of\_variables__
* varpy.__number\_of\_clauses__
* varpy.__number\_of\_edges__
* varpy.__number\_of\_dead_clauses__
* varpy.__number\_of\_dead_edges__
* varpy.__number\_of\_learnt_clauses__
* varpy.__number\_of\_bound_variables__
* varpy.__number\_of\_subst_variables__
* varpy.__number\_of\_unbound_variables__
* varpy.__clause\_n\_counter__
* varpy.__clause\_2\_counter__
* varpy.__clause\_3\_counter__
* varpy.__clause\_d\_counter__
* varpy.__edge\_2\_counter__
* varpy.__edge\_d\_counter__
* varpy.__size__
* varpy.__qtype__
* varpy.__max\_level__
* varpy.__min\_level__
* varpy.__max\_bound__
* varpy.__literal\_size__
* varpy.__literal\_integer__
* varpy.__value\_packing__
* varpy.__edge__
* varpy.__xref__
* varpy.__hash__
* varpy.__phase__
* varpy.__use\_phase__


``` python
varpy.config(vp, item, value)
```

Set configurable items in varp

*    varpy.__max\_conflicting__
 set max number of conflicts during bcp (<= MAX_CONFLICTING=1024)
*    varpy.__xref__
 turn on (True) or off (False) cross reference handling
*    varpy.__hash__
 turn on (True) or off (False) hash table handling		
*    varpy.__qtype__
 set style of literal queueing in bcp
 where value is one of 
 varpy.__lifo__ | varpy.__fifo__ | varpy.__recursive__
	

``` python
varpy.add_variable(vp [,is_atom])
```

Create a new variable. The variables is return as an index to the
next available variable in the variable table. Mark the new variable
as atom if is_atom is True. The atom status may later be queried with
variable info. is\_atom defaults to True.

``` python
varpy.value(vp, x)
```

Return variable value as varp constant 
varpy.__t__ | varpy.__f__ | varpy.__undefined__


``` python
varpy.bind(vp, x, [,level])
```

Bind variable x to True. If level is given then that level 
is used to the variable is bound on that level else the
variable is bound on the current level as set with varpy.set\_level.

``` python
varpy.decide(vp, x [,level])
```

Bind variable x to True and mark x as a decision variable.
If level is given then that level 
is used to the variable is bound on that level else the
variable is bound on the current level as set with varpy.set\_level.

``` python
varpy.subst(vp, x, y)
```

``` python
varpy.implication_clause(vp, x)
```

Return the clause index for the clause where x became a unit.

``` python
varpy.implication_level(vp, x)
```

Return the bind level for x, where it decided/bound or unit.

``` python
varpy.implication_pos(vp, x)
```

Return the position where x is found in the implication clause.

``` python
varpy.conflicting_clause(vp, i)
```

Return the i'th conflicting clause during the last bcp. The number
of conflicting clauses that can be returned is __num_conflicting__.

``` python
varpy.is_variable(vp, x)
```

Return True if literal x is unbound. Return False otherwise

``` python
varpy.is_bound(vp, x)
```

Return True if literal x is bound, through substition, to an other variable.
Return False otherwise.

``` python
varpy.is_equal(vp, x, y)
```

Check if literal x and literal y are the equal, that is bound to the
same variable or are bound to the same constant.


``` python
varpy.set_level(vp, level)
```

Set current level to 'level'. Note that level 0 is treated
as constant level. So be careful when setting level to 0.


``` python
varpy.keep_level(vp, l)
```

Keep all bindings on level l by removing the undo information.

``` python
varpy.move_level(vp, src, dst)
```

Move bindings from level 'src' to level 'dst'. Normally
src level will be hight that dst level but it possible to
move (with warning) to a high level as wll.


``` python
varpy.undo_level(vp, level)
```

Undo all bindings on level 'level'

``` python
varpy.undo(vp)
```

Undo bindings typically after an nbind. Undo will undo all bindings
until a decision and flip the variable if not already flipped.


``` python
varpy.bcp(vp [,[x1,..,xn] [,all]])
```

Run value propagation. Return True if no
contradiction is found, False otherwise.

__[EXPERIMENTAL]__

If literals x1..xn are given they are checked for
"turbo" rule, that is if all clauses that xi
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
in one of four clause sets: varpy.__delta__, varpy.__gamma__, 
varpy.__alpha__, varpy.__beta__.
The varpy.__delta__ clause-set is use to store the "problem" formula
clauses while varpy.__gamma__ is used for storing learnt clauses. 
However the conflict clauses created by varpy.conflict are create in 
varpy.__alpha__ and then, by user, moved into varpy.gamma.


``` python
varpy.get_clause(vp, cix [, skip | varpy.undefined [, raw]] )
```

Retrive a clause as list given the clause index 'cix'.
If literal x is given then literal x is removed from the
clause list returned. if raw is True then literals bound
on level=0 are also return as normal, otherwise they are
remove if False or the clause is dead and empty list is
returned (fixme). 


``` python
varpy.find_clause(vp, [x1,...,xn])
```

Check if the clause [x1,...,xn] exist among the clause sets.
return Clause index if found, return False otherwise.

``` python
varpy.compress_clause(vp,  cix | [x1,...,xn])
```

Return a compressed version of the clause [x1,...,xn], 
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

* varpy.__length__
* varpy.__jump__
* varpy.__status__
* varpy.__watch0__
* varpy.__watch1__
* varpy.__watch__


``` python
varpy.variable_info(vp, x, item)
```

Get information about variable x

* varpy.__implication__
* varpy.__implication\_clause__
* varpy.__implication\_pos__
* varpy.__level__
* varpy.__phase__
* varpy.__is\_atom__
* varpy.__degree__
* varpy.__symbol__
	
``` python
varpy.literal_info(vp, x, item)
```

Get information about literal x

* varpy.__degree__
* varpy.__user__
* varpy.__edge__
* varpy.__symbol__

``` python
varpy.del_clause(vp, cix | [x1,...,xn])
```

Delete clause cix or [x1,...,xn] from clause sets.

``` python
varpy.clean_clause(vp, cix)
```

Cleanup clause by removing all false literals on level 0.
if clause is contradictory then exception is raised, else
varpy.__ok__ is returned.


``` python
varpy.clean_edges(vp, x)
```

Remove x edges, that is clauses on form [-x,y] where y
is constant.


``` python
varpy.get_clauses(vp, cix, skip, raw)
```

Return a list of literals given by clause index cix.
Remove the literal skip from the returned list also
remove literals on level 0 if raw is False.


``` python
varpy.get_decision(vp, level)
```

Get literal on decision level.

``` python
varpy.get_undo_state(vp, level)
```

Return undo state

* varpy.__set__
* varpy.__toggle__
* varpy.__done__
* varpy.__undef__

``` python
varpy.get_bindings(vp, level, clauseinfo, tail, tuple)
```

``` python
varpy.get_nbindings(vp, count clauseinfo, trail)
```

``` python
varpy.get_number_of_bindings(vp, level)
```

``` python
varpy.order_sort(vp, key1, key2, arg)
```

``` python
varpy.order_first(vp, [x1,...,xn])
```

``` python
varpy.order_last(vp, [x1,...,xn])
```

``` python
varpy.next_unbound(varp [, last])
```


``` python
varpy.queue_first(varp)
```

``` python
varpy.queue_next(vp, x)
```

``` python
varpy.queue_clear(varp)
```

``` python
varpy.add_symbol(vp, x, string|term)
```

``` python
varpy.find_symbol(vp, string|term)
```

``` python
varpy.use_clause(vp, cix)
```

``` python
varpy.bump(vp, x, n)
```

``` python
varpy.subscribe(vp, flags)
```

Flags

* varpy.__variable__
* varpy.__atom__
* varpy.__number\_of\_variables__
* varpy.__number\_of\_bound_variables__
* varpy.__number\_of\_subst_variables__
* varpy.__number\_of\_clauses__
* varpy.__number\_of\_dead_clauses__
* varpy.__max\_level__
* varpy.__max\_bound__
* varpy.__min\_level__


``` python
varpy.clauseset_size(vp, set)
```

where set is one of varpy.__delta__, varpy.__gamma__, 
varpy.__alpha__, varpy.__beta__


``` python
varpy.clauseset_offset(vp, set)
```

get offset where set is one of varpy.__delta__, varpy.__gamma__, 
varpy.__alpha__, varpy.__beta__

``` python
varpy.clauseset_offset(vp, set, offset)
```

set offset where set is one of varpy.__delta__, varpy.__gamma__, 
varpy.__alpha__, varpy.__beta__

``` python
varpy.clauseset_sort(vp, set)
```

get offset where set is one of varpy.__delta__, varpy.__gamma__, 
varpy.__alpha__, varpy.__beta__

``` python
varpy.clauseset_first(vp, set)
```

``` python
varpy.clauseset_next(vp, set)
```

``` python
varpy.set_user_count(vp, x, count)
```

Set user value for literal x to count.


``` python
varpy.conflict(vp, level, bump, i)
```

Do conflict analysis, called with level where the conflict i was found
and the bump factor that is applied to variables involved in the conflict.
Return value is a clause index in clause-set varpy.__alpha__. This
clause may then be minimized and later moved to varpy.__gamma__.


``` python
varpy.minimize(vp, cix)
```

Minimize clause, may be called after varpy.conflict and requires
that literals and levels are set like after the conflict.


``` python
varpy.move_clause(vp, cix, set)
```

Move clause cix to clause-set 'set'.
This function is currently limited to clause in varpy.__alpha__
and set must be varpy.__gamma__


``` python
varpy.mark_literals(vp, [x1,...,xn] | (x1,...,xn))
```

Mark variables x1..Xn with MARK0

``` python
varpy.mark_intersect(vp, [x1,...,xn] | (x1,...,xn))
```

Add MARK1 to all variables x1..xn marked with MARK0.
Then variables marked with both MARK0 and MARK1 are
kept while variables kept with only MARK0 are removed


``` python
varpy.mark_intersect_var(vp, x, [x1,...,xn]|(x1,...,xn), tuple)
```


``` python
varpy.get_marked(vp, tuple)
```
