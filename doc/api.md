
# varp python API documentation 

## Instance functions

``` python
varp.new(options)
```
Create a new varp instance from a list of options

* (varp.__size__, size)
  Initial variable table size 
* (varp.__qtype__, varp.lifo|varp.fifo|varp.recursive) 
  use lifo/fifo strategy in bcp
* (varp.__xref__, x)
  use cross references if x is True
* (varp.__hash__, x)
  use hash table for clauses if x is True
* (varp.__edge__, x)
  use edge tables for 2-clauses if x is True

``` python
varp.clone(vp, options)
```

Clone the varp instance using setting options from new with the
follow additions.

*    (varp.__level__, l)
  clone bindings up until level 'l'
*    (varp.__set__, varp.__delta__)
  clone clauseset DELTA
*    (varp.__set__, varp.__gamma__)
  clone clauseset GAMMA
*    (varp.__set__, varp.__beta__)
  clone clauseset BETA
*   (varp.__set__, varp.__alpha__)
  clone clauseset ALPHA
*   (varp.__queue__, x)
  clone bcp queue if x is True

``` python
varp.info(vp,  item)
```

Get varp information 

* varp.__bcp\_counter__
* varp.__conflict\_counter__
* varp.__max\_conflicting__
* varp.__num\_conflicting__
* varp.__number\_of\_variables__
* varp.__number\_of\_clauses__
* varp.__number\_of\_edges__
* varp.__number\_of\_dead_clauses__
* varp.__number\_of\_dead_edges__
* varp.__number\_of\_learnt_clauses__
* varp.__number\_of\_bound_variables__
* varp.__number\_of\_subst_variables__
* varp.__number\_of\_unbound_variables__
* varp.__clause\_n\_counter__
* varp.__clause\_2\_counter__
* varp.__clause\_3\_counter__
* varp.__clause\_d\_counter__
* varp.__edge\_2\_counter__
* varp.__edge\_d\_counter__
* varp.__size__
* varp.__qtype__
* varp.__max\_level__
* varp.__min\_level__
* varp.__max\_bound__
* varp.__literal\_size__
* varp.__literal\_integer__
* varp.__value\_packing__
* varp.__edge__
* varp.__xref__
* varp.__hash__
* varp.__phase__
* varp.__use\_phase__


``` python
varp.config(vp, item, value)
```

Set configurable items in varp

*    varp.__max\_conflicting__
 set max number of conflicts during bcp (<= MAX_CONFLICTING=1024)
		
*    varp.__xref__
 turn on (True) or off (False) cross reference handling
*    varp.__hash__
 turn on (True) or off (False) hash table handling		
*    varp.__qtype__
 set style of literal queueing in bcp
 where value is one of 
 varp.__lifo__ | varp.__fifo__ | varp.__recursive__
	

``` python
varp.add_variable(vp [,is_atom])
```

Create a new variable. The variables is return as an index to the
next available variable in the variable table. Mark the new variable
as atom if is_atom is True. The atom status may later be queried with
variable info. is\_atom defaults to True.

``` python
varp.value(vp, x)
```

Return variable value as varp constant 
varp.__t__ | varp.__f__ | varp.__undefined__


``` python
varp.bind(vp, x, [,leve])
```

Bind variable x to True. If level is given then that level 
is used to the variable is bound on that level else the
variable is bound on the current level as set with varp.set\_level.

``` python
varp.decide(vp, x [,level])
```

Bind variable x to True and mark x as a decision variable.
If level is given then that level 
is used to the variable is bound on that level else the
variable is bound on the current level as set with varp.set\_level.

``` python
varp.subst(vp, x, y)
```

``` python
varp.implication_clause(vp, x)
```

Return the clause index for the clause where x became a unit.

``` python
varp.implication_level(vp, x)
```

Return the bind level for x, where it decided/bound or unit.

``` python
varp.implication_pos(vp, x)
```

Return the position where x is found in the implication clause.

``` python
varp.conflicting_clause(vp, i)
```

Return the i'th conflicting clause during the last bcp. The number
of conflicting clauses that can be returned is __num_conflicting__.

``` python
varp.is_variable(vp, x)
```

Return True if literal x is unbound. Return False otherwise

``` python
varp.is_bound(vp, x)
```

Return True if literal x is bound, through substition, to an other variable.
Return False otherwise.

``` python
varp.is_equal(vp, x, y)
```

Check if literal x and literal y are the equal, that is bound to the
same variable or are bound to the same constant.


``` python
varp.set_level(vp, level)
```

Set current level to 'level'. Note that level 0 is treated
as constant level. So be careful when setting level to 0.


``` python
varp.keep_level(vp, l)
```

Keep all bindings on level l by removing the undo information.

``` python
varp.move_level(vp, src, dst)
```

Move bindings from level 'src' to level 'dst'. Normally
src level will be hight that dst level but it possible to
move (with warning) to a high level as wll.


``` python
varp.undo_level(vp, l)
```

Undo all bindings on level 'l'

``` python
varp.undo(varp)
```

Undo bindings typically after an nbind. Undo will undo all bindings
until a decision and flip the variable if not already flipped.


``` python
varp.bcp(varp [,[x1,..,xn] [,all]])
```

Run value propagation. Return True if no
contradiction is found, False otherwise.

__[EXPERIMENTAL]__

If literals x1..Xn are given they are checked for
"turbo" rule, that is if all clauses that xi
is a part of are true regardless of the value of xi.
If 'all' is true then all xi's must be true for the
rule to hold. If turbo rule is successful then 
varp.__turbo__ is returned.

__[EXPERIMENTAL]__


``` python
varp.nbcp(varp)
```

decide and bind next unbound variables until either
no more variables to bind, return True,
or a contradicion is reached, then return False.
nbcp can be use with undo to implement a tight loop
for simple backtracking.

``` python
    def bt(v):
        while !varp.nbcp(v):
          if varp.undo(v) == False:
            return False; # contradiction
        return True; # model
```


``` python
varp.add_clause(vp, [x1,...,xn] [,clause_set])
```

Create a new clause, given as a literal list and return the
new clause index. All varables indices must already have been
created by calling add_variable. The clause create is installed
in one of four clause sets: varp.__delta__, varp.__gamma__, 
varp.__alpha__, varp.__beta__.
The varp.__delta__ clause-set is use to store the "problem" formula
clauses while varp.__gamma__ is used for storing learnt clauses. 
However the conflict clauses created by varp.conflict are create in 
varp.__alpha__ and then, by user, moved into varp.gamma.


``` python
varp.get_clause(vp, cix, x | varp.undefined, raw)
```

Retrive a clause as list given the clause index 'cix'.
If literal x is given then literal x is removed from the
clause list returned. if raw is True then literals bound
on level=0 are also return as normal, otherwise they are
remove if False or the clause is dead and empty list is
returned (fixme). 


``` python
varp.find_clause(vp, [x1,...,xn])
```

Check if the clause [x1,...,xn] exist among the clause sets.
return Clause index if found, return False otherwise.

``` python
varp.compress_clause(vp,  cix | [x1,...,xn])
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
varp.clause_info(vp, cix, item)
```

Get information about clause given by clause index cix

* varp.__length__
* varp.__jump__
* varp.__status__
* varp.__watch0__
* varp.__watch1__
* varp.__watch__


``` python
varp.variable_info(vp, x, item)
```

Get information about variable x

* varp.__implication__
* varp.__implication\_clause__
* varp.__implication\_pos__
* varp.__level__
* varp.__phase__
* varp.__is\_atom__
* varp.__degree__
* varp.__symbol__
	
``` python
varp.literal_info(vp, x, item)
```

Get information about literal x

* varp.__degree__
* varp.__user__
* varp.__edge__
* varp.__symbol__

``` python
varp.del_clause(vp, cix | [x1,...,xn])
```

Delete clause cix or [x1,...,xn] from clause sets.

``` python
varp.clean_clause(vp, cix)
```

Cleanup clause by removing all false literals on level 0.
if clause is contradictory then exception is raised, else
varp.__ok__ is returned.


``` python
varp.clean_edges(vp, x)
```

Remove x edges, that is clauses on form [-x,y] where y
is constant.


``` python
varp.get_clauses(vp, cix, skip, raw)
```

Return a list of literals given by clause index cix.
Remove the literal skip from the returned list also
remove literals on level 0 if raw is False.


``` python
varp.get_decision(vp, level)
```

Get literal on decision level.

``` python
varp.get_undo_state(vp, level)
```

Return undo state

* varp.__set__
* varp.__toggle__
* varp.__done__
* varp.__undef__

``` python
varp.get_bindings(vp, level, clauseinfo, tail, tuple)
```

``` python
varp.get_nbindings(vp, count clauseinfo, trail)
```

``` python
varp.get_number_of_bindings(vp, level)
```

``` python
varp.order_sort(vp, key1, key2, arg)
```

``` python
varp.order_first(vp, [x1,...,xn])
```

``` python
varp.order_last(vp, [x1,...,xn])
```

``` python
varp.next_unbound(varp [, last])
```


``` python
varp.queue_first(varp)
```

``` python
varp.queue_next(vp, x)
```

``` python
varp.queue_clear(varp)
```

``` python
varp.add_symbol(vp, x, string|term)
```

``` python
varp.find_symbol(vp, string|term)
```

``` python
varp.use_clause(vp, cix)
```

``` python
varp.bump(vp, x, n)
```

``` python
varp.subscribe(vp, flags)
```

Flags

* varp.__variable__
* varp.__atom__
* varp.__number\_of\_variables__
* varp.__number\_of\_bound_variables__
* varp.__number\_of\_subst_variables__
* varp.__number\_of\_clauses__
* varp.__number\_of\_dead_clauses__
* varp.__max\_level__
* varp.__max\_bound__
* varp.__min\_level__


``` python
varp.clauseset_size(vp, set)
```

where set is one of varp.__delta__, varp.__gamma__, 
varp.__alpha__, varp.__beta__


``` python
varp.clauseset_offset(vp, set)
```

get offset where set is one of varp.__delta__, varp.__gamma__, 
varp.__alpha__, varp.__beta__

``` python
varp.clauseset_offset(vp, set, offset)
```

set offset where set is one of varp.__delta__, varp.__gamma__, 
varp.__alpha__, varp.__beta__

``` python
varp.clauseset_sort(vp, set)
```

get offset where set is one of varp.__delta__, varp.__gamma__, 
varp.__alpha__, varp.__beta__

``` python
varp.clauseset_first(vp, set)
```

``` python
varp.clauseset_next(vp, set)
```

``` python
varp.set_user_count(vp, x, count)
```

Set user value for literal x to count.


``` python
varp.conflict(vp, level, bump, i)
```

Do conflict analysis, called with level where the conflict numner i was found
and the bump factor that is applied to variables involved in the conflict.
Return value is a clause index in clause-set varp.__alpha__. This
clause may then be minimized and later moved to varp.__gamma__.


``` python
varp.minimize(vp, cix)
```

Minimize clause, may be called after varp.conflict and requires
that literals and levels are set like after the conflict.


``` python
varp.move_clause(vp, cix, set)
```

Move clause cix to clause-set 'set'.
This function is currently limited to clause in varp.__alpha__
and set must be varp.__GAMMA__


``` python
varp.mark_literals(vp, [x1,...,xn] | (x1,...,xn))
```

Mark variables x1..Xn with MARK0

``` python
varp.mark_intersect(vp, [x1,...,xn] | (x1,...,xn))
```

Add MARK1 to all variables x1..xn marked with MARK0.
Then variables marked with both MARK0 and MARK1 are
kept while variables kept with only MARK0 are removed


``` python
varp.mark_intersect_var(vp, x, tuple, [x1,...,xn]|(x1,...,xn)4)
```


``` python
varp.get_marked(vp, x)
```
