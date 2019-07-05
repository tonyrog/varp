Propositional logic library
===========================

Command line tool

    varp [satisfy|falsify|prove] [plugin [options]]... [bindings] [file1.varp ... filen.varp]

# global options
    
    --print      true|false         (false)
    --method     collect|count      (collect)
    --carry      true|false|ignore  (ignore)
    --borrow     true|false|ignore  (ignore)
    --divz       true|false|ignore  (false)
    --log        level()            (none)	 
    --seed       unsigned()         (0)
	--adder      plain | fast       (plain)
	
    level() = debug | info | notice | warning |
    	      error | critical | alert | emergency | none

#  "order" options
   	 
    --sort      <order>		(identity)
    --order_first "v1..vn"
    --order_last  "v1..vn"

    order() = identity | reverse | '-occur' | '+occur' | random

# Saturation "saturate"/"sat" parameters

    --timeout    timeout()      (infinity)
    --level      unsigned()		(0=eval)
    --pair       boolean()		(true)
    --threshold  unsigned()		(0)
	--laps       unsigned()     (0)

# Backtrack "backtrack"/"bt" parameters

    --max unsigned()
    --method collect|count
    --partial boolean()    	     

# Backjump "backjump"/"bj" parameters

    --timeout timeout()
    --max-learned         L
    --max-learned-factor  F
    --keep_factor         P
    --min-keep-clauses    K

    MaxLearned = 
        min(L, F*|Clauses|)      if L and F are both defined (> 0) then
        F*|Clauses|              if F is defined
        L                        if L is defined
        inf                      otherwise

    KeepSize = 
         inf                     if MaxLearned = inf
         max(K, P*MaxLearned)    if K and P are both defined
         P*MaxLearned            if P is defined
         K                       if K is defined
         inf                     otherwise

    -num-conflicts <N>           Number of conflicts to analyse
    -iorder <N>                  Max size of conflict clauses to activate
    -max-conflicts <N>           Max number of conflict clauses to activate
    
    -stumble <L>                 Extra Backjump if D1 >= L
    -olle <K>                    Extra Backjump if D1 >= K*D2
    -stumble-olle <bool>         Both stumble AND olle must be true to take jump
    
       D1 = Backjump distance
       D2 = Backstumble distance = distance from backjump to next level

    --restart-counter  <#eval>
    --restart-interval <seconds>    

# Model reduction "reduction"/"red" parameters

	-size unsigned()          Number of literal reductions to add 
	-type [both|min|pos|neg]  Type of reductions to add
	
# RAT remove clauses "rat" parameters

	-size unsigned()          Number of liter1al reductions to add 
	-type [both|min|pos|neg]  Type of reductions to add	
	
# DUMP dump CNF

	-f <name>
	
# Binding

    <var> = <value>

Variable (lowercase) variables are passed into varp as
environment (meta) variables that can be used in
formulas in quantifiers.
