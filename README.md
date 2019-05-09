Propositional logic library
===========================

The main module is varp

Current options to varp

    Key         Value
    value	boolean()|none	main formula variable value
    print	boolean()	print models when found
    method	collect|count	count or collect models
    max		unsigned()	max number of models to collect
    order	<order>
    bcp		boolean()	do not use equivalence classes
    saturate	unsigned()	saturation vector width
    pair	boolean()    test two variables at a time
    threshold	unsigned()   take more rounds in saturation.
    carry	boolean()|ignore
    borrow	boolean()|ignore
    divz	boolean()|ignore
    log		<level>

Command line tool

    varp [satisfy|falsify|prove] [options] [bindings] [file1.varp ... filen.varp]

    options
         --value      true|false|none	(none)
         --print      true|false		(false)
         --method     collect|count		(collect)
         --max        <unsigned>		(0=all)
         --order      <order>		(identity)
         --bcp        true|false		(false)
         --saturate   <unsigned>		(0=eval)
         --pair       true|false		(true)
         --threshold  <unsigned>		(0)
         --carry      true|false|ignore	(ignore)
         --borrow     true|false|ignore	(ignore)
         --divz       true|false|ignore	(false)
         --log        <level>		(none)

    bindings
        <var> = <value>

    order
        identity | 
        reverse | 
        depth|
        occure |
        depth_occure |
        occure_depth |
        <var>*

    level
        debug |
        info |
        notice |
        warning |
        error |
        critical |
        alert |
        emergency |
        none

Backjump parameters

    max_learned_clauses L
    max_learned_factor  F
    keep_factor         P
    min_keep_clauses    K

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

    -num_conflicts <N>           Number of conflicts to analyse
    -iorder <N>                  Max size of conflict clauses to activate
    -max_conflicts <N>           Max number of conflict clauses to activate
    
    -stumble <L>                 Extra Backjump if D1 >= L
    -olle <K>                    Extra Backjump if D1 >= K*D2
    -stumble_olle <bool>         Both stumble AND olle must be true to take jump
    
       D1 = Backjump distance
       D2 = Backstumble distance = distance from backjump to next level

    restart_counter  <#eval>
    restart_interval <ms>    