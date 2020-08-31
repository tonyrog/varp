# using varc

import varc
import time

print("loaded varpy version " + varc.info(varc.new({}), 'version'))
        
def bt(vp):
    while not varc.nbcp(vp):
        if varc.undo(vp) == False:
            return False # contradiction
    return True # model

def bt_one(vp):
    t0 = time.time_ns()  # >= 3.7
    r = bt(vp)
    t1 = time.time_ns()
    print("result found in " + str((t1-t0) // 1000) + "us")
    return r

def bt_done(count, limit):
    if limit == None: return False
    elif count >= limit: return True
    else: return False

# limit>=1 !
def bt_all(vp, limit=None):
    t0 = time.time_ns()  # >= 3.7
    count = 0
    b = bt(vp)
    if b:
        print(model(vp))
        count += 1
        while b and varc.undo(vp) and not bt_done(count, limit):
            b = bt(vp)
            if b:
                print(model(vp))
                count += 1
    t1 = time.time_ns()
    print(str(count) + " models found in " + str((t1-t0) // 1000) + "us")
    return count

def model(vp):
    n = varc.info(vp, 'number_of_variables')
    return [symbol(vp, x) for x in range(1,n+1)
            if varc.value(vp, x) and varc.variable_info(vp, x, 'is_atom')]

def symbol(vp, x):
    s = varc.variable_info(vp, x, 'symbol')
    if s == []: return "x("+str(x)+")"
    else: return str((s[0])[0],'utf-8')
    
def get_bindings_list(vp, level, clauseinfo=False, trail=False):
    return varc.get_bindings(vp, level, clauseinfo, trail, False)

def i(vp=False):
    if vp == False:
        vp = varc.new({})
        il(vp,
           ['version','literal_size','literal_integer',
	    'value_packing','edge','xref','hash',
	    'init_phase', 'use_phase'])
    else:
        il(vp,
           ['version','literal_size','literal_integer',
	    'value_packing','edge','xref','hash',
	    'init_phase', 'use_phase',
            'number_of_clauses','number_of_dead_clauses',
            'number_of_edges','number_of_dead_edges',
            'number_of_conflicting_clauses', 'number_of_variables',
            'number_of_bound_variables',
            'number_of_unbound_variables',
            'bcp_counter', 'conflict_counter',
            'clause_n_counter', 'clause_2_counter',
            'clause_3_counter', 'clause_d_counter',
            'edge_2_counter', 'edge_d_counter',
            'size', 'level'])
        
def il(vp, keylist):
    for key in keylist:
        print(key + ": " + str(varc.info(vp, key)))        

def ic(vp):
    i_clauseset(vp, 'delta')
    i_clauseset(vp, 'gamma')
    i_clauseset(vp, 'alpha')
    i_clauseset(vp, 'beta')

def i_clauseset(vp, s):
    i = varc.clauseset_first(vp,s)
    if not isinstance(i, bool): print("clause set " + s)
    while not isinstance(i, bool):
        c = varc.get_clause(vp, i)
        print(str(i)+": "+str(c))
        i = varc.clauseset_next(vp,i)
