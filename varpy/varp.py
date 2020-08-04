# using varc

import varc

print("loaded varpy version " + varc.info(varc.new({}), 'version'))
        
def get_bindings_list(vp, level, clauseinfo=False, trail=False):
    return varc.get_bindings(vp, level, clauseinfo, trail, False)

def bt(v):
    while not varc.nbcp(v):
        if varc.undo(v) == False:
            return False # contradiction
    return True # model

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
