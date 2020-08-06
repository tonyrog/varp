# Circuit library

import varpy

def or_gate(vp, y, z, x=None):
    if x == None: x = varpy.add_variable(vp)
    varpy.add_clause(vp, [-x,y,z])
    varpy.add_clause(vp, [x,-y])
    varpy.add_clause(vp, [x,-z])
    return x

def and_gate(vp, y, z, x=None):
    if x == None: x = varpy.add_variable(vp)
    return or_gate(vp, y, -z, -x)

def xor_gate(vp, y, z, x=None):
    if x == None: x = varpy.add_variable(vp)
    varpy.add_clause(vp,[x,-y,z])
    varpy.add_clause(vp,[x,y,-z])
    varpy.add_clause(vp,[-x,-y,-z])
    varpy.add_clause(vp,[-x,y,z])
    return x
