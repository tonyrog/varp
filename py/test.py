# Test various

import varpy

def symbol():
    vp = varpy.new({})
    v1 = varpy.add_variable(vp)
    sym = ("P",[1000]),
    varpy.add_symbol(vp, v1, sym)
    return (varpy.first_symbol(vp) == sym)

