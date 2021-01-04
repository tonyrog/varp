# build p4 formula

import varpy

# helper to install variable and symbol
def var(vp, Name):
    x = varpy.add_variable(vp)
    varpy.isused(vp, x, True)
    varpy.add_symbol(vp, x, Name)
    return x

def clause(vp, List):
    i = varpy.add_clause(vp, List)
    return i

def p4(vp) :
    X1 = var(vp, ("P",[1,1]))
    X2 = var(vp, ("P",[1,2]))
    X3 = var(vp, ("P",[1,3]))
    X4 = var(vp, ("P",[2,1]))
    X5 = var(vp, ("P",[2,2]))
    X6 = var(vp, ("P",[2,3]))
    X7 = var(vp, ("P",[3,1]))
    X8 = var(vp, ("P",[3,2]))
    X9 = var(vp, ("P",[3,3]))
    X10 = var(vp, ("P",[4,1]))
    X11 = var(vp, ("P",[4,2]))
    X12 = var(vp, ("P",[4,3]))
    clause(vp, [X1,X2,X3])
    clause(vp, [X4,X5,X6])
    clause(vp, [X7,X8,X9])
    clause(vp, [X10,X11,X12])
    clause(vp, [-X1,-X4])
    clause(vp, [-X1,-X7])
    clause(vp, [-X1,-X10])
    clause(vp, [-X4,-X7])
    clause(vp, [-X4,-X10])
    clause(vp, [-X7,-X10])
    clause(vp, [-X2,-X5])
    clause(vp, [-X2,-X8])
    clause(vp, [-X2,-X11])
    clause(vp, [-X5,-X8])
    clause(vp, [-X5,-X11])
    clause(vp, [-X8,-X11])
    clause(vp, [-X3,-X6])
    clause(vp, [-X3,-X9])
    clause(vp, [-X3,-X12])
    clause(vp, [-X6,-X9])
    clause(vp, [-X6,-X12])
    clause(vp, [-X9,-X12])
    return vp

# general pigeon hole clauses for n pigeons and n-1 hols
def p(vp, n):
    ph = {}
    # create all variables and store them in dictionary
    for p in range(n):
        for h in range(n-1):
            ph[p,h] = varpy.add_variable(vp)
            varpy.isused(vp, ph[p,h], True) 
            varpy.add_symbol(vp, ph[p,h], ("P",[p,h]))
    # for a pigeons p the exist a hole h
    for p in range(n):
        varpy.add_clause(vp, [ph[p,h] for h in range(n-1)])
    for h in range(n-1):
        for p in range(n):
            for q in range(n):
                if p < q:
                    varpy.add_clause(vp, [-ph[p,h], -ph[q,h]])
    return vp

def run(n):
    vp = varpy.new({ 'xref' : True })
    p(vp,n)
    return varpy.bt_one(vp)

def run_p4():
    run(4)
