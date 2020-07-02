# using varc

import varc

def p4(V) :
    X1 = var(V, "P(1,1)")
    X2 = var(V, "P(1,2)")
    X3 = var(V, "P(1,3)")
    X4 = var(V, "P(2,1)")
    X5 = var(V, "P(2,2)")
    X6 = var(V, "P(2,3)")
    X7 = var(V, "P(3,1)")
    X8 = var(V, "P(3,2)")
    X9 = var(V, "P(3,3)")
    X10 = var(V, "P(4,1)")
    X11 = var(V, "P(4,2)")
    X12 = var(V, "P(4,3)")
    clause(V, [X1,X2,X3])
    clause(V, [X4,X5,X6])
    clause(V, [X7,X8,X9])
    clause(V, [X10,X11,X12])
    clause(V, [-X1,-X4])
    clause(V, [-X1,-X7])
    clause(V, [-X1,-X10])
    clause(V, [-X4,-X7])
    clause(V, [-X4,-X10])
    clause(V, [-X7,-X10])
    clause(V, [-X2,-X5])
    clause(V, [-X2,-X8])
    clause(V, [-X2,-X11])
    clause(V, [-X5,-X8])
    clause(V, [-X5,-X11])
    clause(V, [-X8,-X11])
    clause(V, [-X3,-X6])
    clause(V, [-X3,-X9])
    clause(V, [-X3,-X12])
    clause(V, [-X6,-X9])
    clause(V, [-X6,-X12])
    clause(V, [-X9,-X12])
    return V

def var(V, Name):
    Vi = varc.add_variable(V)
    varc.add_symbol(V, Vi, Name)
    return Vi

def clause(V, List):
    Ci = varc.add_clause(V, List)
    print(List)
    return Ci

def bt(v):
    while not varc.nbcp(v):
        print("nbcp")
        if varc.undo(v) == False:
            return False # contradiction
    return True # model

def main_p4():
    V = varc.new({})
    p4(V)
    varc.set_level(V, 1)
    return bt(V)

def main():
    V = varc.new({ varc.xref: varc.true})
    X1 = varc.add_variable(V)
    X2 = varc.add_variable(V)
    X3 = varc.add_variable(V)
    X4 = varc.add_variable(V)
    varc.add_clause(V, [X1,X2,X3])
    varc.add_clause(V, [X4,X3,X2])
    return "ok"
