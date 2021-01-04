# functions to 1-"saturate" a formula
import varpy

# saturate variable x return bindings or False
def saturate_var(vp, x):
    if l_eval(vp, x):
        varpy.mark(vp, 2)
        l_undo(vp)
        if l_eval(vp, -x):
            bs = varpy.intersect_var(vp, x, 2, True)
            varpy.unmark(vp)
            l_undo(vp)
            return bs
        else:
            varpy.mark(vp, 1)
            bs = varpy.get_marked(vp, True)
            varpy.unmark(vp)
            l_undo(vp)
            return bs
    else:
        l_undo(vp)
        if l_eval(vp, -x):
            bs = varpy.get_bindings(vp, 2)
            l_undo(vp)
            return bs
        else:
            l_undo(vp)
            return False

def l_eval(vp, x):
    varpy.push(vp)
    if varpy.bind(vp, x):
        varpy.push(vp)
        return varpy.bcp(vp)
    else:
        return False

def l_undo(vp):
    varpy.pop(vp, 0)

def test():
    vp = varpy.new({'xref':True})
    x1 = varpy.add_variable(vp)
    x2 = varpy.add_variable(vp)
    x3 = varpy.add_variable(vp)
    x4 = varpy.add_variable(vp)
    x5 = varpy.add_variable(vp)    
    varpy.add_clause(vp, [-x1, x2])
    varpy.add_clause(vp, [x1, x2])
    varpy.add_clause(vp, [-x1, -x3])
    varpy.add_clause(vp, [x1, -x3])
    varpy.add_clause(vp, [-x1, -x4])
    varpy.add_clause(vp, [x1, x4])
    varpy.add_clause(vp, [-x1, x5])
    varpy.add_clause(vp, [x1, -x5])        

    r = saturate_var(vp, x1)
    print("saturate x1 ")
    print(r)
