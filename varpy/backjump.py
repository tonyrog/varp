# basic backjump implementation
# the use of := operator require 3.8 to be used
import varpy
from .pigeon import *

def bj(vp):
    varpy.config(vp, 'max_conflicting', 1)
    varpy.set_level(vp, 0)
    while not (r := varpy.nbcp(vp)) and ((l := varpy.info(vp, 'level')) > 0):
        print("level = " + str(l))
        cix = varpy.conflict(vp, l, 3.0, 0)
        if varpy.minimize(vp, cix) == False:
            pass
        else:
            clause = varpy.get_clause(vp, cix)
            if len(clause) == 1:
                undo_until(vp, l, 0)
                varpy.bind(vp, clause[0])
            else:
                j = jump(vp, clause)
                undo_until(vp, l, j)
                varpy.move_clause(vp, cix, 'gamma')
    return r
           
def undo_until(vp, level, new_level):
    while level > new_level:
        varpy.undo_level(vp, level)
        level -= 1
    varpy.set_level(vp, level)

def jump(vp, clause):
    print("conflict clause = " + str(clause))
    l = [varpy.implication_level(vp, q) for q in clause]
    list.sort(l)
    list.reverse(l)
    return l[1]

def test():
    vp = varpy.new({'xref':True})
    pigeon.p(vp, 6)
    return bj(vp)

def test2():
    vp = varpy.new({'xref':True})
    a = var(vp, "a")
    b = var(vp, "b")
    c = var(vp, "c")
    d = var(vp, "d")
    e = var(vp, "e")
    f = varpy.eq1(vp, [varpy.or_gate(vp,a,b),
                       varpy.or_gate(vp,a,c),
                       varpy.or_gate(vp,b,c),
                       varpy.or_gate(vp,d,e)])
    varpy.bind(vp, f)
    if bj(vp):
        print(varpy.model(vp))
        return True
    else:
        return False

def var(vp, name):
    x = varpy.add_variable(vp, True)
    varpy.add_symbol(vp, x, name)
    return x
