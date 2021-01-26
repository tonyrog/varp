# basic backjump implementation
# the use of := operator require 3.8 to be used
import varpy
from .pigeon import *

def bj(vp):
    varpy.push(vp)
    varpy.config(vp, 'max_conflicting', 1)
    r = varpy.nbcp(vp)
    l = varpy.info(vp, 'level')
    while not r and (l > 0):
#        gsize = varpy.clauseset_size(vp, 'gamma')
#        if ((gsize > 0) and ((gsize % 100) == 0)):
#            print("|gamma| = "+str(gsize))
        cix = varpy.conflict(vp, 3.0, 0)
        if cix == None:
            pass
        elif varpy.minimize(vp, cix, local) == None:
            pass
        else:
            clause = varpy.get_clause(vp, cix)
            if isinstance(clause, bool):
                if clause == True:
                    pass
                else:
                    varpy.pop(vp, 0)
                    return False
            elif len(clause) == 1:
                varpy.pop(vp, 0)
                varpy.bind(vp, clause[0])
            elif len(clause) > 1:
                j = jump(vp, clause)
                varpy.pop(vp, j)
                varpy.move_clause(vp, cix, 'gamma')
        r = varpy.nbcp(vp)
        l = varpy.info(vp, 'level')
    return r
           
def undo_until(vp, new_level):
    varpy.pop(vp, new_level)

def jump(vp, clause):
    # print("conflict clause = " + str(clause))
    l = [varpy.implication_level(vp, q) for q in clause]
    list.sort(l)
    list.reverse(l)
    return l[1]

# purge among clauses in 'gamma'
# NOTE 'delta' may contain clause i=0,
#  this may in python be mixed up with False!
# if keep is an integer then it is an absolute number
# if keep is a float (range 0..1) then is relative to size
def purge(vp, keep):
    if isinstance(keep, float):
        # calculate from keep factor 0.1 = keep 10%
        if (keep >= 0) and (keep <= 1):
            size = varpy.clauseset_size(vp, 'gamma')
            keep = int(size*keep)
    varpy.clauseset_offset(vp, 'gamma', keep)
    varpy.clauseset_sort(vp, 'gamma')
    i = varpy.clauseset_first(vp, 'gamma')
    while i != False:
        varpy.del_clause(vp, i)
        i = varpy.clauseset_next(vp, i)
    varpy.clauseset_offset(vp, 'gamma', 0)


def test_fill(vp):
    (a,b) = varpy.add_variables(vp, 8)
    [x1,x2,x3,x4,x5,x6,x7,x8] = range(a,b+1)
    varpy.add_clause(vp, [x1,-x2,x3], 'gamma')
    varpy.add_clause(vp, [x1,x3], 'gamma')
    varpy.add_clause(vp, [x2,x1], 'gamma')
    varpy.add_clause(vp, [x4,x1], 'gamma')
    varpy.add_clause(vp, [x5,x1], 'gamma')
    varpy.add_clause(vp, [x6,x7,x8], 'gamma')
    varpy.add_clause(vp, [x6,-x7,x8], 'gamma')
    
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
