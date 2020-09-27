import varpy
import varpy.parser
import varpy.ast
import varpy.backjump
import varpy.saturate
import time

def parse_file(vp, filename, dom={}):
    tree = varpy.parser.file(filename)
    return varpy.ast.build(vp, tree, dom)

def parse_formula(vp, text, dom={}):
    tree = varpy.parser.text(text)
    return varpy.ast.build(vp, tree, dom)

def one_lap_dilemma(vp):
    x = varpy.next_unbound(vp)
    varpy.set_level(vp, 0)
    m = 0  # number of bindings done
    while x != False:
        a = varpy.saturate.saturate_var(vp,x)
        varpy.set_level(vp, 0)
        if a == False:
            return (False, m)
        elif len(a) > 0:
            m += len(a)
            for j in a:
                if isinstance(j,int):
                    print("bind "+str(j))
                    varpy.bind(vp,j)
                else:
                    print("subst "+str(j[0])+"/"+str(j[1]))
                    varpy.subst(vp,j[0],j[1])
            if not varpy.bcp(vp):
                print('unsatisfiable')
                return (False, m)
        x = varpy.next_unbound(vp,x)
    return (True, m)

def num_unbound(vp):
     return varpy.info(vp,'number_of_unbound_variables')

def one_saturate(vp):
    m = 1  # start the loop, number of changes
    varpy.config(vp,'xref',True)
    varpy.set_level(vp, 0)
    n=0 # n no. of laps
    while (num_unbound(vp) > 0) and (m > 0):
        (p, m) = one_lap_dilemma(vp)
        if not p: # contradiction
            print('unsatisfiable')
            break
        else:
            n=n+1
            print(n)

#formula='C:/Users/gunna/OneDrive/Skrivbord/varp-formler/formula_GTn.py'
#formula='C:/Users/gunna/OneDrive/Skrivbord/varp-formler/formula_super.py'
filename='/home/tony/erlang/varp/formulas/gunnar/RR.varp'
#formula='C:/Users/gunna/OneDrive/Skrivbord/varp-program/miniform.py'

vp = varpy.new({})
# f = parse_formula(vp, "(A <-> B) and (C <-> D)")
f = parse_file(vp, filename, { 'n':4, 'k':6 })
t0 = time.time()
if not varpy.bind(vp, f):
    print('unsatisfiable (bind)')
elif not varpy.bcp(vp):
    print('unsatisfiable (bcp)')
else:
    print('start')
    one_saturate(vp)
    print(varpy.next_unbound(vp))
    y = varpy.info(vp,'number_of_unbound_variables')
    print(y)
    t1 = time.time()
    if varpy.bt(vp):
        print(varpy.model(vp))
print("--- "+format((t1-t0),'.3f') + " seconds ---")
