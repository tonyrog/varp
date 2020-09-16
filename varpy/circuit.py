# Circuit library

import varpy

def inv(x):
    if isinstance(x, bool):
        return (not x)
    else:
        return -x

def or_clauses(vp, y, z, x):
    clause(vp, [inv(x),y,z])
    clause(vp, [x,inv(y)])
    clause(vp, [x,inv(z)])
    return x

# x = y AND z ( x = -(-y OR -z) )
def and_clauses(vp, y, z, x):
    or_clauses(vp, inv(y), inv(z), inv(x))
    return x

def xor_clauses(vp, y, z, x):
    clause(vp,[x,inv(y),z])
    clause(vp,[x,y,inv(z)])
    clause(vp,[inv(x),inv(y),inv(z)])
    clause(vp,[inv(x),y,z])
    return x

# x = not y
def inv_clauses(vp, y, x):
    clause(vp,[x,y])
    clause(vp,[inv(x),inv(y)])
    return x

def inv_gate(vp, y, x=None):
    if x == None: x = varpy.add_variable(vp)
    return inv_clauses(vp, y, x)

def inv_pin(vp, y):
    return inv(y)

# x = y OR z
def or_gate(vp, y, z, x=None):
    if x == None: x = varpy.add_variable(vp)
    return or_clauses(vp, y, z, x)

# x = NOT (y OR z)
def nor_gate(vp, y, z, x=None):
    if x == None: x = varpy.add_variable(vp)
    return inv(or_clauses(vp, y, z, x))

# x = y -> z (NOT y OR z)
def imp_gate(vp, y, z, x=None):
    if x == None: x = varpy.add_variable(vp)
    return or_clauses(vp, inv(y), z, x)

# x = y -/> z ( NOT (y -> z) ) = NOT (NOT y OR Z) =  (y AND NOT z)
def nimp_gate(vp, y, z, x=None):
    if x == None: x = varpy.add_variable(vp)
    return and_clauses(vp, y, inv(z), x)

# x = y AND z
def and_gate(vp, y, z, x=None):
    if x == None: x = varpy.add_variable(vp)
    return and_clauses(vp, y, z, x)

# x = NOT (y AND z)
def nand_gate(vp, y, z, x=None):
    if x == None: x = varpy.add_variable(vp)
    return inv(and_clauses(vp, y, z, x))

# x = y XOR z
def xor_gate(vp, y, z, x=None):
    if x == None: x = varpy.add_variable(vp)
    return xor_clauses(vp, y, z, x)

# x = NOT (y XOR z)
def xnor_gate(vp, y, z, x=None):
    if x == None: x = varpy.add_variable(vp)
    return inv(xor_clauses(vp, y, z, x))

# x = MIN(y,z) = (y AND z)
def min_gate(vp, y, z, x=None):
    if x == None: x = varpy.add_variable(vp)
    return and_clauses(vp, y, z, x)

# x = MAX(y,z) = (y OR z)
def max_gate(vp, y, z, x=None):
    if x == None: x = varpy.add_variable(vp)
    return or_clauses(vp, y, z, x)

def half_adder(vp, y, z, x=None, co=None):
    if x == None: x = varpy.add_variable(vp)
    if co == None: co = varpy.add_variable(vp)
    x = xor_gate(vp, y, z, x)
    co = and_gate(vp, y, z, co)
    return (x, co)

def full_adder(vp, y, z, ci=False, x=None, co=None):
    if x == None: x = varpy.add_variable(vp)
    if co == None: co = varpy.add_variable(vp)
    x1 = xor_gate(vp,y,z,x)  # hmmmm check x!
    x = xor_gate(vp,x1,ci)
    a1 = and_gate(vp,x1,ci)
    a2 = and_gate(vp,y,z)
    co = or_gate(vp,a1,a2,co)
    return (x,co)

# (min,max) circuit
def comparator(vp, y, z, x0=None, x1=None):
    if x0 == None: x0 = varpy.add_variable(vp)
    if x1 == None: x1 = varpy.add_variable(vp)
    return (min_gate(vp, y, z, x0), max_gate(vp, y, z, x1))

# x = (((y[0] o y[1]) o y[2]) .. y[n-1])
def left_assoc(vp, gate, ys, x=None):
    n = len(ys)
    y = ys[0]
    for i in range(1,n-1):
        y = gate(vp, y, ys[i])
    return gate(vp, y, ys[n-1], x)

# x = (y[0] o ..(y[n-3] o (y[n-2] o y[n-1])))
def right_assoc(vp, gate, ys, x=None):
    n = len(ys)
    y = ys[n-1]
    for i in range(1,n-1):
        y = gate(vp, y, ys[n-i-1])
    return gate(vp, y, ys[0], x)

def none_assoc(vp,gate,ys,x=None):
    if x == None: x = varpy.add_variable(vp)
    if gate == or_gate:
        clause(vp, [inv(x)] + ys)
        for xi in ys: clause(vp,[x,inv(xi)])
        return x
    elif gate == and_gate:
        clause(vp, [x] + [inv(xi) for xi in ys])
        xn = inv(x)
        for xi in ys: clause(vp,[xn,xi])
        return x
    else:
        return none_assoc_(vp,gate,ys,x)

def none_assoc_(vp,gate,ys,x=None):
    (u,v) = split(len(ys) // 2, ys)
    if len(u) == 1 and len(v) == 1:
        return gate(vp,u[0],v[0],x)
    elif len(u) == 1 and len(v) == 2:
        x1 = varpy.add_variable(vp)
        gate(vp,v[0],v[1],x1)
        return gate(vp,u[0],x1,x)
    else:
        x1 = varpy.add_variable(vp)
        none_assoc_(vp,gate,u,x1)
        x2 = varpy.add_variable(vp)
        none_assoc_(vp,gate,v,x2)
        return gate(vp,x1,x2,x)

def varp_all(vp, ys, x=None):
    return none_assoc(vp, and_gate, ys, x)

def varp_any(vp, ys, x=None):
    return none_assoc(vp, or_gate, ys, x)

def varp_parity(vp, ys, x=None):
    return left_assoc(vp, xor_gate, ys, x)

def varp_odd(vp, ys, x=None):
    return varp_parity(vp, ys, x)

def varp_even(vp, ys, x=None):
    return inv(varp_parity(vp, ys, x))

def varp_none(vp, ys, x=None):
    return inv(varp_any(vp, ys, x))

def varp_one(vp, ys, x=None):
    return eq1(vp, ys, x)

def varp_eq(vp, k, ys, x=None):
    return eqk(vp, k, ys, x)

def varp_neq(vp, k, ys, x=None):
    return inv(eqk(vp, k, ys, x))

def varp_gt(vp, k, ys, x=None):
    if k >= 0: return gtk(vp, k, ys, x)
 
def varp_gte(vp, k, ys, x=None):
    if k == 0: return varp_any(vp, ys, x)
    elif k>0: return gtk(vp,k-1,ys,x)

def varp_lt(vp, k, ys, x=None):
    if k == 0: return False
    elif k == 1: return varp_none(vp,ys,x)
    elif k > 1:
        n = len(ys)
        ys1 = [inv(yi) for yi in ys]
        return gtk(vp, n-k, ys1, x)
 
def varp_lte(vp, k, ys, x=None):
    if k == 0: return varp_none(vp, ys, x)
    elif k>0:
        n = len(ys)
        ys1 = [inv(yi) for yi in ys]
        return gtk(vp,n-k-1,ys1,x)

# sort all ys one lap then or over the
# fixme len(ys) < 2
def eq1(vp, ys, x=None):
    if x == None: x = varpy.add_variable(vp)
    (z0,z1) = comparator(vp, ys[0], ys[1])
    zs = [z0]
    for y in ys[2:]:
        (z0,z1) = comparator(vp, z1, y)
        zs.append(z0)
    return and_gate(vp, z1, inv(left_assoc(vp, or_gate, zs)), x)

def eqk(vp,k,ys,x=None):
    n = len(ys)
    if k == 0: return inv(varp_any(vp,ys,x))
    elif k > n: return False
    elif k == n: return varp_all(vp,ys,x)
    else:
        ys1 = sort(vp,k,ys)
        (a,b) = split(k, ys1)
        a1 = varp_all(vp,a)
        b1 = varp_any(vp,b)
        return and_gate(vp,a1,inv(b1),x)

def gtk(vp,k,ys,x=None):
    n = len(ys)
    if k == 0: return varp_any(vp,ys,x)
    elif k >= n: return False
    else:
        ys1 = sort(vp,k,ys)
        (a,b) = split(k, ys1)
        a1 = varp_all(vp, a)
        b1 = varp_any(vp, b)
        return and_gate(vp,a1,b1,x)

# split list ys in two lists
def split(n, ys):
    u = [ys[i] for i in range(n)]
    v = [ys[i] for i in range(n, len(ys))]
    return (u,v)

def sort(vp,n,xs):
    ys = []
    for i in range(n):
        xs = minmax(vp,xs)
        ys.append(xs.pop())
    return ys + xs
    
# return a one-lap "sorted" list of xs such that
# ys[n-1] is greater that all other elements
def minmax(vp,xs):
    ys = []
    mx = xs[0]
    for i in range(1,len(xs)):
        (mi,mx) = comparator(vp,mx,xs[i])
        ys.append(mi)
    ys.append(mx)
    return ys

def var(vp, name):
    x = varpy.add_variable(vp, True)
    varpy.add_symbol(vp, x, name)
    return x

def clause(vp, ls):
#   print(str(ls))
    ci = varpy.add_clause(vp, ls)
    return ci

def test_gate(gate):
    vp = varpy.new({'xref':True})
    a = var(vp, "a")
    b = var(vp, "b")
    c = gate(vp, a, b)
    if not varpy.bind(vp, c):
        print("0 models found")
        return 0
    else:
        varpy.set_level(vp, 1)
        return varpy.bt_all(vp)

def test_or():
    return test_gate(or_gate)

def test_nor():
    return test_gate(nor_gate)

def test_and():
    return test_gate(and_gate)

def test_nand():
    return test_gate(nand_gate)

def test_xor():
    return test_gate(xor_gate)

def test_xnor():
    return test_gate(xnor_gate)

def test():
    vp = varpy.new({'xref':True})
    a = var(vp, "a")
    b = var(vp, "b")
    c = var(vp, "c")
    d = var(vp, "d")
    e = left_assoc(vp, and_gate, [a,b,c,d])
    f = right_assoc(vp, or_gate, [a,b,c,d])
    g = right_assoc(vp, xor_gate, [a,b,e,f])
    return g

def test_eq1():
    vp = varpy.new({'xref':True})
    a = var(vp, "a")
    b = var(vp, "b")
    c = var(vp, "c")
    d = var(vp, "d")
    e = eq1(vp, [a,b,c,d])
    varpy.bind(vp, e)
    varpy.set_level(vp, 1)
    return varpy.bt_all(vp)

def test_half_adder1():
    vp = varpy.new({'xref':True})
    a = var(vp, "a")
    b = var(vp, "b")
    return half_adder(vp, a, b)

def test_full_adder1():
    vp = varpy.new({'xref':True})
    a = var(vp, "a")
    b = var(vp, "b")
    r = full_adder(vp, a, b)
    varpy.ic(vp)
    return r
