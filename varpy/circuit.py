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

# (min,max) = SORT(y, z)
def sort_gate(vp, y, z, x0=None, x1=None):
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
        xs1 = [x] + [inv(xi) for xi in ys]
        xn = inv(x)
        for xi in ys: clause(vp,[xn,xi])
        return x
    else:
        return none_assoc_(vp,gate,ys,x)

def none_assoc_(vp,gate,ys,x=None):
    n = len(ys) // 2
    u = [ys[i] for i in range(n)]
    v = [ys[i] for i in range(n, len(ys))]
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

# sort all ys one lap then or over the
# fixme len(ys) < 2
def eq1(vp, ys, x=None):
    if x == None: x = varpy.add_variable(vp)
    (z0,z1) = sort_gate(vp, ys[0], ys[1])
    zs = [z0]
    for y in ys[2:]:
        (z0,z1) = sort_gate(vp, z1, y)
        zs.append(z0)
    return and_gate(vp, z1, inv(left_assoc(vp, or_gate, zs)), x)

def var(vp, name):
    x = varpy.add_variable(vp, True)
    varpy.add_symbol(vp, x, name)
    return x

def clause(vp, ls):
    print(str(ls))
    ci = varpy.add_clause(vp, ls)
    return ci

def test_gate(gate):
    vp = varpy.new({'xref':True})
    a = var(vp, "a")
    b = var(vp, "b")
    c = gate(vp, a, b)
    varpy.bind(vp, c)
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
