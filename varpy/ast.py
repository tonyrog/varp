# build clauses from parse tree constructed with varp.lark grammar

import lark
import varpy
import varpy.circuit
import varpy.parser

def build(vp, tree, vs={}):
    return {
        'var' : varp_var,
        'and' : varp_and,
        'or'  : varp_or,
        'xor' : varp_xor,
        'equ' : varp_equ,
        'imp' : varp_imp,
        'not' : varp_not,
        'list' : varp_list,
        'quant' : varp_quant,
        'lt' : varp_lt,
        'lte' : varp_lte,
        'gt' : varp_gt,
        'gte' : varp_gte,
        'eq' : varp_eq,
        'neq' : varp_neq
    } [tree.data](vp, tree, vs)

def nary(vp, gate, tree, vs):
    l = []
    for i in range(len(tree.children)):
        l.append(build(vp, tree.children[i], vs))
    return gate(vp, l)

def binary(vp, gate, tree, vs):
    l = build(vp, tree.children[0], vs)
    r = build(vp, tree.children[1], vs)
    return gate(vp, l, r)

def unary(vp, gate, tree, vs):
    n = build(vp, tree.children[0], vs)
    return gate(vp, n)

# convert a number token into a decimal value
def number_value(n):
    if n.type == 'DECNUM':
        return int(n.value)
    elif n.type == 'HEXNUM':
        return int(n.value,16)
    elif n.type == 'OCTNUM':
        return int(n.value,8)
    elif n.type == 'BINNUM':
        return int(n.value,2)

def token_value(n):
    if n.type == 'DECNUM':
        return int(n.value)
    elif n.type == 'HEXNUM':
        return int(n.value,16)
    elif n.type == 'OCTNUM':
        return int(n.value,8)
    elif n.type == 'BINNUM':
        return int(n.value,2)
    elif n.type == 'IDENTIFIER':
        return n.value

def var_args(args):
    # assert args.data = list
    astr = "(" + var_arg(args.children[0])
    for a in args.children[1:]:
        astr += (","+var_arg(a))
    return astr+")"

def var_arg(arg):
    if isinstance(arg, lark.lexer.Token):
        return arg.value
    elif isinstance(arg, lark.tree.Tree):
        if arg.data == 'number':
            return str(number_value(arg.children[0]))
        elif arg.data == 'id':
            return arg.children[0].value
        else: return arg.data + var_args(arg)

# convert Tree var node into a term that can be stored as symbol in varp
def var_term(tree):
    if len(tree.children) == 1:
        return (tree.children[0].value,[])
    elif len(tree.children) == 2:
        return (tree.children[0].value,var_term_args(tree.children[1]))
    else:
        raise ValueError("malformed variable")

def var_term_args(args):
    return [var_term_arg(a) for a in args.children]

def var_term_arg(arg):
    if isinstance(arg, lark.lexer.Token):
        return token_value(arg)
    elif isinstance(arg, lark.tree.Tree):
        if arg.data == 'number':
            return number_value(arg.children[0])
        elif arg.data == 'id':
            return arg.children[0].value
        elif arg.data == 'call':
            return (var_term_arg(arg.children[0]),var_term_args(arg.children[1]))
        else:
            return (arg.data,var_term_args(arg))

#def eval_term(term, vs):
#    (p, args) = term
#    return (p, [eval_expr(ai, vs) for ai in args])

def eval_expr(ai, vs):
    # print("eval expr ai = " + str(ai))
    if isinstance(ai, int): return ai
    elif isinstance(ai, float): return ai
    elif isinstance(ai, str): return vs[ai]
    elif isinstance(ai, tuple):
        bif = {
            'add' :  lambda x, y: x + y,
            'sub' :  lambda x, y: x - y,
            'mul' :  lambda x, y: x * y,
            'div' :  lambda x, y: x // y,
            'rem' :  lambda x, y: x % y,
            'band' : lambda x, y: x & y,
            'bor' : lambda x, y: x | y,
            'bxor': lambda x, y: x ^ y,
            'neg':  lambda x: -x,
            'pos':  lambda x: +x,
            'bnot': lambda x: ~x,
            'eq': lambda x, y: x == y,
            'neq': lambda x, y: x != y,
            'lt': lambda x, y: x < y,
            'lte': lambda x, y: x <= y,
            'gt': lambda x, y: x > y,
            'gte': lambda x, y: x >= y,
            'range': lambda x, y: range(x,y+1)
        }
        f = ai[0]  # function name
        args = [eval_expr(x,vs) for x in ai[1]]
        # print("f="+str(f)+" args="+str(args))
        if f in bif:
            return bif[f](*args)
        elif f in vs:  # p exist, check if function or dict
            fv = vs[f]  # check function or dictionary
            arity = len(args)
            if isinstance(fv, dict) and (arity > 0):
                if arity == 1:  # assume that key is not singleton
                    r = fv[args[0]]
                    # print("r = "+str(r))
                    return r
                else:
                    r = fv[tuple(args)]
                    # print("r = "+str(r))
                    return r
            elif callable(fv):
                r = fv(*args)
                # print("r = "+str(r))
                return r

# apply a lambda to arguments picked from a list
#def apply(f, args):
#    n = len(args)
#    if n == 0: return f()
#    elif n == 1: return f(args[0])
#    elif n == 2: return f(args[0],args[1])
#    elif n == 3: return f(args[0],args[1],args[2])

# lookup or install variable
def varp_var(vp, tree, vs):
    (p,args) = var_term(tree)
    args1 = [eval_expr(ai,vs) for ai in args]
    term = (p, args1)
    # print("varp_var term=" + str(term))
    x = varpy.find_symbol(vp, term)
    if x == False:
        x = varpy.add_variable(vp, True)
        varpy.isused(vp, True)
        varpy.add_symbol(vp, x, term)
#        print("added variable " + varpy.symbol_str(term))
        return x
    else:
        return x

def varp_and(vp, tree, vs):
    return binary(vp, varpy.circuit.and_gate, tree, vs)

def varp_or(vp, tree, vs):
    return binary(vp, varpy.circuit.or_gate, tree, vs)

def varp_xor(vp, tree, vs):
    return binary(vp, varpy.circuit.xor_gate, tree, vs)

def varp_imp(vp, tree, vs):
    return binary(vp, varpy.circuit.imp_gate, tree, vs)

def varp_equ(vp, tree, vs):
    return binary(vp, varpy.circuit.xnor_gate, tree, vs)

def varp_not(vp, tree, vs):
    return unary(vp, varpy.circuit.inv_pin, tree, vs)

def cond_bin(vp, op, tree, vs):
    l = var_term_arg(tree.children[0])
    r = var_term_arg(tree.children[1])
    if eval_expr((op, [l, r]), vs) == 0:
        return False
    else:
        return True

# implement >, >=, <, <=, != and == they must all evaluate to true or false

def varp_eq(vp, tree, vs):
    return cond_bin(vp, 'eq', tree, vs)

def varp_neq(vp, tree, vs):
    return cond_bin(vp, 'neq', tree, vs)

def varp_gt(vp, tree, vs):
    return cond_bin(vp, 'gt', tree, vs)

def varp_gte(vp, tree, vs):
    return cond_bin(vp, 'gte', tree, vs)

def varp_lt(vp, tree, vs):
    return cond_bin(vp, 'lt', tree, vs)

def varp_lte(vp, tree, vs):
    return cond_bin(vp, 'lte', tree, vs)


def varp_quant(vp, tree, vs):
    q = tree.children[0]
    expr = tree.children[1]
    return {
        'all' : varp_ALL,
        'any' : varp_ANY,
        'none' : varp_NONE,
        'one' : varp_ONE,
        'odd' : varp_ODD,
        'even' : varp_EVEN,
        'parity' : varp_PARITY,
        'eq' : varp_EQ,
        'neq' : varp_NEQ,
        'gt' : varp_GT,
        'gte' : varp_GTE,
        'lt' : varp_LT,
        'lte' : varp_LTE,
    } [q.data](vp, q, expr, vs)

def varp_list(vp, tree, vs):
    ys = []
    for t in tree.children:
        y = build(vp, t, vs)
        ys.append(y)
    return ys

# build expr over a list of generators
def quant(vp, gs, expr, vs):
    out = []
    quant_(vp, 0, len(gs), gs, expr, vs, out)
    return out

def quantk(vp, gs, expr, vs):
    out = []
    k0 = var_term_arg(gs[0])
    k1 = eval_expr(k0, vs)
    quant_(vp, 1, len(gs), gs, expr, vs, out)
    return (k1, out)

def quant_(vp, i, n, gs, expr, vs, out):
    if i == n:
        x = build(vp, expr, vs)
        if isinstance(x, list):
            out += x
        else:
            out.append(x)
    else:
        g = gs[i]
        if g.data == 'assign':
            x = var_term_arg(g.children[0])
            v0 = var_term_arg(g.children[1])
            v1 = eval_expr(v0, vs)
            if isinstance(v1, range) or isinstance(v1, list):
                for v in v1:
                    vs[x] = v
                    quant_(vp, i+1, n, gs, expr, vs, out)
            else:
                vs[x] = v1
                quant_(vp, i+1, n, gs, expr, vs, out)
        else: # filter
            f0 = var_term_arg(g)
            f1 = eval_expr(f0, vs)
            if not f1: return
            else: quant_(vp, i+1, n, gs, expr, vs, out)

def generators(q):
    if len(q.children) == 0: return []
    else:
        g = q.children[0]
        if g.data == 'list': return g.children

def varp_ALL(vp, q, expr, vs):
    return varpy.circuit.varp_ALL(vp, quant(vp, generators(q), expr, vs))

def varp_ANY(vp, q, expr, vs):
    return varpy.circuit.varp_ANY(vp, quant(vp, generators(q), expr, vs))

def varp_NONE(vp, q, expr, vs):
    return varpy.circuit.varp_NONE(vp, quant(vp, generators(q), expr, vs))

def varp_ONE(vp, q, expr, vs):
    return varpy.circuit.varp_ONE(vp, quant(vp, generators(q), expr, vs))

def varp_ODD(vp, q, expr, vs):
    return varpy.circuit.varp_ODD(vp, quant(vp, generators(q), expr, vs))

def varp_EVEN(vp, q, expr, vs):
    return varpy.circuit.varp_EVEN(vp, quant(vp, generators(q), expr, vs))

def varp_PARITY(vp, q, expr, vs):
    return varpy.circuit.varp_PARITY(vp, quant(vp, generators(q), expr, vs))

def varp_EQ(vp, q, expr, vs):
    (k,ys) = quantk(vp, generators(q), expr, vs)
    return varpy.circuit.varp_EQ(vp,k,ys)
                                 
def varp_NEQ(vp, q, expr, vs):
    (k,ys) = quantk(vp, generators(q), expr, vs)
    return varpy.circuit.varp_NEQ(vp,k,ys)

def varp_GT(vp, q, expr, vs):
    (k,ys) = quantk(vp, generators(q), expr, vs)
    return varpy.circuit.varp_GT(vp,k,ys)
    
def varp_GTE(vp, q, expr, vs):
    (k,ys) = quantk(vp, generators(q), expr, vs)
    return varpy.circuit.varp_GTE(vp,k,ys)

def varp_LT(vp, q, expr, vs):
    (k,ys) = quantk(vp, generators(q), expr, vs)
    return varpy.circuit.varp_LT(vp,k,ys)

def varp_LTE(vp, q, expr, vs):
    (k,ys) = quantk(vp, generators(q), expr, vs)
    return varpy.circuit.varp_LTE(vp,k,ys)

def test(text, vs={}):
    f = varpy.parser.text(text)
    vp = varpy.new({})
    x = build(vp, f, vs)
    if varpy.bind(vp, x) and varpy.bcp(vp):
        varpy.set_level(vp, 1)
        return varpy.bt_all(vp)
    else:
        print("0 models found")
        return 0
