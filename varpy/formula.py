# build clauses from parse tree constructed with varp.lark grammar

import varpy
import varpy.circuit

def build(vp, tree):
    return {
        'var' : varp_var,
        'and' : varp_and,
        'or'  : varp_or,
        'xor' : varp_xor,
        'equ' : varp_equ,
        'imp' : varp_imp,
        'not' : varp_not,
    } [tree.data](vp, tree)

def binary(vp, gate, tree):
    l = build(vp, tree.children[0])
    r = build(vp, tree.children[1])
    return gate(vp, l, r)

def unary(vp, gate, tree):
    n = build(vp, tree.children[0])
    return gate(vp, n)

def varp_var(vp, tree):
    if len(tree.children) == 1:
        varname = tree.children[0].value
        x = varpy.find_symbol(vp, varname)
        if x == False:
            x = varpy.add_variable(vp, True)
            varpy.add_symbol(vp, x, varname)
            print("added variable "+varname+" "+str(x))
        return x
    else:
        raise ValueError("malformed/not supported variable")

def varp_and(vp, tree):
    return binary(vp, varpy.circuit.and_gate, tree)

def varp_or(vp, tree):
    return binary(vp, varpy.circuit.or_gate, tree)

def varp_xor(vp, tree):
    return binary(vp, varpy.circuit.xor_gate, tree)

def varp_imp(vp, tree):
    return binary(vp, varpy.circuit.imp_gate, tree)

def varp_equ(vp, tree):
    return binary(vp, varpy.circuit.xnor_gate, tree)

def varp_not(vp, tree):
    return unary(vp, varpy.circuit.inv_pin, tree)
