# build clauses from parse tree constructed with varp.lark grammar

import lark
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

# convert Tree var node into a string
def var_str(tree):
    if len(tree.children) == 1:
        return tree.children[0].value;
    elif len(tree.children) == 2:
        return tree.children[0].value + var_args(tree.children[1])
    else:
        raise ValueError("malformed variable")

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
            return arg.children[0].value;
        else: return arg.data + var_args(arg)

# convert Tree var node into a term that can be stored as symbol in varp
def var_term(tree):
    if len(tree.children) == 1:
        return tree.children[0].value;
    elif len(tree.children) == 2:
        return (tree.children[0].value,var_term_args(tree.children[1]))
    else:
        raise ValueError("malformed variable")

def var_term_args(args):
    return [var_term_arg(a) for a in args.children]
    
def var_term_arg(arg):
    if isinstance(arg, lark.lexer.Token):
        return arg.value
    elif isinstance(arg, lark.tree.Tree):
        if arg.data == 'number':
            return number_value(arg.children[0])
        elif arg.data == 'id':
            return arg.children[0].value
        else:
            return (arg.data,var_term_args(arg))

# lookup or install variable, first version only handle string!
def varp_var(vp, tree):
    varname = var_str(tree)
    x = varpy.find_symbol(vp, varname)
    if x == False:
        x = varpy.add_variable(vp, True)
        varpy.add_symbol(vp, x, varname)
        print("added variable "+varname+" "+str(x))
        return x
    elif isinstance(x, int):
        return x
    else: # fixme maybe a list if integer/bitvector
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
