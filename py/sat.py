# Satisfy formula

import varpy
import varpy.parser
import varpy.ast
import varpy.backjump

def file(file, vs={}):
    tree = varpy.parser.file(file)
    formula(tree, vs)
    
def text(text, vs={}):
    tree = varpy.parser.text(text)
    formula(tree, vs)

def formula(tree, vs={}):
    vp = varpy.new({})
    x = varpy.ast.build(vp, tree, vs)
    varpy.bind(vp, x)
    if varpy.bcp(vp) and varpy.bj(vp):
        print(varpy.model(vp))
        return True
    else:
        print("contradictory")
        return False
