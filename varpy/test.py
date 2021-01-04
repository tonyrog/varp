import varpy
import varpy.parser
import varpy.ast

def formula1():
    tree = varpy.parser.text("A or B")
    vp = varpy.new({})
    f = varpy.ast.build(vp, tree)
    varpy.bind(vp, f)
    varpy.bt_all(vp)


def formula2():
    tree = varpy.parser.text("(A and B) xor (A or B)")
    vp = varpy.new({})
    f = varpy.ast.build(vp, tree)
    varpy.bind(vp, f)
    varpy.bt_all(vp)
