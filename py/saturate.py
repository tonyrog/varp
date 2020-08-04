# functions to 1-"saturate" a formula
import varpy

def saturate_var(vp, x):
    varpy.set_level(vp, 1)
    varpy.bind(vp, x)
    varpy.set_level(vp, 2)
    varpy.bcp(vp)
