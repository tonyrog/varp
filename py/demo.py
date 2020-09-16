
import varpy
vp = varpy.new({})
v1 = varpy.add_variable(vp)
v2 = varpy.add_variable(vp)
v3 = varpy.add_variable(vp)
varpy.add_symbol(vp, v1, "A")
varpy.add_symbol(vp, v2, "B")
varpy.add_symbol(vp, v3, "C")
varpy.bind(vp, v1)
varpy.bind(vp, v3)
print(varpy.model(vp))



