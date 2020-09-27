import varc
import varpy
import varpy.parser
import varpy.ast
import varpy.backjump
import varpy.saturate
import time


#formula='C:/Users/gunna/OneDrive/Skrivbord/varp-formler/formula_GTn.py'
#formula='C:/Users/gunna/OneDrive/Skrivbord/varp-formler/formula_super.py'
#formula='C:/Users/gunna/OneDrive/Skrivbord/varp-formler/formulaRR.py'
#formula='C:/Users/gunna/OneDrive/Skrivbord/varp-program/miniform.py'

formula='/home/tony/erlang/varp/formulas/gunnar/RR.varp'

dom={}
dom['n']=4
dom['k']=6

def parse_formula(formula):

     tree = varpy.parser.file(formula)
     #print(tree)
     vp = varpy.new({})
     f=varpy.ast.build(vp, tree, dom)
     varpy.set_level(vp, 0)
     varpy.bind(vp, f)
     print('start')

     return vp

def one_lap_dilemma(vp):
     #varpy.config(vp,'xref',True)
     x=varpy.next_unbound(vp)
     varpy.set_level(vp, 0)
     flag=0 #flag keep track of changes
     while x!=False:
          a=varpy.saturate.saturate_var(vp,x)
          varpy.set_level(vp, 0)
          if a==False:
               print('unsatisfiable')
               break
          else:
               if len(a)>0:
                    for j in a:
                         if isinstance(j,int):
                              print("bind "+str(a))
                              varpy.bind(vp,j)
                              flag=flag+1

                         else:
                              print("subst "+str(j[0])+"/"+str(j[1]))
                              varpy.subst(vp,j[0],j[1])
                              flag=flag+1

          x=varpy.next_unbound(vp,x)
          
     return flag

def num_unbound(vp):
     return varpy.info(vp,'number_of_unbound_variables')

def one_saturate(vp):
     flag=1
     varpy.config(vp,'xref',True)
     varpy.set_level(vp, 0)
     n=0 # n no. of laps
     while (num_unbound(vp) > 0) and flag>0:
          # flag=0
          flag=one_lap_dilemma(vp)
          if not flag:
               break
          else:
               #vp=p[0]
               #flag=p[1]
               n=n+1
               print(n)
               print(flag)

     return vp

vp=parse_formula(formula)
if varpy.bcp(vp):
     U=time.time()
     one_saturate(vp)
     print(varpy.next_unbound(vp,1))
     y=num_unbound(vp)
     print(y)

     print(vp)

     print("--- %s seconds ---" % format((time.time() - U),'.2f'))
else:
     print('unsatisfiable')

