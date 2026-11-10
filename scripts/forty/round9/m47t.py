import sys; sys.path.insert(0,'../round8')
import numpy as np, sympy as sp
import lib; lib.P=600
from lib import *
P=600
def th(a,b,c,R=40):
    o=np.zeros(P,dtype=np.int64)
    for x in range(-R,R+1):
        for y in range(-R,R+1):
            E=a*x*x+b*x*y+c*y*y
            if E<P: o[E]+=1
    return o
t1,t2,t3=th(1,1,12),th(2,1,6),th(3,1,4)
F=sh(2,mul(fm(1),fm(47)))
M=sp.Matrix([[int(t1[i]),int(t2[i]),int(t3[i])] for i in range(40)])
sol=M.solve_least_squares(sp.Matrix([int(F[i]) for i in range(40)]))
print(sol.T)
a,b,c=sol
print(all(a*t1[i]+b*t2[i]+c*t3[i]==F[i] for i in range(P)))
