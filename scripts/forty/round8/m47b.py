import lib; lib.P=500
from lib import *
import sympy as sp
P=lib.P
Q=47
fp=lambda k: f((1,k),(-1,2*k))
basis={
 'phph':mul(phi(1),phi(Q)), 'phph-':mul(phi(1,-1),phi(Q,-1)), 'ff-':mul(fm(1),fm(Q)), 'f4f4':mul(fm(4),fm(4*Q)),
 'ps2ps2':mul(psi(2),psi(2*Q)), 'psps':mul(psi(1),psi(Q)), 'psps-':mul(psi(1,-1),psi(Q,-1)), 'ph2ph2-':mul(phi(2,-1),phi(2*Q,-1)),
 'ff2':mul(fm(2),fm(2*Q)),
}
target=mul(fp(1),fp(Q))
cols=[];names=[]
for nm,s in basis.items():
    for k in range(0,40):
        cols.append(sh(k,s)); names.append((nm,k))
N=420
import numpy.linalg as la
M=sp.Matrix([[int(c[i]) for c in cols] for i in range(N)])
b=sp.Matrix([int(target[i]) for i in range(N)])
print(M.shape)
try:
    sol,params=M.gauss_jordan_solve(b)
    print("solvable; free params", len(params))
    sol0=sol.subs({p:0 for p in params})
    print([(names[i],sol0[i]) for i in range(len(names)) if sol0[i]!=0])
except ValueError as e:
    print("not solvable")
