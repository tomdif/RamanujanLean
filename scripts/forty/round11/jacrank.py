"""Local test: rank of the Jacobian of the relation set at the true point (q=0.07), and whether
the target's gradient lies in its row span (necessary for the target to follow locally)."""
import sympy as sp, mpmath as mp, sys
mp.mp.dps=40
exec(open('ideal15.py').read().split("target=")[0])
target=p1*m3*p7*m21-m1*p3*m7*p21-2*q*L
q0=mp.mpf('0.07')
def chim_(k,x): return mp.nprod(lambda n: 1-x**(k*(2*n+1)), [0, mp.inf])
def chip_(k,x): return mp.nprod(lambda n: 1+x**(k*(2*n+1)), [0, mp.inf])
vals={q:q0}
for k,(pp,mm) in {1:(p1,m1),3:(p3,m3),7:(p7,m7),21:(p21,m21)}.items():
    vals[pp]=chip_(k,q0); vals[mm]=chim_(k,q0)
vals[L]=(vals[p1]*vals[m3]*vals[p7]*vals[m21]-vals[m1]*vals[p3]*vals[m7]*vals[p21])/(2*q0)
X=[L,p1,m1,p3,m3,p7,m7,p21,m21]
use=sys.argv[1].split(',')
rows=[]
for k in use:
    e=num(rels[k]); print(k,'residual',mp.nstr(sp.lambdify(list(vals),e,'mpmath')(*vals.values()),5))
    rows.append([sp.lambdify(list(vals),sp.diff(e,x),'mpmath')(*vals.values()) for x in X])
M=mp.matrix(rows)
tg=[sp.lambdify(list(vals),sp.diff(target,x),'mpmath')(*vals.values()) for x in X]
def rank(M):
    U,S,V=mp.svd_r(M); return sum(1 for s in S if abs(s)>mp.mpf(10)**-25), S
r,S=rank(M); r2,S2=rank(mp.matrix(rows+[tg]))
print('vars',len(X),'rank',r,'rank+target',r2)
