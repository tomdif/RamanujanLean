# degree-6 relation space among a,b,c,d (series), as nullspace over Q
import itertools, sympy as sp, pickle
N=1200
def cls(r):
    s=[0]*N
    for n in range(-N,N+1):
        e=(7*n+r)**2
        if e<N: s[e]+=1
    return s
import numpy as np
T=[np.array(cls(r),dtype=object) for r in range(4)]
def mul(A,B):
    C=np.zeros(N,dtype=object)
    nz=[(i,x) for i,x in enumerate(A) if x]
    for i,x in nz:
        C[i:]+=x*B[:N-i]
    return C
mons=[m for m in itertools.product(range(7),repeat=4) if sum(m)==6]
cache={}
def ser(m):
    if m in cache: return cache[m]
    if sum(m)==0:
        r=np.zeros(N,dtype=object); r[0]=1; return r
    i=next(k for k in range(4) if m[k]>0)
    m2=list(m); m2[i]-=1
    r=mul(T[i],ser(tuple(m2))); cache[m]=r; return r
S=sp.Matrix([[int(x) for x in ser(m)] for m in mons]).T  # N x 84
ns=S.nullspace()
print(len(mons),len(ns))
pickle.dump((mons,[list(v) for v in ns]),open('rels6.pkl','wb'))
