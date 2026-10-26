"""Find low-degree representations f = A/B with A,B bihomogeneous in t1..t5 (+Q) for f in {g2, g3, z'}."""
import sys, itertools
sys.path.insert(0,'..')
from qs import *
from atkin_basis import basis
from fractions import Fraction
from flint import nmod_mat
M=900
def theta(a,M):
    c=[0]*M
    for k in range(-60,61):
        e=11*k*(k-1)//2+a*k
        if 0<=e<M: c[e]+=(-1)**(k%2)
    return S(fmpq_poly(c),0,M)
th={a:theta(a,M) for a in range(1,6)}
B=basis(M); targets={'g2':B['g2'],'g3':B['g3'],'z':B['z']}
w2={1:-10,2:-6,3:-3,4:-1,5:0}  # second grading *11, Q has weight 11
def monos(k):
    for m in itertools.combinations_with_replacement(range(1,6),k):
        yield m
def ser(m,e):
    s=const(1,M)
    for a in m: s=s*th[a]
    return S(s.p,s.v+e,s.N+e)
p=1000003
def md(x): x=fmpq(x); return (int(x.p)%p)*pow(int(x.q)%p,-1,p)%p
def co(s,n):
    try: return s.coeff(n)
    except: return 0
which=sys.argv[2] if len(sys.argv)>2 else 'g2'
f=targets[which]
K=int(sys.argv[1]) if len(sys.argv)>1 else 4
QS=int(sys.argv[3]) if len(sys.argv)>3 else 6
# group monomials by grading-2 weight class (mod 11 after Q-shifts): weight W = sum w2 + 11*e ; need A and B in same class
from collections import defaultdict
best=None
cls=defaultdict(list)
for m in monos(K):
    w=sum(w2[a] for a in m)
    for e in range(0,QS):
        cls[(w+11*e)].append((m,e))
for W,lst in cls.items():
    if len(lst)<2: continue
    cols=[]
    for (m,e) in lst:
        s=ser(m,e); cols.append(s); cols.append(f*s)   # unknowns: B coefficients (times f) and A coefficients
    rows=range(0,M-200)
    # equation: f*B - A = 0  -> columns [f*s for B] and [-s for A]
    colsE=[f*ser(m,e) for (m,e) in lst]+[ser(m,e) for (m,e) in lst]
    A=nmod_mat(len(rows),len(colsE),[md(co(c,n)) for n in rows for c in colsE],p)
    r=A.rank()
    if r<len(colsE):
        print("weight",W,"#monos",len(lst),"nullity",len(colsE)-r); sys.stdout.flush()

print("--- solutions ---")
from flint import fmpz_mat
for W,lst in cls.items():
    if len(lst)<2: continue
    colsE=[f*ser(m,e) for (m,e) in lst]+[ser(m,e) for (m,e) in lst]
    rows=range(0,M-200)
    A=fmpz_mat(len(rows),len(colsE),[int(fmpq(co(c,n))*1) if fmpq(co(c,n)).q==1 else 0 for n in rows for c in colsE])
    X,nul=A.nullspace()
    for j in range(nul):
        v=[int(X[i,j]) for i in range(len(colsE))]
        nb=len(lst)
        Bs=const(0,M)
        for i,(m,e) in enumerate(lst):
            if v[i]: Bs=Bs+v[i]*ser(m,e)
        nz=any(Bs.coeff(n)!=0 for n in range(0,M-100))
        if nz:
            Bt=" + ".join(f"{v[i]}*Q^{e}*{'*'.join('t'+str(a) for a in m)}" for i,(m,e) in enumerate(lst) if v[i])
            At=" + ".join(f"{-v[nb+i]}*Q^{e}*{'*'.join('t'+str(a) for a in m)}" for i,(m,e) in enumerate(lst) if v[nb+i])
            print("W",W,": f =",f"({At}) / ({Bt})")
