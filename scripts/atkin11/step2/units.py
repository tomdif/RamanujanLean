"""Gamma1(11) modular units q^c prod eta_a^{n_a}: integrality lattice; search Gamma0(11)-traces spanning g2."""
import sys, itertools
sys.path.insert(0,'..')
from qs import *
from fractions import Fraction
from atkin_basis import basis
M=500
def eta_a(a,M):
    p=fmpq_poly([1])
    for n in range(M):
        for e in (11*n+a, 11*n+11-a):
            if e<M: p=fmpq_poly((p*fmpq_poly([1]+[0]*(e-1)+[-1])).coeffs()[:M])
    return S(p,0,M)
H={a:eta_a(a,M) for a in range(1,6)}
Hi={a:H[a].inv() for a in range(1,6)}
def ea(a): return Fraction(6*a*a-66*a+121,132)
def red(a):
    a%=11; return min(a,11-a)
cache={}
def pw(a,k):
    if (a,k) in cache: return cache[(a,k)]
    if k==0: r=const(1,M)
    elif k>0: r=pw(a,k-1)*H[a]
    else: r=pw(a,k+1)*Hi[a]
    cache[(a,k)]=r; return r
def mono(n):
    c=sum(ea(a)*k for a,k in zip(range(1,6),n))
    if c.denominator!=1: return None
    s=const(1,M)
    for a,k in zip(range(1,6),n): s=s*pw(a,k)
    return S(s.p,s.v+int(c),s.N+int(c))
def rot(n):  # a -> 2a : new exponent at red(2a) = old at a
    m=[0]*5
    for a in range(1,6): m[red(2*a)-1]=n[a-1]
    return tuple(m)
B=basis(M); g2=B['g2']; z=B['z']; g3=B['g3']
R=int(sys.argv[1]) if len(sys.argv)>1 else 6
seen=set(); traces=[]; names=[]
for n in itertools.product(range(-R,R+1),repeat=5):
    if sum(n)%12: continue
    orb=[n]; 
    for _ in range(4): orb.append(rot(orb[-1]))
    key=min(orb)
    if key in seen: continue
    seen.add(key)
    ms=[mono(o) for o in orb]
    if any(m is None for m in ms): continue
    lo=min(m.lead()[0] for m in ms)
    if lo<-2: continue
    tr=ms[0]
    for m in ms[1:]: tr=tr+m
    traces.append(tr); names.append(n)
print(len(traces),"traces with order >= -2")
from flint import nmod_mat
p=1000003
def md(x): x=fmpq(x); return (int(x.p)%p)*pow(int(x.q)%p,-1,p)%p
def co(s,n):
    try: return s.coeff(n)
    except: return 0
cols=traces+[const(1,M)]
rows=range(-3,M-60)
A=nmod_mat(len(rows),len(cols),[md(co(c,n)) for n in rows for c in cols],p)
for tname,target in [('g2',g2),('g3',g3),('z',z)]:
    Ab=nmod_mat(len(rows),len(cols)+1,[md(co(c,n)) for n in rows for c in cols+[target]],p)
    print(tname,"in span:",A.rank()==Ab.rank(),A.rank(),Ab.rank())
