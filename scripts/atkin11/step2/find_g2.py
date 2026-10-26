"""Search: g2 (Atkin) as a Z-combination of Gamma0(11)-orbit sums of modular-unit monomials q^c prod eta_a^{n_a},
eta_a = (q^a, q^{11-a}; q^11)_inf, a=1..5."""
import sys, itertools
sys.path.insert(0,'..')
from qs import *
from fractions import Fraction
from atkin_basis import basis
M=400
def eta_a(a,M):
    p=fmpq_poly([1])
    for n in range(M):
        for e in (11*n+a, 11*n+11-a):
            if e<M: p=fmpq_poly((p*fmpq_poly([1]+[0]*(e-1)+[-1])).coeffs()[:M])
    return S(p,0,M)
H={a:eta_a(a,M) for a in range(1,6)}
Hi={a:H[a].inv() for a in range(1,6)}
def ea(a): return Fraction(a*a,22)-Fraction(a,2)+Fraction(11,12)
def red(a):
    a%=11; return min(a,11-a)
def mono(n):  # n dict a->exp ; returns (q-exponent, series) or None if non-integral
    c=sum(ea(a)*k for a,k in n.items())
    if c.denominator!=1: return None
    s=const(1,M)
    for a,k in n.items():
        b = H[a] if k>0 else Hi[a]
        for _ in range(abs(k)): s=s*b
    return int(c), s
def orbit(n):
    out=[]; cur=dict(n)
    for k in range(5):
        out.append(dict(cur)); cur={red(2*a):e for a,e in cur.items()}
    return out
B=basis(M); g2=B['g2']; z=B['z']
cands=[]; names=[]
R=2
seen=set()
for n in itertools.product(range(-R,R+1),repeat=5):
    if all(x==0 for x in n): continue
    d={a+1:n[a] for a in range(5) if n[a]!=0}
    key=tuple(sorted(tuple(sorted(o.items())) for o in orbit(d)))
    if key in seen: continue
    seen.add(key)
    terms=[mono(o) for o in orbit(d)]
    if any(t is None for t in terms): continue
    # trace (signs ignored for now: try sum and alternating later)
    tr=None
    for c,s in terms:
        t=S(s.p,s.v+c,s.N+c)
        tr=t if tr is None else tr+t
    lo=tr.lead()[0]
    if lo is None or lo<-3 or lo>12: continue
    cands.append(tr); names.append(d)
print(len(cands),"orbit traces")
from flint import nmod_mat
p=1000003
def md(x): return (int(x.p)%p)*pow(int(x.q)%p,-1,p)%p
cols=cands+[const(1,M)]
rows=range(-5,300)
def co(s,n):
    try: return s.coeff(n)
    except: return 0
A=nmod_mat(len(rows),len(cols),[md(fmpq(co(c,n))) for n in rows for c in cols],p)
for tname,target in [('g2',g2),('z',z)]:
    Ab=nmod_mat(len(rows),len(cols)+1,[md(fmpq(co(c,n))) for n in rows for c in cols+[target]],p)
    print(tname,"in span:",A.rank()==Ab.rank(),A.rank(),Ab.rank())
