"""Relations among f(q^n) = (q^n, q^{11-n}, q^11; q^11)_inf (theta, nome q^11).
Compare: all degree-2 relations (with q-power coefficients) vs those spanned by Weierstrass 3-term relations."""
import sys, itertools
sys.path.insert(0,'..')
from qs import *
from flint import nmod_mat
M=int(sys.argv[2]) if len(sys.argv)>2 else 400
def f_series(n,M):
    # f(x) = (x, q^11/x, q^11; q^11) at x=q^n, via JTP: sum_k (-1)^k q^{11 k(k-1)/2} x^k
    c=[0]*M; 
    for k in range(-40,41):
        e=11*k*(k-1)//2+n*k
        if 0<=e<M: c[e]+=(-1)**(k%2)
    # may have negative exponents for n<0 or n>11; restrict n in 1..10
    return S(fmpq_poly(c),0,M)
th={a:f_series(a,M) for a in range(1,6)}
def f_of(n):
    # reduce n mod 11 with quasi-periodicity: f(q^{n+11}) = -q^{-n} f(q^n); f(q^{11-n}) = f(q^n); f(q^0)=0
    sign=1; shift=0
    while n>=11: n-=11; sign=-sign; shift-=n  # f(q^{n+11})=-q^{-n}f(q^n)
    while n<0: n+=11; sign=-sign; shift+=n-11  # from f(q^{m}) with m=n_old... handled by inverse
    return n,sign,shift
# simpler: compute f(q^n) series directly for any n via JTP with Laurent support
def fL(n,M,off=200):
    c={}
    for k in range(-60,61):
        e=11*k*(k-1)//2+n*k
        if e<M: c[e]=c.get(e,0)+(-1)**(k%2)
    lo=min(c); 
    arr=[0]*(M-lo)
    for e,v in c.items(): arr[e-lo]+=v
    return S(fmpq_poly(arr),lo,M)
p=1000003
def md(x): x=fmpq(x); return (int(x.p)%p)*pow(int(x.q)%p,-1,p)%p
def co(s,n):
    try: return s.coeff(n)
    except: return 0
# all degree-2 monomials in th1..th5 times q^e, e in 0..E
E=int(sys.argv[1]) if len(sys.argv)>1 else 10
monos=list(itertools.combinations_with_replacement(range(1,6),2))
cols=[]
for m in monos:
    s=const(1,M)
    for a in m: s=s*th[a]
    for e in range(E+1): cols.append(S(s.p,s.v+e,s.N+e))
rows=range(0,M-E-5)
A=nmod_mat(len(rows),len(cols),[md(co(c,n)) for n in rows for c in cols],p)
r=A.rank()
print("degree-2: #cols",len(cols),"rank",r,"-> relation dim",len(cols)-r)
# Weierstrass three-term: f(ab)f(a/b)f(cd)f(c/d) - f(ac)f(a/c)f(bd)f(b/d) - (b/c) f(ad)f(a/d)f(bc)f(b/c) = 0 (x=q^.)
cnt=0; W=[]
for a,b,c_,d in itertools.product(range(0,12),repeat=4):
    t1=fL(a+b,M)*fL(a-b,M)*fL(c_+d,M)*fL(c_-d,M)
    t2=fL(a+c_,M)*fL(a-c_,M)*fL(b+d,M)*fL(b-d,M)
    t3=fL(a+d,M)*fL(a-d,M)*fL(b+c_,M)*fL(b-c_,M)
    rel=t1-t2-S(t3.p,t3.v+b-c_,t3.N+b-c_)
    ok=all(co(rel,n)==0 for n in range(-50,150))
    if not ok: print("3-term FAIL",a,b,c_,d); break
    cnt+=1
print("three-term relations verified:",cnt)
