# Aggregate size of the non-principal part on the Farey line Im tau = 1/N^2:
#   I(N) = \int_0^1 |f(q) - eps_K b(q)| dx,  q = e^{2 pi i (x + i/N^2)},  K = Farey denominator of the arc of x,
# i.e. exactly the quantity that the inequality-only circle method (Andrews66.arc_bound / Hb) must bound by
# |alpha(n) - P_N(n)| + (tail errors). Rademacher-style exactness by absolute-value bounds needs I(N) -> 0.
# Double precision is adequate for N <= 16 (|f| <= e^{pi N^2/48} <= 2e7).
import os, sys, math
os.environ.setdefault("OMP_NUM_THREADS","2")
import numpy as np
from fractions import Fraction as Fr
def farey(N):
    a,b,c,d=0,1,1,N; out=[(0,1)]
    while c<=N:
        k=(N+b)//d; a,b,c,d=c,d,k*c-a,k*d-b; out.append((a,b))
    return out
def run(N,M=60000):
    y=1.0/N**2
    F=farey(N)
    med=[(F[i][0]+F[i+1][0])/(F[i][1]+F[i+1][1]) for i in range(len(F)-1)]
    x=(np.arange(M)+0.5)/M
    idx=np.searchsorted(np.array(med),x)        # arc index into F; arcs of 0/1 and 1/1 merge (both K=1)
    K=np.array([F[i][1] for i in idx])
    eps=np.where(K%2==0, np.where((K//2)%2==0,1.0,-1.0), 0.0)
    q=np.exp(2j*np.pi*(x+1j*y))
    # f = sum q^{n^2}/(-q;q)_n^2
    f=np.zeros(M,complex); den=np.ones(M,complex); qn2=np.ones(M,complex); n=0
    while True:
        term=qn2/den**2
        f+=term
        if n>6*N and np.max(np.abs(term))<1e-14*max(1,np.max(np.abs(f))): break
        n+=1; den=den*(1+q**n); qn2=qn2*q**(2*n-1)
        if n>4000: break
    # b = (q;q)^3/(q^2;q^2)^2
    lb=np.zeros(M,complex); j=1
    while abs(math.exp(-2*math.pi*y*j))>1e-17:
        qj=q**j
        lb+=3*np.log(1-qj)-(2*np.log(1-qj*qj) if True else 0)
        j+=1
    b=np.exp(lb)
    r=np.abs(f-eps*b)
    return r.mean(), r.max(), np.abs(f).max()
for N in [2,3,4,6,8,11,13,16]:
    I,mx,fm=run(N)
    print("N=%2d  I(N)=int|f-eps b|dx=%.4f  max=%.3f  max|f|=%.3g  N^(1/2)=%.2f"%(N,I,mx,fm,math.sqrt(N)),flush=True)
