import random
from sympy import jacobi_symbol as J, factorint
def kron12(e): return 0 if e%2==0 or e%3==0 else (1 if e%12 in (1,11) else -1)
def leg(a,q):
    a%=q
    return 0 if a==0 else (1 if pow(a,(q-1)//2,q)==1 else -1)
def sqf(t): return all(v==1 for v in factorint(t).values())
random.seed(1)
for (j,lam,Q) in [(13,5,5),(13,5,7),(17,7,11),(1,7,5),(1,9,7),(23,10,5)]:
    s=leg(12,Q)*leg((-1)**lam,Q)
    M=10**7
    a={}
    def A(m):
        if m<=0 or (m+j)%24: return 0
        if m not in a: a[m]=random.randint(-50,50)
        return a[m]
    def T(m):
        r=A(Q*Q*m)+s*leg(m,Q)*Q**(lam-1)*A(m)
        if m%(Q*Q)==0: r+=Q**(2*lam-1)*A(m//(Q*Q))
        return r
    def lift(f,t,n):
        return sum((J(d,t) if t>1 else 1)*d**(lam-1)*kron12(n//d)*f(t*(n//d)**2) for d in range(1,n+1) if n%d==0)
    ok=True
    ts=[t for t in range(1,24*40) if (t+j)%24==0 and sqf(t)][:12]
    for t in ts:
        for n in range(1,40):
            lhs=lift(T,t,n)
            rhs=kron12(Q)*(lift(A,t,Q*n)+(Q**(2*lam-1)*lift(A,t,n//Q) if n%Q==0 else 0))
            if lhs!=rhs: ok=False; print("FAIL",j,lam,Q,t,n); break
        if not ok: break
    print(j,lam,Q,"ts",ts[:6],"equivariant:",ok, "incl Q|t:", any(t%Q==0 for t in ts))
