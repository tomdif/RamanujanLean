import sys; sys.path.insert(0,'.')
from katzmat import Katz
from flint import fmpz_mat, nmod_mat, fmpz_poly
import sympy
for p in [29,31,37,41,43,47,53,59]:
    K=Katz(p,4,6); Um,Dm=K.matrices(); X=Dm*Um; mod=K.mod
    cp=fmpz_mat([[int(x) for x in r] for r in X.tolist()]).charpoly()
    # factor charpoly over Z_p: slope-1 roots mu = lambda/p mod p.  Use Newton: scale poly
    x=sympy.symbols('x'); co=[int(c)%mod for c in cp.coeffs()]  # low->high
    n=len(co)-1; P=sum(co[i]*x**i for i in range(n+1))
    # number of unit roots r: smallest k with v(e_k)... simpler: reduce Q(y)=P(p*y)/p^{n-r} ... use p-adic factor via sympy Poly mod p^4 hensel not trivial;
    # Instead: slope-1 part mod p: with r unit roots, coefficient pattern; compute Q(y) = P(p y) / p^{(n - r - s)}..., skip: print vals
    from zmod import val
    vals=[val(co[n-k],p,4) for k in range(n+1)]
    print(p, vals[:8])
print('mu check')
for p,r in [(29,1),(31,1),(37,2),(41,2),(43,2),(47,2)]:
    K=Katz(p,4,6); Um,Dm=K.matrices(); X=Dm*Um; mod=K.mod
    cp=fmpz_mat([[int(x) for x in rr] for rr in X.tolist()]).charpoly()
    co=[int(c)%mod for c in cp.coeffs()]; n=len(co)-1
    e=lambda k: ((-1)**k*co[n-k])%mod
    mu=(e(r+1)//p)*pow(e(r),-1,p)%p
    print(p,'mu=lambda_slope1/l mod l =',mu)
