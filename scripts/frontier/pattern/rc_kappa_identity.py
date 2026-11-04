# Algebra check: with rho_b = (-1)^b C(s,b)/C(k+b-1,b) and l = -s,
# kappa_j := sum_r (-1)^r C(k+j-1,j-r) C(l+j-1,r) sum_i (-1)^i C(r,i) rho_{j-r+i}  equals C(s,j)^2/C(k+j-1,j)
import sympy as sp
k,s=sp.symbols('k s')
def C(a,n):
    return sp.prod([a-i for i in range(n)])/sp.factorial(n)
rho=lambda b:(-1)**b*C(s,b)/C(k+b-1,b)
for j in range(0,9):
    kap=0
    for r in range(j+1):
        inner=sum((-1)**i*sp.binomial(r,i)*rho(j-r+i) for i in range(r+1))
        kap+=(-1)**r*C(k+j-1,j-r)*C(-s+j-1,r)*inner
    print(j,sp.simplify(kap-C(s,j)**2/C(k+j-1,j))==0,flush=True)
