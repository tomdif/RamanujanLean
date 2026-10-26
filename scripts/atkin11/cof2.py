from sympy import symbols, expand, Poly, linsolve
g2,g3,z=symbols('g2 g3 z')
R1=g2*g3-(g2**2-g3+11*z); R2=g3**2-(g2**3-g2*g3-z)
goals=[(g2*g2,g2**2),(g2*g3,g2**2-g3+11*z),(g2*(g2*(g2**2-g3)),z+12*z*g2+11*z*g3),(g3*g2,g2**2-g3+11*z),(g3*g3,g2*(g2**2-g3)-z),
(g3*(g2**2-g3),z+11*z*g2),(g3*(g2*(g2**2-g3)),z*g2+11*z*g3+11*z*(g2**2-g3)),((g2**2-g3)*g2,g2*(g2**2-g3)),((g2**2-g3)*g3,z+11*z*g2),
((g2**2-g3)**2,z*g2+11*z*g3),((g2**2-g3)*g2*(g2**2-g3),z*g3+12*z*(g2**2-g3)+121*z**2)]
def monos(d): return [g2**i*g3**j*z**k for i in range(d+1) for j in range(d+1) for k in range(d+1) if i+j+k<=d]
res=set()
for L,R in goals:
    diff=expand(L-R)
    for deg in range(0,5):
        ms=monos(deg); A=symbols('a0:%d'%len(ms)); B=symbols('b0:%d'%len(ms))
        a=sum(x*m for x,m in zip(A,ms)); b=sum(x*m for x,m in zip(B,ms))
        sol=linsolve(Poly(expand(a*R1+b*R2-diff),g2,g3,z).coeffs(),*(A+B))
        if sol:
            s=[v.subs({f:0 for f in v.free_symbols}) for v in list(sol)[0]]
            aa=expand(sum(v*m for v,m in zip(s[:len(ms)],ms))); bb=expand(sum(v*m for v,m in zip(s[len(ms):],ms)))
            res.add(f"linear_combination ({aa}) * h1 + ({bb}) * h2".replace('**','^')); break
for r in res: print(r)
