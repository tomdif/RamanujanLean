# express 1/G = E(Q)^2/(Q E(Q^13)^2) via J_a = theta(Q^a;Q^13), a=1..6, as combination of degree-0 Laurent monomials
import itertools, sympy as sp
L=80
def mul(a,b):
    c=[0]*L
    for i,x in enumerate(a):
        if x:
            for j in range(L-i): c[i+j]+=x*b[j]
    return c
def inv(a):
    # a[0] may be 0: return (shift, series)
    s=next(i for i,x in enumerate(a) if x)
    a2=a[s:]+[0]*s
    assert a2[0] in (1,-1)
    b=[0]*L; b[0]=a2[0]
    for m in range(1,L): b[m]=-a2[0]*sum(a2[j]*b[m-j] for j in range(1,m+1))
    return s,b
def J(a):
    s=[1]+[0]*(L-1)
    for n in range(L):
        for t in (a+13*n, 13-a+13*n, 13+13*n):
            if t<L:
                f=[0]*L; f[0]=1; f[t]=-1; s=mul(s,f)
    return s
Js={a:J(a) for a in range(1,7)}
# Laurent series rep: (valuation, coeffs)
def lmul(x,y): return (x[0]+y[0], mul(x[1],y[1]))
def linv(x):
    s,b=inv(x[1]); return (-x[0]-s, b)
def lnorm(x):
    s=next(i for i,c in enumerate(x[1]) if c); return (x[0]+s, x[1][s:]+[0]*s)
Jl={a:lnorm((0,Js[a])) for a in Js}
E=[0]*L
for k in range(-30,31):
    e=k*(3*k-1)//2
    if 0<=e<L: E[e]+=(-1)**(k%2)
E13=[0]*L
for i in range(0,L,13): E13[i]=E[i//13]
s,iE13=inv(E13)
w=mul(E,iE13); target=(-1, mul(w,w))  # E(Q)^2/(Q E(Q^13)^2)
# monomials prod J_a^{n_a}, sum n_a = 0, |n_a|<=2
mons=[]
for ns in itertools.product(range(-2,3),repeat=6):
    if sum(ns)!=0: continue
    m=(0,[1]+[0]*(L-1))
    for a,n in zip(range(1,7),ns):
        for _ in range(abs(n)):
            m=lmul(m, Jl[a] if n>0 else linv(Jl[a]))
    m=lnorm(m)
    if m[0]>=-1: mons.append((ns,m))
print(len(mons))
# solve target = sum coef*mon over Laurent coefficients from Q^-1 .. Q^K
K=40
def vec(m):
    v=[0]*(K+2)
    for i,c in enumerate(m[1]):
        e=m[0]+i
        if -1<=e<=K: v[e+1]=c
    return v
A=sp.Matrix([vec(m) for _,m in mons]).T
bvec=sp.Matrix(vec(lnorm(target)))
# least-support: try sympy solve via gauss
sol=A.gauss_jordan_solve(bvec)
x,params=sol
x=x.subs({p:0 for p in params})
for (ns,_),c in zip(mons,x):
    if c!=0: print(ns,c)
