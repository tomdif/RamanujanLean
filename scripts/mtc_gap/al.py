# Laurent series in q with Fraction coeffs, truncated at exponent < T
from fractions import Fraction as Fr
T=120
def L(d): return {e:c for e,c in d.items() if c and e<T}
def lmul(a,b):
    r={}
    for e1,c1 in a.items():
        for e2,c2 in b.items():
            e=e1+e2
            if e<T: r[e]=r.get(e,0)+c1*c2
    return L(r)
def ladd(*xs):
    r={}
    for x in xs:
        for e,c in x.items(): r[e]=r.get(e,0)+c
    return L(r)
def lsc(c,a): return L({e:c*v for e,v in a.items()})
def linv(a):
    e0=min(a); c0=Fr(a[e0])
    # a = c0 q^e0 (1 + u)
    u={e-e0:Fr(c)/c0 for e,c in a.items() if e!=e0}
    # 1/(1+u) = sum (-u)^k ; u has positive exponents
    res={0:Fr(1)}; p={0:Fr(1)}
    global T
    Tsave=T; T=Tsave+abs(e0)+5
    for k in range(1,Tsave+abs(e0)+5):
        p=lmul(p,lsc(-1,u))
        if not p: break
        res=ladd(res,p)
    T=Tsave
    return L({e-e0:c/c0 for e,c in res.items()})
def geom_inv(s,e):  # 1/(1 - s q^e)
    if e>0:
        return L({e*k: Fr(s)**k for k in range(0, T//e+2)})
    if e<0:  # = -s^{-1} q^{-e} / (1 - s^{-1} q^{-e})
        f=-e; si=Fr(1)/s
        return L({f*k: -(si)**k for k in range(1, T//f+2)})
    raise ZeroDivisionError
def j(s,a,Q):  # j(s q^a; q^Q) = sum (-1)^n q^{Q n(n-1)/2} (s q^a)^n
    r={}
    for n in range(-60,61):
        e=Q*n*(n-1)//2+a*n
        if e<T: r[e]=r.get(e,0)+(-1)**n*Fr(s)**n
    return L(r)
def m(xs,xa,Q,zs,za):  # m(x,q^Q,z), x=xs q^xa, z=zs q^za
    tot={}
    for r in range(-40,41):
        e=Q*r*(r-1)//2+za*r
        num={e: (-1)**r*Fr(zs)**r}
        if e>T+400: continue
        den=geom_inv(xs*zs, Q*(r-1)+xa+za)
        tot=ladd(tot,lmul(num,den))
    return lmul(linv(j(zs,za,Q)),tot)
def J(a,mm): return j(1,a,mm)   # J_{a,m}=j(q^a;q^m)
def Jm(mm): # J_m = (q^m;q^m)_inf
    r={0:Fr(1)}
    for k in range(1,T//mm+2): r=lmul(r,{0:Fr(1),mm*k:Fr(-1)})
    return r
def show(a,n=25): return [a.get(e,0) for e in range(min(a) if a else 0, n)]
