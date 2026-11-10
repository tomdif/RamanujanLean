# numeric check of the decomposition of the two R-identities for Entry 3.29 (t = q level)
import lib; lib.P=700
from lib import *
P=lib.P
def ng(a): return np.array([x*(-1)**i for i,x in enumerate(a)],dtype=np.int64)
def th(N,e,c=1):  # theta_N(e,c) = sum (-1)^k c^k t^{N C(k,2)+ek}
    o=z()
    for k in range(-400,401):
        E=N*k*(k-1)//2+e*k
        if 0<=E<P: o[E]+=(-1)**(k%2)*(c**(k%2))
        elif E<0 and abs(k)<399: raise Exception(("neg",N,e,k))
    return o
Q=23
A=lambda s=1: None
GA=add(mul(G(2),G(Q)), sh(5,mul(H(2),H(Q))))
GB=sub(mul(G(2*Q),H(1)), sh(9,mul(G(1),H(2*Q))))
A1=GA; A2=subq(GA,2); A4=subq(GA,4); Am=ng(GA); Bm2=subq(GB,2,-1)
F=lambda k: fm(k)
# det-10 groups (sign (1,0) / (0,1) differ by sign of odd groups)
g6=mul(th(20,6), add(th(1380,644), sh(92,th(1380,184))))
g2=mul(th(20,2), sub(sh(38,th(1380,368)), sh(130,th(1380,92))))
g10=sh(18,mul(th(20,10),th(1380,460)))
g8=mul(th(20,8), add(sh(2,th(1380,598)), sh(48,th(1380,322))))
g4=mul(th(20,4), add(sh(12,th(1380,506)), sh(150,th(1380,46))))
Ye=add(g6,g2,g10); Yo=add(g8,g4)
fQ20=th(1380,460)
# expected: Ye = f(-t^4)f(-Q^4) A(t^4) B(-t^2) / f(-Q^20) * (t-power?) ; check ratios
def ratio(a,b): 
    nz=np.nonzero(b)[0][0]; na=np.nonzero(a)[0][0]
    return na-nz
X=mul(mul(F(4),F(4*Q)),mul(A4,Bm2))
print("Ye shift", ratio(Ye,mul(X,fQ20)), eq(sh(ratio(Ye,mul(X,fQ20)),mul(X,fQ20))[:600],Ye[:600]))
Xo=mul(mul(F(4),F(4*Q)),A2)
r=ratio(Yo,mul(Xo,fQ20)); print("Yo shift",r, eq(sh(r,mul(Xo,fQ20))[:600],Yo[:600]), eq(sc(-1,sh(r,mul(Xo,fQ20)))[:600],Yo[:600]))
# det-5 sides
d5p = add(mul(th(230,92), sub(th(30,14,-1), sh(2,th(30,4,-1)))), sc(-1,sh(10,mul(th(230,46), sub(sh(2,th(30,2,-1)), th(30,8,-1))))))
X5=mul(mul(F(2),F(2*Q)),A2)
print("d5+ vs f f A(t^2) *f(-t^10)", ratio(d5p,mul(X5,th(30,10))), eq(mul(X5,th(30,10))[:600], d5p[:600]))
print("L(1,0):", eq(d5p[:600], sub(Ye,Yo)[:600]))
print("Ye=X", eq(Ye[:600],X[:600]), "Yo=t^2 Xo", eq(Yo[:600],sh(2,Xo)[:600]), "d5=X5", eq(d5p[:600],X5[:600]))
d5m = None
def ths(s,N,e,c=1):
    o=z()
    for k in range(-400,401):
        E=N*k*(k-1)//2+e*k+s
        if 0<=E<P: o[E]+=(-1)**(k%2)*(c**(k%2))
        elif E<0: raise Exception("neg")
    return o
def tt(s,N1,e1,c1,N2,e2,c2):
    # t^s theta theta, allowing negative partial exponents: compute product via shifting
    a=ths(100,N1,e1,c1); b=ths(100,N2,e2,c2)
    return sh(s-200,mul(a,b)) if s-200<0 else None
terms=[(18,230,184,-1,30,38,1),(2,230,138,-1,30,26,1),(0,230,92,-1,30,14,1),(12,230,46,-1,30,2,1),(38,230,0,-1,30,-10,1)]
d5m=sum(tt(*x) for x in terms)
AA=mul(mul(GA,ng(GA)),mul(F(2),F(2*Q)))
print("d5(0,1)=A(t)A(-t)ff", eq(d5m[:500],AA[:500]), "L(0,1)", eq(d5m[:500],add(Ye,Yo)[:500]))
