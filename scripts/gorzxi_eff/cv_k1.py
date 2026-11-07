import sympy as sp, mpmath as mp
x,u=sp.symbols('x u',positive=True)
# term k: phi_k = e^{u/2} f(Kx) * K^{-1/2}?  compute directly: phi_k = e^{u/2}(2K^2x^2-3Kx)e^{-Kx}, x=pi e^{2u}
def derivs(K):
    f=(2*K**2*x**2-3*K*x)  # times e^{-Kx} e^{u/2}
    # operator: d/du (e^{u/2} p(x) e^{-Kx}) = e^{u/2} e^{-Kx} (p/2 + 2x p' - 2K x p)
    Dop=lambda p: sp.expand(p/2+2*x*sp.diff(p,x)-2*K*x*p)
    p0=f;p1=Dop(p0);p2=Dop(p1)
    return p0,p1,p2
p0,p1,p2=derivs(1)
A=sp.expand(p0*p1); B=sp.expand(p1**2-p0*p2)
print("A=",sp.factor(A)); print("B=",sp.factor(B))
print("roots A",[r for r in sp.Poly(A,x).nroots() if abs(sp.im(r))<1e-12])
print("roots B",[r for r in sp.Poly(B,x).nroots() if abs(sp.im(r))<1e-12])
import math
for uu in [0.0,0.05,0.1,0.15,0.2,0.25,0.3,0.4,0.5]:
    xx=math.pi*math.exp(2*uu)
    a=float(A.subs(x,xx)); b=float(B.subs(x,xx)); print(uu, xx, a, b, a+uu*b)
