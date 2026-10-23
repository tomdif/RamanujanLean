# Sympy ansatz that finds the creative-telescoping certificate (P, Q) for isBaileyPair_f0 (MockTheta5F0Pair.lean).
import sympy as sp
q,x,y=sp.symbols('q x y')
R=(y-x)/(y*(1-q*x*y))
W=(1-x)*((1+x) - (1-x/y)*(1-x*y))
D=3
monos=[(i,j) for i in range(0,D+3) for j in range(-D-2,D+3)]
def sh(f): return f.subs(y,q*y)
cp=sp.symbols('p0:%d'%len(monos)); cq=sp.symbols('c0:%d'%len(monos))
P=sum(c*x**i*y**j for c,(i,j) in zip(cp,monos))
Qf=sum(c*x**i*y**j for c,(i,j) in zip(cq,monos))
eqs=[]
for e in ((y-1)*W - (R*sh(P)*q*y**3 - P), 2*W - 2*P + R*y*sh(Qf) + Qf):
    num=sp.numer(sp.together(e)); num=sp.expand(num*y**40)
    eqs+=sp.Poly(num,x,y).coeffs()
sol=list(sp.linsolve(eqs,list(cp)+list(cq)))
print(len(sol))
s=sol[0]; sub=dict(zip(list(cp)+list(cq),s))
Ps=sp.factor(P.subs(sub)); Qs=sp.factor(Qf.subs(sub))
fr=Ps.free_symbols|Qs.free_symbols
print('free',fr-{q,x,y})
z={c:0 for c in fr-{q,x,y}}
print('P =',sp.factor(Ps.subs(z))); print('Q =',sp.factor(Qs.subs(z)))
