"""Is M7 (chi(q)chi(q^7)-chi(-q)chi(-q^7) = 2q/(chi(-q^2)chi(-q^14))) locally implied by entries 3.2, 3.9, 3.10, 3.20
at +-q, q^2, q^7 (Cramer-type consequences)?  Jacobian span test at q=0.07."""
import sympy as sp, mpmath as mp
mp.mp.dps=40
q0=mp.mpf('0.07')
def Pi(f): return mp.nprod(f,[0,mp.inf])
def Gv(x): return 1/Pi(lambda n:(1-x**(5*n+1))*(1-x**(5*n+4)))
def Hv(x): return 1/Pi(lambda n:(1-x**(5*n+2))*(1-x**(5*n+3)))
def chim(x): return Pi(lambda n:1-x**(2*n+1))
q=sp.Symbol('q')
args=[1,-1,2,4,7,-7,14,28,8,-4]
GS={a:sp.Symbol(f'G{a}'.replace('-','n')) for a in args}; HS={a:sp.Symbol(f'H{a}'.replace('-','n')) for a in args}
def x(a): return q0**a if a>0 else -(q0**(-a))
vals={q:q0}
for a in args: vals[GS[a]]=Gv(x(a)); vals[HS[a]]=Hv(x(a))
p1,m1,p7,m7=sp.symbols('p1 m1 p7 m7')
vals[p1]=chim(-q0); vals[m1]=chim(q0); vals[p7]=chim(-q0**7); vals[m7]=chim(q0**7)
m2=p1*m1; m14=p7*m7
m4=sp.Symbol('m4'); vals[m4]=chim(q0**4); p2=m4/m2
G,H=GS,HS
rels=[
 G[7]*H[2]-q*G[2]*H[7]-m1/m7,             # 3.9
 G[-7]*H[2]+q*G[2]*H[-7]-p1/p7,           # 3.9(-q)
 G[1]*G[14]+q**3*H[1]*H[14]-m7/m1,        # 3.10
 G[-1]*G[14]-q**3*H[-1]*H[14]-p7/p1,      # 3.10(-q)
 G[1]*G[4]+q*H[1]*H[4]-p1**2,             # 3.2
 G[-1]*G[4]-q*H[-1]*H[4]-m1**2,           # 3.2(-q)
 G[7]*G[28]+q**7*H[7]*H[28]-p7**2,
 G[-7]*G[28]-q**7*H[-7]*H[28]-m7**2,
 G[1]*H[-1]+G[-1]*H[1]-2/m2**2,           # 3.20
 G[7]*H[-7]+G[-7]*H[7]-2/m14**2,
 G[14]*H[4]-q**2*G[4]*H[14]-m2/m14,       # 3.9(q^2)
 G[2]*G[28]+q**6*H[2]*H[28]-m14/m2,       # 3.10(q^2)
 G[2]*G[8]+q**2*H[2]*H[8]-p2**2,          # 3.2(q^2)
 G[8]*G[-4]+q**4*H[8]*H[-4]*0+0,          # placeholder removed below
]
rels=rels[:-1]
target=(p1*p7-m1*m7)*m2*m14-2*q
X=[v for v in vals if v!=q]
def ev(e): return sp.lambdify(list(vals),e,'mpmath')(*vals.values())
for r in rels: assert abs(ev(r))<1e-30, r
M=mp.matrix([[ev(sp.diff(r,v)) for v in X] for r in rels])
def rank(M):
    U,S,V=mp.svd_r(M); return sum(1 for s in S if abs(s)>mp.mpf(10)**-25)
print('vars',len(X),'rank',rank(M),'with M7',rank(mp.matrix([[ev(sp.diff(r,v)) for v in X] for r in rels+[target]])))
names=['9','9n','10','10n','2','2n','2q7','2nq7','20','20q7','9q2','10q2','2q2']
cur=list(range(len(rels)))
def ok(idx):
    A=[[ev(sp.diff(rels[i],v)) for v in X] for i in idx]
    return rank(mp.matrix(A+[[ev(sp.diff(target,v)) for v in X]]))==rank(mp.matrix(A))
for i in list(cur):
    t=[j for j in cur if j!=i]
    if ok(t): cur=t
print('minimal:',[names[i] for i in cur])
