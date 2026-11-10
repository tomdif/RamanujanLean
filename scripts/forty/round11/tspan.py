"""Is 3.15(ii) (A(q)-A(-q) = 2q L(q^2)) locally implied by Entries 3.2,3.7-3.10,3.15(i),3.20 at +-q^k?
Jacobian span test at q=0.07, then greedy minimal subset."""
import sympy as sp, mpmath as mp
mp.mp.dps=50
q0=mp.mpf('0.07')
def Pi(f): return mp.nprod(f,[0,mp.inf])
def Gv(x): return 1/Pi(lambda n:(1-x**(5*n+1))*(1-x**(5*n+4)))
def Hv(x): return 1/Pi(lambda n:(1-x**(5*n+2))*(1-x**(5*n+3)))
def chimv(x): return Pi(lambda n:1-x**(2*n+1))
q=sp.Symbol('q')
args=[1,-1,2,3,-3,4,6,7,-7,14,21,-21,28,42]
G={a:sp.Symbol(('G%d'%a).replace('-','n')) for a in args}; H={a:sp.Symbol(('H%d'%a).replace('-','n')) for a in args}
def x(a): return q0**a if a>0 else -(q0**(-a))
vals={q:q0}
for a in args: vals[G[a]]=Gv(x(a)); vals[H[a]]=Hv(x(a))
P={};M={}
for k in (1,3,7,21):
    P[k]=sp.Symbol(f'p{k}'); M[k]=sp.Symbol(f'm{k}'); vals[P[k]]=chimv(-q0**k); vals[M[k]]=chimv(q0**k)
def m(k):  # chi(-q^k), k in {1,3,7,21} or 2k
    return M[k] if k in M else P[k//2]*M[k//2]
def p(k): return P[k]
rels={
 '3.2':  G[1]*G[4]+q*H[1]*H[4]-p(1)**2,
 '3.2n': G[-1]*G[4]-q*H[-1]*H[4]-m(1)**2,
 '3.2q7':G[7]*G[28]+q**7*H[7]*H[28]-p(7)**2,
 '3.2nq7':G[-7]*G[28]-q**7*H[-7]*H[28]-m(7)**2,
 '3.7':  G[2]*G[3]+q*H[2]*H[3]-m(3)/m(1),
 '3.7n': G[2]*G[-3]-q*H[2]*H[-3]-p(3)/p(1),
 '3.7q2':G[4]*G[6]+q**2*H[4]*H[6]-m(6)/m(2),
 '3.7q7':G[14]*G[21]+q**7*H[14]*H[21]-m(21)/m(7),
 '3.7nq7':G[14]*G[-21]-q**7*H[14]*H[-21]-p(21)/p(7),
 '3.7q14':G[28]*G[42]+q**14*H[28]*H[42]-m(42)/m(14),
 '3.8':  G[6]*H[1]-q*G[1]*H[6]-m(1)/m(3),
 '3.8n': G[6]*H[-1]+q*G[-1]*H[6]-p(1)/p(3),
 '3.8q7':G[42]*H[7]-q**7*G[7]*H[42]-m(7)/m(21),
 '3.8nq7':G[42]*H[-7]+q**7*G[-7]*H[42]-p(7)/p(21),
 '3.9':  G[7]*H[2]-q*G[2]*H[7]-m(1)/m(7),
 '3.9n': G[-7]*H[2]+q*G[2]*H[-7]-p(1)/p(7),
 '3.9q2':G[14]*H[4]-q**2*G[4]*H[14]-m(2)/m(14),
 '3.9q3':G[21]*H[6]-q**3*G[6]*H[21]-m(3)/m(21),
 '3.9nq3':G[-21]*H[6]+q**3*G[6]*H[-21]-p(3)/p(21),
 '3.10': G[1]*G[14]+q**3*H[1]*H[14]-m(7)/m(1),
 '3.10n':G[-1]*G[14]-q**3*H[-1]*H[14]-p(7)/p(1),
 '3.10q2':G[2]*G[28]+q**6*H[2]*H[28]-m(14)/m(2),
 '3.10q3':G[3]*G[42]+q**9*H[3]*H[42]-m(21)/m(3),
 '3.10nq3':G[-3]*G[42]-q**9*H[-3]*H[42]-p(21)/p(3),
 '3.20': G[1]*H[-1]+G[-1]*H[1]-2/m(2)**2,
 '3.20q7':G[7]*H[-7]+G[-7]*H[7]-2/m(14)**2,
 '3.20q3':G[3]*H[-3]+G[-3]*H[3]-2/m(6)**2,
 '3.20q21':G[21]*H[-21]+G[-21]*H[21]-2/m(42)**2,
 '15i':  G[6]*G[14]+q**4*H[6]*H[14]-(G[42]*H[2]-q**8*G[2]*H[42]),
}
Lq2=G[6]*G[14]+q**4*H[6]*H[14]
target=p(1)*m(3)*p(7)*m(21)-m(1)*p(3)*m(7)*p(21)-2*q*Lq2
X=[v for v in vals if v!=q]
f=sp.lambdify(list(vals),[sp.Matrix([r]).jacobian(X) for r in list(rels.values())+[target]],'mpmath')
vs=list(vals.values())
for k,r in rels.items():
    assert abs(sp.lambdify(list(vals),r,'mpmath')(*vs))<1e-35,k
J=[list(j) for j in f(*vs)]
names=list(rels)
def rank(rows):
    U,S,V=mp.svd_r(mp.matrix(rows)); return sum(1 for s in S if abs(s)>mp.mpf(10)**-30)
def ok(idx): return rank([J[i] for i in idx]+[J[-1]])==rank([J[i] for i in idx])
allidx=list(range(len(names)))
print('vars',len(X),'rank all',rank([J[i] for i in allidx]),'implied:',ok(allidx))
if ok(allidx):
    cur=allidx
    for i in list(cur):
        t=[j for j in cur if j!=i]
        if ok(t): cur=t
    print('minimal:',[names[i] for i in cur])
