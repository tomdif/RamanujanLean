# Prototype of the interval certificate (mpmath.iv, outward rounding) mirroring the planned Lean checker.
import mpmath as mp
iv=mp.iv; iv.dps=40
PI=iv.pi
def step(l):
    r=[0]*(len(l)+1)
    for d,c in enumerate(l):
        r[d]+=c; r[d+1]-=4*c
        if d>=1: r[d-1+1-1]+=0
    # p + 4 z p' - 4 z p :  4 z p' coefficient at degree d is 4 d c_d
    r=[0]*(len(l)+1)
    for d,c in enumerate(l):
        r[d]+=c+4*d*c; r[d+1]-=4*c
    while r and r[-1]==0: r.pop()
    return r
Z=[[0,-3,2]]
for i in range(12): Z.append(step(Z[-1]))
assert Z[1]==[0,-15,30,-8] and Z[2]==[0,-75,330,-224,32], Z[:3]
def pe(l,z):
    acc=iv.mpf(0)
    for c in reversed(l): acc=c+z*acc
    return acc
A=[sum(abs(c) for c in l) for l in Z]
KM=3
def sIv(l,X):
    s=iv.mpf(0)
    for k in range(2,KM+1):
        K=k*k; s+=pe(l,K*X)*iv.exp(-(K-1)*X)
    Al=sum(abs(c) for c in l); n=len(l); K0=(KM+1)**2
    xl=iv.mpf(X.a); xh=iv.mpf(X.b)
    t=2*Al*(K0*xh)**n*iv.exp(-(K0-1)*xl)
    return s+iv.mpf([-t.b,t.b])
def Xof(U): return PI*iv.exp(2*U)
# ---- region (a): u in [u0,U1]
def regionA(cells):
    bad=[]; minr=mp.inf
    for (a,b) in cells:
        U=iv.mpf([a,b]); X=Xof(U)
        p=[pe(Z[i],X)/2**i for i in range(3)]
        s=[sIv(Z[i],X)/2**i for i in range(3)]
        F=8*X**3*(2*U-1)+X**2*(42-48*U)+60*X*(U-1)+iv.mpf(45)/2
        tot=X**2*F + p[0]*(s[1]-U*s[2]) + s[0]*(p[1]-U*p[2]) + s[0]*(s[1]-U*s[2]) + U*(2*p[1]*s[1]+s[1]**2)
        if not tot.a>0: bad.append((a,b,tot))
    return bad
def mkcells(lo,hi,n): 
    lo=mp.mpf(lo); hi=mp.mpf(hi); return [(lo+(hi-lo)*i/n, lo+(hi-lo)*(i+1)/n) for i in range(n)]
for u0 in ['0.15','0.16','0.18','0.2']:
    for n in [50,100,200,400]:
        bad=regionA(mkcells(u0,'0.5',n))
        print('A',u0,n,'bad',len(bad), bad[:1])
        if not bad: break
for n in [50,100,200]:
    bad=regionA(mkcells('0.5','2',n)); print('A [0.5,2]',n,'bad',len(bad))
    if not bad: break
# ---- region (b)
def PhiIv(i,U):  # Phi_i(t) for t in U: e^{t/2} e^{-x} 2^{-i} (pe(x) + s(x))
    X=Xof(U)
    return iv.exp(U/2)*iv.exp(-X)*(pe(Z[i],X)+sIv(Z[i],X))/2**i
KM=7
c=[PhiIv(i,iv.mpf(0)) for i in range(11)]
print('c',[mp.nstr(ci.mid,8) for ci in c[::2]], 'odd (should be ~0):',[mp.nstr(c[i].mid,3) for i in (1,3,5,7,9)])
def hullPhi(i,u0,n):
    lo=mp.inf; hi=-mp.inf
    for (a,b) in mkcells(0,u0,n):
        I=PhiIv(i,iv.mpf([a,b])); lo=min(lo,I.a); hi=max(hi,I.b)
    return iv.mpf([lo,hi])
def regionB(u0,nM,ncell,N=5):
    M=hullPhi(2*N,u0,nM)
    fact=mp.factorial
    c0,c2,c4,c6,c8=[c[2*j] for j in range(5)]
    bad=0; mn=mp.inf
    for (a,b) in mkcells(0,u0,ncell):
        U=iv.mpf([a,b])
        Ph=c0+c2*U**2/2+c4*U**4/24+c6*U**6/720+c8*U**8/fact(8)+M*U**10/fact(10)
        W=-2*c4/6-4*c6*U**2/fact(5)-6*c8*U**4/fact(7) + M*U**6/fact(9) - M*U**6/fact(8)
        V=c2+c4*U**2/6+c6*U**4/fact(5)+c8*U**6/fact(7)+M*U**8/fact(9)
        g=Ph*W+V*V
        mn=min(mn,g.a)
        if not g.a>0: bad+=1
    return M,bad,mn
for u0 in ['0.16','0.18','0.2']:
    for nM in [20,80]:
        for ncell in [10,40]:
            M,bad,mn=regionB(mp.mpf(u0),nM,ncell)
            print('B',u0,'nM',nM,'ncell',ncell,'M',M,'bad',bad,'min',mp.nstr(mn,5))
