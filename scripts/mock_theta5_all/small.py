# depth-1 Weierstrass+dissection certificate search for small identities, atoms mod MOD (q-units)
import os; os.environ["OMP_NUM_THREADS"]="2"
import sys, itertools, numpy as np, pickle
sys.path.insert(0,'.')
import atoms
from atoms import *
from fractions import Fraction as F
rng=np.random.default_rng(7); R=rng.integers(1,2**62,size=MOD+2,dtype=np.int64)
def hv(t):
    h=np.int64(t[1])*R[0]
    for r,n in t[2].items(): h=h+np.int64(n)*R[r]
    return h
def Wrel(M,eps,a,b,c,d):
    ea,eb,ec,ed=eps; J=lambda e,s: th(M,e,s)
    P1=mul(J(a+c,ea*ec),J(a-c,ea*ec),J(b+d,eb*ed),J(b-d,eb*ed))
    P2=mul(J(a+d,ea*ed),J(a-d,ea*ed),J(b+c,eb*ec),J(b-c,eb*ec))
    P3=mul(J(a+b,ea*eb),J(a-b,ea*eb),J(c+d,ec*ed),J(c-d,ec*ed))
    if None in (P1,P2,P3): return None
    return [(F(1),P1),(F(-1),P2),(F(-eb*ec),(P3[0],P3[1]+(b-c),P3[2]))]
def Drel(n,m,e,c):
    out=[(F(1),th(m,e,c))]
    for k in range(n):
        t=th(m*n*n, m*c2(n)+m*n*k+n*e, (-1)**(n+1)*c**n)
        if t is None: return None
        out.append((F(-((-1)**k)*(c**k)),(t[0],t[1]+m*c2(k)+e*k,t[2])))
    return out
def Mrel(N,e1,c1,e2,c2):
    # j(x;q)j(y;q) = j(-xy;q^2) j(-q y/x;q^2) - x j(-q x y;q^2) j(-y/x;q^2), q=t^N
    A=mul(th(N,e1,c1),th(N,e2,c2))
    B=mul(th(2*N,e1+e2,-c1*c2),th(2*N,N+e2-e1,-c2*c1))
    C=mul(th(2*N,N+e1+e2,-c1*c2),th(2*N,e2-e1,-c2*c1))
    if None in (A,B,C): return None
    return [(F(1),A),(F(-1),B),(F(c1),(C[0],C[1]+e1,C[2]))]
def Jinf(N):
    v={}; poch(v,N,N,1,1); return (F(1),0,{r:n for r,n in v.items() if n})
def Qrel(N,e,c):
    A=mul(th(N,e,c),th(2*N,N+2*e,c*c),inv(Jinf(2*N)))
    B=th(3*N,3*e+N,-c**3); C=th(3*N,3*e+2*N,-c**3)
    if None in (A,B,C): return None
    return [(F(1),A),(F(-1),B),(F(c),(C[0],C[1]+e,C[2]))]
def shapes(Ms,mrel=True):
    rels=[]
    seen=set()
    for N in range(1,MOD+1):
        if MOD%(6*N): continue
        for e in range(0,N):
            for c in (1,-1):
                try: r=Qrel(N,e,c)
                except ValueError: continue
                if r is None: continue
                h0=hv(r[0][1]); o=tuple(int(hv(t)-h0) for _,t in r)
                if o in seen: continue
                seen.add(o); rels.append((list(o),('Q',(N,e,c))))
    print(" Qrels",len(rels),flush=True)
    if mrel:
      seen=set()
      for N in range(1,MOD+1):
        if MOD%(4*N): continue
        for e1 in range(0,N):
          for e2 in range(0,N):
            for c1 in (1,-1):
              for c2 in (1,-1):
                try: r=Mrel(N,e1,c1,e2,c2)
                except ValueError: continue
                if r is None: continue
                h0=hv(r[0][1]); o=tuple(int(hv(t)-h0) for _,t in r)
                if o in seen: continue
                seen.add(o); rels.append((list(o),('M',(N,e1,c1,e2,c2))))
      print(" Mrels",len(rels),flush=True)
    for M in Ms:
        TH={}
        E=np.arange(-3*M,3*M+1)
        for s in (1,-1):
            if s==-1 and MOD%(2*M): continue
            arr=np.zeros(len(E),dtype=np.int64); ok=np.ones(len(E),bool)
            for i,e in enumerate(E):
                t=th(M,int(e),s)
                if t is None: ok[i]=False
                else: arr[i]=hv(t)
            TH[s]=(arr,ok)
        al=np.arange(M); seen=set()
        for sg in range(16):
            eps=[1 if (sg>>i)&1==0 else -1 for i in range(4)]; ea,eb,ec,ed=eps
            if any(x not in TH for x in {ea*ec,eb*ed,ea*ed,eb*ec,ea*eb,ec*ed}): continue
            J=lambda x,e:(TH[e][0][x+3*M],TH[e][1][x+3*M])
            A,B,C,D=[x.ravel() for x in np.meshgrid(al,al,al,al,indexing='ij')]
            parts=[J(A+C,ea*ec),J(A-C,ea*ec),J(B+D,eb*ed),J(B-D,eb*ed),J(A+D,ea*ed),J(A-D,ea*ed),J(B+C,eb*ec),J(B-C,eb*ec),J(A+B,ea*eb),J(A-B,ea*eb),J(C+D,ec*ed),J(C-D,ec*ed)]
            ok=np.logical_and.reduce([p[1] for p in parts])
            W1=sum(p[0] for p in parts[0:4]); W2=sum(p[0] for p in parts[4:8]); W3=sum(p[0] for p in parts[8:12])+(B-C).astype(np.int64)*R[0]
            k12=(W2-W1)[ok]; k13=(W3-W1)[ok]; idx=np.nonzero(ok)[0]
            u,first=np.unique(np.stack([k12,k13],1),axis=0,return_index=True)
            for (x,y),fi in zip(u,first):
                if (x,y) in seen: continue
                seen.add((x,y)); i=idx[fi]
                rels.append(([0,int(x),int(y)],('W',(M,tuple(eps),int(A[i]),int(B[i]),int(C[i]),int(D[i])))))
    for n in (2,3,5):
        for m in range(1,MOD+1):
            if MOD%(m*n*n): continue
            for c in (1,-1):
                if c==-1 and MOD%(2*m*n*n): continue
                for e in (range(1,m) if c==1 else range(0,m)):
                    try: r=Drel(n,m,e,c)
                    except ValueError: continue
                    if r is None or any(t is None for _,t in r): continue
                    h0=hv(r[0][1]); rels.append(([int(hv(t)-h0) for _,t in r],('D',(n,m,e,c))))
    return rels
def exact(spec):
    kind,p=spec; return Wrel(*p) if kind=='W' else (Drel(*p) if kind=='D' else (Mrel(*p) if kind=='M' else Qrel(*p)))
def solve(terms,rels,maxit=100):
    # terms: list of (coef, t)
    tk={}
    for c,t in terms:
        kk=key(t); tk[kk]=tk.get(kk,0)+F(c)*t[0]
    tvec={kk:None for kk in tk}
    tt={key(t):t for c,t in terms}
    hT=np.array([hv(t) for t in tt.values()],dtype=np.int64); names=list(tt)
    cand=[]
    for i,kk in enumerate(names):
        for ri,(offs,spec) in enumerate(rels):
            for p in range(len(offs)):
                base=hT[i]-offs[p]; cand.append((tuple(sorted(base+o for o in offs)),i,ri,p))
    # 2-core
    from collections import Counter
    uniq={}
    for c in cand: uniq.setdefault(c[0],c)
    cand=list(uniq.values()); T=set(hT.tolist())
    alive=[True]*len(cand)
    while True:
        cnt=Counter(n for j,c in enumerate(cand) if alive[j] for n in c[0])
        bad=[j for j,c in enumerate(cand) if alive[j] and any(cnt[n]==1 and n not in T for n in c[0])]
        if not bad: break
        for j in bad: alive[j]=False
    core=[c for j,c in enumerate(cand) if alive[j]]
    print(" core",len(core),flush=True)
    cols=[]
    for (_,i,ri,p) in core:
        rel=exact(rels[ri][1]); Ti=tt[names[i]]
        cp,(sp,kp,vp)=rel[p]; e={}
        for cq,(sq,kq,vq) in rel:
            vec={r:vq.get(r,0)+Ti[2].get(r,0)-vp.get(r,0) for r in set(vq)|set(Ti[2])|set(vp)}
            k2=(kq+Ti[1]-kp,tuple(sorted((r,n) for r,n in vec.items() if n)))
            e[k2]=e.get(k2,0)+cq*F(sq)/(cp*F(sp))
        cols.append((e,rels[ri][1],names[i],p))
    import sympy
    rowk=sorted(set(k for e,_,_,_ in cols for k in e)|set(tk))
    ri_={k:i for i,k in enumerate(rowk)}
    A=sympy.zeros(len(rowk),len(cols)); b=sympy.zeros(len(rowk),1)
    for j,(e,_,_,_) in enumerate(cols):
        for k,v in e.items(): A[ri_[k],j]=sympy.Rational(v.numerator,v.denominator)
    for k,v in tk.items(): b[ri_[k]]=sympy.Rational(v.numerator,v.denominator)
    try:
        sol,params=A.gauss_jordan_solve(b)
        sol=sol.subs({p:0 for p in params})
        return [(sol[j],cols[j][1],cols[j][2],cols[j][3]) for j in range(len(cols)) if sol[j]!=0]
    except ValueError:
        return None
