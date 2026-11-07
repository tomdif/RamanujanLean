# (1) Hodge rows: T M_w subset sum_t l^t Fil^t(w).
# (2) Recursion on ALL of gr^{j-1}: R_j(w)[theta Z] = c_j [theta R_{j-1}(w-2)[Z]] in Mbar_w/Lambdabar_j, c_j=(s-j+1)/(k+j-1), k=a-2j.
import sys
exec(open('rc_quotient_test.py').read().rsplit("if __name__=='__main__'",1)[0])
def ech(Lam,p,e):
    "reduced echelon with unit pivots mod p^e (Lam saturated)"
    m=p**e;B=[r[:] for r in Lam];piv=[]
    for i in range(len(B)):
        c=next((c for c,x in enumerate(B[i]) if x%p),None)
        assert c is not None,'not saturated'
        inv=pow(B[i][c],-1,m);B[i]=[x*inv%m for x in B[i]]
        for t in range(len(B)):
            if t!=i and B[t][c]%m:
                f=B[t][c];B[t]=[(x-f*y)%m for x,y in zip(B[t],B[i])]
        piv.append(c)
    return B,piv
def red(v,E_,m):
    B,piv=E_;v=v[:]
    for b,c in zip(B,piv):
        f=v[c]%m
        if f:v=[(x-f*y)%m for x,y in zip(v,b)]
    return [x%m for x in v]
def mv(T,v,m):return [sum(a*b for a,b in zip(r,v))%m for r in T]
def run(p,a,s,j):
    # a = class of w (index-0 weight); w=a+s(p-1); K=w-2 ; k=a-2j
    k=a-2*j;w=a+s*(p-1);K=w-2;e=j+1
    if k<4:return None
    D=dimM(w);Dk=dimM(K);m=p**(e+1)
    A=R(p,e+1,max(D,Dk)+p+8);
    T=heckemat(p,w);TK=heckemat(p,K)
    # q-expansions of Fil^{j-1}(K) = E^{s-j+1} M_{a-2+(j-1)(p-1)}
    Wt=A.pw(A.eis(p-1),s-j+1)
    w0=a-2+(j-1)*(p-1)
    Mb=[A.P([int(x) for x in f.coeffs()]) for f in miller_int(w0,A.L)]
    Z=[A.mul(f,Wt) for f in Mb]
    Lw=low_lattice(T,p,j,e+1) ;ELw=ech(Lw,p,e+1)
    LK=low_lattice(TK,p,j-1,e+1) if j>1 else [];ELK=ech(LK,p,e+1) if j>1 else ([],[])
    c=fr(Fraction(s-j+1,k+j-1),p)
    vec=lambda f,n:[(int(f[i]) if i<f.length() else 0) for i in range(n)]
    res=[]
    Mw=[A.P([int(x) for x in f.coeffs()]) for f in miller_int(w,A.L)]
    def coords_mod_p(f):
        "coordinates in M_w of a q-series that is mod p a reduction of M_w; checks beyond D"
        v=[x%p for x in vec(f,D)]
        g=A.P([0])
        for t,x in enumerate(v):
            if x:g=g+Mw[t]*x
        h=A.tr(g-f);ok=all(int(h[i])%p==0 for i in range(min(h.length(),A.L)))
        return v,ok
    for z in Z:
        zv=vec(z,Dk)
        # theta Z mod p -> M_w coordinates; lift; R_j
        tz,ok1=coords_mod_p(A.th(z))
        out=mv(T,tz,p**(e+1))
        rl=red(out,ELw,p**(e+1))
        dv=all(x%p**j==0 for x in rl)
        lhs=[(x//p**j)%p for x in rl]
        rhs_in=mv(TK,zv,p**(e+1))
        rk=red(rhs_in,ELK,p**(e+1)) if j>1 else [x%p**(e+1) for x in rhs_in]
        dv2=all(x%p**(j-1)==0 for x in rk)
        zp=[(x//p**(j-1))%p for x in rk]
        # q-series of z' in M_K (Miller of K)
        MK=miller_int(K,A.L)
        g=A.P([0])
        for t,x in enumerate(zp):
            if x:g=g+A.P([int(y) for y in MK[t].coeffs()])*x
        tp,ok2=coords_mod_p(A.th(g))
        rhs=[c*x%p for x in tp]
        rhsb=[(c+1)*x%p for x in tp]
        # compare modulo Lambda_j mod p
        B0=([[x%p for x in b] for b in ELw[0]],ELw[1])
        diff=red([(x-y)%p for x,y in zip(lhs,rhs)],B0,p)
        tzr=red(tz,B0,p)
        diffb=red([(x-y)%p for x,y in zip(lhs,rhsb)],B0,p)
        res.append((ok1,ok2,dv,dv2,all(x==0 for x in diff),any(x for x in tzr),all(x==0 for x in diffb),any(x for x in red(tp,B0,p))))
    return res
def hodge(p,a,s):
    w=a+s*(p-1);T=heckemat(p,w);D=dimM(w);e=s+2;m=p**e
    A=R(p,e,D+4);bad=0
    for t in range(1,s+1):
        Wt=A.pw(A.eis(p-1),s-t+1)
        gens=[]
        for f in miller_int(a+(t-1)*(p-1),A.L):
            F=A.mul(A.P([int(x) for x in f.coeffs()]),Wt)
            gens.append([(int(F[i]) if i<F.length() else 0) for i in range(D)])
        for c in range(D):
            col=[T[i][c]%p**t for i in range(D)]
            if not solve(col,[[x%p**t for x in g] for g in gens],p,t):bad+=1
    return bad
if __name__=='__main__':
    p=int(sys.argv[1]);tot=good=nt=ntr=ctl=0;H=[]
    for a in range(int(sys.argv[2]),p+2,2):
      for s in range(1,int(sys.argv[3])+1):
        if a>=2*s+2:H.append((a,s,hodge(p,a,s)))
        for j in range(1,s+1):
            r=run(p,a,s,j)
            if not r:continue
            for x in r:
                tot+=1;good+=all(x[:5]);nt+=bool(x[5]);ntr+=bool(x[7]);ctl+=(bool(x[7]) and x[6])
                if not all(x[:5]):print('FAIL',p,a,s,j,x,flush=True)
    print('recursion ok',good,'/',tot,'theta Z nonzero',nt,'RHS nonzero',ntr,'wrong-constant still passes on nonzero RHS',ctl);print('hodge bad',[h for h in H if h[2]],'of',len(H))
