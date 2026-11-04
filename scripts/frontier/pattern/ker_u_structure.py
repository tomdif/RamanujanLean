import numpy as np,sys
def rank_null(M,p):
    M=[r[:] for r in M];R=[];rows=len(M);cols=len(M[0]) if M else 0;r=0;piv=[]
    for c in range(cols):
        pr=next((i for i in range(r,rows) if M[i][c]%p),None)
        if pr is None:continue
        M[r],M[pr]=M[pr],M[r];iv=pow(M[r][c],-1,p);M[r]=[x*iv%p for x in M[r]]
        for i in range(rows):
            if i!=r and M[i][c]%p:
                f=M[i][c];M[i]=[(x-f*y)%p for x,y in zip(M[i],M[r])]
        piv.append(c);r+=1
    free=[c for c in range(cols) if c not in piv];nul=[]
    for fc in free:
        v=[0]*cols;v[fc]=1
        for i,c in enumerate(piv):v[c]=(-M[i][fc])%p
        nul.append(v)
    return r,nul
def run(p):
    D=p*(2*p+2)+5
    def mul(a,b):
        return np.convolve(a,b)[:D+1]%p
    def euler(d):
        o=np.zeros(D+1,dtype=np.int64);k=0
        while True:
            done=True
            for kk in ((k,-k) if k else (0,)):
                x=kk*(3*kk-1)//2*d
                if x<=D:o[x]=(1 if kk%2==0 else -1)%p;done=False
            if done and k>0:break
            k+=1
        return o
    def pw(a,e):
        r=np.zeros(D+1,dtype=np.int64);r[0]=1
        while e:
            if e&1:r=mul(r,a)
            a=mul(a,a);e>>=1
        return r
    def inv(a):
        # newton
        g=np.zeros(1,dtype=np.int64);g[0]=pow(int(a[0]),-1,p);n=1
        while n<D+1:
            n=min(2*n,D+1);ag=np.convolve(a[:n],g)[:n]%p;t=(-ag)%p;t[0]=(t[0]+2)%p;g=np.convolve(g,t)[:n]%p
        return g
    num=[(2,12,3,2),(2,4,6,4),(1,2,6,12)];den=[(1,6,6,4),(1,2,3,2),(2,4,3,6)]
    W=[]
    for a in range(3):
        d,k,e,r=num[a];N=mul(pw(euler(d),k),pw(euler(e),r))
        d,k,e,r=den[a];Dn=mul(pw(euler(d),k),pw(euler(e),r))
        s=mul(N,inv(Dn));W.append(np.concatenate([np.zeros(a,dtype=np.int64),s])[:D+1])
    def basis(n):
        pa=[np.eye(1,D+1,0,dtype=np.int64)[0]]
        for _ in range(n):pa.append(mul(pa[-1],W[0]))
        pc=[np.eye(1,D+1,0,dtype=np.int64)[0]]
        for _ in range(n+1):pc.append(mul(pc[-1],W[2]))
        return [mul(mul(pa[n-i//2-i%2],W[1] if i%2 else np.eye(1,D+1,0,dtype=np.int64)[0]),pc[i//2]) for i in range(2*n+1)]
    n=p-2;Bb=basis(n);L=2*n+2
    Lp=p-2
    Uv=[[int(b[p*j]) for j in range(Lp+1)] for b in Bb]  # U image first coeffs (target weight p-3, dim p-2)
    Mt=[[Uv[c][r] for c in range(len(Bb))] for r in range(Lp+1)]
    rk,nul=rank_null(Mt,p)
    # kernel check on more coefficients
    # theta(M_{p-5})
    B5=basis((p-5)//2)
    th=[(np.arange(D+1)*b)%p for b in B5]
    # express in Bb coordinates using first L coefficients
    A=[[int(Bb[c][j]) for c in range(len(Bb))] for j in range(L)]
    def coords(v):
        # solve A x = v[:L] by triangular
        x=[0]*len(Bb);w=v.copy()
        for t in range(len(Bb)):
            c=int(w[t])%p;x[t]=c;w=(w-c*Bb[t])%p
        assert not w[:D+1].any() or True
        return x,int(np.count_nonzero(w[:len(Bb)+40]))
    TH=[coords(t) for t in th]
    assert all(z==0 for _,z in TH),'theta M_{p-5} not in M_{2p-4}'
    thv=[x for x,_ in TH]
    r2,_=rank_null(thv,p)
    allv=thv+nul
    r3,_=rank_null(allv,p)
    print(p,'dim M_{2p-4}',len(Bb),'rank U',rk,'dim ker U',len(nul),'dim theta(M_{p-5})',r2,'dim span(ker+theta)',r3)
    # U2,U3 on Q=kerU/theta(M_{p-5}), which should be 3-dimensional
    K=[sum((int(x)*Bb[c] for c,x in enumerate(v)),np.zeros(D+1,dtype=np.int64))%p for v in nul]
    # pick complement of theta image inside ker
    cur=[v[:] for v in thv];comp=[]
    r0=rank_null(cur,p)[0]
    for i,v in enumerate(nul):
        r1=rank_null(cur+[v],p)[0]
        if r1>r0:cur.append(v);comp.append(i);r0=r1
    def act(d):
        M=[[0]*len(comp) for _ in comp]
        for ci,i in enumerate(comp):
            u=np.zeros(D+1,dtype=np.int64)
            L_=D//d+1
            u[:L_]=K[i][::d][:L_]
            x,z=coords(u) if False else (None,None)
            # coordinates in Bb using triangular reduction on first coefficients only
            w=u.copy();xx=[0]*len(Bb)
            for t in range(len(Bb)):
                c=int(w[t])%p;xx[t]=c;w=(w-c*Bb[t])%p
            # solve xx = sum a_j thv_j + sum b_j nul[comp_j]
            A=thv+[nul[j] for j in comp]
            T=[[A[c][r] for c in range(len(A))]+[xx[r]] for r in range(len(Bb))]
            # gaussian elimination
            rows=len(T);cols=len(A);rr=0;piv={}
            for c in range(cols):
                pr=next((q for q in range(rr,rows) if T[q][c]%p),None)
                if pr is None:continue
                T[rr],T[pr]=T[pr],T[rr];iv=pow(T[rr][c],-1,p);T[rr]=[y*iv%p for y in T[rr]]
                for q in range(rows):
                    if q!=rr and T[q][c]%p:
                        f=T[q][c];T[q]=[(y-f*z_)%p for y,z_ in zip(T[q],T[rr])]
                piv[c]=rr;rr+=1
            sol=[T[piv[c]][cols] if c in piv else 0 for c in range(cols)]
            for cj in range(len(comp)):M[cj][ci]=sol[len(thv)+cj]
        return M
    def eig(M):
        n=len(M);out=[]
        for lam in range(p):
            Mm=[[ (M[i][j]-(lam if i==j else 0))%p for j in range(n)] for i in range(n)]
            r,nu=rank_null(Mm,p)
            if nu:out.append((lam,len(nu)))
        return out
    M2=act(2);M3=act(3)
    i4=pow(4,-1,p);i9=pow(9,-1,p)
    n=len(M2)
    # commute check and joint eigenvectors for (1/4,1/9)
    def mm(A,B):return [[sum(A[i][k]*B[k][j] for k in range(n))%p for j in range(n)] for i in range(n)]
    comm=mm(M2,M3)==mm(M3,M2)
    rows=[[ (M2[i][j]-(i4 if i==j else 0))%p for j in range(n)] for i in range(n)]+[[ (M3[i][j]-(i9 if i==j else 0))%p for j in range(n)] for i in range(n)]
    _,nu=rank_null(rows,p)
    sq=lambda A:mm(A,A)
    def sub(A,c):return [[(A[i][j]-(c if i==j else 0))%p for j in range(n)] for i in range(n)]
    pairs=[]
    for l2 in range(1,p):
        for l3 in range(1,p):
            r,nv=rank_null(sub(M2,l2)+sub(M3,l3),p)
            if nv:pairs.append((l2,l3,len(nv)))
    fmt=lambda v:next((f"{sg}2^{e}" for e in range(-8,9) for sg in ('','-') if v%p==(1 if sg=='' else -1)*pow(2,e,p)%p),str(v))
    fm3=lambda v:next((f"{sg}3^{e}" for e in range(-8,9) for sg in ('','-') if v%p==(1 if sg=='' else -1)*pow(3,e,p)%p),str(v))
    print('   Q commute',comm,'joint eigen(1/4,1/9) dim',len(nu),'all joint eigenpairs',[(fmt(a),fm3(b),m) for a,b,m in pairs])
for p in (29,31,37,41,43,47): run(p)
