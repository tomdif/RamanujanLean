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
    
    thv=[x for x,_ in TH]
    r2,_=rank_null(thv,p)
    allv=thv+nul
    r3,_=rank_null(allv,p)
    print(p,'dim M_{2p-4}',len(Bb),'rank U',rk,'dim ker U',len(nul),'dim theta(M_{p-5})',r2,'dim span(ker+theta)',r3)
    Kser=[sum((int(x)*Bb[c] for c,x in enumerate(v)),np.zeros(D+1,dtype=np.int64))%p for v in nul]
    def Ud(w,d):
        o=np.zeros(D+1,dtype=np.int64);L_=D//d+1;o[:L_]=w[::d][:L_];return o
    def Pi(w):
        # P(A,B)=(A-1)(A-32)(B+9)(A^2+6A+32) with A=16 U2, B=81 U3
        A=lambda v:(16*Ud(v,2))%p
        B=lambda v:(81*Ud(v,3))%p
        v=(A(w)+0*w+0)%p
        q=(A(A(w))+6*A(w)+32*w)%p
        q=(B(q)+9*q)%p
        q=(A(q)-32*q)%p
        q=(A(q)-q)%p
        return q
    Lchk=(D//48)
    out=0
    thS=[(np.arange(D+1)*b)%p for b in B5]
    # test membership using coefficients below the truncation of the four U-steps
    rows_th=[[int(t[j]) for j in range(1,Lchk)] for t in thS]
    r0,_=rank_null(rows_th,p)
    for w in Kser:
        pw_=Pi(w)
        r1,_=rank_null(rows_th+[[int(pw_[j]) for j in range(1,Lchk)]],p)
        out+= (r1>r0)
    print('   Pi(ker U) outside theta(M_{p-5}):',out,'of',len(Kser))
    i4=pow(4,-1,p);i9=pow(9,-1,p)
    rows=[]
    for d,val in((2,i4),(3,i9)):
        for j in range(len(Bb)):
            rows.append([int((Kser[i][d*j]-val*Kser[i][j])%p) for i in range(len(Kser))])
    _,nk=rank_null(rows,p)
    rows=[]
    for d,val in((2,i4),(3,i9)):
        for j in range(len(Bb)):
            rows.append([int((thS[i][d*j]-val*thS[i][j])%p) for i in range(len(thS))])
    _,nt=rank_null(rows,p)
    print('   class in kerU',len(nk),'class in theta',len(nt))
for p in (13,17,29,31,37,43,61,67,71,73): run(p)
