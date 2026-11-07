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
    # theta^{p-5} of M_6 and of S_6
    B6=basis(3)
    pw_=np.array([pow(int(j),p-5,p) for j in range(D+1)],dtype=np.int64)
    # lin. comb. vanishing at q^0 only for constant; take all of M_6
    t6=[(pw_*b)%p for b in B6]
    good=[];bad=0
    for t in t6:
        x,z=coords(t)
        good.append(x); bad+= (z!=0)
    r6,_=rank_null(good,p)
    r7,_=rank_null(thv+good,p)
    r8,_=rank_null(nul+good,p)
    # each theta^{p-5}h in M_{2p-4}? (z==0), in ker U?
    print('   theta^{p-5}(M_6): not in M_{2p-4}:',bad,'rank',r6,'| span(theta M_{p-5}, theta^{p-5}M_6)=',r7,'| span with ker=',r8,'(ker dim',len(nul),')')
for p in (13,17,19,23,29,31,37,41,43,47,53,61,67,71,73): run(p)
