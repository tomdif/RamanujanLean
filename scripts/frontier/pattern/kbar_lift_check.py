import ast,re
import numpy as np
from sympy.ntheory import jacobi_symbol as js
tab={}
for line in open('ch.tab'):
    v=ast.literal_eval(line.strip().replace(' ',''));tab[v[0]]=v[1]
def chi12(n):
    return {1:1,5:-1,7:-1,11:1}.get(n%12,0)
def run(l,t=23):
    D=max((t*24**2+1)//24+5,l*32)
    M=l
    def mul(a,b):
        return [int(x)%M for x in np.convolve(np.array(a,dtype=np.int64),np.array(b,dtype=np.int64))[:D+1]]
    def pw(a,e):
        r=[1]+[0]*D
        while e:
            if e&1:r=mul(r,a)
            a=mul(a,a);e>>=1
        return r
    Q=[0]*(D+1);Q[0]=1;m=1
    while m*(3*m-1)//2<=D:
        s=(-1)**m
        for g in (m*(3*m-1)//2,m*(3*m+1)//2):
            if g<=D:Q[g]=s%M
        m+=1
    pent=[i for i in range(1,D+1) if Q[i]]
    P=[0]*(D+1);P[0]=1
    for n in range(1,D+1):
        P[n]=(-sum(Q[i]*P[n-i] for i in pent if i<=n))%M
    sig=lambda s:[0]+[sum(pow(d,s,M) for d in range(1,n+1) if n%d==0)%M for n in range(1,D+1)]
    E4=[1]+[240*x%M for x in sig(3)[1:]];E6=[1]+[-504*x%M for x in sig(5)[1:]]
    Dl=[0]+pw(Q,24)[:D]
    # basis of S_{l-1}: Delta^i E4^a E6^b
    kk=l-1;basis=[]
    for i in range(1,kk//12+2):
        r=kk-12*i
        if r<0:break
        for c in range(3):
            if r-6*c>=0 and (r-6*c)%4==0:
                bb=(r-6*c)//4;break
        else: continue
        if r==2:continue
        basis.append(mul(mul(pw(Dl,i),pw(E4,bb)),pw(E6,c)))
    d=(l*l-1)//24
    # find kernel of Dbar on S: U(Delta^d f)=0
    Dd=([0]*d+pw(Q,24*d))[:D+1]
    U=lambda a:[a[l*i] for i in range((len(a)-1)//l+1)]
    im=[U(mul(Dd,b))[:30] for b in basis]
    # nullspace mod l
    n=len(basis)
    import copy
    A=[[im[j][i] for j in range(n)] for i in range(30)]
    piv=[];R=copy.deepcopy(A);r=0
    for c in range(n):
        pr=next((i for i in range(r,30) if R[i][c]%l),None)
        if pr is None:continue
        R[r],R[pr]=R[pr],R[r];iv=pow(R[r][c],-1,l);R[r]=[x*iv%l for x in R[r]]
        for i in range(30):
            if i!=r and R[i][c]%l:
                f=R[i][c];R[i]=[(x-f*y)%l for x,y in zip(R[i],R[r])]
        piv.append(c);r+=1
    free=[c for c in range(n) if c not in piv]
    print('l',l,'dimS',n,'rank D',r,'ker',len(free))
    for fc in free[:1]:
        co=[0]*n;co[fc]=1
        for i,c in enumerate(piv):co[c]=(-R[i][fc])%l
        f=[sum(co[j]*basis[j][i] for j in range(n))%l for i in range(D+1)]
        A_=mul(f,P)
        lam=l-2
        Nn=24
        def bb(n_):
            s=0
            for e in range(1,n_+1):
                if n_%e==0:
                    dd=n_//e
                    psi=js(dd,t) if dd%t else 0
                    idx=(t*e*e+1)//24
                    s+=psi*pow(dd,lam-1,l)*chi12(e)*A_[idx]
            return s%l
        b=[bb(i) for i in range(1,Nn)]
        g=tab[l]
        th=[(i*g[i])%l for i in range(1,Nn)]
        cand=[c for c in range(1,l) if all((b[i]-c*th[i])%l==0 for i in range(len(b)))]
        print(' lift nonzero',any(b),'b[:8]',b[:8],'theta g[:8]',th[:8],'scalar c with b=c*theta(g):',cand)
for l in (29,31,37,41,43,47):run(l)
