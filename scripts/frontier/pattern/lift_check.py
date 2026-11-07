# Check b_t = sum_{de=n} (d/t) d^(lam-1) chi12(e) a(t e^2) against PARI class forms, all squarefree t = -l mod 24
import subprocess, sympy as sp
from flint import fmpz_poly
def chi12(e): return {1:1,11:1,5:-1,7:-1}.get(e%12,0)
def lift(l,ts,Nb=30):
    j=l%24; kp=(l+j-2)//2; lam=(l-3)//2
    R=(kp//12) if kp%12!=2 else kp//12-1
    tmax=max(ts); N=(tmax*Nb*Nb+j)//24+5
    def trunc(p): return fmpz_poly(p.coeffs()[:N+1])
    sig3=[0]*(N+1); sig5=[0]*(N+1)
    for d in range(1,N+1):
        for m in range(d,N+1,d): sig3[m]+=d**3; sig5[m]+=d**5
    E4=fmpz_poly([1]+[240*sig3[m] for m in range(1,N+1)]); E6=fmpz_poly([1]+[-504*sig5[m] for m in range(1,N+1)])
    Q=[0]*(N+1); k=0
    while k*(3*k-1)//2<=N:
        g1=k*(3*k-1)//2; g2=k*(3*k+1)//2; s=-1 if k%2 else 1
        Q[g1]=s
        if g2<=N: Q[g2]=s
        k+=1
    terms=[(i,Q[i]) for i in range(1,N+1) if Q[i]]
    b=[0]*(N+1); b[0]=1
    for n in range(1,N+1):
        b[n]=-sum(c*b[n-i] for i,c in terms if i<=n)
    P=fmpz_poly(b); Q=fmpz_poly(Q)
    def ppow(p,e):
        r=fmpz_poly([1]);x=p
        while e:
            if e&1:r=trunc(r*x)
            x=trunc(x*x);e>>=1
        return r
    Dz=trunc(fmpz_poly([0,1])*ppow(Q,24)); Pj=ppow(P,j)
    out={}
    for i in range(1,R+1):
        w=kp-12*i
        for bb in range(w//6+1):
            if (w-6*bb)%4==0: a=(w-6*bb)//4;break
        A=trunc(trunc(trunc(ppow(Dz,i)*ppow(E4,a))*ppow(E6,bb))*Pj)
        for t in ts:
            ser=[0]*(Nb+1)
            for n in range(1,Nb+1):
                s=0
                for d in sp.divisors(n):
                    e=n//d; c=chi12(e)
                    if c==0: continue
                    idx=(t*e*e+j)//24
                    s+=int(sp.jacobi_symbol(d%t if t>1 else 0,t) if t>1 else 1)*d**(lam-1)*c*int(A[idx])
                ser[n]=s
            out[(i,t)]=ser
    return R,out
gp=[]
for l in [13,17,19,23,29,31,37,41]:
    r=(-l)%24
    ts=[t for t in range(r,r+24*5,24) if sp.factorint(t)=={} or max(sp.factorint(t).values())==1]
    R,out=lift(l,ts)
    g=f'default(nbthreads,1);mf=mfinit([6,{l-3}],1);B=mfbasis(mf);L=mfcoefs;M=matconcat(apply(f->mfcoefs(f,30)[2..31]~,B));print(matrank(M));'
    Rows=[]
    for (i,t),ser in out.items():
        g+=f'v={ser[1:31]}~;print({i}," ",{t}," ",matrank(matconcat([M,v]))==matrank(M)," ",v!=0*v);'
    p=subprocess.run(['gp','-q','--stacksize=1000000000'],input=g,capture_output=True,text=True)
    print('l',l,'r',r,'R',R,'ts',ts); print(p.stdout.replace('\n',' | ')[:600], p.stderr[:200],flush=True)
