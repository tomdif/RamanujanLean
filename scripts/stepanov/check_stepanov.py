"""Numerical checks for RamanujanTau/Stepanov.
(1) the parameter choice J = floor(sqrt(p)/(4 sqrt m)), l = 2J-1, A = c-m+1 satisfies the
    dimension inequality l*(A+J-1+(l-1)(m-1)) < 2JA for p >= 144 m^2;
(2) N_eps <= p/2 + 2 m^{3/2} sqrt p and |sum chi(f)| <= 12 m^2 sqrt p for random squarefree f;
(3) for small p, actually build the auxiliary polynomial T by linear algebra mod p and check
    T != 0 and every x in S_eps is a root of multiplicity >= l."""
import random, math, sys
random.seed(1)
def isprime(n): return n>1 and all(n%d for d in range(2,int(n**.5)+1))
def pmul(a,b,p):
    r=[0]*(len(a)+len(b)-1) if a and b else []
    for i,x in enumerate(a):
        if x:
            for j,y in enumerate(b): r[i+j]=(r[i+j]+x*y)%p
    return trim(r)
def trim(a):
    while a and a[-1]==0: a.pop()
    return a
def padd(a,b,p):
    n=max(len(a),len(b)); return trim([((a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0))%p for i in range(n)])
def pscale(a,s,p): return trim([x*s%p for x in a])
def deriv(a,p): return trim([i*a[i]%p for i in range(1,len(a))])
def ev(a,x,p):
    r=0
    for c in reversed(a): r=(r*x+c)%p
    return r
def ppow(a,e,p):
    r=[1]
    for _ in range(e): r=pmul(r,a,p)
    return r
def squarefree(f,p):
    # gcd(f,f') const
    def pmod(a,b):
        a=a[:]
        inv=pow(b[-1],p-2,p)
        while len(a)>=len(b):
            q=a[-1]*inv%p; s=len(a)-len(b)
            for i,y in enumerate(b): a[s+i]=(a[s+i]-q*y)%p
            trim(a)
        return a
    a,b=f[:],deriv(f,p)
    if not b: return False
    while b: a,b=b,pmod(a,b)
    return len(a)==1
def params(p,m):
    c=(p-1)//2; A=c-m+1; J=int(math.floor(math.sqrt(p)/(4*math.sqrt(m)))); l=2*J-1
    return c,A,J,l
# (1)
bad=0
for m in range(1,13):
    for p in range(3,40000):
        if p<144*m*m or not isprime(p): continue
        c,A,J,l=params(p,m)
        ok = J>=1 and A>=2 and l<=A and l<=p and 2*(A-1)+m<p and J+m<=p and l*(A+J-1+(l-1)*(m-1))<2*J*A
        bnd=(A-1+c*m+p*(J-1))/l
        if not ok or bnd> p/2+2*m**1.5*math.sqrt(p): bad+=1; print("param fail",p,m)
print("(1) parameter failures:",bad)
# (2)
worst=0
for p in [q for q in range(3,400) if isprime(q)]:
    for m in range(1,7):
        for _ in range(6):
            f=[random.randrange(p) for _ in range(m)]+[random.randrange(1,p)]
            if not squarefree(f,p): continue
            chi=[0]*p
            for x in range(p):
                v=ev(f,x,p); chi[x]=0 if v==0 else (1 if pow(v,(p-1)//2,p)==1 else -1)
            s=sum(chi); worst=max(worst,abs(s)/(m*m*math.sqrt(p)))
            assert abs(s)<=12*m*m*math.sqrt(p)
            if p>=144*m*m:
                for e in (1,-1): assert chi.count(e)<=p/2+2*m**1.5*math.sqrt(p)
print("(2) max |sum chi|/(m^2 sqrt p) =",round(worst,3),"(bound 12)")
# (3) explicit auxiliary polynomial, small parameters (not the asymptotic choice)
def nullvec(M,ncols,p):
    M=[r[:] for r in M]; piv=[]; r=0
    for col in range(ncols):
        pr=next((i for i in range(r,len(M)) if M[i][col]),None)
        if pr is None: continue
        M[r],M[pr]=M[pr],M[r]; inv=pow(M[r][col],p-2,p); M[r]=[x*inv%p for x in M[r]]
        for i in range(len(M)):
            if i!=r and M[i][col]:
                t=M[i][col]; M[i]=[(x-t*y)%p for x,y in zip(M[i],M[r])]
        piv.append(col); r+=1
    free=[c for c in range(ncols) if c not in piv]
    v=[0]*ncols; v[free[0]]=1
    for i,col in enumerate(piv): v[col]=(-M[i][free[0]])%p
    return v
def build(p,f,A,J,l,eps):
    m=len(f)-1; c=(p-1)//2; fp=deriv(f,p); n=2*J*A
    def Qs(v):
        out=[]
        for k in range(l):
            Q=[]
            for j in range(J):
                r=trim(v[(j*2)*A:(j*2)*A+A]); s=trim(v[(j*2+1)*A:(j*2+1)*A+A])
                rk=r
                for _ in range(k): rk=deriv(rk,p)
                u=s
                for i in range(k): u=padd(pmul(f,deriv(u,p),p),pscale(pmul(fp,u,p),(c-i)%p,p),p)
                term=padd(pmul(ppow(f,k,p),rk,p),pscale(u,eps%p,p),p)
                Q=padd(Q,[0]*j+term,p)
            out.append(Q)
        return out
    D=A+J-1+(l-1)*(m-1)
    cols=[]
    for t in range(n):
        e=[0]*n; e[t]=1; Q=Qs(e); cols.append([ (Q[k][d] if d<len(Q[k]) else 0) for k in range(l) for d in range(D)])
        assert all(len(q)<=D for q in Q)
    M=[[cols[t][i] for t in range(n)] for i in range(l*D)]
    v=nullvec(M,n,p)
    T=[]; g=ppow(f,c,p)
    for j in range(J):
        r=trim(v[(j*2)*A:(j*2)*A+A]); s=trim(v[(j*2+1)*A:(j*2+1)*A+A])
        T=padd(T,[0]*(p*j)+padd(r,pmul(s,g,p),p),p)
    assert T, "T vanished!"
    S=[x for x in range(p) if ev(g,x,p)==eps%p]
    for x in S:
        d=T
        for k in range(l): assert ev(d,x,p)==0,(p,x,k); d=deriv(d,p)
    return len(S), len(T)-1
for p,f,J,l in [(61,[1,0,0,1],2,3),(67,[2,3,0,1],2,3),(97,[1,1,0,0,1],2,3),(151,[5,0,1,1],3,5)]:
    m=len(f)-1; A=(p-1)//2-m+1; D=A+J-1+(l-1)*(m-1); assert l*D<2*J*A
    for eps in (1,-1):
        n,dT=build(p,f,A,J,l,eps)
        print(f"(3) p={p} m={m} eps={eps}: |S|={n}, deg T={dT}, l*|S|={l*n} <= degT bound {A-1+(p-1)//2*m+p*(J-1)}")
# (4) Salie fibre count: M(u,v) vs p + sum chi(f_{u,v}), f = A(A-4x), A=(u-x)(vx-1)
def chi(a,p):
    a%=p
    return 0 if a==0 else (1 if pow(a,(p-1)//2,p)==1 else -1)
for p in [5,7,11,13]:
    M={}
    for x in range(1,p):
        for y in range(1,p):
            for z in range(1,p):
                k=((x+y+z)%p,(pow(x,p-2,p)+pow(y,p-2,p)+pow(z,p-2,p))%p); M[k]=M.get(k,0)+1
    dev=0
    for u in range(p):
        for v in range(p):
            m=M.get((u,v),0)
            S=sum(chi(((u-x)*(v*x-1))*((u-x)*(v*x-1)-4*x),p) for x in range(p))
            bad=1 if (u!=0 and u*v%p==1) else 0
            assert abs(m-p)<=4+abs(S)+(p-1)*bad,(p,u,v)
            dev+=(m-p)**2
    print(f"(4) p={p}: fibre inequality OK; sum (M-p)^2 / p^3 = {dev/p**3:.3f} (proved bound 196^2+18)")
