import sys,subprocess,re; sys.path.insert(0,'.')
from katzmat import Katz
from flint import fmpz_mat
def val(x,p,PR):
    x%=p**PR
    if x==0:return PR
    v=0
    while x%p==0:x//=p;v+=1
    return v
def segs(p,PR,N):
    K=Katz(p,PR,N);Um,Dm=K.matrices();X=Dm*Um;mod=K.mod
    cp=fmpz_mat([[int(x)%mod for x in r] for r in X.tolist()]).charpoly()
    co=[int(c)%mod for c in cp.coeffs()];n=len(co)-1
    e=[co[n-k] for k in range(n+1)]  # coefficient of x^{n-k}
    pts=[(k,val(e[k],p,PR)) for k in range(n+1) if val(e[k],p,PR)<PR]
    hull=[]
    for q in pts:
        while len(hull)>=2 and (hull[-1][1]-hull[-2][1])*(q[0]-hull[-1][0])>=(q[1]-hull[-1][1])*(hull[-1][0]-hull[-2][0]):hull.pop()
        hull.append(q)
    out=[]
    for a,b in zip(hull,hull[1:]):
        m=b[0]-a[0];s=(b[1]-a[1])/m
        if s!=int(s): out.append((s,m,None));continue
        s=int(s)
        # residual polynomial: sum_{i} [e_{a0+i}/p^{a1+i s} mod p] x^{m-i}; monic after normalising
        c=[]
        for i in range(m+1):
            v=a[1]+i*s
            x=e[a[0]+i]
            c.append((x//p**v)%p if v<PR and x%p**v==0 else 0)
        inv=pow(c[0],-1,p)
        out.append((s,m,[y*inv%p for y in c]))  # high to low degree
    return out
def tl(l,k):
    if k<2:return None
    src=f"""default(parisize,800000000);
l={l};k={k};mf=mfinit([6,k],0);
if(mfdim(mf)==0,print([1]);quit);
F=mfeigenbasis(mf);a2=mfatkineigenvalues(mf,2);a3=mfatkineigenvalues(mf,3);
P=Mod(1,l)*x^0;
for(i=1,#F,if(a2[i][1]==-kronecker(2,l)&&a3[i][1]==-kronecker(3,l),v=mfcoefs(F[i],l)[l+1];cp=if(type(v)=="t_POLMOD",charpoly(v),x-v);P*=Mod(1,l)*cp));
print(lift(Vec(P)));
quit;
"""
    fn='/private/tmp/claude-501/-Users-thomasdifiore/3c9a29fe-4bf4-4965-be2d-1c6f6abd56b0/scratchpad/tl.gp';open(fn,'w').write(src)
    o=subprocess.run(['gp','-q',fn],stdin=subprocess.DEVNULL,capture_output=True,text=True).stdout
    L=[x for x in o.splitlines() if x.startswith('[')]
    return [int(t) for t in re.findall(r'-?\d+',L[-1])] if L else None

from math import comb,gcd
def polydiv(c,d,p):
    c=c[:];q=[]
    for i in range(len(c)-len(d)+1):
        t=c[i]%p;q.append(t)
        for j in range(len(d)):c[i+j]=(c[i+j]-t*d[j])%p
    return q,c[-(len(d)-1):] if len(d)>1 else [0]
res=[]
PL=[(29,12),(31,12),(37,12),(41,11),(43,11),(47,11),(53,10),(59,10),(61,10),(67,10),(71,10),(73,10),(79,9),(83,9),(89,9),(97,9),(101,9),(103,9),(107,8),(109,8),(113,8)]
for p,PR in PL:
    eps=1 if p%12 in(1,11) else -1
    for s_,m,c in segs(p,PR,10 if p<60 else 8):
        if c is None or s_>2: 
            if c is None: print(p,'nonint',s_,m)
            continue
        k=p-3-2*s_;T=tl(p,k) or [1];d=len(T)-1
        u=eps*pow(comb(2*s_+3,s_),-1,p)%p
        pred=[pow(u,i,p)*T[i]%p for i in range(d+1)]
        if m==d:
            print(p,'slope',s_,'mult=dim',m,'match',pred==c)
        elif m>d:
            q,r=polydiv(c,pred,p)
            ok=all(x==0 for x in r)
            print(p,'slope',s_,'mult',m,'dim',d,'divides',ok,'quotient',q)
            if ok and m==d+1: res.append((p,eps,(-q[1])%p))
        else:
            print(p,'slope',s_,'mult',m,'<dim',d,'(truncated)')
print('extras',res)
for name,f in [('r',lambda p,e,r:r),('e*r',lambda p,e,r:e*r%p)]:
    pts=[(p,f(p,e,r)) for p,e,r in res]
    fits=[]
    for b in range(1,600):
        for a in range(-6000,6001):
            if a and gcd(abs(a),b)==1 and all((a-b*v)%p==0 for p,v in pts): fits.append((a,b))
    print(name,pts,'fits',fits[:6])
