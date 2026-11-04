import sys,subprocess,re,time; sys.path.insert(0,'.')
from katzmat import Katz
from flint import fmpz_mat
from math import comb
SC=sys.argv[1]
def val(x,p,PR):
    x%=p**PR
    if x==0:return PR
    v=0
    while x%p==0:x//=p;v+=1
    return v
def segs(p,PR,N):
    K=Katz(p,PR,N);U,D=K.matrices_list();mod=K.mod
    X=fmpz_mat(D)*fmpz_mat(U)
    X=fmpz_mat([[int(x)%mod for x in r] for r in X.tolist()])
    cp=X.charpoly();co=[int(c)%mod for c in cp.coeffs()];n=len(co)-1
    e=[co[n-k] for k in range(n+1)]
    pts=[(k,val(e[k],p,PR)) for k in range(n+1) if val(e[k],p,PR)<PR]
    hull=[]
    for q in pts:
        while len(hull)>=2 and (hull[-1][1]-hull[-2][1])*(q[0]-hull[-1][0])>=(q[1]-hull[-1][1])*(hull[-1][0]-hull[-2][0]):hull.pop()
        hull.append(q)
    out={}
    for a,b in list(zip(hull,hull[1:])):
        m=b[0]-a[0];s=(b[1]-a[1])/m
        if s!=int(s): out[s]=(m,None);continue
        s=int(s);c=[]
        for i in range(m+1):
            v=a[1]+i*s;x=e[a[0]+i]
            c.append((x//p**v)%p if v<PR else 0)
        inv=pow(c[0],-1,p);out[s]=(m,[y*inv%p for y in c])
    return out,hull[-1]
def gp(src):
    fn=SC+'/lw.gp';open(fn,'w').write('default(parisize,1000000000);\n'+src+'\nquit;\n')
    o=subprocess.run(['gp','-q',fn],stdin=subprocess.DEVNULL,capture_output=True,text=True).stdout
    L=[x for x in o.splitlines() if x.startswith('[')]
    return [int(t) for t in re.findall(r'-?\d+',L[-1])] if L else None
def cls(l,k,s2,s3,inv=False):
    # coefficients (high->low) of charpoly of a_l on new class, mod l
    if k<4: return [1]
    src=f"""l={l};k={k};mf=mfinit([6,k],0);
if(mfdim(mf)==0,print([1]);quit);
F=mfeigenbasis(mf);a2=mfatkineigenvalues(mf,2);a3=mfatkineigenvalues(mf,3);P=Mod(1,l)*x^0;
for(i=1,#F,if(a2[i][1]=={s2}&&a3[i][1]=={s3},v=mfcoefs(F[i],l)[l+1];cp=if(type(v)=="t_POLMOD",charpoly(v),x-v);P*=Mod(1,l)*cp));
print(lift(Vec(P)));"""
    return gp(src) or [1]
def b_zero(j,p):return comb(2*j+3,j)%p==0
def scale(T,u,p):return [pow(u,i,p)*T[i]%p for i in range(len(T))]
def rev(T,p):  # charpoly of inverse
    if len(T)==1:return T
    r=T[::-1];i=pow(r[0],-1,p);return [x*i%p for x in r]
def pmul(a,b,p):
    o=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):o[i+j]=(o[i+j]+x*y)%p
    return o
for arg in sys.argv[4:]:
    p=int(arg);PR=int(sys.argv[2]);N=int(sys.argv[3]);t=time.time()
    eps=1 if p%12 in(1,11) else -1
    S,reach=segs(p,PR,N)
    s2,s3=-(1 if p%8 in(1,7) else -1),-(1 if p%12 in(1,11) else -1)
    print(f'== l={p} eps={eps} reach={reach} {time.time()-t:.0f}s',flush=True)
    for j in sorted(S):
        m,c=S[j]
        if c is None:
            print(' slope',j,'mult',m,'NONINT');continue
        if b_zero(j,p):
            print(f' slope {j} mult {m} BINOM0',flush=True);continue
        b=comb(2*j+3,j)
        A=scale(cls(p,p-3-2*j,s2,s3),eps*pow(b,-1,p)%p,p)
        h=cls(p,2*j+4,-1,-1)
        if len(h)>1 and h[-1]%p==0:
            print(f' slope {j} mult {m} NONORDINARY h wt {2*j+4}',flush=True);continue
        B=scale(rev(h,p),eps*pow(b,-1,p)%p,p)
        pred=pmul(A,B,p)
        print(f' slope {j} mult {m} pred {len(A)-1}+{len(B)-1} match {pred==c}',flush=True)
