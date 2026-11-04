# Mod-l operator B[x] = Ubar(e x) on ker Ubar in Mbar_{k+l+1}(1), modulo Ebar Mbar_{k+2}.
# Tests: (a) charpoly of B on gr^1 = (1/k)T|S_k * (1/k)T^{-1}|M_{l+1-k};
#        (b) for h' eigen of weight k'=l+1-k with T h'=alpha h': B[theta^k h'] == (1/(k alpha)) theta^k h' mod theta Mbar_k + Mbar_{k+2}.
import sys,sympy
from fractions import Fraction
from flint import nmod_poly,nmod_mat
exec(open('rc_slope_law_level1.py').read().split("tot=ok=0")[0])
def dimM(k):
    if k<0 or k%2 or k==2:return 0
    return k//12+(0 if k%12==2 else 1)
def rank_basis(vs,p):
    "row reduce vectors mod p; returns echelon rows, pivots"
    rows=[];piv=[]
    for v in vs:
        v=[x%p for x in v]
        for r,c in zip(rows,piv):
            if v[c]:
                f=v[c];v=[(a-f*b)%p for a,b in zip(v,r)]
        c=next((i for i,x in enumerate(v) if x),None)
        if c is None:continue
        inv=pow(v[c],-1,p);v=[x*inv%p for x in v]
        for i in range(len(rows)):
            if rows[i][c]:
                f=rows[i][c];rows[i]=[(a-f*b)%p for a,b in zip(rows[i],v)]
        rows.append(v);piv.append(c)
    return rows,piv
def red(v,E_,p):
    v=[x%p for x in v]
    for r,c in zip(*E_):
        if v[c]:
            f=v[c];v=[(a-f*b)%p for a,b in zip(v,r)]
    return v
class S:
    def __init__(s,p,L):
        s.p,s.L=p,L;m=p*p;s.m=m
        def eis(k,mod):
            B=sympy.bernoulli(k);c=Fraction(-2*k)/Fraction(B.p,B.q);c=c.numerator*pow(c.denominator,-1,mod)%mod
            sg=[0]*L
            for d in range(1,L):
                dk=pow(d,k-1,mod)
                for n in range(d,L,d):sg[n]+=dk
            return [1]+[c*(sg[n]%mod)%mod for n in range(1,L)]
        E=eis(p-1,m);assert all(x%p==0 for x in E[1:])
        s.e=nmod_poly([0]+[x//p for x in E[1:]],p)
        s.E4=nmod_poly([x%p for x in eis(4,m)],p);s.E6=nmod_poly([x%p for x in eis(6,m)],p)
        s.Dl=s.tr((s.E4*s.E4*s.E4-s.E6*s.E6)*pow(1728,-1,p))
        s.memo={}
    def tr(s,f,n=None):return nmod_poly(f.coeffs()[:n or s.L],s.p)
    def pw(s,f,n):
        r=nmod_poly([1],s.p);b=f
        while n:
            if n&1:r=s.tr(r*b)
            b=s.tr(b*b);n>>=1
        return r
    def miller(s,k):
        if k in s.memo:return s.memo[k]
        d=dimM(k);out=[]
        for a in range(d):
            r=k-12*a
            for c in range(3):
                if r-6*c>=0 and (r-6*c)%4==0:b=(r-6*c)//4;break
            out.append(s.tr(s.tr(s.pw(s.Dl,a)*s.pw(s.E4,b))*s.pw(s.E6,c)))
        for t in range(d-1,-1,-1):
            for u in range(t):
                c=int(out[u][t]) if t<out[u].length() else 0
                if c:out[u]=out[u]-out[t]*c
        s.memo[k]=out;return out
    def th(s,f,r=1):
        c=f.coeffs();return nmod_poly([pow(i,r,s.p)*int(x)%s.p for i,x in enumerate(c)],s.p)
    def U(s,f):
        c=f.coeffs();p=s.p
        return nmod_poly([int(c[p*n]) if p*n<len(c) else 0 for n in range((len(c)+p-1)//p)],p)
def vec(f,n):return [(int(f[i]) if i<f.length() else 0) for i in range(n)]
def charpoly_mat(M,p):
    n=len(M)
    if n==0:return [1]
    c=nmod_mat(n,n,[x%p for r in M for x in r],p).charpoly()
    co=[int(x) for x in c.coeffs()];return co[::-1]
def pmul(a,b,p):
    o=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):o[i+j]=(o[i+j]+x*y)%p
    return o
def scale(T,u,p):return [pow(u,i,p)*T[i]%p for i in range(len(T))]
def rev(T,p):
    if len(T)==1:return T
    r=T[::-1];i=pow(r[0],-1,p);return [x*i%p for x in r]
def run(p,k):
    W=k+p+1;Dw=dimM(W);L=p*(Dw+8)+2;A=S(p,L);N=Dw+6
    Mw=A.miller(W)
    # U on M_W as q-series first N coeffs; kernel inside M_W
    Uv=[vec(A.U(f),N) for f in Mw]
    M_=nmod_mat(Dw,N,[x for r in Uv for x in r],p)
    # left kernel of Uv
    rows=[r+[1 if i==t else 0 for i in range(Dw)] for t,r in enumerate(Uv)]
    ker=[]
    Rr,Pv=[],[]
    for r in rows:
        v=r[:]
        for x,c in zip(Rr,Pv):
            if v[c]:
                f=v[c];v=[(a-f*b)%p for a,b in zip(v,x)]
        c=next((i for i,x in enumerate(v[:N]) if x),None)
        if c is None:ker.append(v[N:]);continue
        inv=pow(v[c],-1,p);v=[x*inv%p for x in v];Rr.append(v);Pv.append(c)
    kerf=[]
    for cf in ker:
        g=nmod_poly([0],p)
        for t,x in enumerate(cf):
            if x:g=g+Mw[t]*x
        kerf.append(A.tr(g))
    low=[vec(f,Dw) for f in A.miller(k+2)]     # Ebar M_{k+2} == M_{k+2} as q-series mod p
    Elow=rank_basis(low,p)
    # image of ker in gr^1
    imgs=[red(vec(f,Dw),Elow,p) for f in kerf]
    Eker=rank_basis(imgs,p)
    rk=len(Eker[0])
    # B on kerf, expressed in gr^1 coordinates (columns = echelon rows' pivots)
    Bm=[]
    idx=[]
    ER,ERp=[],[]
    picks=[]
    for f,im in zip(kerf,imgs):
        r=rank_basis(ER+[im],p)
        if len(r[0])>len(ER):
            ER=ER+[im];picks.append((f,im))
    Ebas=rank_basis([im for _,im in picks],p)
    # coordinates of v in terms of picks
    def coords(v):
        A_=[im for _,im in picks];n=len(A_)
        rows=[list(col)+[0] for col in zip(*A_)] if False else None
        # solve via augmented elimination on pivot columns
        cols=Ebas[1]
        Mat=[[A_[j][c] for j in range(n)]+[v[c]] for c in cols]
        for i in range(n):
            pv=next(r for r in range(i,n) if Mat[r][i]%p)
            Mat[i],Mat[pv]=Mat[pv],Mat[i]
            inv=pow(Mat[i][i],-1,p);Mat[i]=[x*inv%p for x in Mat[i]]
            for r in range(n):
                if r!=i and Mat[r][i]%p:
                    g=Mat[r][i];Mat[r]=[(a-g*b)%p for a,b in zip(Mat[r],Mat[i])]
        return [Mat[i][n]%p for i in range(n)]
    closed=True
    for f,im in picks:
        out=vec(A.U(A.tr(f*A.e)),Dw)
        rr=red(out,Elow,p)
        chk=red(rr,Ebas,p)
        if any(chk):closed=False
        Bm.append(coords(rr))
    n=len(picks)
    mat=[[Bm[j][i] for j in range(n)] for i in range(n)]
    cB=charpoly_mat(mat,p) if closed else None
    ki=pow(k,-1,p)
    Tk=[x%p for x in cp(p,k)] if k>=12 else [1]
    hp=[x%p for x in cp(p,p+1-k)] if p+1-k>=12 else [1]
    if p+1-k>=4:hp=pmul(hp,[1,p-1],p)
    pred=pmul(scale(Tk,ki,p),scale(rev(hp,p),ki,p),p)
    return dict(k=k,kerdim=len(kerf),gr1=rk,dimGr=Dw-dimM(k+2),closed=closed,match=(cB==pred),deg=len(pred)-1)
if __name__=='__main__':
    p=int(sys.argv[1]);good=tot=0
    for k in range(int(sys.argv[2]),p-1,2):
        r=run(p,k);tot+=1;good+=bool(r['match']);print(p,r,flush=True)
    print('match',good,'/',tot)
