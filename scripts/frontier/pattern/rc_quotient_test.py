# Test in M_w/Lambda, Lambda = saturated slope<j part of T_l on M_w(1):
#   T [g,E^s]_j == l^j u [Tg,E^s]_j   mod (Lambda + l^{j+1} M_w), u = C(s,j)/C(k+j-1,j).  Control: u+1.
import sys
from flint import fmpz_poly
exec(open('rc_tri_test.py').read().split("if __name__")[0])
cachePow={}
def miller_int(w,L):
    d=dimM(w)
    E4=[1]+[240*sum(x**3 for x in range(1,n+1) if n%x==0) for n in range(1,L)]
    E6=[1]+[-504*sum(x**5 for x in range(1,n+1) if n%x==0) for n in range(1,L)]
    tr=lambda f:fmpz_poly(f.coeffs()[:L])
    a4=fmpz_poly(E4);a6=fmpz_poly(E6)
    def pw(f,n):
        r=fmpz_poly([1])
        for _ in range(n):r=tr(r*f)
        return r
    Dl=fmpz_poly([int(x)//1728 for x in tr(a4*a4*a4-a6*a6).coeffs()])
    base=[]
    for a in range(d):
        r=w-12*a
        for c in range(3):
            if r-6*c>=0 and (r-6*c)%4==0:b=(r-6*c)//4;break
        base.append(tr(tr(pw(Dl,a)*pw(a4,b))*pw(a6,c)))
    for t in range(d-1,-1,-1):
        for u_ in range(t):
            c=int(base[u_][t]) if t<len(base[u_].coeffs()) else 0
            if c:base[u_]=base[u_]-base[t]*c
    return base
def heckemat(p,w):
    d=dimM(w);L=p*d+2;B=miller_int(w,L)
    M=[[0]*d for _ in range(d)]
    for t,f in enumerate(B):
        c=f.coeffs()
        for i in range(d):
            x=int(c[p*i]) if p*i<len(c) else 0
            if i%p==0 and i//p<len(c) : x+=p**(w-1)*int(c[i//p])
            M[i][t]=x
    return M
def matmul(A,B,m):
    n=len(A);return [[sum(A[i][k]*B[k][j] for k in range(n))%m for j in range(n)] for i in range(n)]
def low_lattice(T,p,j,e):
    "basis (mod p^e) of saturated slope<j sublattice"
    if j==0:return []
    n=8;M=p**(n*j+2*e+4);A=[[x%M for x in r] for r in T]
    P=A
    for _ in range(n-1):P=matmul(P,A,M)
    cols=[[P[i][c] for i in range(len(P))] for c in range(len(P))]
    out=[];used=[False]*len(cols)
    def val(x):
        x%=M
        if x==0:return 10**6
        t=0
        while x%p==0:x//=p;t+=1
        return t
    limit=n*(j-1)+n//2  # slopes<=j-1 have pivot val <= n(j-1)+small; slopes>=j have val>=nj
    while True:
        best=None
        for a,g in enumerate(cols):
            if used[a]:continue
            for r in range(len(g)):
                t=val(g[r])
                if best is None or t<best[0]:best=(t,a,r)
        if best is None or best[0]>limit:break
        t,a,r=best;used[a]=True;g=cols[a]
        un=pow(g[r]//p**t,-1,M)
        for b,h in enumerate(cols):
            if b!=a and not used[b] and h[r]%M:
                f=(h[r]//p**t)*un%M
                cols[b]=[(x-f*y)%M for x,y in zip(h,g)]
        out.append([ (y//p**t)%p**e for y in g])
    return out
def run2(p,s,j,k):
    e=j+1;l=s*(p-1);w=k+l+2*j;D=dimM(w)
    T=heckemat(p,w);Tk=heckemat(p,k);dk=dimM(k)
    A=R(p,e,D+2);m=A.m
    A.L=max(D+2,8)
    E4=A.eis(4);E6=A.eis(6);Dl=A.tr((A.pw(E4,3)-A.mul(E6,E6))*pow(1728,-1,m))
    W=A.pw(A.eis(p-1),s)
    Bk=[]
    for t,f in enumerate(miller_int(k,D+2)):
        Bk.append(A.P([int(x) for x in f.coeffs()]))
    def br(g):
        z=A.P([0])
        for r in range(j+1):
            co=(-1)**r*cbin(k+j-1,j-r)*cbin(l+j-1,r)
            z=z+A.mul(A.th(g,r),A.th(W,j-r))*fr(co,m)
        return A.tr(z)
    vec=lambda f:[(int(f[i]) if i<f.length() else 0) for i in range(D)]
    Lam=low_lattice(T,p,j,e)
    den=cbin(k+j-1,j)
    if den.numerator%p==0 or cbin(s,j).numerator%p==0:return 'binom0'
    u=fr(cbin(s,j)/den,m)
    out=[]
    Fs=[vec(br(g)) for g in Bk]
    for t in range(dk):
        TF=[sum(T[i][c]*Fs[t][c] for c in range(D))%m for i in range(D)]
        Tg=[sum(Tk[i][t]*Fs[i][c] for i in range(dk))%m for c in range(D)]
        pj=p**j
        a=[(x-pj*u*y)%m for x,y in zip(TF,Tg)]
        b=[(x-pj*(u+1)*y)%m for x,y in zip(TF,Tg)]
        sig=solve(Tg,Lam,p,e)  # True would make the test vacuous
        out.append((solve(a,Lam,p,e),solve(b,Lam,p,e),sig))
    return out,'lamrank',len(Lam),'dim',D
if __name__=='__main__':
    p=int(sys.argv[1])
    for s in map(int,sys.argv[2].split(',')):
      for j in map(int,sys.argv[3].split(',')):
        if j>s:continue
        for k in map(int,sys.argv[4].split(',')):
            print(f'p={p} s={s} j={j} k={k}',run2(p,s,j,k),flush=True)
