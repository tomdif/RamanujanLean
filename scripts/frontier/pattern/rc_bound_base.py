# Katz matrix of U on p-adic weight w: basis x_t = b_t E^{s-i(t)}, w = a+s(p-1), b_t top-Miller in M_{a+i(p-1)}.
# Checks v(entry row i, col j) >= ceil((p i - j)/(p+1)) with no -1, and how often the bound is attained.
import sys,sympy
from fractions import Fraction
from flint import nmod_poly
from math import ceil
exec(open('rc_tri_test.py').read().split("def cbin")[0].split("class R:")[0])
exec("class R:"+open('rc_tri_test.py').read().split("class R:")[1].split("def cbin")[0])
def run(p,a,s,PR,N):
    m=p**PR
    dims=[dimM(a+i*(p-1)) for i in range(N+1)];dN=dims[N]
    idx=[next(i for i in range(N+1) if dims[i]>t) for t in range(dN)]
    LQ=dN+2;L=p*LQ+2;A=R(p,PR,L)
    E4=A.eis(4);E6=A.eis(6);E=A.eis(p-1)
    Dl=A.tr((A.pw(E4,3)-A.mul(E6,E6))*pow(1728,-1,m))
    def inv(f):
        g=A.P([pow(int(f[0]),-1,m)]);n=1
        while n<L:
            n=min(2*n,L);fg=nmod_poly(((f*g)).coeffs()[:n],m);g=nmod_poly((g*(A.P([2])-fg)).coeffs()[:n],m)
        return g
    Ei=inv(E)
    def miller(kk):
        d=dimM(kk);out=[]
        for x in range(d):
            r=kk-12*x
            for c in range(3):
                if r-6*c>=0 and (r-6*c)%4==0:b=(r-6*c)//4;break
            out.append(A.mul(A.mul(A.pw(Dl,x),A.pw(E4,b)),A.pw(E6,c)))
        for t in range(d-1,-1,-1):
            for u in range(t):
                c=int(out[u][t]) if t<out[u].length() else 0
                if c:out[u]=out[u]-out[t]*c
        return out
    M={i:miller(a+i*(p-1)) for i in range(N+1)}
    EM={i:[A.mul(f,E) for f in M[i-1]] for i in range(1,N+1)}
    EN=A.pw(E,N)
    def Epow(n):
        return A.pw(E,n) if n>=0 else A.pw(Ei,-n)
    def decompose(F):
        # F has weight a (after dividing by E^s); coordinates of E^N F in Katz decomposition
        G=nmod_poly(A.mul(F,EN).coeffs()[:LQ],m);out=[0]*dN
        for i in range(N,0,-1):
            R_=G;c=[]
            for t in range(len(EM[i])):
                ct=int(R_[t]) if t<R_.length() else 0;c.append(ct)
                if ct:R_=R_-nmod_poly(EM[i][t].coeffs()[:LQ],m)*ct
            for t in range(dims[i-1],dims[i]):
                out[t]=int(R_[t]) if t<R_.length() else 0
            G=A.P([0])
            for t,x in enumerate(c):
                if x:G=G+nmod_poly(M[i-1][t].coeffs()[:LQ],m)*x
        for t in range(dims[0]):
            out[t]=int(G[t]) if t<G.length() else 0
        return out
    Es=Epow(s);Es_inv=Epow(-s)
    viol=[];att=tot=0;viol1=0
    def v(x):
        x%=m
        if x==0:return PR
        c=0
        while x%p==0:x//=p;c+=1
        return c
    for col in range(dN):
        j=idx[col]
        x=A.mul(M[j][col],Epow(s-j))     # x_t, true weight w
        Ux=A.U(x)
        Ux=A.P(list(Ux.coeffs())+[0]*(L-Ux.length())) if False else Ux
        co=decompose(A.tr(Ux*Es_inv))
        for row in range(dN):
            i=idx[row];bd=ceil(Fraction(p*i-j,p+1))
            bd=max(bd,0)
            if bd>=PR-1:continue
            tot+=1;val=v(co[row])
            if val<bd:viol.append((i,j,val,bd))
            if val==bd:att+=1
    return tot,att,viol
p=int(sys.argv[1]);PR=int(sys.argv[2]);N=int(sys.argv[3])
for a,s in [tuple(map(int,x.split(':'))) for x in sys.argv[4].split(',')]:
    t,at,vi=run(p,a,s,PR,N)
    print(f'p={p} a={a} s={s}: entries {t}, attained {at}, violations {len(vi)}',vi[:6],flush=True)
