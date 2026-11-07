# Level-6 version of rc_tail_lattice: tame level Gamma0(6), s=-1, k'=l+1-k small.
# M_k(6) has basis G^{k/2} H^i, 0<=i<=k, with H=eta1^-5 eta2 eta3^-1 eta6^5 = q+..., G=eta1^12 eta2^-6 eta3^-4 eta6^2 = 1+...
# Law on the whole space: u*T|S_k(6) * u*T^-1|M_{k'}(6), both with Eisenstein eigenvalue 1.
import sys
src=open('rc_tail_lattice.py').read().split("if __name__=='__main__'")[0]
exec(src)
def dimM(k):
    return k+1 if k>=0 and k%2==0 else 0
_K=K
class K(_K):
    cache={}
    def __init__(S,p,a,PR,N):
        S.p,S.PR=p,PR;key=(p,PR,N)
        S._gh=None
        _K.__init__(S,p,a,PR,N)
    def gh(S):
        if S._gh is None:
            A=S.A;L=S.Lq;m=S.m
            def e(d,r):
                # (q^d;q^d)^r mod m, r possibly negative
                c=[0]*L;n=0
                while True:
                    g1=n*(3*n-1)//2*d;g2=n*(3*n+1)//2*d
                    if g1>=L:break
                    sg=1 if n%2==0 else -1
                    c[g1]=sg%m
                    if n and g2<L:c[g2]=sg%m
                    n+=1
                f=A.P(c)
                return A.pw(f,r) if r>=0 else A.pw(S.inv(f),-r)
            def prod(rs):
                o=A.P([1])
                for d,r in rs:o=A.mul(o,e(d,r))
                return o
            G=prod([(1,12),(2,-6),(3,-4),(6,2)])
            Hs=prod([(1,-5),(2,1),(3,-1),(6,5)])
            H=A.P([0]+[int(x) for x in Hs.coeffs()][:L-1])
            S._gh=(G,H)
        return S._gh
    def miller(S,kk):
        A=S.A;G,H=S.gh();d=kk+1;m0=kk//2
        Gm=A.pw(G,m0);out=[];cur=Gm
        for i in range(d):
            out.append(cur);cur=A.mul(cur,H)
        for t in range(d-1,-1,-1):
            for u in range(t):
                c=int(out[u][t]) if t<out[u].length() else 0
                if c:out[u]=out[u]-out[t]*c
        return out
    def Epow(S,n):
        S.__dict__.setdefault('_ep',{})
        if n not in S._ep:S._ep[n]=_K.Epow(S,n)
        return S._ep[n]
_memoT={}
def Tcp(p,kk,S):
    "charpoly high->low of U=T_l on Mbar_kk(6) mod p, via q-expansions"
    if kk<0:return [1]
    if (p,kk) in _memoT:return _memoT[(p,kk)]
    A=S.A;d=kk+1
    B=[[int(f[i])%p if i<f.length() else 0 for i in range(p*(d+1))] for f in S.miller(kk)]
    # B echelon q^t+O(q^d) mod p
    Um=[[b[p*i]%p for i in range(d)] for b in B]  # rows: images in coords of basis
    M=nmod_mat(d,d,[Um[c][r] for r in range(d) for c in range(d)],p)
    co=[int(x) for x in M.charpoly().coeffs()][::-1]
    _memoT[(p,kk)]=co;return co
def pdiv1(c,p,times):
    c=c[:]
    for _ in range(times):
        o=[];r=0
        for x in c:
            r=(x+r)%p;o.append(r)
        if o[-1]!=0:raise Exception('no factor x-1')
        c=o[:-1]
    return c
def law6(p,k,s,j,S):
    u=Fraction(1)
    for i in range(j):u*=Fraction(s-i,k+i)
    if u.numerator%p==0 or u.denominator%p==0:return None
    uu=u.numerator*pow(u.denominator,-1,p)%p
    sc=lambda T,x:[pow(x,i,p)*T[i]%p for i in range(len(T))]
    def rev(T):
        if len(T)==1:return T
        r=T[::-1];iv=pow(r[0],-1,p);return [y*iv%p for y in r]
    def mul(A,B):
        o=[0]*(len(A)+len(B)-1)
        for i,x in enumerate(A):
            for t,y in enumerate(B):o[i+t]=(o[i+t]+x*y)%p
        return o
    kp=p+1-k
    Tk=pdiv1(Tcp(p,k,S),p,4)
    Tp=Tcp(p,kp,S)
    Tp=Tp if kp!=2 else pdiv1(Tp,p,0)
    if Tp[-1]==0:return None
    return mul(sc(Tk,uu),sc(rev(Tp),uu))
def run(p,k,j,s=-1):
    a=k+2*j;PR=j+5;N=k+j+3
    while p**PR>=2**63:PR-=1
    return a,PR,N
if __name__=='__main__':
    p=int(sys.argv[1])
    for spec in sys.argv[2].split(','):
        k,j=map(int,spec.split(':'))
        a,PR,N=run(p,k,j)
        S0=K(p,k+2,PR,1)
        law=lambda P,KK,ss,jj:law6(P,KK,ss,jj,S0)
        print(f'p={p} k={k} kp={p+1-k} j={j} w={a-p+1}',rec_test(p,a,-1,j,PR,N),flush=True)
