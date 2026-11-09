# exact integer q-series to order N
N = 400
def mul(a,b):
    r=[0]*N
    for i,x in enumerate(a):
        if x:
            for j in range(N-i):
                r[i+j]+=x*b[j]
    return r
def inv(a):
    assert a[0] in (1,-1)
    r=[0]*N; r[0]=a[0]
    for k in range(1,N):
        s=sum(a[i]*r[k-i] for i in range(1,k+1))
        r[k]=-s*a[0]
    return r
def mono(e,c=1):
    r=[0]*N
    if 0<=e<N: r[e]=c
    return r
def add(*xs):
    return [sum(t) for t in zip(*xs)]
def sc(c,a): return [c*x for x in a]
def one(): return mono(0)
def fac(z_e, sgn, step, n):  # prod_{k<n} (1 - sgn q^{z_e+k step})
    r=one()
    for k in range(n):
        e=z_e+k*step
        if e>=N: break
        r=mul(r, add(one(), mono(e,-sgn)))
    return r
def inf(z_e, step, sgn=1): # prod_{k>=0}(1 - sgn q^{z_e+k step})
    return fac(z_e,sgn,step,(N//step)+2)
def sub_q(a,m):  # a(q^m)
    r=[0]*N
    for i,x in enumerate(a):
        if i*m<N: r[i*m]=x
        else: break
    return r
def negq(a): return [x*(-1)**i for i,x in enumerate(a)]
def ssum(term, nmax=40):
    r=[0]*N
    for n in range(nmax):
        t=term(n)
        if t is None: break
        r=add(r,t)
    return r
def qmul_shift(a,e): return mul(mono(e),a)
# fifth order
def f0(): return ssum(lambda n: mul(mono(n*n), inv(fac(1,-1,1,n))) if n*n<N else None)
def f1(): return ssum(lambda n: mul(mono(n*n+n), inv(fac(1,-1,1,n))) if n*n<N else None)
def F0(): return ssum(lambda n: mul(mono(2*n*n), inv(fac(1,1,2,n))) if 2*n*n<N else None)
def F1(): return ssum(lambda n: mul(mono(2*n*n+2*n), inv(fac(1,1,2,n+1))) if 2*n*n<N else None)
def phi0(): return ssum(lambda n: mul(mono(n*n), fac(1,-1,2,n)) if n*n<N else None)
def phi1(): return ssum(lambda n: mul(mono((n+1)**2), fac(1,-1,2,n)) if n*n<N else None)
def psi0(): return ssum(lambda n: mul(mono((n+1)*(n+2)//2), fac(1,-1,1,n)) if n*(n+1)//2<N else None)
def psi1(): return ssum(lambda n: mul(mono(n*(n+1)//2), fac(1,-1,1,n)) if n*(n+1)//2<N else None)
def chi0(): return ssum(lambda n: mul(mono(n), inv(fac(n+1,1,1,n))) if n<N else None, N)
def chi1(): return ssum(lambda n: mul(mono(n), inv(fac(n+1,1,1,n+1))) if n<N else None, N)
# Ramanujan's Phi, Psi (repo's phi, psi)
def RPhi(): return add(sc(-1,one()), ssum(lambda n: mul(mono(5*n*n), inv(mul(fac(1,1,5,n+1),fac(4,1,5,n)))) if 5*n*n<N else None))
def RPsi(): return add(sc(-1,one()), ssum(lambda n: mul(mono(5*n*n), inv(mul(fac(2,1,5,n+1),fac(3,1,5,n)))) if 5*n*n<N else None))
def eta_exps(a):
    """if a = c q^s prod (1-q^n)^{e_n}, return (s,c,e list) else None"""
    s=next(i for i,x in enumerate(a) if x)
    c=a[s]; b=a[s:]+[0]*s
    if abs(c)!=1: return s,c,None
    b=[x*c for x in b]
    e=[0]*(N-s)
    cur=b[:]
    # successive: find e_n so that cur * prod (1-q^n)^{-e_n} = 1
    M=N-s
    for n in range(1,M):
        # coefficient of q^n in cur after removing lower factors
        e[n]=-cur[n]
        if abs(e[n])>40: return s,c,None
        # divide cur by (1-q^n)^{e[n]}
        if e[n]>0:
            for _ in range(e[n]):
                # cur /= (1-q^n)
                for k in range(n,M): cur[k]+=cur[k-n]
        elif e[n]<0:
            for _ in range(-e[n]):
                for k in range(M-1,n-1,-1): cur[k]-=cur[k-n]
    return s,c,e
def period(e, maxp=60, start=1):
    M=len(e)
    for p in range(1,maxp+1):
        if all(e[n]==e[n+p] for n in range(start, M//2) ):
            return p, e[1:p+1]
    return None
