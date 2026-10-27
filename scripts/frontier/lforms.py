# L_l(b) as q-series mod l^k, from p(n) table
import numpy as np, sys
l=int(sys.argv[1]) if len(sys.argv)>1 else 17
p=np.fromfile('p1e8.bin',dtype=np.uint64); NMAX=len(p)-1
Mtab={17:17**5,19:19**4,23:23**4}
def Eser(L,step=1):
    E=[0]*L
    for k in range(-2000,2001):
        e=step*(k*(3*k-1)//2)
        if 0<=e<L: E[e]+=(1 if k%2==0 else -1)
    return E
def mul(a,b,mod,L):
    c=[0]*L
    for i,x in enumerate(a[:L]):
        if x:
            for j in range(L-i):
                if b[j]: c[i+j]=(c[i+j]+x*b[j])%mod
    return c
def Lform(b,L,mod):
    # P(b;z)=sum p((l^b n+1)/24) q^{n/24}, n ≡ -l^{-b} mod 24
    r=(-pow(l,-b,24))%24
    if b%2==1: shift=l   # eta(l z)
    else: shift=1
    # term q^{(n+shift)/24}; (r+shift)%24 should be 0
    assert (r+shift)%24==0
    off=(r+shift)//24
    S=[0]*L
    for k in range(L):
        n=24*k+r; m=(l**b*n+1)//24
        e=k+off
        if e<L:
            if m>NMAX: return None
            S[e]=int(p[m])%mod
    E=Eser(L, l if b%2==1 else 1)
    return mul(S,E,mod,L)
if __name__=='__main__':
    for b in range(1,5):
        f=Lform(b,40,l**3)
        print(b, None if f is None else f[:8])
