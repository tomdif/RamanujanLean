import sys
exec(open('filt.py').read().split("mod=l**3")[0])
mod=l**2
E=[1]+[0]*(L-1)
# E_{l-1} via E4,E6 combos: use normalized Eisenstein E_{l-1} = 1 - (2(l-1)/B) sum sigma ; compute directly
from fractions import Fraction
import sympy
k=l-1; B=sympy.bernoulli(k); c=Fraction(-2*k)/Fraction(B.p,B.q)
Ek=[1]+[int((c*sigma(n,k-1)).numerator*pow((c*sigma(n,k-1)).denominator,-1,mod))%mod if (c*sigma(n,k-1)).denominator%l else None for n in range(1,L)]
assert None not in Ek
def pw(f,e):
    r=[1]+[0]*(L-1)
    for _ in range(e): r=mul(r,f,mod,L)
    return r
Epow=pw(Ek,l-1)   # E_{l-1}^{l-1}: weight (l-1)^2, ≡1 mod l
for b in (1,2,3):
    G=Lform(b,L,mod)
    if G is None: continue
    g0=[x%l for x in G]                 # digit 0, filtration l-1 : multiple of Delta*E_{l-13}
    # weight-(l-1) lift: find c with g0 ≡ c*h (h = basis element of S_{l-1}, take from basis(l-1))
    S=basis(l-1,mod)
    # cusp form of weight l-1 with leading q coefficient: combination of E4^aE6^b with zero constant term
    # simplest: use h = first-order part via solving: find combination vanishing at q^0
    import itertools
    best=None
    # brute small search over two basis elements
    for i,j in itertools.combinations(range(len(S)),2):
        a0,b0=S[i][0],S[j][0]
        h=[(b0*x-a0*y)%mod for x,y in zip(S[i],S[j])]
        if h[0]%mod==0 and any(v%l for v in h): best=h;break
    h=best
    i0=next(i for i,x in enumerate(h) if x%l)
    cc=G[i0]*pow(h[i0],-1,mod)%mod
    lift=[cc*x%mod for x in h]
    d1=[((x-y)%mod) for x,y in zip(G, mul(lift,Epow,mod,L))]
    assert all(x%l==0 for x in d1)
    d1=[(x//l)%l for x in d1]
    print(f'l={l} b={b}: filtration of digit 1 of L(b) mod l^2 =', filtration(d1, l*(l-1)), ' (B-W bound', l*(l-1),', needed <=',(l-1)**2,')',flush=True)
