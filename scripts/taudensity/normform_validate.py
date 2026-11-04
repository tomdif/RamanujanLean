import math
from sympy import factorint
# 1) inertness: primes q = 690 mod 691 up to bound: -691 nonsquare mod q
from sympy import primerange, legendre_symbol
bad=0;cnt=0
for q in primerange(3,3_000_000):
    if q%691==690:
        cnt+=1
        if legendre_symbol((-691)%q,q)!=-1: bad+=1
print("inert check primes",cnt,"bad",bad)
# 2) values x^2+691y^2 <= N: valuations at q=-1 mod 691 even; counts, energy
for N in [10**5,10**6,4*10**6]:
    A=math.isqrt(N//2); B=math.isqrt(N//1382)
    from collections import Counter
    r=Counter(x*x+691*y*y for x in range(1,A+1) for y in range(1,B+1))
    P=A*B; E=sum(v*v for v in r.values()); img=len(r)
    M=2*A; T=sum(M//s for s in range(1,M+1))
    allvals=set(x*x+691*y*y for x in range(0,math.isqrt(N)+1) for y in range(0,math.isqrt(N//691)+1) if 0<x*x+691*y*y<=N)
    L=math.log(N)
    print(N,"A,B",A,B,"P",P,"E",E,"E/P",round(E/P,3),"img",img,"P^2/E",round(P*P/E),"bound P+2T^2",P+2*T*T,
          "img/(N/logN)",round(img/(N/L),3),"all values",len(allvals),"all/(N/sqrt logN)",round(len(allvals)/(N/math.sqrt(L)),3),
          "proved-const N/(884480(1+logN)^2)",round(N/(884480*(1+L)**2),4))
# valuation check sample
bad=0
for x in range(0,300):
    for y in range(0,40):
        n=x*x+691*y*y
        if n==0: continue
        for p,e in factorint(n).items():
            if p%691==690 and e%2: bad+=1
print("odd valuation at q=-1 mod 691:",bad)
