import sympy as sp, sys
from math import comb
NM=7000
p=[0]*(NM+20); p[0]=1
for n in range(1,len(p)):
    s=0;k=1
    while True:
        g1=k*(3*k-1)//2
        if g1>n: break
        g2=k*(3*k+1)//2
        t=p[n-g1]+(p[n-g2] if g2<=n else 0)
        s+= t if k%2 else -t
        k+=1
    p[n]=s
X=sp.Symbol('X')
for d in range(int(sys.argv[2]),int(sys.argv[1])+1):
    last=None
    for n in range(1,NM):
        P=sp.Poly([comb(d,j)*p[n+j] for j in range(d,-1,-1)],X)
        if P.count_roots()!=d: last=n
    print('d',d,'last failure n =',last,flush=True)
