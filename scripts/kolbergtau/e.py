import numpy as np, sympy
N=30000
s1=np.zeros(N+1,dtype=np.int64)
for d in range(1,N+1): s1[d::d]+=d
s1%=4; ts1=(np.arange(N+1)*s1)%4
X=np.convolve(s1,ts1)[:N+1]%4; A=np.convolve(X,X)[:N+1]%4
pr=[p for p in sympy.primerange(3,N) if p%16==15]
print(len(pr), sum(1 for p in pr if A[p]%4))
print("n=15 mod 16 nonzero:", sum(1 for n in range(15,N,16) if A[n]%4), len(range(15,N,16)))
