import numpy as np
N=100000; M=1<<14
J={}
k=0
while k*(k+1)//2<=N:
    J[k*(k+1)//2]=((-1)**k*(2*k+1))%M; k+=1
r=np.zeros(N+1,dtype=np.int64); r[0]=1
for _ in range(8):
    s=np.zeros(N+1,dtype=np.int64)
    for e,c in J.items(): s[e:]+=c*r[:N+1-e]
    r=s%M
tau=np.zeros(N+2,dtype=np.int64); tau[1:]=r[:N+1]   # tau[n]=r[n-1]
sig=np.zeros(N+1,dtype=np.int64)
for d in range(1,N+1): sig[d::d]+=pow(d,11,M)
sig%=M
fails=[n for n in range(1,N+1) if n%8==1 and (tau[n]-sig[n])%2048]
print("fails 2^11 n=1 mod 8:",len(fails))
for cls,mod in [(1,4096)]:
    print("fails 2^12:",sum(1 for n in range(1,N+1) if n%8==1 and (tau[n]-sig[n])%4096))
print(tau[2]-M, tau[3], tau[9]%2048)
