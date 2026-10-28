import sys
from fkatz import *
p=int(sys.argv[1]);PR=int(sys.argv[2]);N=int(sys.argv[3])
g=setup(p,PR,N); globals().update(g)
Ep=[0]*L
for i in range(0,L,p): Ep[i]=int(eta[i//p]) if i//p<eta.length() else 0
Ep=P(Ep)
Q=mul(mul(E,mul(Ep,Ep)),inv(pw(eta,2*p)))
res=katz(mul(Q,pw(E,N)),N)
vals=[val(a,DMAX) for a in res]
print(f'p={p} Q Katz valuations:',vals)
print('ceil(p i/(p+1))        :',[-(-(p*i)//(p+1)) for i in range(N+1)])
