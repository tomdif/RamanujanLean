import sys
from fkatz import *
p=int(sys.argv[1]);PR=int(sys.argv[2]);N=int(sys.argv[3])
g=setup(p,PR,N); globals().update(g)
s=(p+1)//2
El2=[0]*L
for i in range(0,L,p*p): El2[i]=int(eta[i//(p*p)]) if i//(p*p)<eta.length() else 0
El2=P(El2)
W=mul(El2,inv(pw(eta,p*p)))
F=mul(mul(pw(E,s),W),pw(E,N))
res=katz(F,N)
print(f'p={p} E^s W Katz valuations:',[val(a,DMAX) for a in res])
print('ceil(i/(p+1)) needed      :',[-(-i//(p+1)) for i in range(N+1)])
