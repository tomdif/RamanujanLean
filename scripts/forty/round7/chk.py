from ser import *
a1=T(10,4);a2=T(10,2);b1=T(65,26);b2=T(65,13)
A=add(mul(a1,b1),sh(3,mul(a2,b2)))
f2=T(6,2);f13=T(39,13);f1=T(3,1);f26=T(78,26)
psi=[0]*P
n=0
while n*(n+1)//2<P: psi[n*(n+1)//2]+=1;n+=1
phim13=T(26,13)
br=add(mul(psi,phim13),sc(-1,sh(1,mul(f1,f26))))
lhs=mul(A,A); rhs=mul(mul(f2,f13),br)
print(lhs==rhs, lhs[:12],rhs[:12])
E0=add(T(30,16),sh(2,T(30,26)));E4=add(T(30,22),sc(-1,sh(2,T(30,2))))
print(lhs==rhs)
G0=add(T(195,104),sh(13,T(195,169)));G4=add(T(195,143),sc(-1,sh(13,T(195,13))))
F10=T(30,10);F65=T(195,65)
B=add(mul(E0,G0),sh(3,sc(2,mul(F10,F65))),sh(6,mul(E4,G4)))
print(B==br)
print(mul(a2,E0)==mul(F10,a1), mul(a1,E4)==mul(F10,a2))
