import os; os.environ['MOD']='80'
import atoms
from atoms import *
from fractions import Fraction as F
def P(r,M):
    v={}; poch(v,r,M,1,1); return (F(1),0,{r:n for r,n in v.items() if n})
def P2(r,M): return P(2*r,2*M)
def q(t,k=1): return (t[0],t[1]+k,t[2])
def m(*a): return mul(*a)
I=inv
th4=m(P(1,1),P(1,1),I(P(2,2))); th45=m(P(5,10),P(5,10),P(10,10))
G=I(m(P(1,5),P(4,5))); H=I(m(P(2,5),P(3,5)))
psi2=m(P(4,4),I(P(2,4))); H4=I(m(P(8,20),P(12,20))); G4=I(m(P(4,20),P(16,20)))
EF0=m(P(10,10),I(m(P(4,10),P(5,10),P(6,10))))
Ephi0=m(P(4,10),P(5,10),P(6,10),P(10,10),I(m(P(2,10),P(2,10),P(3,10),P(7,10),P(8,10),P(8,10))))
Epsi0=m(P(1,10),P(9,10),P(10,10),I(m(P(2,10),P(3,10),P(7,10),P(8,10))))
Ephi1=m(P(2,10),P(5,10),P(8,10),P(10,10),I(m(P(1,10),P(4,10),P(4,10),P(6,10),P(6,10),P(9,10))))
EF1=m(P(10,10),I(m(P(2,10),P(5,10),P(8,10))))
Epsi1=m(P(3,10),P(7,10),P(10,10),I(m(P(1,10),P(4,10),P(6,10),P(9,10))))
Echi1=m(P(1,5),P(4,5),P(5,5),I(m(P(2,5),P(2,5),P(3,5),P(3,5))))

EF0_2=m(P2(10,10),I(m(P2(4,10),P2(5,10),P2(6,10))))
Ephi0_2=m(P2(4,10),P2(5,10),P2(6,10),P2(10,10),I(m(P2(2,10),P2(2,10),P2(3,10),P2(7,10),P2(8,10),P2(8,10))))
Ephi1_2=m(P2(2,10),P2(5,10),P2(8,10),P2(10,10),I(m(P2(1,10),P2(4,10),P2(4,10),P2(6,10),P2(6,10),P2(9,10))))
EF1_2=m(P2(10,10),I(m(P2(2,10),P2(5,10),P2(8,10))))
IDS={
 'phi0':[(1,m(th45,G)),(1,m(th4,G)),(-2,Ephi0_2)],
 'F0':[(2,q(m(psi2,H4))),(-1,m(th45,G)),(1,m(th4,G)),(2,q(EF0_2,2))],
 'psi0':[(1,m(psi2,H4)),(-1,q(EF0_2)),(-1,Epsi0)],
 'phi1':[(1,m(th45,H)),(-1,m(th4,H)),(-2,q(Ephi1_2))],
 'F1':[(2,m(psi2,G4)),(-1,m(th45,H)),(-1,m(th4,H)),(-2,q(EF1_2))],
 'psi1':[(1,m(psi2,G4)),(1,q(EF1_2)),(-1,Epsi1)],
 'chi1':[(2,EF1),(-1,Ephi1),(-1,Echi1)],
}
def ser(t,M=240):
    s,k,v=t
    a=[0]*M; a[0]=1
    for r,n in v.items():
        for _ in range(abs(n)):
            if n>0:
                for j in range(r,M,MOD):
                    for i in range(M-1,j-1,-1): a[i]-=a[i-j]
            else:
                for j in range(r,M,MOD):
                    for i in range(j,M): a[i]+=a[i-j]
    res=[0]*M
    for i in range(M):
        if 0<=i+k<M: res[i+k]=a[i]*s
    return res
if __name__=='__main__':
  for nm,terms in IDS.items():
    tot=[0]*240
    for c,t in terms:
        tot=[x+c*y for x,y in zip(tot,ser(t))]
    print(nm, all(x==0 for x in tot[:230]), tot[:8])
