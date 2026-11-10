# numeric check of the decomposition of the two R-identities for Entry 3.35 (t = q level)
import lib; lib.P=900
from lib import *
P=lib.P
def ng(a): return np.array([x*(-1)**i for i,x in enumerate(a)],dtype=np.int64)
def ths(s,N,e,c=1):
    o=z()
    for k in range(-400,401):
        E=N*k*(k-1)//2+e*k+s
        if 0<=E<P: o[E]+=(-1)**(k%2)*(c**(k%2))
        elif E<0: raise Exception("neg")
    return o
def tt(s,N1,e1,c1,N2,e2,c2):
    a=ths(100,N1,e1,c1); b=ths(100,N2,e2,c2); return sh(s-200,mul(a,b))
Q=47
A = sub(mul(H(2),G(Q)), sh(9,mul(G(2),H(Q))))
B = add(mul(G(1),G(2*Q)), sh(19,mul(H(1),H(2*Q))))
F=fm
# everything multiplied by t^2 to avoid negative exponents
g2=add(tt(0,20,2,1,2820,1316,1), tt(188,20,2,1,2820,376,1)); g2=-g2
g6=sub(tt(262,20,6,1,2820,188,1), tt(74,20,6,1,2820,752,1))
g10=tt(36,20,10,1,2820,940,1)
g4=add(tt(4,20,4,1,2820,1222,1), tt(98,20,4,1,2820,658,1))
g8=sc(-1,add(tt(22,20,8,1,2820,1034,1), tt(304,20,8,1,2820,94,1)))
Ye=add(g2,g6,g10); Yo=add(g4,g8)
d5p=add(sc(-1,tt(0,470,188,1,30,8,-1)), tt(2,470,188,1,30,2,-1), tt(18,470,94,1,30,14,-1), sc(-1,tt(20,470,94,1,30,4,-1)))
d5m=add(sc(-1,tt(0,470,188,-1,30,8,1)), tt(2,470,188,-1,30,2,1), tt(18,470,94,-1,30,14,1), tt(20,470,94,-1,30,4,1), sc(-1,tt(56,470,0,-1,30,10,1)))
N=650
print("Lp", eq(d5p[:N],add(Ye,Yo)[:N]), "Lm", eq(d5m[:N],sub(Ye,Yo)[:N]))
ff=mul(F(2),F(2*Q)); f4=mul(F(4),F(4*Q))
A2=subq(A,2); A4=subq(A,4); Bm2=subq(B,2,-1)
print("d5p=-ffA2", eq(d5p[:N], sc(-1,mul(ff,A2))[:N]))
print("Yo=t^4 f4 A2", eq(Yo[:N], sh(4,mul(f4,A2))[:N]))
print("Ye=-f4 A4 B(-t^2)", eq(Ye[:N], sc(-1,mul(f4,mul(A4,Bm2)))[:N]))
print("d5m=-A A(-t) ff", eq(d5m[:N], sc(-1,mul(ff,mul(A,ng(A))))[:N]))
for k in range(0,12,2):
    print(k, eq(Yo[:N], sh(k,mul(f4,A2))[:N]), eq(Yo[:N], sc(-1,sh(k,mul(f4,A2)))[:N]))
