from ser import *
P_=P
def ng(a): return [x*(-1)**i for i,x in enumerate(a)]
def S(k,a):
    o=[0]*P
    for i,x in enumerate(a):
        if i*k<P: o[i*k]+=x
    return o
f1=T(3,1)            # f(-q)
fp=ng(f1)            # f(q)
def fm(a): return S(a,f1)
psi=[0]*P;n=0
while n*(n+1)//2<P: psi[n*(n+1)//2]+=1;n+=1
phim=T(2,1)          # phi(-q)
# Br = f(-q^22,-q^33) f(q,-q^4) + q^2 f(-q^2,q^3) f(-q^11,-q^44)
# f(q,-q^4) = Ng(f(-q,-q^4)) ; f(-q^2,q^3)=Ng(f(-q^2,-q^3))
Br=add(mul(T(55,22),ng(T(5,1))), sh(2,mul(ng(T(5,2)),T(55,11))))
lhs=mul(Br,mul(fm(2),fm(22)))
rhs=add(mul(mul(psi,ng(S(11,psi))),mul(S(4,phim),S(44,phim))), sc(-2,sh(3,mul(mul(fp,fm(11)),mul(fm(8),fm(88))))))
print(lhs==rhs, lhs[:15])
