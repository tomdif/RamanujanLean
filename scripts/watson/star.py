import os,sys
sys.argv=['x']
exec(open('small.py').read())
def J(N):
    v={}; poch(v,N,N,1,1); return (F(1),0,{r:n for r,n in v.items() if n})
G=mul(th(5,2,1),inv(J(1)))
H4=mul(th(20,4,1),inv(J(4)))
psi2=mul(J(4),J(4),inv(J(2)))
th4=th(2,1,1); th45=th(10,5,1)
P2=mul(J(10),J(10),th(10,4,1),inv(th(10,2,1)),inv(th(10,2,1)))
A=mul(psi2,H4); A=(A[0],A[1]+1,A[2])
terms=[(4,A),(1,mul(th4,G)),(-3,mul(th45,G)),(2,P2)]
# numeric check via exact product expansion
import pr
def ser(t,M=200):
    s,k,v=t
    import numpy as np
    out=[0]*M; out[0]=1
    # product over atoms (q^r;q^MOD)^n
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
tot=[0]*200
for c,t in terms:
    s=ser(t)
    tot=[x+c*y for x,y in zip(tot,s)]
print('numeric (star):',all(x==0 for x in tot[:180]),tot[:10])
rels=shapes([5,10,20,40] if MOD%40==0 else [5,10,20])
sol=solve(terms,rels)
print("cert" if sol else "NONE")
if sol:
    for c,sp,nm,p in sol: print(c,sp)
print("=== detail")
names={key(t):(c,t) for c,t in terms}
tl=[(c,t) for c,t in terms]
for c,sp,nm,p in sol:
    rel=exact(sp)
    Ti=[t for cc,t in tl if key(t)==nm][0]
    cp,(sp_,kp,vp)=rel[p]
    # scale monomial: Ti / rel[p]
    sc=(Fraction(Ti[0])/(cp*Fraction(sp_)), Ti[1]-kp, {r:Ti[2].get(r,0)-vp.get(r,0) for r in set(Ti[2])|set(vp) if Ti[2].get(r,0)-vp.get(r,0)})
    tidx=[i for i,(cc,t) in enumerate(tl) if key(t)==nm][0]
    print("coef",c,"rel",sp,"anchored at term",tidx,"position",p,"scale",sc)
