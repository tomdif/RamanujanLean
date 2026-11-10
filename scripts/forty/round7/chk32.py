from ser import *
def ng(a): return [x*(-1)**i for i,x in enumerate(a)]
def S(k,a):
    o=[0]*P
    for i,x in enumerate(a):
        if i*k<P: o[i*k]+=x
    return o
f1=T(3,1)
def fm(a): return S(a,f1)
psi=[0]*P;n=0
while n*(n+1)//2<P: psi[n*(n+1)//2]+=1;n+=1
g=T(5,2); h=T(5,1)
def chim(a): # chi(-q^a) = f(-q^a)/f(-q^{2a}) ; compute via product
    o=[0]*P;o[0]=1
    k=a
    while k<P:
        # multiply by (1-q^k)
        o=[o[i]-(o[i-k] if i>=k else 0) for i in range(P)]
        k+=2*a
    return o
Pp=add(mul(psi,ng(S(33,psi))),mul(ng(psi),S(33,psi)))
Pm=add(mul(S(3,psi),ng(S(11,psi))),sc(-1,mul(ng(S(3,psi)),S(11,psi))))
lhs24=sc(2,add(mul(S(6,g),S(44,g)),sh(10,mul(S(6,h),S(44,h)))))
rhs24=mul(mul(chim(6),chim(66)),Pp)
print('5.24',lhs24==rhs24)
lhs13=sh(3,sc(2,add(mul(S(4,g),S(66,g)),sh(14,mul(S(4,h),S(66,h))))))
print('5.13',lhs13==mul(mul(chim(6),chim(66)),Pm))
lhs20=sc(2,add(mul(S(12,h),S(22,g)),sc(-1,sh(2,mul(S(12,g),S(22,h))))))
print('5.20',lhs20==mul(mul(chim(2),chim(22)),Pp))
lhs25=sh(3,sc(2,add(mul(S(2,h),S(132,g)),sc(-1,sh(26,mul(S(2,g),S(132,h)))))))
print('5.25',lhs25==mul(mul(chim(2),chim(22)),Pm))
Phi=add(mul(T(8,3,-1),T(264,99,-1)),sc(-1,sh(17,mul(T(8,1,-1),T(264,33,-1)))))
Ub=add(mul(S(6,h),S(11,g)),sc(-1,sh(1,mul(S(6,g),S(11,h)))))
Tb=add(mul(S(3,g),S(22,g)),sh(5,mul(S(3,h),S(22,h))))
print('U',Ub==mul(mul(chim(1),chim(11)),Phi))
print('T',Tb==mul(mul(chim(3),chim(33)),Phi))
