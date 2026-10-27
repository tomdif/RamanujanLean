import json, sympy as sp
chi=json.load(open('chi13.json')); co=json.load(open('modeq_coeffs.json'))
J1,J2,J3,J4,J5,J6,Q=sp.symbols('J1:7 Q')
c=[J4/J2,-J6/J3,-J2/J1,J5/J4,Q*J1/J6,-J3/J5]
T=-1-c[0]*c[1]/Q-c[2]*c[5]-c[3]*c[4]
L=90
def mul(a,b):
    r=[0]*L
    for i,x in enumerate(a):
        if x:
            for j in range(L-i): r[i+j]+=x*b[j]
    return r
def Jser(a):
    s=[1]+[0]*(L-1)
    for n in range(L):
        for t in (a+13*n, 13-a+13*n, 13+13*n):
            if t<L:
                f=[0]*L; f[0]=1; f[t]=-1; s=mul(s,f)
    return s
JS=[Jser(a) for a in range(1,7)]
import random
for j in (3,4):
    X=sum(v*sp.Mul(*[ci**a for ci,a in zip(c,k)])*Q**q for k,q,v in chi[j])
    a=co[f'phi{13-j}']
    Fj=sum(ai*T**(7-i) for i,ai in enumerate(a) if ai)
    expr=sp.together(X-Fj)
    num,den=sp.fraction(expr)
    num=sp.expand(num)
    # evaluate num as series (Q -> shift)
    P=sp.Poly(num,J1,J2,J3,J4,J5,J6,Q)
    tot=[0]*L
    for mon,cf in P.terms():
        s=[1]+[0]*(L-1)
        for idx in range(6):
            for _ in range(mon[idx]): s=mul(s,JS[idx])
        m=mon[6]
        for i in range(L-m): tot[i+m]+=int(cf)*s[i]
    print(j,'num zero as series?',all(x==0 for x in tot[:L-30]), 'nterms',len(P.terms()))
for j in (3,4,5):
    X=sum(v*sp.Mul(*[ci**a for ci,a in zip(c,k)])*Q**q for k,q,v in chi[j])
    a=co[f'phi{13-j}']
    Fj=sum(ai*T**(7-i) for i,ai in enumerate(a) if ai)
    num,den=sp.fraction(sp.together(X-Fj))
    print(j, sp.factor(sp.expand(num)), '   den', den)
