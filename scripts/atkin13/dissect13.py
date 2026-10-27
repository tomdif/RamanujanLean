# 13-dissection of E(q)=prod(1-q^n): E(q) = sum over k of (-1)^k q^{k(3k-1)/2}
from collections import defaultdict
M=13*60
cls=defaultdict(lambda: defaultdict(int))
for k in range(-200,201):
    e=k*(3*k-1)//2
    if e< M*13: cls[e%13][e//13]+=(-1)**(k%2)
print(sorted(cls.keys()))
# Q-series per class: E(q)=sum_r q^r C_r(Q), Q=q^13
def series(r,L=60): return [cls[r].get(i,0) for i in range(L)]
L=60
def mul(a,b):
    c=[0]*L
    for i,x in enumerate(a):
        if x:
            for j in range(L-i): c[i+j]+=x*b[j]
    return c
def inv(a):
    b=[0]*L; b[0]=1//a[0]
    for m in range(1,L): b[m]=-sum(a[j]*b[m-j] for j in range(1,m+1))//a[0]
    return b
# E(Q^13) as Q-series: E(q^169) = E(Q^13)
E=[0]*L
for k in range(-50,51):
    e=k*(3*k-1)//2
    if e<L: E[e]+=(-1)**(k%2)
E13=[0]*L
for i in range(0,L,13): E13[i]=E[i//13]
# J_a = (Q^a;Q^13)(Q^{13-a};Q^13)(Q^13;Q^13)
def J(a):
    s=[1]+[0]*(L-1)
    for n in range(L):
        for t in (a+13*n, 13-a+13*n, 13+13*n):
            if t<L:
                f=[0]*L; f[0]=1; f[t]=-1; s=mul(s,f)
    return s
Js={a:J(a) for a in range(1,7)}
for r in sorted(cls):
    c=mul(series(r),inv(E13))  # C_r/E(Q^13)
    # find leading exponent and try match ratio of J's
    lead=next(i for i,x in enumerate(c) if x)
    found=None
    for a in range(1,7):
        for b in range(1,7):
            rat=mul(Js[a],inv(Js[b]))
            for s in (1,-1):
                sh=[0]*L
                for i in range(L-lead): sh[i+lead]=s*rat[i]
                if sh[:50]==c[:50]: found=(s,lead,a,b)
    print(r, c[:6], found)
