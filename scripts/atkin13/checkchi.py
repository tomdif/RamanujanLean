import json
from collections import defaultdict
L=100
def mul(a,b):
    c=[0]*L
    for i,x in enumerate(a):
        if x:
            for j in range(L-i): c[i+j]+=x*b[j]
    return c
def inv(a):
    b=[0]*L; b[0]=1
    for m in range(1,L): b[m]=-sum(a[j]*b[m-j] for j in range(1,m+1))
    return b
cls=defaultdict(lambda:[0]*L)
for k in range(-400,401):
    e=k*(3*k-1)//2
    if e//13<L: cls[e%13][e//13]+=(-1)**(k%2)
E=[0]*L
for k in range(-40,41):
    e=k*(3*k-1)//2
    if 0<=e<L: E[e]+=(-1)**(k%2)
E13=[0]*L
for i in range(0,L,13): E13[i]=E[i//13]
iE13=inv(E13)
R=[0,1,2,5,9,12]
C=[mul(cls[r],iE13) for r in R]
# Laurent series as dict shift: represent with offset OFF
OFF=20
def lz(a): return [0]*OFF+a[:L-OFF]
def lmul(a,b):
    c=mul(a,b)  # both have OFF shift -> result has 2*OFF; shift back
    return c[OFF:]+[0]*OFF
one=lz([1]+[0]*(L-1))
Cl=[lz(c) for c in C]
Qinv=[0]*L; Qinv[OFF-1]=1
def powl(a,n):
    r=one
    for _ in range(n): r=lmul(r,a)
    return r
chi=json.load(open('chi13.json'))
co=json.load(open('modeq_coeffs.json'))
# T = -1 - c0c1/Q - c2c12 - c5c9
T=[ -o for o in one]
for t in (lmul(lmul(Cl[0],Cl[1]),Qinv), lmul(Cl[2],Cl[5]), lmul(Cl[3],Cl[4])):
    T=[x-y for x,y in zip(T,t)]
for j in range(1,14):
    s=[0]*L
    for k,q,v in chi[j]:
        m=one
        for idx,a in enumerate(k): m=lmul(m,powl(Cl[idx],a))
        if q>=0:
            m=lmul(m,powl(lz([0]+[1]+[0]*(L-2)),q))
        else:
            m=lmul(m,powl(Qinv,-q))
        s=[x+v*y for x,y in zip(s,m)]
    # f_j(T) = sum_i a_i T^{7-i}, a = coeffs of e_{13-j}(phi)
    a=co[f'phi{13-j}'] if j<13 else [1]
    f=[0]*L
    for i,ai in enumerate(a):
        if ai: f=[x+ai*y for x,y in zip(f,powl(T,7-i))]
    print(j, s[:L-40]==f[:L-40])
