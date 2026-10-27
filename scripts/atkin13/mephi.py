# modular equations for g and phi over Q=q^13: e_j of conjugates via Newton from power sums 13*U(f^m)
import sys
L=13*14*13+50   # q-precision
P=(1<<127)-1
def mul(a,b,L=None):
    L=L or len(a)
    c=[0]*L
    for i,x in enumerate(a[:L]):
        if x:
            bi=b
            for j in range(L-i):
                y=bi[j]
                if y: c[i+j]=(c[i+j]+x*y)
    return c
def Eser(L,step=1):
    E=[0]*L
    for k in range(-400,401):
        e=step*(k*(3*k-1)//2)
        if 0<=e<L: E[e]+=(-1)**(k%2)
    return E
def inv(a):
    L=len(a); b=[0]*L; b[0]=1
    for m in range(1,L):
        s=0
        for j in range(1,m+1):
            if a[j]: s+=a[j]*b[m-j]
        b[m]=-s
    return b
which=sys.argv[1]
E1=Eser(L); E13=Eser(L,13); E169=Eser(L,169)
iE1=inv(E1)
if which=='g':
    base=mul(E13,iE1); f=[0]+mul(base,base)[:L-1]; lead=1
else:
    base=mul(E169,iE1); f=[0]*7+base[:L-7]; lead=7
M=L//13
pm=[]; fk=[1]+[0]*(L-1)
for m in range(1,14):
    fk=mul(fk,f)
    pm.append([13*fk[13*n] for n in range(M)])
# Newton: e_j as Q-series
def smul(c,a): return [c*x for x in a]
def add(a,b): return [x+y for x,y in zip(a,b)]
def mulM(a,b): return mul(a,b,M)
e=[[1]+[0]*(M-1)]
for j in range(1,14):
    s=[0]*M
    for i in range(1,j+1):
        t=mulM(e[j-i],pm[i-1])
        if (i-1)%2: t=smul(-1,t)
        s=add(s,t)
    assert all(x%j==0 for x in s)
    e.append([x//j for x in s])
import json
json.dump(e,open(f'e_{which}.json','w'))
for j in range(1,14):
    nz=[i for i,x in enumerate(e[j]) if x]
    print(j,'lowest Q-exp',nz[0] if nz else None, e[j][:4])
