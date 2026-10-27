import numpy as np
P=(1<<61)-1  # work mod prime for degree structure
N=13*172
E=[0]*N
for n in range(-80,81):
    e=n*(3*n-1)//2
    if 0<=e<N: E[e]+=(1 if n%2==0 else -1)
inv=[0]*N; inv[0]=1
for m in range(1,N):
    s=0
    for j in range(1,m+1):
        if E[j]: s+=E[j]*inv[m-j]
    inv[m]=(-s)%P
def mul(a,b):
    c=[0]*N
    for i,x in enumerate(a):
        if x:
            for j in range(N-i):
                if b[j]: c[i+j]=(c[i+j]+x*b[j])%P
    return c
E13=[0]*N
for i in range(0,N,13): E13[i]=E[i//13]%P
r=mul(E13,inv); g=[0]+mul(r,r)[:N-1]
M=N//13
def U(f): return [f[13*n] for n in range(M)]
G=g[:M]
gp=[[1]+[0]*(M-1)]
def mulM(a,b):
    c=[0]*M
    for i,x in enumerate(a):
        if x:
            for j in range(M-i):
                if b[j]: c[i+j]=(c[i+j]+x*b[j])%P
    return c
for r_ in range(1,M): gp.append(mulM(gp[-1],G))
def topoly(f):
    f=f[:]; co=[]
    for r_ in range(M):
        c=f[r_]; co.append(c)
        if c: f=[(f[i]-c*gp[r_][i])%P for i in range(M)]
    return co
pm=[]; gk=[1]+[0]*(N-1)
for k in range(1,14):
    gk=mul(gk,g); pm.append([13*x%P for x in topoly(U(gk))])
    print('k',k,flush=True)
# Newton: e_j from power sums p_1..p_13 (polynomials in g, as coefficient lists mod P)
def padd(a,b): 
    n=max(len(a),len(b)); return [((a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0))%P for i in range(n)]
def pmul(a,b):
    c=[0]*(len(a)+len(b))
    for i,x in enumerate(a):
        if x:
            for j,y in enumerate(b):
                if y: c[i+j]=(c[i+j]+x*y)%P
    return c
e=[[1]]
for j in range(1,14):
    s=[0]
    for i in range(1,j+1):
        t=pmul(e[j-i],pm[i-1])
        if (i-1)%2: t=[(-x)%P for x in t]
        s=padd(s,t)
    invj=pow(j,P-2,P)
    e.append([x*invj%P for x in s])
for j in range(1,14):
    d=[i for i,x in enumerate(e[j]) if x]
    print(j,'deg',max(d) if d else None,'min',min(d) if d else None)
