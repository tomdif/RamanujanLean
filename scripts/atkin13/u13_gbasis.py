# U13(g^k) as polynomials in g, g=(eta(13t)/eta(t))^2 = q prod (1-q^{13n})^2/(1-q^n)^2
import sys
N=13*40
def mul(a,b):
    c=[0]*N
    for i,x in enumerate(a):
        if x:
            for j in range(N-i):
                c[i+j]+=x*b[j]
    return c
E=[0]*N
# Euler product via pentagonal
for n in range(-60,61):
    e=n*(3*n-1)//2
    if 0<=e<N: E[e]+=(1 if n%2==0 else -1)
# 1/E
inv=[0]*N; inv[0]=1
for m in range(1,N):
    inv[m]=-sum(E[j]*inv[m-j] for j in range(1,m+1))
E13=[0]*N
for i in range(0,N,13): E13[i]=E[i//13]
r=mul(E13,inv); r2=mul(r,r)
g=[0]+r2[:N-1]
M=N//13
def U(f): return [f[13*n] for n in range(M)]
def topoly(f):
    # express f (len M, f[0]=const) as sum c_r g^r, r>=0
    gs=[[1]+[0]*(M-1)]
    G=g[:M]
    coeffs=[]; f=f[:]
    for r in range(M):
        if r>0: gs.append(mul(gs[-1]+[0]*(N-M),G+[0]*(N-M))[:M])
        c=f[r]  # g^r = q^r + ...
        coeffs.append(c)
        f=[f[i]-c*gs[r][i] for i in range(M)]
    return coeffs
def val13(x):
    if x==0: return 99
    v=0
    while x%13==0: x//=13; v+=1
    return v
gk=[1]+[0]*(N-1)
for k in range(1,4):
    gk=mul(gk,g)
    c=topoly(U(gk))
    nz=[(r,val13(x)) for r,x in enumerate(c) if x]
    print(k, nz[:16], 'maxdeg', max(r for r,_ in nz))
print(U(g)[:20])
c=topoly(U(g)); print(c[:20])
