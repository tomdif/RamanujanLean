N=80
def mul(a,b):
    c=[0]*N
    for i,x in enumerate(a):
        if x:
            for j in range(N-i): c[i+j]+=x*b[j]
    return c
def inv(a):
    b=[0]*N; b[0]=1
    for n in range(1,N): b[n]=-sum(a[k]*b[n-k] for k in range(1,n+1))
    return b
def mono(e,c=1):
    a=[0]*N
    if 0<=e<N: a[e]=c
    return a
def add(a,b): return [x+y for x,y in zip(a,b)]
def onep(e,s=1):
    a=mono(0)
    if e<N: a[e]+=s
    return a
psi=[0]*N
for n in range(1,10):
    d=mono(0)
    for j in range(1,n+1): d=mul(d,onep(2*j-1,-1))
    psi=add(psi,mul(mono(n*n),inv(d)))
for m in [1,2,4]:
    P=mono(0)
    for j in range(1,N): P=mul(P,onep(m*j,-1))
    print(m, [(i,x) for i,x in enumerate(mul(P,psi)) if x][:30])
P=mono(0)
for j in range(1,N): P=mul(P,onep(4*j,-1))
t=mul(P,psi)
s=[0]*N
for n in range(-12,13):
    e=6*n*n+6*n+1; D=4*n+1
    if D>0:
        k=0
        while e+D*k<N: s[e+D*k]+=(-1)**n; k+=1
    else:
        # 1/(1-q^D) = -q^{-D}/(1-q^{-D})
        k=0; e2=e-D
        while e2+(-D)*k<N: s[e2+(-D)*k]+=-(-1)**n; k+=1
print("psi rep:", t==s)
