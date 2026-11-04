# verify Appell-Lerch representations of f, phi, psi as power series (exact integer arithmetic)
N=60
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
def onep(e,s=1): # 1 + s q^e
    a=mono(0); 
    if e<N: a[e]+=s
    return a
qq=mono(0)
for j in range(1,N): qq=mul(qq,onep(j,-1))
# f
f=[0]*N
for n in range(0,9):
    d=mono(0)
    for j in range(1,n+1): d=mul(d,onep(j)); 
    d=mul(d,d)
    f=add(f,mul(mono(n*n),inv(d)))
phi=[0]*N
for n in range(0,9):
    d=mono(0)
    for j in range(1,n+1): d=mul(d,onep(2*j))
    phi=add(phi,mul(mono(n*n),inv(d)))
psi=[0]*N
for n in range(1,9):
    d=mono(0)
    for j in range(1,n+1): d=mul(d,onep(2*j-1,-1))
    psi=add(psi,mul(mono(n*n),inv(d)))
def ALsum(term):
    s=[0]*N
    for n in range(-12,13):
        t=term(n)
        if t is not None: s=add(s,t)
    return s
# f: 2 sum (-1)^n q^{n(3n+1)/2}/(1+q^n), n=0 term =1
def tf(n):
    e=n*(3*n+1)//2
    if n==0: return mono(0)
    if n>0: return mul(mono(e,2*(-1)**n),inv(onep(n)))
    # n<0: q^e/(1+q^n) = q^{e-n}/(1+q^{-n})
    return mul(mono(e-n,2*(-1)**n),inv(onep(-n)))
print("f ok", mul(qq,f)==ALsum(tf))
# phi candidate: sum (-1)^n q^{n(3n+1)/2}(1+q^n)/(1+q^{2n})
def tphi(n):
    e=n*(3*n+1)//2
    if n==0: return mono(0)
    m=abs(n)
    # (1+q^n)/(1+q^{2n}); for n<0 multiply num,den by q^{2m}: (q^{2m}+q^{m})/(q^{2m}+1)
    if n>0: num=add(mono(e),mono(e+n))
    else: num=add(mono(e+2*m),mono(e+m))
    return mul([(-1)**n*x for x in num],inv(onep(2*m)))
print("phi ok", mul(qq,phi)==ALsum(tphi))
print([x for x in mul(qq,phi)[:15]]); print(ALsum(tphi)[:15])
target=mul(qq,psi)
print("target",target[:12])
from fractions import Fraction as Fr
found=[]
for a2 in range(1,8):        # a = a2/2
  for b2 in range(-8,9):
    for c in range(0,4):
      for dn in [(1,2,1),(1,1,1),(2,1,-1),(2,2,1)]:  # denominator 1 - s q^{alpha n + beta}
        al,be,sg=dn
        for sgn in [1,-1]:
          s=[0]*N; ok=True
          for n in range(-12,13):
            num2=a2*n*n+b2*n
            if num2%2: ok=False;break
            e=num2//2+c
            D=al*n+be
            if D==0: ok=False;break
            if D>0: t=mul(mono(e,sgn**n if sgn==1 else (-1)**(n%2)),inv(onep(D,-sg)))
            else:
              # 1/(1 - s q^D) = -s^{-1} q^{-D}/(1 - s^{-1} q^{-D})
              t=mul(mono(e-D,-(sgn**n if sgn==1 else (-1)**(n%2))*sg),inv(onep(-D,-sg)))
            if min([i for i,x in enumerate(t) if x] or [N])<0: pass
            s=add(s,t)
          if ok and s[:40]==target[:40]: found.append((a2,b2,c,dn,sgn))
print(found)
