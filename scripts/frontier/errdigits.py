import sys
exec(open('filt.py').read().split("mod=l**3")[0])
D=int(sys.argv[5]) if len(sys.argv)>5 else 3
mod=l**D
E=[1]+[0]*(L-1)
# E_{l-1} via E4,E6 combos: use normalized Eisenstein E_{l-1} = 1 - (2(l-1)/B) sum sigma ; compute directly
from fractions import Fraction
import sympy
k=l-1; B=sympy.bernoulli(k); c=Fraction(-2*k)/Fraction(B.p,B.q)
Ek=[1]+[int((c*sigma(n,k-1)).numerator*pow((c*sigma(n,k-1)).denominator,-1,mod))%mod if (c*sigma(n,k-1)).denominator%l else None for n in range(1,L)]
assert None not in Ek
def pw(f,e):
    r=[1]+[0]*(L-1)
    for _ in range(e): r=mul(r,f,mod,L)
    return r
Epow=pw(Ek,l-1)   # E_{l-1}^{l-1}: weight (l-1)^2, ≡1 mod l

# iterative digit extraction: L(b) = sum_j l^j d_j * E^{...}; at each stage subtract a lift of the current digit
def lift_of(dig, w):
    # find classical form of weight w (basis) congruent to dig mod l, return integer lift mod 'mod'
    Bs=basis(w,mod)
    C=min(len(dig),120)
    # solve sum a_i Bs_i ≡ dig mod l (first C coeffs) via gaussian elimination mod l
    import copy
    n=len(Bs)
    M=[[Bs[i][t]%l for i in range(n)]+[dig[t]%l] for t in range(C)]
    # row reduce
    piv=[];r=0
    for col in range(n):
        pr=next((i for i in range(r,C) if M[i][col]),None)
        if pr is None: continue
        M[r],M[pr]=M[pr],M[r]; inv=pow(M[r][col],l-2,l); M[r]=[x*inv%l for x in M[r]]
        for i in range(C):
            if i!=r and M[i][col]: f=M[i][col]; M[i]=[(x-f*y)%l for x,y in zip(M[i],M[r])]
        piv.append(col); r+=1
    a=[0]*n
    for i,col in enumerate(piv): a[col]=M[i][n]
    f=[0]*L
    for i in range(n):
        if a[i]: f=[(x+a[i]*y)%mod for x,y in zip(f,Bs[i])]
    return f

# kappa from deepest proportionality available: K at b=3 mod l^3
Lf={b:Lform(b,L,mod) for b in (1,2,3,4,5)}
def Kat(b,prec):
    A,B=Lf[b+2],Lf[b]; i0=next(i for i,x in enumerate(B) if x%l)
    return A[i0]*pow(B[i0],-1,l**prec)%(l**prec)
kap=Kat(3,3)
for b in (1,2):
    e=[(x-kap*y)%mod for x,y in zip(Lf[b+2],Lf[b])]
    v=min((next((j for j in range(D) if x%(l**(j+1))), D) for x in e[:100]))
    g=[(x//l**v) for x in e]
    R=g[:]; ws=[]
    for j in range(D-v-1):   # digits reliable below precision of kappa
        dig=[(x//l**j)%l for x in R]
        if all(x==0 for x in dig[:100]): ws.append(None); continue
        w=filtration(dig, l**(j+3)*(l-1)); ws.append(w)
        lf=lift_of(dig,w); t=(l**(D-1)*(l-1)-w)//(l-1); lf=mul(lf,pw(Ek,t),mod,L)
        R=[(x-(l**j)*y)%mod for x,y in zip(R,lf)]
    print(f'l={l} b={b}: v(e_b)={v}; digit filtrations of e_b/l^v:',ws,flush=True)
