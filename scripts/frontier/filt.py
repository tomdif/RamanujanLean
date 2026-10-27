import sys
from lforms2 import *
l=int(sys.argv[1]); P=l
L=int(sys.argv[4]) if len(sys.argv)>4 else 400
def eis(k,L):
    from sympy import bernoulli, divisor_sigma
    import sympy
    B=sympy.bernoulli(k); c=-2*k/B
    s=[1]+[int(c*sympy.divisor_sigma(n,k-1)) if False else 0 for n in range(1,L)]
    # integral form for E4,E6
    return None
def sigma(n,k):
    s=0
    for d in range(1,int(n**0.5)+1):
        if n%d==0:
            s+=d**k
            if d*d!=n: s+=(n//d)**k
    return s
E4=[1]+[240*sigma(n,3) for n in range(1,L)]
E6=[1]+[-504*sigma(n,5) for n in range(1,L)]
def pmul(a,b,mod):
    return mul(a,b,mod,L)
def basis(w,mod):
    out=[]
    for a in range(w//4+1):
        r=w-4*a
        if r%6: continue
        b=r//6
        f=[1]+[0]*(L-1)
        for _ in range(a): f=pmul(f,E4,mod)
        for _ in range(b): f=pmul(f,E6,mod)
        out.append(f)
    return out
def rank_mod(rows,p):
    M=[[x%p for x in r] for r in rows]; rk=0; cols=len(M[0]) if M else 0
    for c in range(cols):
        piv=next((i for i in range(rk,len(M)) if M[i][c]),None)
        if piv is None: continue
        M[rk],M[piv]=M[piv],M[rk]; inv=pow(M[rk][c],P-2,P)
        M[rk]=[x*inv%P for x in M[rk]]
        for i in range(len(M)):
            if i!=rk and M[i][c]:
                f=M[i][c]; M[i]=[(x-f*y)%P for x,y in zip(M[i],M[rk])]
        rk+=1
    return rk
def filtration(f,wmax):
    # minimal w ≡ wmax mod (l-1) with f ≡ g in M_w mod l (compare first C coefficients)
    C=min(120,L)
    for w in range(wmax%(l-1) or (l-1), wmax+1, l-1):
        B=[b[:C] for b in basis(w,P)]
        if rank_mod(B+[f[:C]],P)==rank_mod(B,P): return w
    return None
def U(f): return [f[l*n] for n in range(len(f)//l)]
mod=l**3
Ls={b:Lform(b,L*l,mod) for b in range(1,4)}
L1,L3=Ls[1],Ls[3]
K=L3[1]*pow(L1[1],-1,l*l)%(l*l)
E1=[((x-K*y)%(l*l))//1 for x,y in zip(L3,L1)]
assert all(x%l==0 for x in E1)
E1=[ (x//l)%l for x in E1]
print('l',l,'filtration of L1 mod l:',filtration([x%l for x in L1[:L]], l*(l-1)))
print('filtration of E1=(L3-K L1)/l mod l:', filtration(E1[:L], l*(l-1)))
Phi_mod=None
