# numerically compute weighted-homogeneous relations among J_a (deg d) and compare with Weierstrass span
import itertools, json, sys
from fractions import Fraction as F
import numpy as np
P=2147483647
L=260
def mul(a,b):
    c=[0]*L
    for i,x in enumerate(a):
        if x:
            for j in range(L-i): c[i+j]=(c[i+j]+x*b[j])
    return c
def J(a):
    s=[1]+[0]*(L-1)
    for n in range(L):
        for t in (a+13*n, 13-a+13*n, 13+13*n):
            if t<L:
                f=[0]*L; f[0]=1; f[t]=-1; s=mul(s,f)
    return s
Js={a:J(a) for a in range(1,7)}
w={a:F(13*a-a*a,26) for a in range(1,7)}
d=int(sys.argv[1]); Wmax=int(sys.argv[2])
mons=list(itertools.combinations_with_replacement(range(1,7),d))
mser={}
for mon in mons:
    s=[1]+[0]*(L-1)
    for a in mon: s=mul(s,Js[a])
    mser[mon]=s
W=json.load(open('weier13.json'))
def rank_mod(M):
    M=[[x%P for x in row] for row in M]
    r=0; rows=len(M); cols=len(M[0]) if M else 0
    for c in range(cols):
        piv=None
        for i in range(r,rows):
            if M[i][c]: piv=i;break
        if piv is None: continue
        M[r],M[piv]=M[piv],M[r]
        inv=pow(M[r][c],P-2,P)
        M[r]=[x*inv%P for x in M[r]]
        for i in range(rows):
            if i!=r and M[i][c]:
                f=M[i][c]; M[i]=[(x-f*y)%P for x,y in zip(M[i],M[r])]
        r+=1
    return r
tot_ker=0; tot_w=0
classes={}
for mon in mons:
    sw=sum(w[a] for a in mon)
    classes.setdefault(sw%1,[]).append((mon,sw))
for cl,lst in classes.items():
    for Wv in range(0,Wmax+1):
        W0=cl+Wv
        terms=[(mon,int(W0-sw)) for mon,sw in lst if W0-sw>=0 and (W0-sw).denominator==1]
        if not terms: continue
        K=L-max(m for _,m in terms)-1
        # columns = terms, rows = series coefficients
        A=[[ (mser[mon][i-m] if i>=m else 0) for (mon,m) in terms] for i in range(K)]
        rk=rank_mod(A)
        ker=len(terms)-rk
        # Weierstrass relations (times Q^k) in this class, degree 4 only
        if ker>0: tot_ker+=ker
        if ker>0: print('class',cl,'W',W0,'terms',len(terms),'ker',ker)
print('total kernel dim',tot_ker)
# compare with Weierstrass span (degree 4)
if d==4:
    missing=0
    for cl,lst in classes.items():
        for Wv in range(0,Wmax+1):
            W0=cl+Wv
            terms=[(mon,int(W0-sw)) for mon,sw in lst if W0-sw>=0 and (W0-sw).denominator==1]
            if not terms: continue
            idx={t:i for i,t in enumerate(terms)}
            K=L-max(m for _,m in terms)-1
            A=[[ (mser[mon][i-m] if i>=m else 0) for (mon,m) in terms] for i in range(K)]
            ker=len(terms)-rank_mod(A)
            vecs=[]
            for rel in W:
                # weight of rel
                s0,m0,mon0=rel[0]; rw=m0+sum(w[a] for a in mon0)
                k=W0-rw
                if k<0 or k.denominator!=1: continue
                v=[0]*len(terms); okk=True
                for s,m,mon in rel:
                    t=(tuple(mon),m+int(k))
                    if t not in idx: okk=False;break
                    v[idx[t]]+=s
                if okk and any(v): vecs.append(v)
            rw_=rank_mod(vecs) if vecs else 0
            if rw_<ker: missing+=ker-rw_; print('MISSING class',cl,'W',W0,'ker',ker,'weier',rw_)
    print('missing',missing)
