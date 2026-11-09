import itertools, random, pickle, sys
import sympy as sp
from collections import Counter
n=int(sys.argv[1]); MAXU=int(sys.argv[4]); seed=int(sys.argv[2]); TRIES=int(sys.argv[3])
random.seed(seed)
mons=[m for m in itertools.product(range(n+1),repeat=4) if sum(m)==n]
midx={m:i for i,m in enumerate(mons)}
cl=lambda r: min(r%7,(-r)%7)
Z=(0,)*n
def span(vecs):
    S={Z}
    for v in vecs:
        v=tuple(x%7 for x in v)
        if v in S: continue
        S={tuple((x+k*y)%7 for x,y in zip(s,v)) for s in S for k in range(7)}
    return S
def poly(S):
    vec=[0]*len(mons)
    for v in S:
        c=Counter(cl(x) for x in v); vec[midx[(c[0],c[1],c[2],c[3])]]+=1
    return vec
def enum(k,rem):
    if k==0:
        if rem==0: yield ()
        return
    m=int(rem**0.5)
    for x in range(-m,m+1):
        for t in enum(k-1,rem-x*x): yield (x,)+t
V49=list(enum(n,49)); print(len(V49),flush=True)
def randM():
    cols=[]; cand=V49
    for k in range(n):
        cand=[v for v in cand if all(sum(a*b for a,b in zip(v,c))==0 for c in cols)]
        if not cand: return None
        cols.append(random.choice(cand))
    return [[cols[j][i] for j in range(n)] for i in range(n)]
def basisof(U):
    ub=[]; cur={Z}
    for v in sorted(U):
        if v not in cur: ub.append(v); cur=span(ub)
    return ub
def kernel(M):
    # right kernel mod 7 via gaussian elimination
    A=[[x%7 for x in r] for r in M]
    piv=[];r=0
    for c in range(n):
        pr=next((i for i in range(r,n) if A[i][c]),None)
        if pr is None: continue
        A[r],A[pr]=A[pr],A[r]; inv=pow(A[r][c],-1,7); A[r]=[x*inv%7 for x in A[r]]
        for i in range(n):
            if i!=r and A[i][c]: f=A[i][c]; A[i]=[(x-f*y)%7 for x,y in zip(A[i],A[r])]
        piv.append(c); r+=1
    free=[c for c in range(n) if c not in piv]
    B=[]
    for f in free:
        v=[0]*n; v[f]=1
        for i,c in enumerate(piv): v[c]=(-A[i][f])%7
        B.append(tuple(v))
    return B
basis=[]; data=[]
def rank(vs): return sp.Matrix(vs).rank() if vs else 0
for t in range(TRIES):
    M=randM()
    if M is None: continue
    cb=basisof(span([[x%7 for x in r] for r in M]))
    K=kernel(M)
    if len(cb)==0: continue
    # random U between
    for rep in range(6):
        ext=[]
        k=random.randint(0,len(K)-len(cb))
        for _ in range(k):
            cf=[random.randrange(7) for v in K]; ext.append(tuple(sum(c*v[i] for c,v in zip(cf,K))%7 for i in range(n)))
        U=span(cb+ext)
        if len(U)>7**4: continue
        imgs=[]
        for u in basisof(U):
            z=[sum(M[i][j]*u[j] for j in range(n)) for i in range(n)]
            assert all(x%7==0 for x in z); imgs.append([x//7 for x in z])
        for j in range(n): imgs.append([M[i][j] for i in range(n)])
        U2=span(imgs); assert len(U2)==len(U)
        r=[x-y for x,y in zip(poly(U),poly(U2))]
        if any(r) and len(U)<=MAXU:
            basis.append(r); data.append((M,basisof(U),len(U)))
pickle.dump((mons,basis,data),open(f'all{n}_{seed}.pkl','wb'))
print('done',len(basis))
