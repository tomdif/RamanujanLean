import pickle, sympy as sp, itertools, random
from collections import Counter
A,B,C,D=sp.symbols('a b c d')
P=1000003
mons9=[m for m in itertools.product(range(10),repeat=4) if sum(m)==9]; mi={m:i for i,m in enumerate(mons9)}
def todict(vec,mons): return {m:c for c,m in zip(vec,mons) if c}
cands=[]
for fn in ['all6_3.pkl','all7_3.pkl']:
    mons,basis,data=pickle.load(open(fn,'rb'))
    for v,dt in zip(basis,data): cands.append((todict(v,mons),sum(mons[0]),dt[2],fn,dt))
print(Counter((c[1],c[2]) for c in cands))
Phi4 = A**4 + 24*A*B*C*D + 8*(B**3*C + C**3*D + D**3*B)
iii = sp.Poly(sp.expand(A*Phi4**2 + (A**3 - 8*B*C*D)**3 - (2*A**5 + 40*A**2*B*C*D)*Phi4),A,B,C,D)
target=[0]*len(mons9)
for m,c in iii.terms(): target[mi[m]]=int(c)%P
def gens(rel,deg):
    out=[]
    for e in itertools.product(range(10),repeat=4):
        if sum(e)!=9-deg: continue
        v=[0]*len(mons9)
        for m,c in rel.items(): v[mi[tuple(x+y for x,y in zip(m,e))]]=c%P
        out.append(v)
    return out
def rank_mod(rows):
    rows=[r[:] for r in rows]; rk=0; ncol=len(mons9); piv=[]
    M=rows
    for col in range(ncol):
        pr=next((i for i in range(rk,len(M)) if M[i][col]%P),None)
        if pr is None: continue
        M[rk],M[pr]=M[pr],M[rk]; inv=pow(M[rk][col],P-2,P); M[rk]=[x*inv%P for x in M[rk]]
        for i in range(len(M)):
            if i!=rk and M[i][col]: f=M[i][col]; M[i]=[(x-f*y)%P for x,y in zip(M[i],M[rk])]
        rk+=1
    return rk
def ok(sel):
    rows=[]
    for i in sel: rows+=gens(cands[i][0],cands[i][1])
    return rank_mod(rows+[target])==rank_mod(rows)
# order: prefer small U, deg6 first
order=sorted(range(len(cands)),key=lambda i:(cands[i][2],cands[i][1]))
# greedy add: build span-increasing set
sel=[]; rows=[]; rk=0
for i in order:
    g=gens(cands[i][0],cands[i][1])
    r2=rank_mod(rows+g)
    if r2>rk: sel.append(i); rows+=g; rk=r2
    if rank_mod(rows+[target])==rk: break
print('greedy',len(sel),[(cands[i][1],cands[i][2]) for i in sel], ok(sel))
# prune
for i in list(sel)[::-1]:
    t=[j for j in sel if j!=i]
    if ok(t): sel=t
print('pruned',len(sel),[(cands[i][1],cands[i][2]) for i in sel])
pickle.dump([cands[i] for i in sel],open('sel.pkl','wb'))
