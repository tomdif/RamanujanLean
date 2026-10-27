import json
from collections import defaultdict
chi=json.load(open('chi13.json'))
R=[0,1,2,5,9,12]
# poly in (c0..c12 [6], q, Q) as dict key (e6..., eq, eQ)
def add(d,k,v):
    d[k]=d.get(k,0)+v
    if d[k]==0: del d[k]
def mul(A,B):
    C=defaultdict(int)
    for ka,va in A.items():
        for kb,vb in B.items():
            C[tuple(x+y for x,y in zip(ka,kb))]+=va*vb
    return {k:v for k,v in C.items() if v}
Psi={}
for idx,r in enumerate(R):
    k=[0]*8; k[idx]=1; k[6]=r; Psi[tuple(k)]=1
k=[0]*8; k[6]=7; Psi[tuple(k)]=1
pows=[{(0,)*8:1}]
for _ in range(13): pows.append(mul(pows[-1],Psi))
LHS={}
for i in range(14):
    chis={}
    for kk,q,v in chi[i]:
        key=list(kk)+[7*i,q]
        chis[tuple(key)]=((-1)**i)*v
    t=mul(chis,pows[13-i])
    for kk,v in t.items(): add(LHS,kk,v)
print('LHS terms',len(LHS))
# reduce q^13 -> Q and check zero; compute H with LHS = (q^13 - Q) H by division in q
# division: process highest q power down
rem=dict(LHS); H={}
while True:
    top=[k for k in rem if k[6]>=13]
    if not top: break
    mx=max(k[6] for k in top)
    for k in [k for k in rem if k[6]==mx]:
        v=rem.pop(k)
        hk=list(k); hk[6]-=13; hk=tuple(hk)
        H[hk]=H.get(hk,0)+v
        # subtract v*(q^13 - Q)*q^{..} => rem -= v*k ; rem += v*Q*(k with q-13)
        k2=list(hk); k2[7]+=1; k2=tuple(k2)
        add(rem,k2,v)
print('remainder terms (should be 0):',len(rem),' H terms',len(H))
mq=min(k[7] for k in LHS); print('min Q exp',mq)
