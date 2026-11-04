# Test: slope-j part of T_l on S_w(1) has residual charpoly = (C(s,j)/C(k+j-1,j)) * T_l on S_k(1),
# where w = k + 2j + s(l-1), 3 <= k <= l+1.  All via exact integer charpolys from PARI.
import subprocess,re,sys
from math import comb
from functools import lru_cache
@lru_cache(None)
def cp(l,k):
    "charpoly of T_l on S_k(1), high->low, exact"
    if k<12 or k%2 or k==14: return [1]
    src=f"default(parisize,2000000000);\nmf=mfinit([1,{k}],1);print(Vec(charpoly(mfheckemat(mf,{l}))));quit;"
    o=subprocess.run(['gp','-q'],input=src,capture_output=True,text=True).stdout
    o=[x for x in o.splitlines() if x.startswith('[')][-1]
    return [int(t) for t in re.findall(r'-?\d+',o)]
def val(x,p):
    if x==0:return 10**9
    v=0
    while x%p==0:x//=p;v+=1
    return v
def segs(co,p):
    n=len(co)-1
    pts=[(i,val(co[i],p)) for i in range(n+1) if co[i]!=0]
    hull=[]
    for q in pts:
        while len(hull)>=2 and (hull[-1][1]-hull[-2][1])*(q[0]-hull[-1][0])>=(q[1]-hull[-1][1])*(hull[-1][0]-hull[-2][0]):hull.pop()
        hull.append(q)
    out=[]
    for a,b in zip(hull,hull[1:]):
        m=b[0]-a[0];d=b[1]-a[1]
        if d%m: out.append((d/m,m,None));continue
        s=d//m
        c=[]
        for i in range(m+1):
            v=a[1]+i*s;x=co[a[0]+i]
            c.append((x//p**v)%p if x%p**v==0 else None)
        i0=pow(c[0],-1,p);out.append((s,m,[y*i0%p for y in c]))
    return out
def divmod_(c,d,p):
    c=c[:];q=[]
    for i in range(len(c)-len(d)+1):
        t=c[i]%p;q.append(t)
        for j in range(len(d)):c[i+j]=(c[i+j]-t*d[j])%p
    r=c[len(c)-len(d)+1:] if len(d)>1 else []
    return q,r
tot=ok=0
for l in map(int,sys.argv[1].split(',')):
  for w in range(int(sys.argv[2]),int(sys.argv[3])*(l-1),2):
    co=cp(l,w)
    if len(co)==1: continue
    line=[]
    for j,m,c in segs(co,l):
        if c is None: line.append(f'{j:.2f}x{m}'); continue
        k=(w-2*j)%(l-1)
        while k<3:k+=l-1
        while k>l+1:k-=l-1
        s=(w-k-2*j)//(l-1)
        P=cp(l,k) if k>=0 else [1]
        P=[x%l for x in P]
        num=comb(s,j) if s>=0 else None
        den=comb(k+j-1,j)
        if len(P)==1 and m>=1:
            line.append(f'j{j}[k{k},s{s}]m{m}:noPred'); continue
        if den%l==0 or num%l==0:
            line.append(f'j{j}[k{k},s{s}]m{m}:binom0'); continue
        u=num*pow(den,-1,l)%l
        pred=[pow(u,i,l)*P[i]%l for i in range(len(P))]
        if len(pred)-1>m: line.append(f'j{j}[k{k},s{s}]m{m}<dim{len(pred)-1}'); continue
        q,r=divmod_(c,pred,l)
        good=all(x==0 for x in r)
        tot+=1;ok+=good
        line.append(f'j{j}[k{k},s{s}]m{m}/{len(pred)-1}:{"OK" if good else "NO"}')
    print(l,w,' '.join(line),flush=True)
print('TOTAL',ok,'/',tot)
