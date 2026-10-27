import sys, os
exec(open('gen_cert_lean.py').read().split("# common:")[0])
def packm(e):
    m=0
    for v in reversed(e): m=m*1024+v
    return m
def todict(poly):
    d={}
    for e,c in poly:
        k=packm(e); d[k]=d.get(k,0)+c
    return {k:v for k,v in d.items() if v}
def mul(a,b):
    r={}
    for k1,v1 in a.items():
        for k2,v2 in b.items():
            r[k1+k2]=r.get(k1+k2,0)+v1*v2
    return {k:v for k,v in r.items() if v}
def addd(ds):
    r={}
    for d in ds:
        for k,v in d.items(): r[k]=r.get(k,0)+v
    return {k:v for k,v in r.items() if v}
K=int(os.environ.get('K','1500')); F=4
def build(nm, sat=0):
    G=[todict(readp(f'{D}/G{j}.txt')) for j in range(1,26)]
    units=[]
    for j in range(1,26):
        L=readp(f'{D}/{nm}_{j}.txt')
        for s in range(0,len(L),K):
            piece=L[s:s+K]
            units.append((j,piece,mul(todict(piece),G[j-1])))
    level=[u[2] for u in units]; tree=[]
    while len(level)>1:
        groups=[level[i:i+F] for i in range(0,len(level),F)]
        nxt=[addd(g) for g in groups]
        tree.append((groups,nxt)); level=nxt
    T=todict(readp(f'{D}/{nm}_T.txt'))
    if sat:
        mm=sum(sat*1024**i for i in range(5)); T={k+mm:v for k,v in T.items()}
    assert level[0]==T, "root mismatch"
    return units,tree
if __name__=="__main__":
    for nm in sys.argv[1:]:
        units,tree=build(nm)
        print(nm,"units",len(units),"unit R sizes max",max(len(u[2]) for u in units),"sum",sum(len(u[2]) for u in units))
        for lv,(groups,nxt) in enumerate(tree):
            print("  level",lv,"nodes",len(nxt),"sizes max",max(map(len,nxt)),"sum",sum(map(len,nxt)))
