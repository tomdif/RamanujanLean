# Weierstrass 3-term relations among J_a = f(Q^a), f(x) = (x;p)(p/x;p)(p;p), p = Q^13.
# f(xy)f(x/y)f(uv)f(u/v) - f(xv)f(x/v)f(uy)f(u/y) = (u/y) f(yv)f(y/v)f(xu)f(x/u)
# normalize f(Q^e) = sign * Q^m * J_r, r in 0..6 (J_0 = 0)
import itertools, json
def norm(e):
    # f(x p) = -x^{-1} f(x) ; f(p/x) = f(x)  (for f=(x;p)(p/x;p)(p;p))
    s=1; m=0
    while e<0 or e>=13:
        if e>=13:
            # f(Q^e) = f(Q^{e-13} p) = -(Q^{e-13})^{-1} f(Q^{e-13})
            s=-s; m+=-(e-13); e-=13
        else:
            # e<0: f(Q^e) with Q^e = Q^{e+13}/p : f(x/p) = -(x/p) f(x)?? use f(x) = -x f(x p)?
            # from f(xp) = -x^{-1} f(x): f(x) = -x^{-1}... set y=x/p: f(y p) = -y^{-1} f(y) => f(y) = -y f(yp)
            s=-s; m+=e; e+=13
    if e>6: e=13-e
    return s,m,e
rels=set()
out=[]
import fractions
HALF=[x/2 for x in range(1,26,2)]
for a,b,c,d in list(itertools.product(range(0,13),repeat=4))+list(itertools.product(HALF,repeat=4)):
    # x=Q^a,y=Q^b,u=Q^c,v=Q^d
    terms=[]
    def prodf(exps):
        s=1;m=0;mon=[]
        for e in exps:
            ss,mm,r=norm(e)
            if r==0: return None
            s*=ss;m+=mm;mon.append(r)
        return (s,m,tuple(sorted(mon)))
    T1=prodf([int(a+b),int(a-b),int(c+d),int(c-d)]); T2=prodf([int(a+d),int(a-d),int(c+b),int(c-b)]); T3=prodf([int(b+d),int(b-d),int(a+c),int(a-c)])
    if T1 is None or T2 is None or T3 is None: continue
    # T1 - T2 - Q^{c-b} T3 = 0
    rel=((T1[0],T1[1],T1[2]),(-T2[0],T2[1],T2[2]),(-T3[0],T3[1]+int(c-b),T3[2]))
    mn=min(t[1] for t in rel)
    rel=tuple(sorted((s,m-mn,mon) for s,m,mon in rel))
    if rel not in rels:
        rels.add(rel); out.append(rel)
print(len(out))
json.dump(out,open('weier13.json','w'))
# numeric check
L=120
def mul(x,y):
    z=[0]*L
    for i,u in enumerate(x):
        if u:
            for j in range(L-i): z[i+j]+=u*y[j]
    return z
def J(a):
    s=[1]+[0]*(L-1)
    for n in range(L):
        for t in (a+13*n, 13-a+13*n, 13+13*n):
            if t<L:
                f=[0]*L; f[0]=1; f[t]=-1; s=mul(s,f)
    return s
Js={a:J(a) for a in range(1,7)}
bad=0
for rel in out:
    tot=[0]*L
    for s,m,mon in rel:
        p=[1]+[0]*(L-1)
        for r in mon: p=mul(p,Js[r])
        for i in range(L-m): tot[i+m]+=s*p[i]
    if any(tot[:L-40]): bad+=1
print('bad',bad)
