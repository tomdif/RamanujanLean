import itertools, sympy as sp, sys
L=120
def mul(a,b):
    c=[0]*L
    for i,x in enumerate(a):
        if x:
            for j in range(L-i): c[i+j]+=x*b[j]
    return c
def inv(a):
    s=next(i for i,x in enumerate(a) if x); a2=a[s:]+[0]*s
    b=[0]*L; b[0]=a2[0]
    for m in range(1,L): b[m]=-a2[0]*sum(a2[j]*b[m-j] for j in range(1,m+1))
    return s,b
def J(a):
    s=[1]+[0]*(L-1)
    for n in range(L):
        for t in (a+13*n, 13-a+13*n, 13+13*n):
            if t<L:
                f=[0]*L; f[0]=1; f[t]=-1; s=mul(s,f)
    return s
Js={a:J(a) for a in range(1,7)}
def ratio(a,b,sh=0,sg=1):
    s,ib=inv(Js[b]); r=mul(Js[a],ib); assert s==0
    out=[0]*L
    for i in range(L-sh): out[i+sh]=sg*r[i]
    return out
c={'c0':ratio(4,2),'c1':ratio(6,3,0,-1),'c2':ratio(2,1,0,-1),'c5':ratio(5,4),'c9':ratio(1,6,1),'c12':ratio(3,5,0,-1)}
E=[0]*L
for k in range(-40,41):
    e=k*(3*k-1)//2
    if 0<=e<L: E[e]+=(-1)**(k%2)
E13=[0]*L
for i in range(0,L,13): E13[i]=E[i//13]
_,iE13=inv(E13); w=mul(E,iE13); w2=mul(w,w); _,iw2=inv(w2)
names=list(c)
deg=int(sys.argv[1])
mons=[]
for ex in itertools.product(range(deg+1),repeat=6):
    if sum(ex)>deg: continue
    m=[1]+[0]*(L-1)
    for n,e in zip(names,ex):
        for _ in range(e): m=mul(m,c[n])
    mons.append((ex,m))
K=L-1
for tname,t in (('w2',w2),('w-2',iw2)):
    A=sp.Matrix([m[:K] for _,m in mons]).T
    b=sp.Matrix(t[:K])
    try:
        x,params=A.gauss_jordan_solve(b)
        x=x.subs({p:0 for p in params})
        print(tname,'FOUND',[(ex,v) for (ex,_),v in zip(mons,x) if v!=0], 'free params',len(params))
    except ValueError:
        print(tname,'no')
