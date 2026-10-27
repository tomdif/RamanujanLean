import itertools, json, sympy as sp
from fractions import Fraction as F
exec(open('relnum.py').read().split("d=int(sys.argv[1])")[0])
d=4
mons=list(itertools.combinations_with_replacement(range(1,7),d))
mser={}
for mon in mons:
    s=[1]+[0]*(L-1)
    for a in mon: s=mul(s,Js[a])
    mser[mon]=s
for target in (F(70,13),F(57,13),F(61,13)):
    terms=[]
    for mon in mons:
        sw=sum(w[a] for a in mon); m=target-sw
        if m>=0 and m.denominator==1: terms.append((mon,int(m)))
    K=120
    A=sp.Matrix([[ (mser[mon][i-m] if i>=m else 0) for (mon,m) in terms] for i in range(K)])
    ns=A.nullspace()
    print(target,[ (t) for t in terms])
    for v in ns: print('  ',list(v))
