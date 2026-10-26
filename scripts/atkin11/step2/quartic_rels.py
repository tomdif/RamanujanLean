"""Exact rational basis of degree-4 relations sum c_{m,e} Q^e m(theta) = 0 (e<=E), for Singular."""
import sys, itertools
sys.path.insert(0,'..')
from qs import *
from flint import fmpq_mat, fmpq
E=int(sys.argv[1]); M=int(sys.argv[2])
def f_series(n,M):
    c=[0]*M
    for k in range(-40,41):
        e=11*k*(k-1)//2+n*k
        if 0<=e<M: c[e]+=(-1)**(k%2)
    return S(fmpq_poly(c),0,M)
th={a:f_series(a,M) for a in range(1,6)}
monos=list(itertools.combinations_with_replacement(range(1,6),4))
cols=[];names=[]
for m in monos:
    s=const(1,M)
    for a in m: s=s*th[a]
    for e in range(E+1): cols.append(S(s.p,s.v+e,s.N+e)); names.append((m,e))
rows=list(range(0,M-E-5))
import flint
A=flint.fmpz_mat(len(rows),len(cols),[int(c.coeff(n)) for n in rows for c in cols])
K=A.nullspace()[0] if hasattr(A,'nullspace') else None
X,nul=A.nullspace()
print("nullity",nul,file=sys.stderr)
rels=[]
for j in range(nul):
    terms=[]
    for i in range(len(cols)):
        v=int(X[i,j])
        if v: 
            (m,e)=names[i]
            terms.append(f"({v})*Q^{e}*"+"*".join(f"t{a}" for a in m))
    rels.append("+".join(terms))
open(f'quartic_E{E}.txt','w').write(",\n".join(rels))
