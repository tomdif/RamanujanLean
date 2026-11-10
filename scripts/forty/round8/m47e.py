# linear-algebra version of the gluing search: weights w[term,opt], sum_opt w = coef; leaves by signature cancel
exec(open('m47d.py').read().split("names=list(terms)")[0])
import sympy as sp
names=list(terms); opts=list(SPL)
var={}
for nm in names:
    for o in opts: var[(nm,o)]=sp.Symbol(f"w_{nm}_{o}")
eqs=[]
for nm in names:
    eqs.append(sp.Eq(sum(var[(nm,o)] for o in opts), sp.Rational(terms[nm][0])))
grp=defaultdict(lambda:0)
for nm in names:
    for o in opts:
        for (c,k0,shape,G,kk) in pieces[(nm,o)]:
            grp[(k0,shape)]+= var[(nm,o)]*sp.Rational(c)/sp.Rational(terms[nm][0])
for k,v in grp.items(): eqs.append(sp.Eq(v,0))
sol=sp.solve(eqs, list(var.values()), dict=True)
print(sol)
