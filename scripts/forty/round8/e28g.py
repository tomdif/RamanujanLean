import sympy as sp
exec(open('e28f.py').read().split("out=[]")[0])
for k,v in rels.items():
    n=sp.expand(sp.numer(sp.together(v)))
    print(k, "zero" if n==0 else f"nonzero, {len(n.as_ordered_terms())} terms, deg {sp.Poly(n,a1,a2,b1,b2,q).total_degree()}")
