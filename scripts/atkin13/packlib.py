import sympy as sp
J=sp.symbols('J1:7'); Q=sp.Symbol('Q')
VARS=list(J)+[Q]
def pack_poly(expr):
    P=sp.Poly(sp.expand(expr),*VARS)
    out=[]
    for mon,c in P.terms():
        e=sum(int(x)*1024**k for k,x in enumerate(mon))
        c=int(c)
        out.append(e*2**100 + 2*abs(c) + (1 if c<0 else 0))
    return out
def lean_list(name,nums,per=6,block=1500):
    if len(nums)<=block:
        chunks=[', '.join(str(n) for n in nums[i:i+per]) for i in range(0,len(nums),per)]
        return f"def {name} : List ℕ := [" + ",\n  ".join(chunks) + "]"
    parts=[]; names=[]
    for b in range(0,len(nums),block):
        nm=f"{name}_{b//block}"; names.append(nm)
        parts.append(lean_list(nm,nums[b:b+block],per,block))
    parts.append(f"def {name} : List ℕ := " + " ++ ".join(names))
    return "\n".join(parts)
