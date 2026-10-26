from sympy import symbols, expand, Poly, linsolve, Rational, Matrix, together
import itertools, json
g2,g3,z=symbols('g2 g3 z')
R1=g2*g3-(g2**2-g3+11*z)
R2=g3**2-(g2**3-g2*g3-z)
g4=g2**2-g3; g6=g2*g4
gi={1:g2,2:g3,3:g4,4:g6,5:z}
ST=json.load(open('structure.json'))
def J(t):
    a,r=divmod(t,5)
    return z**a*(1 if r==0 else gi[r])
def monos(d):
    return [g2**i*g3**j*z**k for i in range(d+1) for j in range(d+1) for k in range(d+1) if i+j+k<=d]
out={}
for key,d in ST.items():
    b,r=map(int,key.split(','))
    diff=expand(gi[b]*gi[r]-sum(v*J(int(t)) for t,v in d.items()))
    for deg in range(0,6):
        ms=monos(deg)
        A=symbols('a0:%d'%len(ms)); B=symbols('b0:%d'%len(ms))
        a=sum(x*m for x,m in zip(A,ms)); bb=sum(x*m for x,m in zip(B,ms))
        eq=Poly(expand(a*R1+bb*R2-diff),g2,g3,z).coeffs()
        sol=linsolve(eq,*(A+B))
        if sol:
            s=list(sol)[0]
            subs={x:(0 if v.free_symbols else v) for x,v in zip(A+B,s)}
            # set free params to 0
            s2=[v.subs({f:0 for f in v.free_symbols}) for v in s]
            aa=expand(sum(v*m for v,m in zip(s2[:len(ms)],ms))); bb2=expand(sum(v*m for v,m in zip(s2[len(ms):],ms)))
            assert expand(aa*R1+bb2*R2-diff)==0
            out[key]=(str(aa),str(bb2)); print(key,deg,aa,'|',bb2); break
json.dump(out,open('mult_cofactors.json','w'))
