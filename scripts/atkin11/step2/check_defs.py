import sys, pickle, sympy as sp
sys.path.insert(0,'..')
from qs import *
from atkin_basis import basis
M=300
def eta_a(a,M):
    p=fmpq_poly([1])
    for n in range(M):
        for e in (11*n+a, 11*n+11-a):
            if e<M: p=fmpq_poly((p*fmpq_poly([1]+[0]*(e-1)+[-1])).coeffs()[:M])
    return S(p,0,M)
H={a:eta_a(a,M) for a in range(1,6)}
Qs=S(fmpq_poly([0,1]),0,M)
E=pickle.load(open('E_sym.pkl','rb'))
c0,c1,c2,c4,c7,Q=sp.symbols('c0 c1 c2 c4 c7 Q')
vals={c0:H[4]*H[2].inv(), c1:-1*H[2]*H[1].inv(), c2:-1*H[5]*H[3].inv(), c7:H[3]*H[4].inv(), c4:-1*Qs*H[1]*H[5].inv()}
def ev(expr):
    tot=const(0,M)
    for term in sp.Add.make_args(sp.expand(expr)):
        coef,rest=term.as_coeff_Mul()
        s=const(fmpq(int(sp.numer(coef)),int(sp.denom(coef))),M)
        for f,pw in rest.as_powers_dict().items():
            if f==1: continue
            if f==Q: s=S(s.p,s.v+int(pw),s.N+int(pw))
            else:
                for _ in range(int(pw)): s=s*vals[f]
        tot=tot+s
    return tot
e={j:ev(E[j]) for j in (5,7,9)}
B=basis(M); z=B['z']
g4=(e[5]*z+1331*z)*fmpq(1,22)
g3=(e[7]*z-1452*g4-14641*z)*fmpq(1,22)
g2=(968*g3+11979*g4+161051*z-e[9]*z)*fmpq(1,11)
def zero(s,n=200): return all(s.coeff(k)==0 for k in range(max(s.v,0),n))
print("g2==Atkin:",zero(g2-B['g2']),"g3:",zero(g3-B['g3']),"g4:",zero(g4-B['g4']))
print("G4",zero(g4-(g2*g2-g3)),"R1",zero(g2*g3-(g2*g2-g3+11*z)),"R2",zero(g3*g3-(g2*g2*g2-g2*g3-z)))
