# express J-homogeneous relations / targets in c-variables (Laurent), Q = -c0c1c2c5c9c12
import json, sympy as sp, itertools
from packlib import J, Q
c0,c1,c2,c5,c9,c12=C=sp.symbols('c0 c1 c2 c5 c9 c12')
# c_r = sign * Q^qe * J^num / J^den
cdef={c0:(1,0,4,2),c1:(-1,0,6,3),c2:(-1,0,2,1),c5:(1,0,5,4),c9:(1,1,1,6),c12:(-1,0,3,5)}
# cycle: J1 -c2-> J2 -c0-> J4 -c5-> J5 -c12-> J3 -c1-> J6 -c9-> J1
# so J2 = -c2*J1, J4 = c0*J2, J5 = c5*J4, J3 = -c12*J5, J6 = -c1*J3, J1 = c9*J6/Q
Jc={1:sp.Integer(1)}
Jc[2]=-c2*Jc[1]; Jc[4]=c0*Jc[2]; Jc[5]=c5*Jc[4]; Jc[3]=-c12*Jc[5]; Jc[6]=-c1*Jc[3]
# consistency: J1 = c9*J6/Q  => 1 = c9*(-c1)(-c12)c5 c0 (-c2) /Q => Q = -c0c1c2c5c9c12 ✓
Qc=-c0*c1*c2*c5*c9*c12
def to_c(expr):
    # expr homogeneous in J's: substitute J_a = Jc[a] * J1 (J1 cancels by homogeneity), Q = Qc
    e=expr.subs({J[a-1]:Jc[a] for a in range(1,7)}).subs(Q,Qc)
    return sp.expand(e)
if __name__=='__main__':
    inst=json.load(open('weier13_inst.json'))
    loc={f'J{i}':J[i-1] for i in range(1,7)}; loc['Q']=Q
    out=[]
    for _,t in inst:
        e=to_c(sp.sympify(t,locals=loc))
        # clear denominators (none expected since substitution polynomial) -> divide by gcd monomial
        P=sp.Poly(e,*C)
        g=None
        mons=P.monoms()
        mn=[min(m[i] for m in mons) for i in range(6)]
        e=sp.expand(e/sp.Mul(*[v**k for v,k in zip(C,mn)]))
        out.append(str(e))
        print(len(sp.Poly(e,*C).terms()), sp.Poly(e,*C).total_degree())
    json.dump(out,open('wc13.json','w'))
