import json
from fractions import Fraction as F
W=json.load(open('weier13.json'))
def w(a,sgn): return sgn*F(a*a-13*a,26)
for sgn in (1,-1):
    ok=True
    for rel in W:
        vals={s and (m+sum(w(x,sgn) for x in mon)) for s,m,mon in rel}
        if len(vals)>1: ok=False;break
    print(sgn,ok)
