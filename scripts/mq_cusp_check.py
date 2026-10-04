import sys, math
sys.path.insert(0, __import__('os').path.dirname(__file__))
from quintuple_vanishing_scan import product_coefficients, quintuple_terms, multiply_truncated
def unsigned(p,idx,limit):
    res={0:1}
    for i in idx:
        t={e:abs(c) for e,c in quintuple_terms(p,i,limit).items()}
        res=multiply_truncated(res,t,limit)
    return res
for (p,trip) in [(71,(1,4,14)),(79,(1,9,32)),(101,(1,10,40)) ]:
    limit=p*600
    co=product_coefficients(p,trip,limit); un=unsigned(p,trip,limit)
    for r in [0,1,5]:
        S=0;T=0;C2=0
        for t in range(600):
            K=p*t+r
            S+=co.get(K,0); T+=un.get(K,0); C2+=co.get(K,0)**2
        print(p,trip,"r",r,"signed sum",S,"unsigned(point count)",T,"sum c^2",C2, "ratio |S|/T=%.4f"%(abs(S)/max(T,1)))
