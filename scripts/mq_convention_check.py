import sys
sys.path.insert(0, __import__('os').path.dirname(__file__))
from quintuple_vanishing_scan import product_coefficients
from collections import defaultdict
def series(p,idx,Kmax,conv):
    per=[]
    for i in idx:
        lst=[]
        M=int((6*Kmax/p)**0.5)+5
        for m in range(-M,M+1):
            if conv==1:
                if m%3==1: continue
                E=i*m+p*m*(m+1)//6; s=1 if m%3==0 else -1
            else:
                if m%3==2: continue
                E=i*m+p*m*(m-1)//6; s=1 if m%3==0 else -1
            if 0<=E<=Kmax: lst.append((E,s))
        per.append(lst)
    out=defaultdict(int)
    for a in per[0]:
        for b in per[1]:
            for c in per[2]:
                K=a[0]+b[0]+c[0]
                if K<=Kmax: out[K]+=a[1]*b[1]*c[1]
    return {k:v for k,v in out.items() if v}
for p,t in [(71,(1,4,14)),(43,(1,6,7)),(7,(1,2,3))]:
    Kmax=p*20
    ref=product_coefficients(p,t,Kmax)
    print(p,t,"my m(m+1) convention matches:",series(p,t,Kmax,1)==ref,"  m(m-1) convention matches:",series(p,t,Kmax,2)==ref)
