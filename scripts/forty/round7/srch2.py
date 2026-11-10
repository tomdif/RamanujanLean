import numpy as np, itertools, sys
from srch import thd,dmul,dadd,dsh
L=300
def norm(d):
    ks=sorted(k for k,v in d.items() if v)
    if not ks: return {},0,0
    k0=ks[0]; c=d[k0]
    return {k-k0: v//c if v%c==0 else v/c for k,v in d.items() if v and k-k0<L-60}, k0, c
def formsum(A,B,C,d,e,d1,d2,R=40):
    o={}
    for x in range(-R,R+1):
        for y in range(-R,R+1):
            Q=A*x*x+2*B*x*y+C*y*y+d*x+e*y
            if Q<L+400: o[Q]=o.get(Q,0)+(-1)**((d1*x+d2*y)%2)
    return {k:v for k,v in o.items() if v}
def tq(d): return {2*k:v for k,v in d.items()}
LIM=400
SA=dadd(dmul(thd(30,6),dadd(thd(330,143),dsh(11,1,thd(330,253))),LIM), dsh(1,-1,dmul(thd(30,12),dadd(thd(330,209),dsh(33,1,thd(330,319))),LIM)))
SAt=norm(tq(SA))[0]
def search(A,B,C,target,dr,er):
    hits=[]
    for d in dr:
        for e in er:
            for d1 in (0,1):
                for d2 in (0,1):
                    # quick: minimal exps
                    F=formsum(A,B,C,d,e,d1,d2,R=12)
                    nF,k0,c=norm(F)
                    ok=all(nF.get(k,0)==target.get(k,0) for k in range(0,120))
                    if ok: hits.append((d,e,d1,d2,k0,c))
    return hits
if __name__=="__main__":
    A,B,C=map(int,sys.argv[1:4])
    # shifts lattice: (2A,2B),(2B,2C)
    h=search(A,B,C,SAt,range(0,2*A),range(-B*2-C,2*C+1))
    print(h[:10],len(h))
