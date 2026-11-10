# generic search: split forms by index-2 sublattices, pair up pieces by series equality
import numpy as np, itertools
P=600
def form(a,b,c,d,e,s1,s2,R=60,k0=0):
    o=np.zeros(P,dtype=np.int64)
    for x in range(-R,R+1):
        for y in range(-R,R+1):
            E=a*x*x+2*b*x*y+c*y*y+d*x+e*y+k0
            if E<P:
                assert E>=0
                o[E]+=(-1)**((s1*x+s2*y)%2)
    return o
def sub(F,M,r):
    """substitute (x,y) = M (u,v) + r. F=(a,b,c,d,e,s1,s2). returns (const, sign, newF)"""
    a,b,c,d,e,s1,s2=F; (m11,m12),(m21,m22)=M; r1,r2=r
    def Qf(x,y): return a*x*x+2*b*x*y+c*y*y
    A=Qf(m11,m21); C=Qf(m12,m22)
    B=a*m11*m12+b*(m11*m22+m12*m21)+c*m21*m22
    # linear: grad at r
    gx=2*a*r1+2*b*r2+d; gy=2*b*r1+2*c*r2+e
    D=gx*m11+gy*m21; E=gx*m12+gy*m22
    const=Qf(r1,r2)+d*r1+e*r2
    sign=(-1)**((s1*r1+s2*r2)%2)
    S1=(s1*m11+s2*m21)%2; S2=(s1*m12+s2*m22)%2
    return const,sign,(A,B,C,D,E,S1,S2)
SPL={'x':([[2,0],[0,1]],[(0,0),(1,0)]),'y':([[1,0],[0,2]],[(0,0),(0,1)]),'xy':([[1,1],[-1,1]],[(0,0),(1,0)])}
def pieces(F,how):
    if how is None: return [(0,1,F)]
    M,rs=SPL[how]
    return [sub(F,M,r) for r in rs]
def norm(s):
    nz=np.nonzero(s)[0]
    if len(nz)==0: return None
    k=nz[0]; return k, s[k], tuple(s[k:k+P-100])
def find_map(G1,G2,R=2,Rs=3):
    """find (M, r) with det M = +-1 such that G1 o (M w + r) = const * sign * G2(w)"""
    out=[]
    for m in itertools.product(range(-R,R+1),repeat=4):
        if abs(m[0]*m[3]-m[1]*m[2])!=1: continue
        M=[[m[0],m[1]],[m[2],m[3]]]
        for r in itertools.product(range(-Rs,Rs+1),repeat=2):
            k,sg,G=sub(G1,M,r)
            if G[:5]==G2[:5] and G[5]%2==G2[5]%2 and G[6]%2==G2[6]%2:
                out.append((M,r,k,sg))
    return out
