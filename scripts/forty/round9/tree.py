"""round 9: general split-tree gluing search (index-2 sublattice splits, depth D), linear relaxation (as round8/m47f)."""
import numpy as np, itertools, sys
import scipy.sparse as sps, scipy.sparse.linalg as spl
from collections import defaultdict
from fractions import Fraction as Fr
P=1600; R=70; L=900
xs,ys=np.meshgrid(np.arange(-R,R+1),np.arange(-R,R+1)); xs=xs.ravel(); ys=ys.ravel()
def form(F,k0=0):
    a,b,c,d,e,s1,s2=F
    E=a*xs*xs+2*b*xs*ys+c*ys*ys+d*xs+e*ys+k0
    assert E.min()>=0,(F,k0)
    m=E<P; w=np.where(((s1*xs+s2*ys)%2)==0,1,-1)
    return np.bincount(E[m],weights=w[m],minlength=P).astype(np.int64)[:P]
def sub(F,M,r):
    a,b,c,d,e,s1,s2=F; (m11,m12),(m21,m22)=M; r1,r2=r
    Qf=lambda x,y: a*x*x+2*b*x*y+c*y*y
    A=Qf(m11,m21); C=Qf(m12,m22); B=a*m11*m12+b*(m11*m22+m12*m21)+c*m21*m22
    gx=2*a*r1+2*b*r2+d; gy=2*b*r1+2*c*r2+e
    return Qf(r1,r2)+d*r1+e*r2,(-1)**((s1*r1+s2*r2)%2),(A,B,C,gx*m11+gy*m21,gx*m12+gy*m22,(s1*m11+s2*m21)%2,(s1*m12+s2*m22)%2)
SPL={'x':([[2,0],[0,1]],[(0,0),(1,0)]),'y':([[1,0],[0,2]],[(0,0),(0,1)]),'xy':([[1,1],[-1,1]],[(0,0),(1,0)])}
def sig(s):
    nz=np.nonzero(s[:P-L-50])[0]
    if len(nz)==0: return None
    k=nz[0]; return k,int(s[k]),tuple(Fr(int(v),int(s[k])) for v in s[k:k+L])
def search(terms,DEPTH):
    nodes=[]
    def addnode(G,kk):
        g=sig(form(G,kk))
        nodes.append(dict(G=G,k=kk,sig=None if g is None else (g[0],g[2]),lead=0 if g is None else g[1],ch={}))
        return len(nodes)-1
    roots=[addnode(F,k) for (c,k,F) in terms]
    def expand(i,d):
        if d==0: return
        for o,(M,rs) in SPL.items():
            ch=[]
            for r in rs:
                k0,sg,G=sub(nodes[i]['G'],M,r); j=addnode(G,nodes[i]['k']+k0); ch.append((j,sg))
            nodes[i]['ch'][o]=ch
            for (j,sg) in ch: expand(j,d-1)
    for r in roots: expand(r,DEPTH)
    vidx={}
    for i,n in enumerate(nodes):
        for o in [None]+list(n['ch']): vidx[(i,o)]=len(vidx)
    amount={roots[t]:[(None,float(terms[t][0]))] for t in range(len(terms))}
    for i,n in enumerate(nodes):
        for o,ch in n['ch'].items():
            for (j,sg) in ch: amount[j]=[((i,o),float(sg))]
    rows=[];cols=[];vals=[];rhs=[];r=0
    for i,n in enumerate(nodes):
        for o in [None]+list(n['ch']): rows.append(r);cols.append(vidx[(i,o)]);vals.append(1.0)
        b=0.0
        for (src,f) in amount[i]:
            if src is None: b+=f
            else: rows.append(r);cols.append(vidx[src]);vals.append(-f)
        rhs.append(b); r+=1
    sigrow={}
    for i,n in enumerate(nodes):
        if n['sig'] is None: continue
        if n['sig'] not in sigrow: sigrow[n['sig']]=r; rhs.append(0.0); r+=1
        rows.append(sigrow[n['sig']]);cols.append(vidx[(i,None)]);vals.append(float(n['lead']))
    A=sps.csr_matrix((vals,(rows,cols)),shape=(r,len(vidx)))
    res=spl.lsqr(A,np.array(rhs),atol=1e-13,btol=1e-13,iter_lim=500000)
    x=res[0]; resid=np.linalg.norm(A@x-np.array(rhs))
    return resid,nodes,vidx,x
