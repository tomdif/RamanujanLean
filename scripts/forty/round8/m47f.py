# depth-2 linear gluing search for (5.18)
exec(open('m47d.py').read().split("names=list(terms)")[0])
import scipy.sparse as sps, scipy.sparse.linalg as spl
nodes=[]  # (name, coef(or None), series-sig, form, shift)
def addnode(G,kk):
    s=form(G,kk); g=sig(s)
    nodes.append(dict(G=G,k=kk,sig=None if g is None else (g[0],g[2]),lead=0 if g is None else g[1],children={}))
    return len(nodes)-1
roots={}
for nm,(c,k,F) in terms.items():
    roots[nm]=addnode(F,k)
def expand(i,depth):
    if depth==0: return
    n=nodes[i]
    for opt,sp_ in SPL.items():
        if sp_ is None: continue
        M,rs=sp_
        ch=[]
        for r in rs:
            k0,sg,G=sub(n['G'],M,r)
            j=addnode(G,n['k']+k0); ch.append((j,sg))
        n['children'][opt]=ch
        for (j,sg) in ch: expand(j,depth-1)
DEPTH=int(__import__('sys').argv[1]) if len(__import__('sys').argv)>1 else 2
for nm in terms: expand(roots[nm],DEPTH)
print("nodes",len(nodes))
# variables: y[i,opt] for opt in children keys + None
vidx={}
for i,n in enumerate(nodes):
    for o in [None]+list(n['children']): vidx[(i,o)]=len(vidx)
rows=[];cols=[];vals=[];rhs=[]
r=0
# amount of node i: a_i ; root: a=c ; child: a_j = sg * y[parent,opt]
amount={}
for nm,(c,k,F) in terms.items(): amount[roots[nm]]=[(None,float(c))]
for i,n in enumerate(nodes):
    for o,ch in n['children'].items():
        for (j,sg) in ch: amount[j]=[((i,o),float(sg))]
for i,n in enumerate(nodes):
    # sum_o y[i,o] - amount_i = 0
    for o in [None]+list(n['children']):
        rows.append(r);cols.append(vidx[(i,o)]);vals.append(1.0)
    b=0.0
    for (src,f) in amount[i]:
        if src is None: b+=f
        else: rows.append(r);cols.append(vidx[src]);vals.append(-f)
    rhs.append(b); r+=1
sigrow={}
for i,n in enumerate(nodes):
    if n['sig'] is None: continue
    key=n['sig']
    if key not in sigrow: sigrow[key]=r; rhs.append(0.0); r+=1
    rows.append(sigrow[key]);cols.append(vidx[(i,None)]);vals.append(float(n['lead']))
A=sps.csr_matrix((vals,(rows,cols)),shape=(r,len(vidx)))
import numpy as np
res=spl.lsqr(A,np.array(rhs),atol=1e-12,btol=1e-12,iter_lim=200000)
x=res[0]
print("residual",np.linalg.norm(A@x-np.array(rhs)), "vars",len(vidx),"eqs",r)
import pickle; pickle.dump((nodes,vidx,x,roots),open('/private/tmp/claude-501/-Users-thomasdifiore/1baa43e0-9643-458b-8681-0a73f9f4e386/scratchpad/m47f.pkl','wb'))
