#!/usr/bin/env python3
"""Test the actual partition seed in the computed second-order Katz operator.

The ordinary projector is constructed by Bezout separation modulo p and
idempotent lifting 3P^2-2P^3 modulo p^2. This avoids enormous group-exponent
matrix powers. Agreement of two truncations is evidence, not proof of the
infinite-series identification needed for universal sharpness.
"""
import sys,time,json
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent))
from katzmat import get
from flint import nmod_mat,nmod_poly

def run(p,N):
 st=time.time();d=get(p,2,N);q=p*p;n=d['dN'];d1=d['dims'][1]-1;ix=list(range(1,d1+1))
 U=nmod_mat(d['U'],q);D=nmod_mat(d['D'],q);X=D*U
 Uf=nmod_mat([[d['U'][i][j]%p for j in ix] for i in ix],p)
 Df=nmod_mat([[d['D'][i][j]%p for j in ix] for i in ix],p)
 ns,k=Df.nullspace();Kb=[[int(ns[i,j]) for i in range(d1)] for j in range(k)]
 UV=Uf*Df;cols=[]
 for j in range(d1):
  c=[int(UV[i,j]) for i in range(d1)]
  if nmod_mat(cols+[c],p).rank()>len(cols):cols.append(c)
 B=nmod_mat([[row[i] for row in cols+Kb] for i in range(d1)],p);assert B.rank()==d1;Bi=B.inv();r=len(cols)
 def project(vec):
  z=Bi*nmod_mat([[int(vec[i,0])%p] for i in ix],p)
  return [int(z[r+j,0]) for j in range(k)]
 tc=[]
 for col in Kb:
  l=nmod_mat([[0] for _ in range(n)],q)
  for i,x in zip(ix,col):l[i,0]=x
  y=D*l;assert all(int(y[i,0])%p==0 for i in range(n))
  w=nmod_mat([[int(y[i,0])//p] for i in range(n)],q)
  tc.append(project(U*w))
 T=nmod_mat([[tc[j][i] for j in range(k)] for i in range(k)],p)
 Xf=nmod_mat([[int(X[i,j])%p for j in range(n)] for i in range(n)],p)
 cp=Xf.charpoly();cs=list(map(int,cp.coeffs()));s=next(i for i,x in enumerate(cs) if x)
 g=nmod_poly(cs[s:],p);xp=nmod_poly([0]*s+[1],p);gcd,a,b=xp.xgcd(g);assert gcd==nmod_poly([1],p)
 e=a*xp
 assert not (e*e-e)%cp and not e%xp and not (e-1)%g
 eco=list(map(int,e.coeffs()))
 L1=nmod_mat([[d['D'][i][0]] for i in range(n)],q)
 def P0(v):
  out=nmod_mat([[0] for _ in range(n)],q)
  for c in reversed(eco):out=X*out+c*v
  return out
 z1=P0(L1);z2=P0(z1);z3=P0(z2);ordinary=3*z2-2*z3
 z=L1-ordinary;uz=U*z;assert all(int(uz[i,0])%p==0 for i in range(n))
 seed=project(nmod_mat([[int(uz[i,0])//p] for i in range(n)],q))
 seedv=nmod_mat([[x] for x in seed],p);last=seedv
 for _ in range(k):last=T*last
 alive=any(int(last[i,0]) for i in range(k))
 result=dict(prime=p,precision=2,katz_cutoff=N,dim_kernel=k,theta_rank=T.rank(),theta_matrix=[[int(T[i,j]) for j in range(k)] for i in range(k)],seed=seed,survives_dimension_steps=alive,theta_charpoly=list(map(int,T.charpoly().coeffs())),seconds=round(time.time()-st,2))
 print({k:v for k,v in result.items() if k!='theta_matrix'},flush=True);return result
if __name__=='__main__':
 import argparse
 parser=argparse.ArgumentParser(description='Exact seed-survival computation in two Katz truncations; not an arithmetic identification proof.')
 parser.add_argument('--primes',default='233,257,307,401,607')
 parser.add_argument('--output',type=Path,required=True)
 args=parser.parse_args()
 results=[]
 for p in map(int,args.primes.split(',')):
  for N in (3,4):
   results.append(run(p,N))
   args.output.write_text(json.dumps({'status':'bounded Katz-model computation; arithmetic identification not formalized','results':results},indent=2)+'\n')
  a,b=results[-2:]
  assert a['theta_matrix']==b['theta_matrix'] and a['seed']==b['seed']
