#!/usr/bin/env python3
"""Discover exact affine branch certificates for four quintuple products.

Requires python-flint for lattice reduction and determinant arithmetic.
An independent standard-library checker validates the resulting identities.
A certificate proves the listed infinite vanishings by finite sign cancellation;
a failure to find one is not a nonvanishing proof or a converse theorem.
"""
from fractions import Fraction as F
from itertools import product
from math import isqrt
from flint import fmpz_mat
import json

def dot(a,b): return sum(x*y for x,y in zip(a,b))
def tr(A):return list(map(list,zip(*A)))
def mv(A,v):return [dot(r,v) for r in A]
def mm(A,B):return [[dot(r,c) for c in tr(B)] for r in A]
def inv(A):
 n=len(A);B=[[F(x) for x in row]+[F(i==j) for j in range(n)] for i,row in enumerate(A)]
 for i in range(n):
  k=next(k for k in range(i,n) if B[k][i]);B[i],B[k]=B[k],B[i];a=B[i][i];B[i]=[x/a for x in B[i]]
  for k in range(n):
   if k!=i:
    a=B[k][i];B[k]=[x-a*y for x,y in zip(B[k],B[i])]
 return [r[n:] for r in B]
def det(A):return int(fmpz_mat(A).det())
def vectors(norm,p,v):
 n=len(v);out=[]
 def go(prefix,left):
  if len(prefix)==n-1:
   a=isqrt(left)
   if a*a==left:
    for x in ({a,-a} if a else {0}):
     w=prefix+[x]
     if dot(v,w)%p==0:out.append(w)
   return
  for a in range(-isqrt(left),isqrt(left)+1):go(prefix+[a],left-a*a)
 go([],norm);return out

def run(p,v):
 n=len(v);B=[[int(i==j) for j in range(n)] for i in range(n)]
 B[-1]=[(-x*pow(v[-1],-1,p))%p for x in v[:-1]]+[p]
 B=tr([[int(x) for x in row] for row in fmpz_mat(tr(B)).lll().tolist()]);Bi=inv(B);H=mm(tr(B),B)
 assert abs(det(B))==p
 for col in tr(B):assert dot(v,col)%p==0
 cand=[vectors(H[i][i],p,v) for i in range(n)]
 print('basis',B,'norms',[H[i][i] for i in range(n)],'candidate_counts',list(map(len,cand)),flush=True)
 autos=[]
 def go(cols):
  j=len(cols)
  if j==n:
   A=mm(Bi,tr(cols));assert all(x.denominator==1 for row in A for x in row)
   A=[[int(x) for x in r] for r in A]
   assert abs(det(A))==1 and mm(mm(tr(A),H),A)==H
   autos.append(A);return
  for w in cand[j]:
   if all(dot(cols[i],w)==H[i][j] for i in range(j)):go(cols+[w])
 go([]);print('automorphisms',len(autos),flush=True)
 Q=[[3*p*x for x in r] for r in H];Qi=inv(Q);branches=list(product((0,1),repeat=n));ev=[b for b in branches if sum(b)%2==0];od=[b for b in branches if sum(b)%2]
 results={}
 for R in range(p):
  ds={};polys={}
  for b in branches:
   c0=(R-dot(v,b))*pow(3*v[-1],-1,p)%p;d=[0]*(n-1)+[c0];ell=[6*x+(2*z-1)*p for x,z in zip(v,b)]
   l=mv(tr(B),[6*p*x+y for x,y in zip(d,ell)])
   c=3*p*dot(d,d)+dot(ell,d)+2*dot(v,b)
   ds[b]=[x/2 for x in mv(Qi,l)];polys[b]=(l,c)
  edges={}
  for b in ev:
   for t in od:
    for A in autos:
     c=[x-y for x,y in zip(mv(A,ds[b]),ds[t])]
     if all(x.denominator==1 for x in c):
      c=list(map(int,c));lt,ct=polys[t];ls,cs=polys[b]
      assert dot(c,mv(Q,c))+dot(lt,c)+ct==cs
      assert mv(tr(A),[2*x+y for x,y in zip(mv(Q,c),lt)])==ls
      edges[b,t]=(A,c);break
  def match(bs,used):
   if not bs:return []
   b=bs[0]
   for t in od:
    if t not in used and (b,t) in edges:
     rest=match(bs[1:],used|{t})
     if rest is not None:return [(b,t,*edges[b,t])]+rest
  cert=match(ev,set())
  if cert is not None:
   results[R]=cert
   print('certified residue',R,'matrices',len({str(x[2]) for x in cert}),flush=True)
 return dict(p=p,indices=v,basis=B,gram=H,automorphisms=autos,certificates=results)
if __name__ == '__main__':
 import argparse
 from pathlib import Path
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('--prime',type=int,default=41)
 parser.add_argument('--indices',default='1,4,5,9')
 parser.add_argument('--output',type=Path,required=True)
 args=parser.parse_args()
 v=tuple(map(int,args.indices.split(',')))
 if len(v)!=4 or not all(0<2*x<args.prime for x in v):
  parser.error('four canonical positive indices are required')
 if args.prime<5 or any(args.prime%d==0 for d in range(2,isqrt(args.prime)+1)):
  parser.error('prime must be a prime at least 5')
 result=run(args.prime,v)
 result['method']='exact affine identities; no universal converse asserted'
 args.output.write_text(json.dumps(result,indent=2)+'\n')
