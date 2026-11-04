#!/usr/bin/env python3
import sys,json,time,random
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent))
from quintuple_vanishing_scan import quintuple_terms,primes_through
from paley_spinor_scan import short_projective_roots,projective_root_target,restricted_lattice,isotropic_j_representatives
from flint import fmpz_poly
from math import isqrt

def coefficients(p,v,limit):
 out=fmpz_poly([1])
 for x in v:
  terms=quintuple_terms(p,x,limit)
  cs=[0]*(max(terms)+1)
  for a,c in terms.items():cs[a]=c
  out=fmpz_poly((out*fmpz_poly(cs)).coeffs()[:limit+1])
 return out

def test(p,v):
 roots=short_projective_roots(p,v)
 predicted={projective_root_target(r,restricted_lattice(p,v))[1] for r in roots} if roots else set()
 missing=set(range(p))-predicted
 depth=min(8,p//4);first={}
 while True:
  co=coefficients(p,v,p*depth+p-1)
  for r in list(missing):
   for n in range(depth+1):
    c=int(co[p*n+r])
    if c:
     first[r]=(n,c);missing.remove(r);break
  assert all(not co[p*n+r] for r in predicted for n in range(depth+1))
  if not missing or depth==p//4:break
  depth=min(p//4,2*depth)
 if missing:return {'p':p,'indices':v,'missing_nonroot_residues':sorted(missing),'depth':depth}
 r=max(first,key=lambda r:first[r][0]);return {'p':p,'indices':v,'R':r,'first':first[r],'ratio':first[r][0]/p}
import argparse
parser=argparse.ArgumentParser(description='Exact first-witness tests, including non-normalized triples; not a proof of a universal bound.')
parser.add_argument('--small-prime-max',type=int,default=151)
parser.add_argument('--sample-prime-max',type=int,default=3000)
parser.add_argument('--samples',type=int,default=800)
parser.add_argument('--seed',type=int,default=20261101)
parser.add_argument('--output',type=Path,required=True)
args=parser.parse_args()
start=time.time();best=None;count=0;viol=[];rng=random.Random(args.seed)
records=[]
def record(p,v):
 global best,count
 t=test(p,v);count+=1
 if 'missing_nonroot_residues' in t:
  viol.append(t);print('VIOLATION',t,flush=True);json.dump({'tested':count,'violations':viol},args.output.open('w'),indent=2);raise SystemExit(2)
 if best is None or t['ratio']>best['ratio']:
  best=t;print('new worst',t,'count',count,'seconds',round(time.time()-start,1),flush=True)
for p in primes_through(args.small_prime_max):
 sq={k*k%p:k for k in range(1,(p+1)//2)}
 for i in range(1,(p+1)//2):
  for j in range(i+1,(p+1)//2):
   k=sq.get((-i*i-j*j)%p,0)
   if k>j:record(p,(i,j,k))
 print('all triples through',p,'tested',count,flush=True)
small_count=count
primes=list(primes_through(args.sample_prime_max))
for _ in range(args.samples):
 p=rng.choice([p for p in primes if p>args.small_prime_max])
 reps=list(isotropic_j_representatives(p).values());v=rng.choice(reps)
 a=rng.randrange(1,p)
 v=tuple(sorted(min(a*x%p,(-a*x)%p) for x in v))
 record(p,v)
 if count%100==0:print('sampled',count-small_count,'seconds',round(time.time()-start,1),flush=True)
json.dump({'status':'bounded exact evidence, not a proof','small_prime_max':args.small_prime_max,'sample_prime_max':args.sample_prime_max,'all_canonical_triples':small_count,'random_projective_rescalings':count-small_count,'random_seed':args.seed,'total':count,'worst':best,'violations':viol,'seconds':time.time()-start},args.output.open('w'),indent=2)
print('DONE',count,'worst',best,flush=True)
