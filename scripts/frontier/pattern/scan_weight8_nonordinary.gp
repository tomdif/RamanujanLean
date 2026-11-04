\\ Exact bounded scan of the normalized newform 6.8.a.a.
\\ This is a PARI computation, not a Lean certificate or an all-prime theorem.
default(parisize,1500000000);
{iferr(
N=250000; gettime();
mf=mfinit([6,8],0); h=mfeigenbasis(mf)[1]; v=mfcoefs(h,N);
if([v[3],v[4],v[6]] != [8,27,-114],error("wrong weight-eight form"));
P=primes([5,N]); hits=select(p->v[p+1]%p==0,P);
print("pari_version=",version());
print("weight8_bound=",N," primes=",#P," hits=",hits);
print("weight8_a2_a3_a5=",[v[3],v[4],v[6]]);
for(i=1,#hits,p=hits[i];print("hit=",p," coefficient=",v[p+1]));
h6=mfeigenbasis(mfinit([6,6],0))[1]; w=mfcoefs(h6,1000);
control=select(p->w[p+1]%p==0,primes([5,1000]));
if(control != [859],error("weight-six positive control failed"));
print("weight6_control_bound=1000 hits=",control);
print("elapsed_ms=",gettime());
, E, print(E); quit(1));}
quit;
