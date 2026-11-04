default(parisize,3000000000);
n8=mfinit([6,8],0);h=mfeigenbasis(n8)[1];N=60000;
v=mfcoefs(h,N);print("a2,a3,a5=",v[3],",",v[4],",",v[6]);
n6=mfinit([6,6],0);h6=mfeigenbasis(n6)[1];w=mfcoefs(h6,N);print("wt6 a2,a3,a5=",w[3],",",w[4],",",w[6]);
print("wt8 nonordinary primes <=",N,": ",select(p->p>=5&&v[p+1]%p==0,primes([2,N])));
print("wt6 nonordinary primes <=",N,": ",select(p->p>=5&&w[p+1]%p==0,primes([2,N])));
quit;
