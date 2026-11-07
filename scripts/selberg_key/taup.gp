\\ tau(p) for primes p <= 40000, format "p tau(p)" (consumed by sk.c and ../qf_proof/q.c)
default(nbthreads,1);
default(parisize, 200000000);
f = "taup.txt";
mf = mfinit([1,12],1); D = mfbasis(mf)[1]; c = mfcoefs(D, 40000);
forprime(p=2,40000, write(f, p, " ", c[p+1]));
quit;
