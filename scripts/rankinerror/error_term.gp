\\ Numerics for the Rankin-Selberg error term S(x) - c x, S(x) = sum_{n<=x} tau(n)^2/n^11.
default(nbthreads,1); default(parisizemax, 4000000000); default(realprecision,40);
N = 1000000;
v = mfcoefs(mfDelta(), N);   \\ v[n+1] = tau(n)
c = 0.384084054468170370;
S = 0.; M = vector(7); X=vector(7);
\\ max |S(x)-cx| over x in [10^(j-1),10^j)
for(n=1,N, S += (v[n+1]^2/n^11)*1.; e=abs(S-c*n); j=floor(log(n)/log(10)+1e-9)+1; if(e>M[j],M[j]=e;X[j]=n));
for(j=1,7, if(M[j]>0, printf("decade %d: max|S-cx| = %.5g at x=%d ; /x^(3/5) = %.4g ; /x^(1/2) = %.4g\n", j, M[j], X[j], M[j]/X[j]^(3/5), M[j]/X[j]^(1/2))));
