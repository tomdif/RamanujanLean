\\ Numerics for RankinSharp: error of S(x)=sum tau(n)^2/n^11 and of B(x)=sum b_n,
\\ b = (indicator of squares) * a  (Dirichlet series zeta(2s) D(s)), residue c0 = c*zeta(2).
default(nbthreads,1); default(parisizemax, 2000000000); default(realprecision,30);
N = 1000000;
v = mfcoefs(mfDelta(), N);
c = 0.384084054468170370; c0 = c*zeta(2);
a = vector(N, n, v[n+1]^2/n^11*1.);
b = vector(N); for(m=1, sqrtint(N), my(q=m^2); for(j=1, N\q, b[q*j] += a[j]));
S=0.; B=0.; MS=vector(6); MB=vector(6);
for(n=1,N, S+=a[n]; B+=b[n]; j=min(6,floor(log(n)/log(10)+1e-9)+1); MS[j]=max(MS[j],abs(S-c*n)); MB[j]=max(MB[j],abs(B-c0*n)));
for(j=2,6, printf("decade %d: max|S-cx|=%.4g  max|B-c0x|=%.4g  slopeS=%.3f slopeB=%.3f\n", j, MS[j], MB[j], if(j>2,log(MS[j]/MS[j-1])/log(10),0), if(j>2,log(MB[j]/MB[j-1])/log(10),0)));
