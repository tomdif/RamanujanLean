default(nbthreads,1); default(realprecision,30);
\\ |zeta(1/2+it)|^2  vs  sum_{m,n} (mn)^{-1/2} (n/m)^{it} erfc(log(mn/tau)/2),  tau=t/2pi
afe(t)={my(tau=t/(2*Pi),M=ceil(tau*exp(8)),s=0.);
 for(m=1,M, for(n=1,M\m, s+= (m*n)^(-1/2)*exp(I*t*log(n/m))*erfc(log(m*n/tau)/2))); real(s)};
{forstep(t=20,110,30, my(z=abs(zeta(1/2+I*t))^2, a=afe(t)); printf("t=%d |zeta|^2=%.8f afe=%.8f diff=%.3e  t^-1/4=%.3f\n",t,z,a,z-a,t^(-1/4)))}
