default(nbthreads,1); default(parisizemax,10^9); default(realprecision,19);
\\ The first-derivative test bounds |Off(T)| by M(T) = sum_{m!=n} |a(m)a(n)| (mn)^(-1/2) * 2V(log(mn/tau^2)) / |log(n/m)|,
\\ a(n)=tau(n)/n^(11/2), V(L)=erfc(L/2), tau=T/2pi.  For degree 2 this majorant is of size T log T (no saving).
Nmax=60000; tv=mfcoefs(mfDelta(),Nmax);
av=vector(Nmax,n,abs(tv[n+1])/n^(11/2));
M(T)=
{
  my(t2=(T/(2*Pi))^2, X=min(Nmax,floor(t2*exp(5))), s=0.);
  for(m=1,X,
    for(n=1,min(Nmax,X\m),
      if(n!=m, s+=av[m]*av[n]/sqrt(m*n)*2*erfc(log(m*n/t2)/2)/abs(log(n/m)))));
  s;
}
{
  foreach([25,50,100,200],T,
    my(v=M(T)); printf("T=%d  M(T)=%.1f  M(T)/(T log T)=%.3f\n",T,v,v/(T*log(T))));
}
