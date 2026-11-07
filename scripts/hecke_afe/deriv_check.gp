\\ Check of HeckeAFE2.V_deriv_bound: (1+|t|) |d/dt V(6+it, xi)| (1+xi/(1+|t|))^A bounded in t.
default(nbthreads,1); default(realprecision,30);
H = 1/40.; K = 480;
Vprep(s, c=2) = [Polrev(vector(2*K+1, j, my(u=c+I*(j-1-K)*H); exp(lngamma(s+u)-lngamma(s)+u^2)/u)), c];
Vev(P, xi) = my(w=exp(-I*H*log(xi))); H/(2*Pi)*xi^(-P[2])*w^(-K)*subst(P[1],'x,w);
dV(t, xi) = my(e=1e-8); (Vev(Vprep(6+I*(t+e)),xi) - Vev(Vprep(6+I*(t-e)),xi))/(2*e);
{
foreach([10,100,1000,10000], t, my(m0=0., m2=0.);
  for(k=-6,10, my(r=2.^k, xi=r*(1+t), d=abs(dV(t,xi))*(1+t)); m0=max(m0,d); m2=max(m2, d*(1+r)^2));
  printf("t=%6d  max_r (1+t)|dV/dt| = %.5g   max_r (1+t)|dV/dt|(1+r)^2 = %.5g\n", t, m0, m2));
}
