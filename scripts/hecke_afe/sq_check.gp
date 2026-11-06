\\ Check of HeckeAFE3.tauL_normSq_afe:
\\   |L(6+it)|^2 = 2 sum_{m,n} tau(m)tau(n) m^-(6+it) n^-(6-it) W_t(4 pi^2 m n),
\\   W_t(xi) = (1/2pi) int Gamma(s+z)Gamma(sbar+z)/(Gamma(s)Gamma(sbar)) xi^-z e^{z^2}/z dy,  z = 2+iy.
default(nbthreads,1); default(realprecision,25);
L2 = lfuncreate([n->vector(n,k,ramanujantau(k)), 0, [0,1], 12, 1, 1]);
H = 1/40.; K = 480;
Wprep(t, c=2) = my(s=6+I*t, sb=6-I*t); [Polrev(vector(2*K+1, j, my(z=c+I*(j-1-K)*H); exp(lngamma(s+z)+lngamma(sb+z)-lngamma(s)-lngamma(sb)+z^2)/z)), c];
Wev(P, xi) = my(w=exp(-I*H*log(xi))); H/(2*Pi)*xi^(-P[2])*w^(-K)*subst(P[1],'x,w);
{
foreach([1, 5, 10], t, my(P=Wprep(t), s=6+I*t, X=ceil((t+6)^2*exp(7)/(4*Pi^2)), S=0., tv=vector(X,k,ramanujantau(k)));
  for(m=1,X, for(n=1, X\m, S += tv[m]*tv[n]*m^(-s)*n^(-(12-s))*Wev(P, 4*Pi^2*m*n)));
  my(Lv=abs(lfun(L2,s))^2);
  printf("t=%3d  mn<=%6d  |L|^2=%.12g   2*S=%.12g   |diff|=%.2e\n", t, X, Lv, real(2*S), abs(Lv-2*S)));
}
