\\ Numerical check of the smoothed AFE for L(Delta,s)   (Lean: RamanujanTau/HeckeAFE)
\\   L(s) = sum tau(n) n^-s V_s(2 pi n/X) + eps(s) sum tau(n) n^(s-12) V_{12-s}(2 pi n X)
\\   V_s(xi) = (1/2pi) int_R Gamma(s+u)/Gamma(s) xi^-u e^(u^2)/u dy,  u = c+iy  (Lean: c = 2)
\\   eps(s) = (2pi)^(2s-12) Gamma(12-s)/Gamma(s)
\\ Quadrature: trapezoid rule in y, step h = 1/40 on [-12,12] (spectrally accurate: the integrand
\\ is analytic for |Im y| < |c| with Gaussian decay).  NB: PARI's intnum on [-12,12] is NOT
\\ reliable for this oscillatory integrand (it gives 0.5405 instead of 1/2 for e^{u^2}/u).
\\ Since xi^{-iy_k} = w^k with w = xi^{-ih}, V_s(xi) is a polynomial in w: precompute per s.
default(nbthreads,1);
default(realprecision,28);
L2 = lfuncreate([n->vector(n,k,ramanujantau(k)), 0, [0,1], 12, 1, 1]);
H = 1/40.; K = 480;
\\ data for V_s on the line Re u = c: [polynomial in w, c]
Vprep(s, c=2) = [Polrev(vector(2*K+1, j, my(u=c+I*(j-1-K)*H); exp(lngamma(s+u)-lngamma(s)+u^2)/u)), c];
Vev(P, xi) = my(w=exp(-I*H*log(xi))); H/(2*Pi)*xi^(-P[2])*w^(-K)*subst(P[1],'x,w);
epsf(s) = exp((2*s-12)*log(2*Pi) + lngamma(12-s) - lngamma(s));
afe(s, X, N) = {
  my(P1=Vprep(s), P2=Vprep(12-s), S1=0., S2=0.);
  for(n=1,N, my(tn=ramanujantau(n));
    S1 += tn*n^(-s)*Vev(P1, 2*Pi*n/X);
    S2 += tn*n^(s-12)*Vev(P2, 2*Pi*n*X));
  [S1, S2, S1 + epsf(s)*S2];
}
print("== (1) contour independence (WGam_shift) and residue (WGam_residue: V(c=2) - V(c=-1) = 1) ==");
{
foreach([[10,3.],[50,20.],[50,400.],[1000,5000.]], tx, my(s=6+I*tx[1], xi=tx[2], a=Vev(Vprep(s,2),xi));
  printf("t=%5d xi=%7g  V(c=2)=%.12g   |V(c=2)-V(c=5)|=%.2e   |V(c=2)-1-V(c=-1)|=%.2e\n", tx[1], xi,
    a, abs(a-Vev(Vprep(s,5),xi)), abs(a-1-Vev(Vprep(s,-1),xi))));
}
print("== (2) the AFE itself: |L(6+it) - AFE_N|, N = (|t|+6) e^8 max(X,1/X)/(2pi) ==");
{
foreach([[0.5,1],[1,1],[10,1],[10,2],[10,0.5],[30,1],[30,4],[60,1]], tx,
  my(t=tx[1], X=tx[2], s=6+I*t, N=ceil((abs(t)+6)*exp(8)*max(X,1/X)/(2*Pi)), r=afe(s,X,N), Lv=lfun(L2,s));
  printf("t=%5.1f X=%4.2f N=%6d  L=%.14g  |L-AFE|=%.2e  |eps|-1=%.1e\n", t, X, N, Lv, abs(Lv-r[3]), abs(epsf(s))-1));
}
print("== (3) uniform decay (V_bound): max over r=xi/(1+|t|) in 2^[-6..12] of |V|(1+r)^A ==");
{
foreach([10,100,1000,10000], t, my(P=Vprep(6+I*t), m2=0., m4=0., d=0.);
  for(k=-6,12, my(r=2.^k, v=abs(Vev(P, r*(1+abs(t))))); m2=max(m2, v*(1+r)^2); m4=max(m4, v*(1+r)^4));
  for(k=-12,-4, my(r=2.^k); d=max(d, abs(Vev(P, r*(1+abs(t)))-1)/r));
  printf("t=%6d  A=2: %.5g  A=4: %.5g   max |V-1|/r (r<=1/16): %.5g\n", t, m2, m4, d));
}
