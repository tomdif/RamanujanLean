\\ Mean-square consequence of the AFE vs CriticalMeanSquareAsymp (constant cDelta = 2c ~ 0.768168).
\\ With X = 1 and |eps| = 1, the AFE diagonal is
\\   D(t) = sum_n lambda(n)^2/n (|V_t(2 pi n)|^2 + |V_{-t}(2 pi n)|^2) = 2 sum_n lambda(n)^2/n |V_t(2 pi n)|^2
\\ (|V_{-t}| = |V_t| by conjugation), and Rankin's sum_{n<=x} lambda(n)^2/n ~ c log x with an
\\ effective length x ~ t/(2pi) gives D(t) ~ 2c log(t/2pi) + O(1): the leading term of Good's
\\ asymptotic.  We compare (1/T) int_T^{2T} |L(6+it)|^2 dt with (1/T) int_T^{2T} D(t) dt.
default(nbthreads,1);
default(realprecision,20);
L2 = lfuncreate([n->vector(n,k,ramanujantau(k)), 0, [0,1], 12, 1, 1]);
H = 1/40.; K = 480;
Vprep(s, c=2) = [Polrev(vector(2*K+1, j, my(u=c+I*(j-1-K)*H); exp(lngamma(s+u)-lngamma(s)+u^2)/u)), c];
Vev(P, xi) = my(w=exp(-I*H*log(xi))); H/(2*Pi)*xi^(-P[2])*w^(-K)*subst(P[1],'x,w);
NMAX = 6000;
lam2 = vector(NMAX, n, ramanujantau(n)^2 / n^12.);   \\ lambda(n)^2 / n
Dg(t) = my(P=Vprep(6+I*t), N=min(NMAX, ceil((t+6)*exp(5)/(2*Pi)))); 2*sum(n=1,N, lam2[n]*abs(Vev(P,2*Pi*n))^2);
cD = 0.768168;
{
foreach([25,50,100,200], T,
  my(hL=0.05, ML, MD, hD=T/40.);
  ML = hL*sum(k=0, round(T/hL)-1, abs(lfun(L2, 6+I*(T+(k+0.5)*hL)))^2)/T;
  MD = hD*sum(k=0, 39, Dg(T+(k+0.5)*hD))/T;
  printf("T=%4d  (1/T)int|L|^2 = %.5f   (1/T)int D = %.5f   ratio = %.4f   2c*avg log(t/2pi) = %.5f\n",
    T, ML, MD, ML/MD, cD*(intnum(t=T,2*T,log(t/(2*Pi)))/T)));
}
