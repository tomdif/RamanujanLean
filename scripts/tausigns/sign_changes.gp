\\ Numerical checks for docs/TAU_SIGN_CHANGES.md.  PARI/GP, nbthreads = 1.
default(nbthreads,1);
N = 200000;
v = Vec(mfcoefs(mfDelta(), N)); \\ v[n+1] = tau(n)
t(n) = v[n+1];
\\ sign changes (n, next nonzero m with opposite sign)
cnt = 0; last = 0; lastch = 0; lastsign = 0; maxgap = 0; maxgapat = 0; chk = [1000,10000,100000,200000]; ci = 1;
{
for (n = 1, N,
  s = sign(t(n));
  if (s != 0,
    if (lastsign != 0 && s != lastsign, cnt++; g = n - lastch; lastch = n; if (g > maxgap, maxgap = g; maxgapat = n));
    last = n; lastsign = s);
  if (ci <= #chk && n == chk[ci],
    printf("x=%d  sign changes=%d  ratio/x=%.4f  max gap between sign changes=%d (at %d)  x^(83/84)=%.0f  x^(1/84)=%.3f\n",
      n, cnt, cnt/n, maxgap, maxgapat, n^(83/84), n^(1/84)); ci++));
}
\\ Hecke partial sums |S(M)|/M^6
S = 0; mx = 0.;
{
for (M = 1, N, S += t(M);
  r = abs(S) / M^6; if (r > mx, mx = r);
  if (M == 1000 || M == 10000 || M == 100000 || M == 200000,
    printf("M=%d  |S(M)|/M^6=%.4f  max so far=%.4f  |S|/M^(11/2+1/3)=%.4f\n", M, abs(S)/M^6, mx, abs(S)/M^(35/6))));
}
\p 250
\\ Delta(iy) = sum tau(n) e^{-2 pi n y} stays bounded (indeed -> 0) as y -> 0
{
foreach([1., 0.5, 0.2, 0.1, 0.05], y,
  q = exp(-2*Pi*y); s = 0.; qn = 1.; Nmax = min(N, ceil(400/(2*Pi*y)));
  for (n = 1, Nmax, qn *= q; s += t(n) * qn);
  printf("y=%.2f  Delta(iy)=%.6e   y^-12 Delta(i/y) = %.6e\n", y, s,
    y^-12 * suminf(n = 1, if (n > 50, 0, t(n) * exp(-2*Pi*n/y)))));
}
\\ fraction of n<=N with tau(n)>0, and shortest window length L(x) such that both signs occur in (x,x+L]
pos = sum(n = 1, N, t(n) > 0); printf("fraction tau>0 up to %d: %.4f\n", N, pos/N);
