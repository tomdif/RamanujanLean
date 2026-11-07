\\ RankinOmegaPM numerics (evidence level (4) only).
\\ R(x) = sum_{n<=x} tau(n)^2/n^11 - c x,  c = (3/Pi)(4Pi)^12 ||Delta||^2/11!.
\\ On [n, n+1) R is S_n - c x (decreasing), so sup_{[n,n+1)} R = R(n), inf = S_n - c(n+1).
\\ Reports: signed extremes of R/x^(3/8) (Omega+- shape), sign changes,
\\ G(X) = int_1^X R(x)^2 x^(-7/4) dx (exact piecewise), G(X)/log X,
\\ and delta * int_1^X R^2 x^(-2 sigma - 1) dx, sigma = 3/8 + delta (truncated Mellin mean square).
default(nbthreads, 1);
default(parisizemax, 2000000000);
default(realprecision, 38);
{
my(NMAX = 500000, P = 1.035362056804320922e-6, c, v, S = 0., mxp = -1e9, mnm = 1e9, sc = 0, lastsgn = 0,
   G = 0., D = [1/10, 1/20, 1/40], F = vector(3), a, b, Rp, Rm, sg, pr);
c = 3/Pi * (4*Pi)^12 * P / 11!;
print("c = ", c);
v = mfcoefs(mfDelta(), NMAX);
for (n = 1, NMAX - 1,
  S += v[n+1]^2 / n^11;
  a = n; b = n + 1;
  \\ int_a^b (S - c x)^2 x^(-7/4) dx
  G += S^2 * (-4/3) * (b^(-3/4) - a^(-3/4)) - 2*S*c*4*(b^(1/4) - a^(1/4)) + c^2*(4/5)*(b^(5/4) - a^(5/4));
  for (j = 1, 3, my(p = 2*(3/8 + D[j]) + 1);
    F[j] += S^2 * (b^(1-p) - a^(1-p))/(1-p) - 2*S*c*(b^(2-p) - a^(2-p))/(2-p) + c^2*(b^(3-p) - a^(3-p))/(3-p));
  Rp = S - c*n; Rm = S - c*(n+1);
  if (n > 1000, mxp = max(mxp, Rp / n^(3/8)); mnm = min(mnm, Rm / (n+1)^(3/8)));
  sg = if (Rp > 0 && Rm < 0, 0, sign(Rp));
  if (Rp > 0 && Rm < 0, sc++,
    if (lastsgn != 0 && sign(Rp) != lastsgn && sign(Rp) != 0, sc++));
  lastsgn = sign(Rm);
  if (b == 10^3 || b == 10^4 || b == 10^5 || b == 2*10^5 || b == NMAX,
    printf("X=%d  G(X)=%.5f  G/logX=%.5f  max R/x^(3/8)=%.4f  min R/x^(3/8)=%.4f  signchanges=%d\n",
      b, G, G/log(b), mxp, mnm, sc);
    printf("      delta*int_1^X R^2 x^(-2s-1), s=3/8+delta: d=1/10: %.5f  d=1/20: %.5f  d=1/40: %.5f\n",
      D[1]*F[1], D[2]*F[2], D[3]*F[3])));
}
quit;
