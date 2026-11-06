\\ Numerical look at R(N) = sum_{n<=N} tau(n)^2/n^11 - c N,  c = (3/Pi)(4Pi)^12 ||Delta||^2 / 11!
\\ ||Delta||^2 (Petersson, dx dy / y^2 over F) = 1.035362056804320922...e-6.
\\ Evidence level (4) only: illustrates the size of R(N) against N^(3/8) and N^(3/5).
default(nbthreads, 1);
default(parisizemax, 2000000000);
default(realprecision, 38);
{
my(NMAX = 200000, P = 1.035362056804320922e-6, c, v, S = 0., mx = -1e9, mn = 1e9, ms = 0., cnt = 0, R, r);
c = 3/Pi * (4*Pi)^12 * P / 11!;
print("c = ", c);
v = mfcoefs(mfDelta(), NMAX);
for (n = 1, NMAX,
  S += v[n+1]^2 / n^11; R = S - c*n; r = R / n^(3/8);
  if (n > 1000, ms += R^2; cnt++; mx = max(mx, r); mn = min(mn, r));
  if (n == 10^3 || n == 10^4 || n == 10^5 || n == 2*10^5,
    printf("N=%d  R(N)=%.4f  R/N^(3/8)=%.4f  R/N^(3/5)=%.4f\n", n, R, r, R/n^(3/5))));
printf("over 1000<N<=%d: max R/N^(3/8) = %.4f, min = %.4f\n", NMAX, mx, mn);
printf("(1/X) sum_{1000<N<=X} R(N)^2 / X^(3/4) = %.4f   (conjecturally ~ const)\n", ms/cnt/NMAX^(3/4));
}
quit;
