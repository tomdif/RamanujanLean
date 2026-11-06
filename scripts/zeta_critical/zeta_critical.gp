\\ Numeric sanity check (evidence level 4) for RamanujanTau/ZetaCritical.
\\ I(T) = int_0^T |zeta(1/2+it)|^2 dt, compared with
\\   T log T                          (Hardy-Littlewood, the proved leading term)
\\   T log(T/2pi) + (2 gamma - 1) T   (Ingham's two-term formula, NOT formalized)
\\ and the Lean error envelope T sqrt(log T).
\\ Also checks the off-diagonal bound of Bound.lean:
\\   sum_{m != n <= N} (mn)^{-1/2} * 2/(log n - log m)^2 <= 20 N^2.
\\ Also checks the averaged identity avg_mv numerically for a small N.
default(nbthreads, 1);
default(realprecision, 30);
f(t) = norm(zeta(1/2 + I*t));
I0(T) = sum(k = 0, ceil(T) - 1, intnum(t = k, min(k + 1, T), f(t)));
{
  my(acc = 0., prev = 0);
  print("T, I(T), I/(T log T), I - T log T, (I - TlogT)/(T sqrt(log T)), I - Ingham");
  forstep(T = 50, 1000, 50,
    acc += sum(k = prev, T - 1, intnum(t = k, k + 1, f(t)));
    prev = T;
    my(L = log(T), ing = T*log(T/(2*Pi)) + (2*Euler - 1)*T);
    printf("%5d  %12.3f  %.5f  %10.3f  %.4f  %8.3f\n", T, acc, acc/(T*L), acc - T*L,
           (acc - T*L)/(T*sqrt(L)), acc - ing));
}
\\ off-diagonal weight versus 20 N^2
{
  print("N, offdiag, offdiag/N^2");
  foreach([10, 50, 100, 300], N,
    my(s = 0.);
    for(m = 1, N, for(n = 1, N, if(n != m,
      s += (m*n)^(-1/2) * 2/(log(n) - log(m))^2)));
    printf("%4d  %14.3f  %.4f\n", N, s, s/N^2));
}
\\ averaged mean value: int_a^b G(u) du with G(u) = int_0^u |P_N|^2, versus the formula
PN(N, t) = norm(sum(n = 1, N, n^(-1/2 - I*t)));
GN(N, u) = intnum(t = 0, u, PN(N, t));
{
  my(N = 5, a = 3., b = 7., lhs, rhs);
  lhs = intnum(u = a, b, GN(N, u));
  rhs = (b^2 - a^2)/2 * sum(n = 1, N, 1/n) +
        sum(m = 1, N, sum(n = 1, N, if(n == m, 0,
          (m*n)^(-1/2) * (cos((log(n) - log(m))*a) - cos((log(n) - log(m))*b))/(log(n) - log(m))^2)));
  printf("avg_mv identity N=5 [3,7]: lhs=%.15f rhs=%.15f diff=%.2e\n", lhs, rhs, lhs - rhs);
}
quit;
