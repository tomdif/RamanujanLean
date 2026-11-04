\\ Numerical check (evidence level 4) for the Rankin-Selberg mean square of tau.
\\ Run: nice gp -q scripts/rankinselberg/mean_square.gp
default(nbthreads,1); default(realprecision,38); default(parisizemax, 2*10^9);
N = 100000;
v = mfcoefs(mfDelta(), N);                 \\ v[n+1] = tau(n)
print("coefficients done");
pet = mfpetersson(mfsymbol(mfDelta()));    \\ int_{SL2Z\H} |Delta|^2 y^12 dmu
R = 3/Pi * (4*Pi)^12 / 11! * pet;          \\ predicted constant c
print("||Delta||^2 = ", pet);
print("predicted c = (3/pi)(4pi)^12/11! ||Delta||^2 = ", R);
\\ S(x) = sum_{n<=x} tau(n)^2/n^11 (floating point) and A(x) = sum_{n<=x} tau(n)^2 (exact)
S = 0.; A = 0; ck = [10,100,1000,10000,30000,100000]; j = 1;
mn = 1e9; mx = 0.; mnA = 1e9; mxA = 0.;
{for (n = 1, N,
  t = 1. * v[n+1]; S += t^2 / n^11; A += v[n+1]^2;
  mn = min(mn, S/n); mx = max(mx, S/n);
  r = A * 1. / (1.*n)^12; mnA = min(mnA, r); mxA = max(mxA, r);
  if (j <= #ck && n == ck[j],
    printf("x=%7d  S(x)/x=%.8f  (S(x)-c x)/x^(3/5)=%+.5f  A(x)/x^12=%.6f\n", n, S/n, (S-R*n)/(1.*n)^(3/5), r);
    j++));}
printf("min,max of S(x)/x over 1<=x<=%d: %.6f %.6f\n", N, mn, mx);
printf("min,max of A(x)/x^12 over 1<=x<=%d: %.6g %.6g ; c/12 = %.6f\n", N, mnA, mxA, R/12);
\\ Parseval check: sum tau^2 e^{-4 pi n y} vs int_0^1 |Delta(x+iy)|^2 dx (q-series, y = 0.2)
y = 0.2; P = sum(n = 1, 400, v[n+1]^2 * exp(-4*Pi*n*y));
D(z) = sum(n = 1, 400, v[n+1] * exp(2*Pi*I*n*z));
Iq = intnum(x = 0, 1, abs(D(x + I*y))^2);
printf("Parseval y=%.2f: sum=%.15g  integral=%.15g\n", y, P, Iq);
