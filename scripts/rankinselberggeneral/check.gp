\\ Rankin-Selberg constants c_f = (3/pi)(4pi)^k ||f||^2/(k-1)! for the normalized generator of
\\ S_k(SL2(Z)), k = 12,16,18,20,22,26 (f = Delta*E_{k-12}), against S(x)/x, S(x) = sum a(n)^2/n^(k-1).
default(nbthreads,1); default(realprecision,30); default(parisizemax, 2000000000);
N = 100000;
{
foreach([12,16,18,20,22,26], k,
  mf = mfinit([1,k],1); f = mfbasis(mf)[1];
  a = mfcoefs(f, N);
  P = mfpetersson(mfsymbol(mf,f));
  c = 3/Pi*(4*Pi)^k*P/(k-1)!;
  S = 0.; out = [];
  for(n=1, N, S += a[n+1]^2/n^(k-1);
    if(n==10 || n==100 || n==1000 || n==10000 || n==100000, out = concat(out, [S/n])));
  printf("k=%d a(1..4)=%s ||f||^2=%.12e c=%.10f  S(x)/x at 10..1e5: %s\n", k, a[2..5], P, c,
    apply(t->Strprintf("%.6f",t), out));
);
}
