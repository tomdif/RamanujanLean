\\ Hardy Z for L(Delta,s) on the line Re s = 6 (normalization of HafnerProportion.ZH):
\\ Z(t) = e^{i theta(t)} L(Delta, 6+it), theta(t) = arg Gamma(6+it) - t log(2 pi); |Z| = |L|.
\\ Output: t Z(t) Im-residual, grid t = T0 .. T1 step dt.
default(nbthreads,1);
default(realprecision, 30);
T0 = 400; T1 = 803; dt = 0.01;
mf = mfinit([1,12],1); F = mfbasis(mf)[1];
L = lfunmf(mf, F);
Li = lfuninit(L, [6, T1 + 5]);
f = "zgrid.txt";
mx = 0;
{forstep(t = T0, T1, dt, my(s = 6 + I*t, z = lfun(Li, s) * exp(I*(imag(lngamma(s)) - t*log(2*Pi))));
  mx = max(mx, abs(imag(z)) / (1 + abs(z))); write(f, t, " ", real(z)));}
print("max relative imaginary part: ", mx);
quit;
