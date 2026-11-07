\\ Level-4 check of HorocycleLimit(L), L = (3/Pi)*||Delta||^2 (EisensteinReal/Asymptotic.lean).
\\ I(y) = int_0^1 G(x+iy) dx = y^12 * sum_n tau(n)^2 exp(-4 Pi n y)   (Parseval).
\\ Run: nice gp -q scripts/eisensteinreal/horocycle_check.gp
default(nbthreads,1); default(realprecision,38); default(parisizemax, 2*10^9);
N = 100000; v = mfcoefs(mfDelta(), N);
pet = mfpetersson(mfsymbol(mfDelta()));
L = 3/Pi*pet; c = (4*Pi)^12*L/11!;
printf("||Delta||^2 = %.20g\nL = %.20g\nc = %.18g\n", pet, L, c);
Iy(y) = my(s = 0., q = exp(-4*Pi*y), w = 1.); for (n = 1, N, w *= q; s += (1.*v[n+1])^2*w; if (w < 1e-80, break)); y^12*s;
{foreach([0.5,0.2,0.1,0.05,0.02,0.01,0.005,0.002,0.001,0.0005,0.0002], y,
  my(t = Iy(y)); printf("y=%-7g I(y)/L=%.10f  (I(y)/L-1)/y^(1/2)=%+.4f\n", y, t/L, (t/L-1)/sqrt(y)));}
\\ Direct check of the definition petNormSq = int over |x|<=1/2, x^2+y^2>=1 of |Delta|^2 y^12 dx dy / y^2
default(realprecision, 19);
Dl(z) = sum(n = 1, 60, v[n+1] * exp(2*Pi*I*n*z));
Fd = 2*intnum(x = 0, 1/2, intnum(y = sqrt(1-x^2), 12, abs(Dl(x+I*y))^2 * y^10));
printf("direct integral over F = %.15g   (mfpetersson %.15g)\n", Fd, pet);
