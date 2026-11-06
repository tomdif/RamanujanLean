\\ Numerical checks for VoronoiTruncComplete (k = 24, S_24 has dim 2).
default(nbthreads,1); default(realprecision,38); default(parisizemax, 2*10^9);
L = 33000;
D = q*eta(q+O(q^L))^24;           \\ Delta
E4 = 1 + 240*sum(n=1,L-1,sigma(n,3)*q^n) + O(q^L);
g = D*E4^3;                        \\ Delta E4^3, a(1)=1 (real)
h = D^2;                           \\ Delta^2, a(1)=0, a(2)=1 (real, n0 = 2)
k = 24; m = 12; e = (k-1)/2 + 1/4;
cf(F) = vector(L-1, n, polcoef(F, n));
ag = cf(g); ah = cf(h);
\\ --- (1) Ingham kernel average at frequency n0 for h = Delta^2 -------------------
\\ (1/X) int_X^{2X} S(x) x^{-e} (1 + s cos(4 pi sqrt(n0 x) - pi/4)) dx  ->  s * a(n0) n0^{-(m+1/4)}/(2 pi sqrt 2)
kern(a, n0, X, s, st) = {
  my(S = sum(n=1, floor(X), a[n]), acc = 0., x, nx = floor(X)+1);
  forstep(x = X + st/2, 2*X, st,
    while(nx <= x, S += a[nx]; nx++);
    acc += S * x^(-e) * (1 + s*cos(4*Pi*sqrt(n0*x) - Pi/4)));
  acc*st/X };
pred = ah[2]*2^(-(m+1/4))/(2*Pi*sqrt(2));
print("h = Delta^2: a(1) = ", ah[1], ", a(2) = ", ah[2], "; predicted kernel mean +-", pred);
{
foreach([2000, 8000, 16000], X,
  printf("  X=%6d  s=+1: %.6e   s=-1: %.6e   ratio(+)/pred = %.4f\n", X,
    kern(ah, 2, X, 1, 0.02), kern(ah, 2, X, -1, 0.02), kern(ah, 2, X, 1, 0.02)/pred));
}
\\ frequency-1 kernel on h (a(1)=0) should give ~0
printf("  frequency-1 kernel on h (a(1)=0), X=8000: %.3e (should be ~0)\n", kern(ah,1,8000,1,0.02));
\\ extremes of S/x^e on [X,2X] at integers (S is a step function, sup is approached from the left)
ext(a, X) = { my(S = sum(n=1, X-1, a[n]), mx = -oo, mn = oo, v);
  for(n = X, 2*X, S += a[n]; v = S/n^e; mx = max(mx, v); mn = min(mn, v)); [mx, mn] };
printf("  max/min S_h/x^e on [8000,16000]: %s   (threshold |a(n0)| n0^{-(m+1/4)}/(2 pi sqrt2) = %.4e)\n", ext(ah,8000), pred);
\\ --- (2) complex Cramer for f = g + i h -------------------------------------------
af = vector(L-1, n, ag[n] + I*ah[n]);
Bf = sum(n=1, L-1, norm(af[n]) * n^(-(k+1/2)));
cr = Bf/((4*k+2)*Pi^2);
cram(a, X) = { my(S = 0, acc = 0.); for(n = 1, X-1, S += a[n]; acc += norm(S)); acc / X^(k+1/2) };
print("complex Cramer, f = Delta E4^3 + i Delta^2: predicted ", cr);
foreach([4000, 16000, 32000], X, printf("  X=%6d  X^{-k-1/2} int_1^X |S|^2 = %.6e   ratio = %.4f\n", X, cram(af,X), cram(af,X)/cr));
\\ --- (3) complex L2 Voronoi on [X,2X] ---------------------------------------------
V(a, N, x) = x^e/(Pi*sqrt(2)) * sum(n=1, N, a[n] * n^(-(k/2+1/4)) * cos(4*Pi*sqrt(n*x) - Pi/4));
l2(a, X, N, st) = { my(S = sum(n=1, floor(X), a[n]), nx = floor(X)+1, accD = 0., accS = 0.);
  forstep(x = X + st/2, 2*X, st, while(nx <= x, S += a[nx]; nx++);
    accD += norm(S - V(a, N, x)) * x^(-(k-1/2)); accS += norm(S) * x^(-(k-1/2)));
  [accD*st/X, accS*st/X] };
print("complex L2 Voronoi: mean |S-V_N|^2/x^{k-1/2} vs mean |S|^2/x^{k-1/2} (B_f/(4pi^2) = ", Bf/(4*Pi^2), ")");
foreach([[2000,20],[8000,120]], P, my(r = l2(af, P[1], P[2], 0.05)); printf("  X=%5d N=%4d : %.5e  vs  %.5e\n", P[1], P[2], r[1], r[2]));
