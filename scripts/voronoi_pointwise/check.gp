\\ Sanity check of the pointwise truncated Voronoi formula for S(x)=sum_{n<=x} tau(n).
\\ Normalized error R(x,N) = |S(x)-V_N(x)| / x^{11/2}; classical prediction (Deligne): R << x^{1/2} N^{-1/2}.
default(nbthreads,1);
default(realprecision,38);
L = 320000;
E = Vec(eta('q + O('q^L))^24); T = vector(L, n, E[n]);  \\ tau(n) = [q^{n-1}] prod(1-q^m)^24
if(T[1]!=1 || T[2]!=-24 || T[12]!=-370944, error("tau table"));
P = vector(L); s = 0; for(n=1,L, s += T[n]; P[n] = s);
S(x) = P[floor(x)];
V(x,N) = x^(23/4)/(Pi*sqrt(2)) * sum(n=1,N, T[n]*n^(-25/4)*cos(4*Pi*sqrt(n*x)-Pi/4));
{
print("x        N     R=|S-V_N|/x^5.5   R/(x^.5 N^-.5)   |V_N|/x^5.5   |S|/x^5.5");
foreach([20000.3, 80000.7, 250000.1], x,
  foreach([1, floor(x^(1/4)), floor(x^(1/3)), floor(x^(1/2))], N,
    my(R = abs(S(x)-V(x,N))/x^(11/2));
    printf("%-9.1f %-5d %-17.5f %-16.5f %-13.5f %.5f\n", x, N, R, R/(x^(1/2)*N^(-1/2)),
      abs(V(x,N))/x^(11/2), abs(S(x))/x^(11/2))));
}
\\ Average over many x of R/(x^.5 N^-.5) at N = x^{1/3}: stays bounded as x grows
{
foreach([10000, 40000, 150000], X,
  my(mx = 0, av = 0, K = 200);
  for(j=1,K, my(x = X + j*X/K + 0.37, N = floor(x^(1/3)), r);
    r = abs(S(x)-V(x,N))/x^(11/2) / (x^(1/2)*N^(-1/2)); av += r; mx = max(mx, r));
  printf("X=%-7d N~x^(1/3): mean ratio %.4f  max ratio %.4f\n", X, av/K, mx));
}
\\ Exponent arithmetic
print("59/10 = 11/2+2/5: ", 11/2+2/5 == 59/10, "   35/6 = 11/2+1/3: ", 11/2+1/3 == 35/6);
print("uncond formula at N=x^(3/5): 121/20 - 3/20 = ", 121/20-3/20);
print("Rankin error theta -> exponent 1/4+theta/4: theta=3/5 ->", 1/4+3/20, "; theta=3/8 ->", 1/4+3/32, " > 1/3");
