\\ Numerical validation for TauDensity (PARI/GP). Run: gp -q RamanujanTau/TauDensity/validate.gp
default(nbthreads,1); default(parisize, 200000000);
N = 200000;
t = vector(N, n, ramanujantau(n));
nz = 0; for(n=1,N, if(t[n]!=0, nz++));
print("nonzero count n<=", N, ": ", nz, " (expect ", N, ")");
\\ mod 691 congruence at primes, and tau(p)=0 => p = -1 mod 691 contrapositive
bad = 0; forprime(p=2, N, if((t[p] - 1 - p^11) % 691 != 0, bad++)); print("tau(p) != 1+p^11 mod 691 failures: ", bad);
\\ x -> x^11 injective on F_691^x (gcd(11,690)=1), so 1+x^11=0 iff x=-1
sol = 0; for(x=0,690, if(Mod(1+x^11,691)==0, sol++; print("  root x=", x))); print("roots of 1+x^11 mod 691: ", sol);
\\ tau(p^2) = tau(p)^2 - p^11 and tau(p^{2j}) = (-p^11)^j when tau(p)=0 (algebraic check of recurrence)
ok = 1; forprime(p=2, 400, if(t[p^2] != t[p]^2 - p^11, ok = 0)); print("Hecke p^2 recurrence ok: ", ok);
\\ squares: tau(m^2) != 0
sq = 1; for(m=1, sqrtint(N), if(t[m^2]==0, sq=0)); print("tau(m^2)!=0 for m<=sqrt(N): ", sq);
\\ Rankin-Selberg: (1/n) sum tau^2/n^11, min over n (empirical c1) and value at N
S = 0.; mn = 10.^9; for(n=1,N, S += t[n]^2/n^11; if(S/n < mn, mn = S/n));
print("RS ratio at N: ", S/N, "  (Zagier constant 0.38408...)   min_{n<=N} ratio: ", mn);
\\ Weil-type constant: max |tau(n)| / n^{23/4+eps}, eps = 1/20, and Deligne ratio
e = 1/20; W = 0.; D = 0.; for(n=1,N, W = max(W, abs(t[n])/n^(23/4+e)); D = max(D, abs(t[n])/(numdiv(n)*n^(11/2))));
print("max |tau(n)|/n^(23/4+1/20): ", W, "   max |tau(n)|/(d(n) n^(11/2)) (Deligne <= 1): ", D);
\\ implied constant of analytic headline with eps=1/10 (pointwise eps/2 = 1/20): c = c1 / C^2
print("empirical c = c1/C^2 (eps=1/10): ", mn / W^2);
\\ zero-count bound N(1+log N)/M vs actual 0
print("bound N(1+log N)/M at N: ", N*(1+log(N))/10746432000.);
\\ smallest Lehmer candidate p = -1 mod M, p = 3,5,6 mod 7: check primality of 21492863999
print("21492863999 prime: ", isprime(21492863999), " mod 7: ", 21492863999 % 7, "  tau(21492863999) != 0: ", ramanujantau(21492863999) != 0);
\\ count n<=N excluded neither by squares-bound: compare sqrt(N), N^{1/2-eps}
print("sqrtN = ", sqrtint(N), "; N^{0.4} = ", N^0.4);
quit;
