\\ Check (a): sum_{r<=x} lam(h1 r) lam(k1 r)/r = r0 rho(h1)rho(k1) log x + K1 + o(1),
\\ K1 = r0 (rho1(h1)rho(k1) + rho(h1)rho1(k1)) + gammaD rho(h1)rho(k1).
default(nbthreads,1); default(parisizemax, 2*10^9); default(realprecision, 30);
r0 = 0.38408405446817036992636710674931703817;
gD = 0.79602825584793044651331756509910255024;
M = 1200000;
tv = mfcoefs(mfDelta(), M);   \\ tv[n+1] = tau(n)
lam(n) = tv[n+1] * n^(-11/2.);
J = 80;
\\ local series at s = 1 (and derivative in s), using lam(p^j) from the Hecke recursion
lp(p, j) = { my(a = tv[p+1]*p^(-11/2.), u0 = 1., u1 = a, t); if(j==0, return(1.)); for(i=2, j, t = a*u1 - u0; u0 = u1; u1 = t); u1 };
Dp(p) = sum(j=0,J, lp(p,j)^2 * p^(-j));
Dpd(p) = -sum(j=0,J, j*log(p)*lp(p,j)^2 * p^(-j));
Np(p,a) = sum(j=0,J, lp(p,j+a)*lp(p,j) * p^(-j));
Npd(p,a) = -sum(j=0,J, j*log(p)*lp(p,j+a)*lp(p,j) * p^(-j));
rhoP(p,a) = Np(p,a)/Dp(p);
rhoPd(p,a) = (Npd(p,a)*Dp(p) - Np(p,a)*Dpd(p))/Dp(p)^2;
rho(m) = { my(f = factor(m)); prod(i=1, #f~, rhoP(f[i,1], f[i,2])) };
rho1(m) = { my(f = factor(m), s = 0.); for(i=1, #f~, s += rhoPd(f[i,1], f[i,2]) * prod(l=1, #f~, if(l==i, 1, rhoP(f[l,1], f[l,2])))); s };
check(h1, k1) = {
  my(X = M \ max(h1,k1), S = 0., pred0, K1, out = []);
  pred0 = r0*rho(h1)*rho(k1);
  K1 = r0*(rho1(h1)*rho(k1) + rho(h1)*rho1(k1)) + gD*rho(h1)*rho(k1);
  for(r = 1, X, S += lam(h1*r)*lam(k1*r)/r;
    if(r == X\8 || r == X\4 || r == X\2 || r == X, out = concat(out, [[r, S - pred0*log(r)]])));
  printf("(h1,k1)=(%d,%d): r0*rho*rho=%.8f  K1(pred)=%.8f\n", h1, k1, pred0, K1);
  for(i=1,#out, printf("   x=%8d  S(x)-r0 rho rho log x = %.8f   diff=%.2e\n", out[i][1], out[i][2], out[i][2]-K1));
  \\ also check lam(h1 r)lam(k1 r) = lam(h1 k1 r)lam(r) (coprime)
  printf("   max |lam(h1 r)lam(k1 r) - lam(h1k1 r)lam(r)| (r<=500) = %.2e\n", vecmax(vector(min(500, M\(h1*k1)), r, abs(lam(h1*r)*lam(k1*r) - lam(h1*k1*r)*lam(r)))));
};
check(1,1); check(1,2); check(2,3); check(1,4); check(3,4); check(1,6); check(5,1);
