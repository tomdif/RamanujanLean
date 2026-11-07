\\ For ell in {13,17,19,23}: F = f/eta^ell, f the normalized cusp form of weight ell-1 (dim 1).
\\ F = q^{(24-ell)/24} * sum c(N) q^N ; index m = 24N + 24 - ell.
\\ T(Q^2) eigenvalue mod ell, from the first coefficient; flag mu = 0 (Ono/Weaver Q^3 type)
\\ and mu = +-s Q^(lam-1) (Atkin type). lam = (ell-3)/2, s = kron(12,Q)*kron((-1)^lam, Q).
default(nbthreads,1);
scan(ell, QMAX) = {
  my(r = 24-ell, lam = (ell-3)/2, res = List(), Nmax, E, c, f);
  forprime(Q = 5, QMAX, if(Q == ell, next);
    \\ need a(Q^2 * r): N = (Q^2 r - r)/24
    Nmax = (Q^2*r - r)/24 + 2;
    E = Mod(1,ell)*prod(n=1, Nmax, 1 - 'q^n + O('q^(Nmax+1)));
    f = if(ell==13, 1, if(ell==17, 1+240*sum(n=1,Nmax,sigma(n,3)*'q^n), if(ell==19, 1-504*sum(n=1,Nmax,sigma(n,5)*'q^n), (1+240*sum(n=1,Nmax,sigma(n,3)*'q^n))*(1-504*sum(n=1,Nmax,sigma(n,5)*'q^n))))) + O('q^(Nmax+1));
    c = E^r * f;  \\ F/q^{r/24} = eta^r-part * E_k
    my(s = kronecker(12,Q)*kronecker((-1)^lam, Q), a1 = polcoeff(c, (Q^2*r - r)/24), a0 = polcoeff(c,0));
    my(mu = lift(a1 + s*kronecker(r,Q)*Mod(Q,ell)^(lam-1)*a0));
    my(tag = if(mu==0, "ONO-WEAVER mod ell*Q^4", if(mu == lift(s*Mod(Q,ell)^(lam-1)), "ATKIN (n/Q)=+1 class", if(mu == lift(-s*Mod(Q,ell)^(lam-1)), "ATKIN (n/Q)=-1 class", ""))));
    if(tag != "", listput(res, [Q, mu, tag])));
  print("ell=", ell, ": ", res);
};
scan(13, 120); scan(17, 120); scan(19, 120); scan(23, 120);
