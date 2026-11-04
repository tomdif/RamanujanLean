\\ Char-0 evidence for EtaHecke Q k j, computed modulo a large prime p:
\\ T(Q^2) maps G*P^j (G in S_k level 1) into S_k*P^j, with the sign of HalfHecke.lean.
default(nbthreads,1); default(parisizemax, 2000000000);
pp = nextprime(2^61);
testj(k, j, Q, N0) = {
  my(prec = Q^2*N0 + 5, q='q, E4, E6, eta, D, Pj, B = [], d, lam = k - (j+1)/2, s, dsh = (Q^2-1)*j/24, ok = 1);
  s = kronecker(12, Q) * kronecker((-1)^lam, Q);
  E4 = Mod(1,pp) + 240*sum(n=1,prec, Mod(sigma(n,3),pp)*q^n) + O(q^(prec+1));
  E6 = Mod(1,pp) - 504*sum(n=1,prec, Mod(sigma(n,5),pp)*q^n) + O(q^(prec+1));
  eta = prod(n=1,prec, Mod(1,pp) - q^n + O(q^(prec+1)));
  D = q*eta^24; Pj = 1/eta^j;
  forvec(ab=[[0,k\4],[0,k\6]], if(4*ab[1]+6*ab[2]==k-12, B = concat(B, [D*E4^ab[1]*E6^ab[2]])));
  d = #B;
  for(i=1, d,
    my(F = B[i]*Pj, c = vector(prec+1, t, polcoeff(F, t-1)), t = vector(N0+1), ser, M, sol);
    for(N=0, N0,
      my(a1 = if(Q^2*N >= dsh, c[Q^2*N - dsh + 1], 0), a3 = if((N+dsh) % Q^2 == 0, c[(N+dsh)/Q^2+1], 0));
      t[N+1] = a1 + s*kronecker(24*N-j, Q)*Mod(Q,pp)^(lam-1)*c[N+1] + Mod(Q,pp)^(2*lam-1)*a3);
    ser = (Ser(t, q) + O(q^(N0+1))) * eta^j;
    M = matrix(N0+1, d, r, jj, polcoeff(B[jj], r-1));
    sol = matsolve(M[2..d+1,], vector(d, r, polcoeff(ser, r))~);
    if(M*sol != vector(N0+1, r, polcoeff(ser, r-1))~, ok = 0));
  print("EtaHecke Q=",Q," k=",k," j=",j,": dim ",d,", ",N0+1," coefficients, consistent=",ok);
};
testj(168, 1, 11, 30);
testj(168, 1, 37, 20);
testj(12, 13, 59, 8);
testj(16, 17, 41, 8);
testj(18, 19, 101, 4);
testj(22, 23, 5, 40);
