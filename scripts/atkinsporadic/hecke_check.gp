\\ Char-0 test: T(Q^2) on S_k/eta (weight k-1/2, lambda=k-1) preserves the space, and sign convention.
default(nbthreads,1);
\\ c: vector, c[N+1] = coeff of q^N of G*P  (index m = 24N-1)
heckeQ2(c, Q, lam, s, N0) = {
  my(v = vector(N0+1), N, m, a1, a3);
  for(N=0, N0,
    m = 24*N-1;
    a1 = if(Q^2*N-(Q^2-1)/24 >= 0, c[Q^2*N-(Q^2-1)/24+1], 0);
    a3 = if((N+(Q^2-1)/24) % Q^2 == 0, c[(N+(Q^2-1)/24)/Q^2+1], 0);
    v[N+1] = a1 + s*kronecker(m, Q)*Q^(lam-1)*c[N+1] + Q^(2*lam-1)*a3);
  v
};
test(k, Q, N0) = {
  my(prec = Q^2*N0+5, q = 'q, E4, E6, D, P, eta, B, d, lam = k-1, res = []);
  E4 = 1 + 240*sum(n=1,prec, sigma(n,3)*q^n) + O(q^(prec+1));
  E6 = 1 - 504*sum(n=1,prec, sigma(n,5)*q^n) + O(q^(prec+1));
  eta = prod(n=1,prec,1-q^n + O(q^(prec+1)));
  D = q*eta^24; P = 1/eta;
  B = [];
  forvec(ab=[[0,k\4],[0,k\6]], if(4*ab[1]+6*ab[2]==k-12, B = concat(B, [D*E4^ab[1]*E6^ab[2]])));
  d = #B;
  foreach([1,-1], s,
    my(ok = 1);
    for(i=1, d,
      my(c = Vec(B[i]*P + O(q^(prec+1)),-(prec+1)), t, ser, M, sol);
      \\ Vec with shift: ensure c[1] = coeff q^0
      c = vector(prec+1, j, polcoeff(B[i]*P, j-1));
      t = heckeQ2(c, Q, lam, s, N0);
      ser = Ser(t, q) * eta + O(q^(N0+1));
      M = matrix(N0+1, d, r, j, polcoeff(B[j], r-1));
      sol = matsolve(M[2..d+1,], vector(d, r, polcoeff(ser, r))~);
      if(M*sol != vector(N0+1, r, polcoeff(ser, r-1))~, ok = 0));
    res = concat(res, [[s, ok]]));
  print("k=",k," Q=",Q," dim=",d," [sign,ok]: ", res);
};
test(12, 5, 30);
test(12, 7, 30);
test(12, 11, 20);
test(84, 11, 16);
