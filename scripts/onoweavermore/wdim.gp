\\ Dimension of W = { f in M_{2 lam}(Gamma0(6)) : a(2n) = c2 a(n), a(3n) = c3 a(n) for all n }
\\ (c2 = (2/t) 2^(lam-1), c3 = (3/t) 3^(lam-1), t = 24 - j), optionally mod ell with a(ell n) = 0.
default(nbthreads,1); default(parisizemax, 4000000000);
wdim(j, lam, p, useU) = {
  my(k = 2*lam, mf = mfinit([6, k], 4), B = mfbasis(mf), t = 24 - j, n0 = 2*k + 10, L, c2, c3, rows = List(), M);
  c2 = kronecker(2, t) * 2^(lam-1); c3 = kronecker(3, t) * 3^(lam-1);
  my(nmax = if(useU, p*n0, 3*n0));
  L = [mfcoefs(f, nmax) | f <- B];   \\ L[i][n+1] = a_n
  for(n = 1, n0,
    listput(rows, vector(#B, i, L[i][2*n+1] - c2*L[i][n+1]));
    listput(rows, vector(#B, i, L[i][3*n+1] - c3*L[i][n+1]));
    if(useU, listput(rows, vector(#B, i, L[i][p*n+1]))));
  M = matrix(#rows, #B, r, c, rows[r][c]);
  if(p, M = M*Mod(1,p));
  return([#B, #B - matrank(M)]);
};
print("l=29 j=5 lam=13 (wt26) over Q: ", wdim(5, 13, 0, 0), " mod 29: ", wdim(5,13,29,0));
print("l=31 j=7 lam=14 (wt28) over Q: ", wdim(7, 14, 0, 0), " mod 31: ", wdim(7,14,31,0));
print("l=13 check: ", wdim(13,5,0,0));
