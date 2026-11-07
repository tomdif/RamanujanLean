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
print("j=13 lam=5  (wt10) over Q: ", wdim(13, 5, 0, 0));
print("j=17 lam=7  (wt14) over Q: ", wdim(17, 7, 0, 0));
print("j=19 lam=8  (wt16) over Q: ", wdim(19, 8, 0, 0));
print("j=23 lam=10 (wt20) over Q: ", wdim(23, 10, 0, 0));
print("j=13 lam=5 mod 13: ", wdim(13, 5, 13, 0), "  j=17 lam=7 mod 17: ", wdim(17, 7, 17, 0));
print("j=1 lam=83 (wt166) over Q: ", wdim(1, 83, 0, 0));
print("j=1 lam=83 mod 13 with U13-kernel: ", wdim(1, 83, 13, 1));
print("j=1 lam=83 mod 13 no U13: ", wdim(1, 83, 13, 0));
