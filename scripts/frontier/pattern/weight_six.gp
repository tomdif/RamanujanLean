\\ Independent classical modular-form check for the proposed Theorem A.
\\ PARI computes the actual rational Hecke matrices. This is not a Lean proof
\\ that the formal integer matrices represent Hecke operators.
check_weight_six() = {
  my(mf = mfinit([6, 6], 1), A = mfheckemat(mf, 2), B = mfheckemat(mf, 3));
  my(Idm = matid(3));
  if(mfdim(mf) != 3, error("unexpected cusp dimension"));
  if(A != [-6, 1, 0; -32, 0, 0; 0, 0, 4], error("unexpected U2 matrix"));
  if(B != [9, 0, 0; 0, 9, 0; 0, 0, -9], error("unexpected U3 matrix"));
  if((B + 9*Idm)*(A^2 + 6*A + 32*Idm) != matrix(3,3), error("cusp relation failed"));
  print("S6(level 6): dimension 3; exact matrices and annihilator checked.");
  \\ A concrete eta-product basis for the remaining analytic identification.
  \\ Columns of C express g(z), g(2z), H(z) in PARI's old/new basis.
  my(g = mffrometaquo([1,6;3,6]), v = mffrometaquo([2,6;6,6]));
  my(H = mffrometaquo([1,5;2,5;3,1;6,1]));
  my(C = matconcat([mftobasis(mf,g),mftobasis(mf,v),mftobasis(mf,H)]));
  if(C != [1,0,1/2;0,1,-4;0,0,1/2], error("unexpected eta basis"));
  if(C^-1*A*C != [-6,1,-9;-32,0,0;0,0,4], error("eta-basis U2 failed"));
  if(C^-1*B*C != [9,0,9;0,9,-72;0,0,-9], error("eta-basis U3 failed"));
  my(first = matrix(3,3,i,j,mfcoefs([g,v,H][j],3)[i+1]));
  if(first != [1,0,1;-6,1,-5;9,0,0] || matdet(first) != -9,
    error("eta-basis initial coefficients failed"));
  print("Eta basis g, g(2z), H: exact basis and operator matrices checked; first-three determinant -9.");
  my(h = mflinear([g,v,H],[-1,8,2]));
  if(mfcoefs(g,9) != [0,1,-6,9,4,6,-54,-40,168,81] ||
     mfcoefs(v,9) != [0,0,1,0,-6,0,9,0,4,0] ||
     mfcoefs(h,9) != [0,1,4,-9,16,-66,-36,176,64,81],
    error("finite weight-six coefficient certificate failed"));
  print("Old/new basis: all 27 positive coefficients through q^9 match the Lean certificate input.");
  mf = mfinit([6, 6]); A = mfheckemat(mf, 2); B = mfheckemat(mf, 3); Idm = matid(7);
  if(mfdim(mf) != 7, error("unexpected full-space dimension"));
  if((A-Idm)*(A-32*Idm)*(B+9*Idm)*(A^2+6*A+32*Idm) != matrix(7,7),
    error("full-space relation failed"));
  print("M6(level 6): dimension 7; Eisenstein-augmented annihilator checked.");
}
check_weight_six();
