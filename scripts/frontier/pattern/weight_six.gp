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
  mf = mfinit([6, 6]); A = mfheckemat(mf, 2); B = mfheckemat(mf, 3); Idm = matid(7);
  if(mfdim(mf) != 7, error("unexpected full-space dimension"));
  if((A-Idm)*(A-32*Idm)*(B+9*Idm)*(A^2+6*A+32*Idm) != matrix(7,7),
    error("full-space relation failed"));
  print("M6(level 6): dimension 7; Eisenstein-augmented annihilator checked.");
}
check_weight_six();
