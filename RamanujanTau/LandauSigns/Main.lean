/-
# `LandauSigns`: Landau's theorem for nonnegative Dirichlet series, and sign changes of
real level-one cusp-form coefficients

* `landau`, `landau_real`, `landau_abscissa` (`Landau.lean`): if `a ≥ 0` and `LSeries a` agrees
  on `Re s > x` (with `abscissaOfAbsConv a ≤ x`) with an entire function, then `LSeries a`
  converges absolutely everywhere.
* `coeff_sign_changes` (`Signs.lean`): every nonzero `f ∈ S_k(SL₂(ℤ))` with real q-coefficients
  has infinitely many positive and infinitely many negative coefficients.
* `tau_sign_changes`: the `τ` specialization (via `coef_discriminant`).

Build: `nice -n 10 lake build RamanujanTau.LandauSigns.Main`.
-/
import RamanujanTau.LandauSigns.Signs

#print axioms RamanujanTau.LandauSigns.landau_real_of_real
#print axioms RamanujanTau.LandauSigns.landau_real
#print axioms RamanujanTau.LandauSigns.landau
#print axioms RamanujanTau.LandauSigns.landau_abscissa
#print axioms RamanujanTau.LandauSigns.twelve_le_weight
#print axioms RamanujanTau.LandauSigns.not_eventually_nonneg
#print axioms RamanujanTau.LandauSigns.coeff_pos_infinitely_often
#print axioms RamanujanTau.LandauSigns.coeff_neg_infinitely_often
#print axioms RamanujanTau.LandauSigns.coeff_sign_changes
#print axioms RamanujanTau.LandauSigns.tau_sign_changes
