/-
# `QFProof3/` — `QDecomp` and `QDecomp1` discharged (unconditional); see `docs/QF_PROOF.md`

Build: `nice -n 10 lake build RamanujanTau.QFProof3.Main`.

* `qDecomp : QDecomp Wd Ud`, `qDecomp1 : QDecomp1 Wd W1d Ud Vd` (level 1) — the explicit Cholesky
  data and its `s`-derivative.
* `qFactor_canon` (level 1): `QFactor U (Γc U)` for the canonical `Γc` (Dirichlet inverse `Fi = fR⁻¹/n`).
* `qfHyp_of_euler` (level 2 on the three `QEuler` bounds only).
-/
import RamanujanTau.QFProof3.Decomp1
import RamanujanTau.QFProof3.Factor

namespace RamanujanTau.QFProof3

open RamanujanTau.QFProof

/-- **`QFHyp` from the factorization and Euler hypotheses alone** (the decompositions are proved). -/
theorem qfHyp_of_factor_euler {Γ Γ' : ℕ → ℕ → ℕ → ℝ} (hF : QFactor Ud Γ) (hF1 : QFactor Vd Γ')
    (hE : QEuler Wd Γ 1) (hE1 : QEuler W1d Γ 2) (hE2 : QEuler Wd Γ' 3) :
    RamanujanTau.HafnerBridge.QFHyp :=
  qfHyp_of qDecomp qDecomp1 hF hF1 hE hE1 hE2

/-- **`QFHyp` from the three Euler bounds alone** (decompositions and factorizations proved). -/
theorem qfHyp_of_euler (hE : QEuler Wd (Γc Ud) 1) (hE1 : QEuler W1d (Γc Ud) 2)
    (hE2 : QEuler Wd (Γc Vd) 3) : RamanujanTau.HafnerBridge.QFHyp :=
  qfHyp_of_factor_euler (qFactor_canon Ud) (qFactor_canon Vd) hE hE1 hE2

end RamanujanTau.QFProof3

#print axioms RamanujanTau.QFProof3.sum_divisors_prod_local'
#print axioms RamanujanTau.QFProof3.loc_chol_sym
#print axioms RamanujanTau.QFProof3.Kq_prod
#print axioms RamanujanTau.QFProof3.qDecomp
#print axioms RamanujanTau.QFProof3.dchol_loc
#print axioms RamanujanTau.QFProof3.dloc_sym
#print axioms RamanujanTau.QFProof3.Kq1_prod
#print axioms RamanujanTau.QFProof3.qDecomp1
#print axioms RamanujanTau.QFProof3.qfHyp_of_factor_euler
#print axioms RamanujanTau.QFProof3.recFA_mul
#print axioms RamanujanTau.QFProof3.Fi_mul_F
#print axioms RamanujanTau.QFProof3.qFactor_canon
#print axioms RamanujanTau.QFProof3.qfHyp_of_euler
