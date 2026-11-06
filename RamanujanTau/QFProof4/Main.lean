/-
# `QFProof4/` — gap 4 (multiplicativity) done; see `docs/QF_PROOF.md`

Build: `nice -n 10 lake build RamanujanTau.QFProof4.Main`.

* `recF_eq_prod` (level 1): `recF g` is multiplicative for `g` supported on prime powers.
* `Fi_eq_prod`, `recF_gRm_prime` (level 1); `abs_recF_gRm_ppow [DeligneBound]` (level 2).
* `Γc_eq_prod`, `Mass_le_prod`, `conv_prod`, `Vd_eq_sum`, `MassV_le` (level 1): the canonical `Γ`
  is multiplicative in `(u₁,u₂)`, and the truncated masses are bounded by products of local masses.
* `mv2_of_euler` (level 2 on the three `QEuler` bounds): Hafner's (MV2) for Selberg's mollifier.
-/
import RamanujanTau.QFProof4.GammaMultV
import RamanujanTau.QFProof3.Main
import RamanujanTau.HafnerBridge2.Assemble

namespace RamanujanTau.QFProof4

open RamanujanTau.QFProof RamanujanTau.QFProof3 Complex
open RamanujanTau.HafnerProportion RamanujanTau.HeckeL RamanujanTau.SelbergCoeffs

/-- **(MV2) for Selberg's mollifier from the three Euler bounds** (everything else proved). -/
theorem mv2_of_euler {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 81600)
    (hE : QEuler Wd (Γc Ud) 1) (hE1 : QEuler W1d (Γc Ud) 2) (hE2 : QEuler Wd (Γc Vd) 3) :
    ∃ B T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      (∫ u in T..(3 * T), ‖tauL (6 + u * I) * Mc (bSel ⌊T ^ θ⌋₊) ⌊T ^ θ⌋₊ (6 + u * I) ^ 2‖ ^ 2) ≤ B * T :=
  RamanujanTau.HafnerBridge2.mv2_of_QF hθ0 hθ (qfHyp_of_euler hE hE1 hE2)

end RamanujanTau.QFProof4

#print axioms RamanujanTau.QFProof4.recF_eq_prod
#print axioms RamanujanTau.QFProof4.Fi_eq_prod
#print axioms RamanujanTau.QFProof4.recF_gRm_prime
#print axioms RamanujanTau.QFProof4.abs_recF_gRm_ppow
#print axioms RamanujanTau.QFProof4.Γc_eq_prod
#print axioms RamanujanTau.QFProof4.Mass_le_prod
#print axioms RamanujanTau.QFProof4.conv_prod
#print axioms RamanujanTau.QFProof4.Vd_eq_sum
#print axioms RamanujanTau.QFProof4.MassV_le
#print axioms RamanujanTau.QFProof4.mv2_of_euler
