/-
# The `f₁` group: `F₁`, `φ₁`, `ψ₁`, `χ₁` from the second mock theta conjecture

With `Ψ = RankProof.Phi 2` (so Andrews–Garvan's `Ψ(q) = Ψ − 1`):

* `qF₁(q) = (Ψ(q) − 1) + q (q¹⁰;q¹⁰)_∞/((q²;q¹⁰)_∞(q⁵;q¹⁰)_∞(q⁸;q¹⁰)_∞)`                    (`mtc_F1`)
* `φ₁(−q) = (Ψ(q) − 1) − q (q²,q⁵,q⁸,q¹⁰;q¹⁰)_∞/((q;q¹⁰)(q⁴;q¹⁰)²(q⁶;q¹⁰)²(q⁹;q¹⁰))`        (`mtc_phi1`)
* `qψ₁(q) = (Ψ(q²) − 1) + q (q³,q⁷,q¹⁰;q¹⁰)_∞/((q,q⁴,q⁶,q⁹;q¹⁰)_∞)`                         (`mtc_psi1`)
* `qχ₁(q) = 3(Ψ(q) − 1) + q (q,q⁴,q⁵;q⁵)_∞/((q²;q⁵)²_∞(q³;q⁵)²_∞)`                          (`mtc_chi1`)

Proof: MTC₁ (`MTC.mock_theta_conjecture_f1`) with Watson's (3₁), (2₁), (1₁), (B₁), and the theta identities
`Theta.theta_F1`, `theta_phi1`, `theta_psi1`, `theta_chi1`, compared in `ℂ((q))`.
-/
import RamanujanTau.MockTheta5All.Common

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

namespace MockTheta5All
open PowerSeries Watson Finset RankProof

/-- the product in the `F₁` identity. -/
noncomputable def EF1 : PowerSeries ℤ := Pinf 10 10 * Ring.inverse (Pinf 2 10 * Pinf 5 10 * Pinf 8 10)

/-- the product in the `φ₁` identity. -/
noncomputable def Ephi1 : PowerSeries ℤ :=
  Pinf 2 10 * Pinf 5 10 * Pinf 8 10 * Pinf 10 10 * Ring.inverse (Pinf 1 10 * Pinf 4 10 ^ 2 * Pinf 6 10 ^ 2 * Pinf 9 10)

/-- the product in the `ψ₁` identity. -/
noncomputable def Epsi1 : PowerSeries ℤ :=
  Pinf 3 10 * Pinf 7 10 * Pinf 10 10 * Ring.inverse (Pinf 1 10 * Pinf 4 10 * Pinf 6 10 * Pinf 9 10)

/-- the product in the `χ₁` identity. -/
noncomputable def Echi1 : PowerSeries ℤ :=
  Pinf 1 5 * Pinf 4 5 * Pinf 5 5 * Ring.inverse (Pinf 2 5 ^ 2 * Pinf 3 5 ^ 2)

/-- MTC₁ in Watson's notation. -/
lemma mtc1_w : X * f1w = X * (Pinf 5 10 * Pinf 5 10 * Pinf 10 10 * Ring.inverse (Pinf 2 5 * Pinf 3 5)) -
    2 * (expand 2 two_ne_zero (Phi 2) - 1) := by
  rw [f1w_eq]; exact MTC.mock_theta_conjecture_f1

/-- **`F₁`**: `qF₁(q) = (Ψ(q) − 1) + q (q¹⁰;q¹⁰)_∞/((q²;q¹⁰)_∞(q⁵;q¹⁰)_∞(q⁸;q¹⁰)_∞)`. -/
theorem mtc_F1 : X * F1w = (Phi 2 - 1) + X * EF1 := by
  apply expand_injective 2 two_ne_zero
  apply ιq_injective
  apply eq_of_two_mul
  have h3 := congrArg ιq watson_3_1
  have hM := congrArg ιq mtc1_w
  have hT := Theta.theta_F1
  rw [th4w_eq, Hw_eq, psi2w_eq, Gw_eq] at h3
  simp (disch := unit_tac) only [map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one, ιq_inv,
    expand_inv', expand_Pinf', expand_X, ιq_X, EF1, Nat.reduceMul] at h3 hM ⊢
  linear_combination ALz.mono 1 1 * h3 - hM + ALz.mono 1 1 * hT

/-- **`φ₁`**: `φ₁(−q) = (Ψ(q) − 1) − q (q²,q⁵,q⁸,q¹⁰;q¹⁰)_∞/((q;q¹⁰)(q⁴;q¹⁰)²(q⁶;q¹⁰)²(q⁹;q¹⁰))`. -/
theorem mtc_phi1 : negQ phi1w = (Phi 2 - 1) - X * Ephi1 := by
  rw [negQ_phi1w]
  apply expand_injective 2 two_ne_zero
  apply ιq_injective
  apply eq_of_two_mul
  have h2 := congrArg ιq watson_2_1
  have hM := congrArg ιq mtc1_w
  have hT := Theta.theta_phi1
  rw [th4w_eq, Hw_eq] at h2
  simp (disch := unit_tac) only [map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one, ιq_inv,
    expand_inv', expand_Pinf', expand_X, ιq_X, Ephi1, Nat.reduceMul] at h2 hM ⊢
  linear_combination h2 - hM - ALz.mono 1 1 * hT

/-- **`ψ₁`**: `qψ₁(q) = (Ψ(q²) − 1) + q (q³,q⁷,q¹⁰;q¹⁰)_∞/((q,q⁴,q⁶,q⁹;q¹⁰)_∞)`. -/
theorem mtc_psi1 : X * psi1w = (expand 2 two_ne_zero (Phi 2) - 1) + X * Epsi1 := by
  apply ιq_injective
  have h11 := congrArg ιq watson_1_1
  have hF := congrArg ιq (congrArg (expand 2 two_ne_zero) mtc_F1)
  have hT := Theta.theta_psi1
  rw [psi2w_eq, Gw_eq] at h11
  simp (disch := unit_tac) only [map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one, ιq_inv,
    expand_inv', expand_Pinf', expand_X, ιq_X, EF1, Epsi1, Nat.reduceMul] at h11 hF ⊢
  linear_combination ALz.mono 1 1 * h11 + hF + ALz.mono 1 1 * hT

/-- **`χ₁`**: `qχ₁(q) = 3(Ψ(q) − 1) + q (q,q⁴,q⁵;q⁵)_∞/((q²;q⁵)²_∞(q³;q⁵)²_∞)`. -/
theorem mtc_chi1 : X * chi1w = 3 * (Phi 2 - 1) + X * Echi1 := by
  apply ιq_injective
  have hB := congrArg ιq watson_B1
  have hF := congrArg ιq mtc_F1
  have hP := congrArg ιq mtc_phi1
  have hT := Theta.theta_chi1
  rw [negQ_phi1w] at hP
  simp (disch := unit_tac) only [map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one, ιq_inv,
    ιq_X, EF1, Ephi1, Echi1, Nat.reduceMul] at hB hF hP ⊢
  linear_combination hB + 2 * hF + hP + ALz.mono 1 1 * hT

end MockTheta5All
