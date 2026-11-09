/-
# The `f₀` group: `F₀`, `φ₀`, `ψ₀` from the first mock theta conjecture

With `Φ = RankProof.Phi 1` (so Andrews–Garvan's `Φ(q) = Φ − 1`):

* `F₀(q) = Φ(q) − q (q¹⁰;q¹⁰)_∞/((q⁴;q¹⁰)_∞(q⁵;q¹⁰)_∞(q⁶;q¹⁰)_∞)`                      (`mtc_F0`)
* `φ₀(−q) = −(Φ(q) − 1) + (q⁴,q⁵,q⁶,q¹⁰;q¹⁰)_∞/((q²;q¹⁰)²(q³;q¹⁰)(q⁷;q¹⁰)(q⁸;q¹⁰)²)`     (`mtc_phi0`)
* `ψ₀(q) = (Φ(q²) − 1) + q (q,q⁹,q¹⁰;q¹⁰)_∞/((q²,q³,q⁷,q⁸;q¹⁰)_∞)`                         (`mtc_psi0`)

Proof: MTC₀ (`MTC.mock_theta_conjecture_f0`) with Watson's (3₀), (2₀), (1₀), and the theta identities
`Theta.theta_F0`, `theta_phi0`, `theta_psi0`, compared in `ℂ((q))`.
-/
import RamanujanTau.MockTheta5All.Common

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

namespace MockTheta5All
open PowerSeries Watson Finset RankProof

/-- the product in the `F₀` identity. -/
noncomputable def EF0 : PowerSeries ℤ := Pinf 10 10 * Ring.inverse (Pinf 4 10 * Pinf 5 10 * Pinf 6 10)

/-- the product in the `φ₀` identity. -/
noncomputable def Ephi0 : PowerSeries ℤ :=
  Pinf 4 10 * Pinf 5 10 * Pinf 6 10 * Pinf 10 10 * Ring.inverse (Pinf 2 10 ^ 2 * Pinf 3 10 * Pinf 7 10 * Pinf 8 10 ^ 2)

/-- the product in the `ψ₀` identity. -/
noncomputable def Epsi0 : PowerSeries ℤ :=
  Pinf 1 10 * Pinf 9 10 * Pinf 10 10 * Ring.inverse (Pinf 2 10 * Pinf 3 10 * Pinf 7 10 * Pinf 8 10)

/-- MTC₀ in Watson's notation. -/
lemma mtc0_w : f0w = Pinf 5 10 * Pinf 5 10 * Pinf 10 10 * Ring.inverse (Pinf 1 5 * Pinf 4 5) -
    2 * (expand 2 two_ne_zero (Phi 1) - 1) := by
  rw [f0w_eq]; exact MTC.mock_theta_conjecture_f0

/-- **`F₀`**: `F₀(q) = Φ(q) − q (q¹⁰;q¹⁰)_∞/((q⁴;q¹⁰)_∞(q⁵;q¹⁰)_∞(q⁶;q¹⁰)_∞)`. -/
theorem mtc_F0 : F0w = Phi 1 - X * EF0 := by
  apply expand_injective 2 two_ne_zero
  apply ιq_injective
  apply eq_of_two_mul
  have h3 := congrArg ιq watson_3_0
  have hM := congrArg ιq mtc0_w
  have hT := Theta.theta_F0
  rw [th4w_eq, Gw_eq, psi2w_eq, Hw_eq] at h3
  simp (disch := unit_tac) only [map_add, map_sub, map_mul, map_pow, map_ofNat, map_one, ιq_inv, expand_inv',
    expand_Pinf', expand_X, ιq_X, EF0, Nat.reduceMul] at h3 hM ⊢
  linear_combination h3 - hM + hT

/-- **`φ₀`**: `φ₀(−q) = −(Φ(q) − 1) + (q⁴,q⁵,q⁶,q¹⁰;q¹⁰)_∞/((q²;q¹⁰)²(q³;q¹⁰)(q⁷;q¹⁰)(q⁸;q¹⁰)²)`. -/
theorem mtc_phi0 : negQ phi0w = -(Phi 1 - 1) + Ephi0 := by
  rw [negQ_phi0w]
  apply expand_injective 2 two_ne_zero
  apply ιq_injective
  apply eq_of_two_mul
  have h2 := congrArg ιq watson_2_0
  have hM := congrArg ιq mtc0_w
  have hT := Theta.theta_phi0
  rw [th4w_eq, Gw_eq] at h2
  simp (disch := unit_tac) only [map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one, ιq_inv,
    expand_inv', expand_Pinf', expand_X, ιq_X, Ephi0, Nat.reduceMul] at h2 hM ⊢
  linear_combination -h2 + hM + hT

/-- **`ψ₀`**: `ψ₀(q) = (Φ(q²) − 1) + q (q,q⁹,q¹⁰;q¹⁰)_∞/((q²,q³,q⁷,q⁸;q¹⁰)_∞)`. -/
theorem mtc_psi0 : psi0w = (expand 2 two_ne_zero (Phi 1) - 1) + X * Epsi0 := by
  apply ιq_injective
  have h10 := congrArg ιq watson_1_0
  have hF := congrArg ιq (congrArg (expand 2 two_ne_zero) mtc_F0)
  have hT := Theta.theta_psi0
  rw [psi2w_eq, Hw_eq] at h10
  simp (disch := unit_tac) only [map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one, ιq_inv,
    expand_inv', expand_Pinf', expand_X, ιq_X, EF0, Epsi0, Nat.reduceMul] at h10 hF ⊢
  linear_combination h10 + hF + ALz.mono 1 1 * hT

end MockTheta5All
