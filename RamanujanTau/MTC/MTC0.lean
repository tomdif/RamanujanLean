/-
# The first mock theta conjecture (MTC₀)

Ramanujan's fifth-order mock theta function `f₀(q) = Σ_{n≥0} q^{n²}/(−q;q)_n` satisfies

  `f₀(q) = θ₄(0, q⁵) G(q) − 2 Φ(q²)`,

where `θ₄(0, q⁵) = (q⁵;q¹⁰)²_∞ (q¹⁰;q¹⁰)_∞ = Σ_n (−1)ⁿ q^{5n²}`, `G(q) = 1/((q;q⁵)_∞ (q⁴;q⁵)_∞)` and
`Φ(q) = −1 + Σ_{n≥0} q^{5n²}/((q;q⁵)_{n+1} (q⁴;q⁵)_n)` (Andrews–Garvan's form of Hickerson's theorem).

The proof follows Hickerson–Mortenson: Andrews' Hecke form of `f₀` (`MockTheta5F0Pair`), HM Theorem 0.3 for
`f_{3,7,3}` at the MTC₀ point (`Zeros373`), the rank generating function as Appell–Lerch sums (`L5`), four changes
of `z`, and the theta identities F1′, P1.1 (Weierstrass), (8.17) (via the zero count `F19_zero` for HM (1.9)) and
product identities.
-/
import RamanujanTau.MTC.H19b

set_option autoImplicit false

namespace MTC
open PowerSeries RankProof

/-- **MTC₀**, multiplied by `(q;q)_∞`: `(q;q)_∞ f₀(q) + 2 (q;q)_∞ Φ(q²) = J_{5,10} J_{2,5}`. -/
theorem mock_theta_conjecture_f0_mul :
    MockTheta5.JTP.qfacInf * MockTheta5.JTP.f0 +
        2 * MockTheta5.JTP.qfacInf * (Ea 2 two_ne_zero (Phi 1) - 1) = Jp 5 10 * Jp 2 5 :=
  mtc0

/-- `(q;q)_∞ = J_{2,5} (q;q⁵)_∞ (q⁴;q⁵)_∞`. -/
lemma qfacInf_split : MockTheta5.JTP.qfacInf = Jp 2 5 * (Pinf 1 5 * Pinf 4 5) := by
  rw [← Pinf_one_one, Pinf_splitk 1 1 5 le_rfl le_rfl (by norm_num), Jp]
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
  norm_num
  ring

/-- **The first mock theta conjecture** (Hickerson 1988; Andrews–Garvan form):
`f₀(q) = θ₄(0, q⁵)/((q;q⁵)_∞ (q⁴;q⁵)_∞) − 2 Φ(q²)`. -/
theorem mock_theta_conjecture_f0 :
    MockTheta5.JTP.f0 =
      Pinf 5 10 * Pinf 5 10 * Pinf 10 10 * Ring.inverse (Pinf 1 5 * Pinf 4 5) - 2 * (Ea 2 two_ne_zero (Phi 1) - 1) := by
  have h := mtc0
  have hu : IsUnit (Pinf 1 5 * Pinf 4 5) := (isUnit_Pinf 1 5 le_rfl (by norm_num)).mul (isUnit_Pinf 4 5 (by norm_num) (by norm_num))
  have hJ : Jp 2 5 ≠ 0 := by
    unfold Jp
    exact ((isUnit_Pinf 2 5 (by norm_num) (by norm_num)).mul (isUnit_Pinf (5 - 2) 5 (by norm_num) (by norm_num))).mul
      (isUnit_Pinf 5 5 (by norm_num) (by norm_num)) |>.ne_zero
  rw [qfacInf_split] at h
  have h2 : (Pinf 1 5 * Pinf 4 5) * (MockTheta5.JTP.f0 + 2 * (Ea 2 two_ne_zero (Phi 1) - 1)) = Jp 5 10 := by
    apply mul_left_cancel₀ hJ
    linear_combination h
  have h3 : MockTheta5.JTP.f0 + 2 * (Ea 2 two_ne_zero (Phi 1) - 1) = Ring.inverse (Pinf 1 5 * Pinf 4 5) * Jp 5 10 := by
    rw [← h2, ← mul_assoc, Ring.inverse_mul_cancel _ hu, one_mul]
  rw [show Pinf 5 10 * Pinf 5 10 * Pinf 10 10 = Jp 5 10 by unfold Jp; norm_num]
  linear_combination h3

end MTC
