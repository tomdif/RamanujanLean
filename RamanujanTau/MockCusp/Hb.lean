/-
# `Andrews66.Hb` at every odd cusp, and the reduction of `Hb` to the even cusps

`Hb_odd`: the odd-denominator half of `Andrews66.Hb`, unconditionally, with `C = 216(1+C₀)`, `D = 3/2`.

`Hb_of_even`: `Andrews66.Hb` follows from its even-denominator half `HbEven`.
-/
import RamanujanTau.MockCusp.OddCusp
import RamanujanTau.Andrews66.BNear

set_option autoImplicit false

namespace MockCusp
open Complex

noncomputable section

/-- the constant of the odd cusps. -/
def Codd : ℝ := 216 * (1 + HardyRamanujan.C0)

lemma Codd_nonneg : 0 ≤ Codd := by unfold Codd; have := HardyRamanujan.C0_nonneg; positivity

/-- **`Hb` at the odd cusps** (`ε_K = 0`): `‖f(q)‖ ≤ 216(1+C₀)‖z‖^{−3/2}`. -/
theorem Hb_odd : ∀ K : ℕ, 0 < K → ¬ Even K → ∀ h : ℕ, Nat.Coprime h K → ∀ z : ℂ, 0 < z.re →
    (K : ℝ) / 2 ≤ (1 / z).re →
    ‖Andrews66.fA (Rademacher.qp h K z) - Andrews66.epsK K * Andrews66.bE (Rademacher.qp h K z)‖ ≤
      Codd * ‖z‖ ^ (-(3 / 2 : ℝ)) := by
  intro K _ hKe h hcop z hz hR
  have hK : Odd K := Nat.not_even_iff_odd.mp hKe
  rw [Andrews66.epsK, if_neg hKe, zero_mul, sub_zero]
  exact f_odd_bound hK hcop hz hR

/-- the even-denominator half of `Andrews66.Hb`. -/
def HbEven (C D : ℝ) : Prop :=
  ∀ K : ℕ, 0 < K → Even K → ∀ h : ℕ, Nat.Coprime h K → ∀ z : ℂ, 0 < z.re → (K : ℝ) / 2 ≤ (1 / z).re →
    ‖Andrews66.fA (Rademacher.qp h K z) - Andrews66.epsK K * Andrews66.bE (Rademacher.qp h K z)‖ ≤
      C * ‖z‖ ^ (-D)

/-- **`Hb` from its even half.** -/
theorem Hb_of_even {C : ℝ} (hE : HbEven C (3 / 2)) : Andrews66.Hb (max C Codd) (3 / 2) := by
  intro K hK h hcop z hz hR
  have hp : 0 ≤ ‖z‖ ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
  by_cases hKe : Even K
  · exact (hE K hK hKe h hcop z hz hR).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hp)
  · exact (Hb_odd K hK hKe h hcop z hz hR).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hp)

end

end MockCusp
