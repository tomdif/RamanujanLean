/-
# `SvStripE` (S5): `SvCBound` from `S4Bound`, and positive proportion from `S4Bound` (level 2)

* **`svCBound_of_S4`**: `S4Bound c₁ → SvCBound (c₁ + 4)`.  From `SvC_eq_diag`
  (`𝒮 = Σ_d W(d) y_d²`) and `SvStripB.yd_bound_div`
  (`|y_d| ≤ K(1+ℓ)(1+|Re z|ℓ)y^{2|Im z|}ℓ^{−2} M_d`):

      |𝒮(z)| ≤ K²(1+ℓ)²(1+|Re z|ℓ)² y^{4|Im z|} ℓ^{−4} Σ_d |W(d)| M_d² ≤ 9K²A (1+|Re z|ℓ)² y^{(c₁+4)|Im z|}/ℓ.

* **`svStripHyp_of_S4`**, and **`tauL_positive_proportion_deligne_S4`**: `[DeligneBound]` and `S4Bound c₁`
  (`c₁ ≥ 0`) give a positive proportion of zeros of `L(Δ,s)` on the critical line.
-/
import RamanujanTau.SvStripE.S4Stmt
import RamanujanTau.SvStripC.Ident
import RamanujanTau.SvStripC.Holo
import RamanujanTau.SvStripB.Downstream
import RamanujanTau.HafnerFinal.Strip

set_option autoImplicit false

namespace RamanujanTau.SvStripE

open Complex Finset
open RamanujanTau.SvStripA (WdC SvC SvCBound svStripHyp_of_bound stripR_sub_Ω)
open RamanujanTau.SvStripC (Γz YdJ SvC_eq_diag)
open RamanujanTau.SvStripB (yd_bound_div)
open RamanujanTau.SKQFProof (stripR SvStripHyp)

/-- The final scalar inequality `B²·A e^{c₁iℓ} ℓ ≤ 9K²A(1+rℓ)² e^{(c₁+4)iℓ}/ℓ`. -/
lemma scalar_le {K A c₁ ℓ r i : ℝ} (hA : 0 ≤ A) (hℓ : 1 / 2 ≤ ℓ) (hr : 0 ≤ r) :
    (K * (1 + ℓ) * (1 + r * ℓ) * Real.exp (2 * i * ℓ) / ℓ ^ 2) ^ 2 *
        (A * Real.exp (c₁ * i * ℓ) * ℓ) ≤
      9 * K ^ 2 * A * (1 + r * ℓ) ^ 2 * Real.exp ((c₁ + 4) * i * ℓ) / ℓ := by
  have hℓ0 : 0 < ℓ := by linarith
  set P := K ^ 2 * A * (1 + r * ℓ) ^ 2 * Real.exp ((c₁ + 4) * i * ℓ) with hP
  have hP0 : 0 ≤ P := by positivity
  have he : Real.exp (2 * i * ℓ) ^ 2 * Real.exp (c₁ * i * ℓ) = Real.exp ((c₁ + 4) * i * ℓ) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
  have e1 : (K * (1 + ℓ) * (1 + r * ℓ) * Real.exp (2 * i * ℓ) / ℓ ^ 2) ^ 2 *
      (A * Real.exp (c₁ * i * ℓ) * ℓ) = P * (1 + ℓ) ^ 2 / ℓ ^ 3 := by
    rw [hP, ← he]; field_simp
  have e2 : 9 * K ^ 2 * A * (1 + r * ℓ) ^ 2 * Real.exp ((c₁ + 4) * i * ℓ) / ℓ = 9 * P / ℓ := by
    rw [hP]; ring
  rw [e1, e2, div_le_div_iff₀ (by positivity) hℓ0]
  have : 0 ≤ P * ℓ * (2 * ℓ - 1) * (4 * ℓ + 1) := by
    have := mul_nonneg (mul_nonneg (mul_nonneg hP0 hℓ0.le) (by linarith : (0 : ℝ) ≤ 2 * ℓ - 1))
      (by linarith : (0 : ℝ) ≤ 4 * ℓ + 1)
    exact this
  nlinarith [this]

/-- **S5: `SvCBound (c₁ + 4)` from the twisted Euler-mass bound `S4Bound c₁`.** -/
theorem svCBound_of_S4 {c₁ : ℝ} (H : S4Bound c₁) : SvCBound (c₁ + 4) := by
  obtain ⟨A, δ₀, hA, hδ, hδ1, hS⟩ := H
  obtain ⟨K, hK, hY⟩ := yd_bound_div
  refine ⟨9 * K ^ 2 * A, δ₀, by positivity, hδ, hδ1, fun y hy z hz => ?_⟩
  have hy1 : 1 < y := by omega
  have hℓ : 1 / 2 ≤ Real.log y := by
    have h2 : Real.log 2 ≤ Real.log y := Real.log_le_log (by norm_num) (by exact_mod_cast hy)
    linarith [Real.log_two_gt_d9]
  set ℓ := Real.log y with hℓdef
  set B := K * (1 + ℓ) * (1 + |z.re| * ℓ) * Real.exp (2 * |z.im| * ℓ) / ℓ ^ 2 with hB
  have hB0 : 0 ≤ B := by
    have : 0 ≤ ℓ := by linarith
    positivity
  set M : ℕ → ℝ := fun d => ∑ u₁ ∈ Ioc 0 y, ∑ u₂ ∈ Ioc 0 y, ‖Γz z d u₁ u₂‖ with hM
  have hYd : ∀ d, ‖YdJ y z d‖ ≤ B * M d := fun d => hY (Γz z d) z y (by omega)
  rw [SvC_eq_diag hy1 (stripR_sub_Ω hδ1 hz)]
  calc ‖∑ d ∈ Icc 1 (y ^ 2), WdC (1 - z * I) d * YdJ y z d ^ 2‖
      ≤ ∑ d ∈ Icc 1 (y ^ 2), ‖WdC (1 - z * I) d‖ * (B ^ 2 * M d ^ 2) := by
        refine (norm_sum_le _ _).trans (sum_le_sum fun d _ => ?_)
        rw [norm_mul, norm_pow]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        rw [← mul_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (hYd d) 2
    _ = B ^ 2 * ∑ d ∈ Icc 1 (y ^ 2), ‖WdC (1 - z * I) d‖ * M d ^ 2 := by
        rw [mul_sum]; exact sum_congr rfl fun d _ => by ring
    _ ≤ B ^ 2 * (A * Real.exp (c₁ * |z.im| * ℓ) * ℓ) :=
        mul_le_mul_of_nonneg_left (hS y hy z hz) (sq_nonneg _)
    _ ≤ _ := scalar_le hA hℓ (abs_nonneg _)

/-- **`SvStripHyp (c₁ + 4)` from `S4Bound c₁`.** -/
theorem svStripHyp_of_S4 {c₁ : ℝ} (H : S4Bound c₁) : SvStripHyp (c₁ + 4) :=
  svStripHyp_of_bound (svCBound_of_S4 H)

/-- **Hafner's positive proportion for `L(Δ,s)` from `[DeligneBound]` and `S4Bound c₁`.** -/
theorem tauL_positive_proportion_deligne_S4 [RamanujanTau.DeligneBound] {c₁ : ℝ} (hc₁ : 0 ≤ c₁)
    (H : S4Bound c₁) :
    ∃ c T₀ : ℝ, 0 < c ∧ ∀ T : ℝ, T₀ ≤ T → ∃ S : Finset ℝ,
      (∀ γ ∈ S, 0 < γ ∧ γ ≤ 3 * T ∧ RamanujanTau.HeckeL.tauL (6 + γ * I) = 0) ∧
        c * (RamanujanTau.ZeroCount.zeroCount (3 * T) : ℝ) ≤ S.card :=
  RamanujanTau.HafnerFinal.tauL_positive_proportion_deligne_strip (by linarith) (svStripHyp_of_S4 H)

end RamanujanTau.SvStripE
