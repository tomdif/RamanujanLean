/-
# The Mellin transform of the partial sums `A(x) = ∑_{n ≤ x} a_f(n)`

If `‖A(x)‖ ≤ c₀ x^α` for `x ≥ X₀` (some `α > 0`), then for `Re w > α`

    ∫₀^∞ A(x) x^{−w−1} dx = mellin A (−w) = L(f, w) / w.

For `Re w > (k+1)/2` this is Abel summation (`LSeries_eq_mul_integral'`); both sides are
holomorphic on `Re w > α` (`mellin_differentiableAt_of_isBigO_rpow`, `fL_entire`), so the identity
principle extends it.
-/
import Mathlib
import RamanujanTau.HeckeConvexGeneral.Main

set_option autoImplicit false

namespace RamanujanTau.TauOmegaPartial

open Complex MeasureTheory Set Filter Topology Asymptotics
open RamanujanTau.HeckeConvexGeneral
open scoped MatrixGroups

variable {k : ℕ}

/-- The partial sum `A(x) = ∑_{1 ≤ n ≤ x} a_f(n)`. -/
noncomputable def A (f : CuspForm 𝒮ℒ (k : ℤ)) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, coef f n

lemma A_of_lt_one (f : CuspForm 𝒮ℒ (k : ℤ)) {x : ℝ} (hx : x < 1) : A f x = 0 := by
  have : ⌊x⌋₊ = 0 := Nat.floor_eq_zero.mpr hx
  simp [A, this]

lemma measurable_A (f : CuspForm 𝒮ℒ (k : ℤ)) : Measurable (A f) := by
  have h : A f = (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, coef f n) ∘ (fun x : ℝ => ⌊x⌋₊) := rfl
  rw [h]
  exact (measurable_from_nat).comp Nat.measurable_floor

lemma norm_A_le (f : CuspForm 𝒮ℒ (k : ℤ)) {x X : ℝ} (hx : x ≤ X) :
    ‖A f x‖ ≤ ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, ‖coef f n‖ := by
  refine (norm_sum_le _ _).trans ?_
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.Icc_subset_Icc le_rfl (Nat.floor_le_floor hx)) (fun _ _ _ => norm_nonneg _)

lemma locallyIntegrableOn_A (f : CuspForm 𝒮ℒ (k : ℤ)) : LocallyIntegrableOn (A f) (Ioi 0) := by
  have h := locallyIntegrableOn_mul_sum_Icc (c := coef f) (m := 1) (a := (0 : ℝ)) le_rfl
    (g := fun _ => (1 : ℂ)) (continuousOn_const.locallyIntegrableOn measurableSet_Ici)
  simp only [one_mul] at h
  exact h.mono_set Ioi_subset_Ici_self

/-- The Mellin identity in the half-plane of absolute convergence. -/
lemma mellin_A_eq_of_large (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 1 ≤ k) {w : ℂ}
    (hw : ((k : ℝ) + 1) / 2 < w.re) : mellin (A f) (-w) = fL f w / w := by
  obtain ⟨B, hB0, hB⟩ := exists_sum_norm_coef_le f hk
  have hO : (fun n : ℕ ↦ ∑ j ∈ Finset.Icc 1 n, ‖coef f j‖) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (((k : ℝ) + 1) / 2) := by
    refine IsBigO.of_bound B (Eventually.of_forall fun N => ?_)
    rw [Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _),
      Real.norm_of_nonneg (by positivity)]
    exact hB N
  have hL := LSeries_eq_mul_integral' (coef f) (r := ((k : ℝ) + 1) / 2) (by positivity) hw hO
  rw [← fL_eq_LSeries f hk hw] at hL
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hw0 : w ≠ 0 := by
    intro h; rw [h] at hw; simp at hw; linarith
  rw [hL, mul_div_cancel_left₀ _ hw0, mellin]
  rw [← setIntegral_eq_of_subset_of_ae_diff_eq_zero measurableSet_Ioi.nullMeasurableSet
    (Ioi_subset_Ioi zero_le_one)]
  · refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    simp only [A, smul_eq_mul]
    rw [mul_comm]; congr 2; ring
  · have h1 : ∀ᵐ x : ℝ ∂volume, x ∈ ({1} : Set ℝ)ᶜ :=
      compl_mem_ae_iff.mpr (measure_singleton 1)
    filter_upwards [h1] with x hx1 hx
    have hx1' : x ≠ 1 := hx1
    rcases hx with ⟨h0, h1⟩
    simp only [mem_Ioi, not_lt] at h1 h0
    have : x < 1 := lt_of_le_of_ne h1 hx1'
    have h2 := A_of_lt_one f this
    simp only [A] at h2
    rw [h2, zero_mul]

/-- **The Mellin identity on `Re w > α`**, under the growth hypothesis `‖A(x)‖ ≤ c₀ x^α`. -/
theorem mellin_A_eq (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 1 ≤ k) {α c0 X0 : ℝ} (hα : 0 ≤ α)
    (hX : ∀ x ≥ X0, ‖A f x‖ ≤ c0 * x ^ α) {w : ℂ} (hw : α < w.re) :
    mellin (A f) (-w) = fL f w / w := by
  set U : Set ℂ := {w | α < w.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const continuous_re
  have hUc : IsPreconnected U := (convex_halfSpace_re_gt α).isPreconnected
  have htop : A f =O[atTop] (· ^ (-(-α))) := by
    simp only [neg_neg]
    refine IsBigO.of_bound c0 ?_
    filter_upwards [eventually_ge_atTop X0, eventually_gt_atTop 0] with x hx hx0
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)]; exact hX x hx
  have hbot (b : ℝ) : A f =O[𝓝[>] 0] (· ^ (-b)) := by
    have : A f =ᶠ[𝓝[>] 0] 0 := by
      filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with x hx using A_of_lt_one f hx.2
    exact this.trans_isBigO (isBigO_zero _ _)
  have hF1 : DifferentiableOn ℂ (fun w => mellin (A f) (-w)) U := by
    intro w hw
    have hw' : α < w.re := hw
    have hd := mellin_differentiableAt_of_isBigO_rpow (locallyIntegrableOn_A f) htop
      (s := -w) (by simp; exact hw') (hbot (-w.re - 1)) (by simp)
    exact (hd.comp w differentiableAt_id.neg).differentiableWithinAt
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hF2 : DifferentiableOn ℂ (fun w => fL f w / w) U := by
    refine (fL_entire f hk).differentiableOn.div differentiableOn_id fun w hw h => ?_
    have hw' : α < w.re := hw
    rw [h] at hw'; simp at hw'; linarith
  set r : ℝ := max α (((k : ℝ) + 1) / 2) + 1 with hr
  have hz0 : ((r : ℝ) : ℂ) ∈ U := by
    show α < ((r : ℝ) : ℂ).re
    rw [Complex.ofReal_re, hr]; linarith [le_max_left α (((k : ℝ) + 1) / 2)]
  have hev : (fun w => mellin (A f) (-w)) =ᶠ[𝓝 ((r : ℝ) : ℂ)] (fun w => fL f w / w) := by
    have hVo : IsOpen {w : ℂ | ((k : ℝ) + 1) / 2 < w.re} := isOpen_lt continuous_const continuous_re
    have hz : ((r : ℝ) : ℂ) ∈ {w : ℂ | ((k : ℝ) + 1) / 2 < w.re} := by
      show ((k : ℝ) + 1) / 2 < ((r : ℝ) : ℂ).re
      rw [Complex.ofReal_re, hr]; linarith [le_max_right α (((k : ℝ) + 1) / 2)]
    filter_upwards [hVo.mem_nhds hz] with w hw using mellin_A_eq_of_large f hk hw
  exact AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (hF1.analyticOnNhd hUo)
    (hF2.analyticOnNhd hUo) hUc hz0 hev hw

end RamanujanTau.TauOmegaPartial
