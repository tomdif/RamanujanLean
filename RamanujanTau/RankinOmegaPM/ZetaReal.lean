/-
# `1/ζ` is holomorphic near the real segment `(0, 2]`

`Z₁(w) = w − w(w−1) I₁(w)`, with `I₁(w) = ∫₁^∞ {t} t^{−w−1} dt` (`RankinOmega.IN 1`), is holomorphic
on `Re w > 0` and equals `(w−1)ζ(w)` for `Re w > 1` (`Z1_eq`, from `zeta_formula_large`).
For real `σ ∈ (0,1]`, `Re Z₁(σ) = σ + σ(1−σ) I₁(σ) ≥ σ > 0`; for `σ > 1`, `ζ(σ) ≠ 0` (Mathlib).
So `Z₁(σ) ≠ 0` for every real `σ > 0` (`Z1_real_ne_zero`) — in particular `ζ` has no zero in
`(0,1)` — and by compactness `Z₁ ≠ 0` on a thin strip around any segment `[β₀, B] ⊂ (0,∞)`
(`exists_strip`). `Q(w) = (w−1)/Z₁(w)` is then a holomorphic version of `1/ζ(w)` there.
-/
import RamanujanTau.RankinOmega.ZetaApprox

set_option autoImplicit false

namespace RamanujanTau.RankinOmegaPM

open Complex MeasureTheory Set Filter Topology Metric
open RamanujanTau.RankinOmega

/-- `Z₁(w) = w − w(w−1) I₁(w)` (`= (w−1)ζ(w)`). -/
noncomputable def Z1 (w : ℂ) : ℂ := w - w * (w - 1) * IN 1 w

lemma differentiableAt_Z1 {w : ℂ} (hw : 0 < w.re) : DifferentiableAt ℂ Z1 w := by
  unfold Z1
  exact differentiableAt_id.sub ((differentiableAt_id.mul (differentiableAt_id.sub_const 1)).mul
    (differentiableAt_IN 1 le_rfl hw))

lemma Z1_eq {w : ℂ} (hw : 1 < w.re) : Z1 w = (w - 1) * riemannZeta w := by
  have h := zeta_formula_large 1 le_rfl hw
  simp only [Finset.Icc_self, Finset.sum_singleton, Nat.cast_one, Complex.one_cpow] at h
  have hw1 : w - 1 ≠ 0 := by
    intro h1; rw [sub_eq_zero] at h1; rw [h1] at hw; simp at hw
  unfold Z1
  rw [show riemannZeta w = 1 + 1 / (w - 1) - w * IN 1 w by linear_combination h]
  field_simp
  ring

lemma IN_real_re_nonneg (σ : ℝ) : 0 ≤ (IN 1 (σ : ℂ)).re := by
  rw [IN_eq 1 le_rfl]
  have e : ∫ t in Ioi ((1 : ℕ) : ℝ), ((fr t : ℝ) : ℂ) * (t : ℂ) ^ (-(σ : ℂ) - 1) =
      ((∫ t in Ioi ((1 : ℕ) : ℝ), fr t * t ^ (-σ - 1) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : (0 : ℝ) < t := lt_trans (by norm_num) ht
    rw [Complex.ofReal_mul, Complex.ofReal_cpow ht0.le]
    push_cast; ring_nf
  rw [e, Complex.ofReal_re]
  refine setIntegral_nonneg measurableSet_Ioi fun t ht => ?_
  have ht0 : (0 : ℝ) < t := lt_trans (by norm_num) ht
  have := fr_nonneg ht0.le
  have := Real.rpow_nonneg ht0.le (-σ - 1)
  positivity

/-- **`Z₁(σ) ≠ 0` for every real `σ > 0`.** -/
lemma Z1_real_ne_zero {σ : ℝ} (h0 : 0 < σ) : Z1 (σ : ℂ) ≠ 0 := by
  rcases le_or_gt σ 1 with h1 | h1
  · intro hz
    have hre := congrArg Complex.re hz
    have e : (Z1 (σ : ℂ)).re = σ - σ * (σ - 1) * (IN 1 (σ : ℂ)).re := by
      unfold Z1
      rw [show (σ : ℂ) * ((σ : ℂ) - 1) = ((σ * (σ - 1) : ℝ) : ℂ) by push_cast; ring]
      simp only [sub_re, ofReal_re, re_ofReal_mul]
    rw [e, zero_re] at hre
    have := IN_real_re_nonneg σ
    have : σ * (σ - 1) ≤ 0 := by nlinarith
    nlinarith
  · rw [Z1_eq (by simpa using h1)]
    refine mul_ne_zero ?_ (riemannZeta_ne_zero_of_one_lt_re (by simpa using h1))
    intro h; rw [sub_eq_zero] at h
    have := congrArg Complex.re h; simp at this; linarith

/-- The holomorphic version of `1/ζ(w)`. -/
noncomputable def Qz (w : ℂ) : ℂ := (w - 1) / Z1 w

lemma Qz_mul_zeta {w : ℂ} (hw : 1 < w.re) : Qz w * riemannZeta w = 1 := by
  have hw1 : w - 1 ≠ 0 := by
    intro h1; rw [sub_eq_zero] at h1; rw [h1] at hw; simp at hw
  have hζ := riemannZeta_ne_zero_of_one_lt_re hw
  unfold Qz; rw [Z1_eq hw]; field_simp

lemma differentiableAt_Qz {w : ℂ} (hw : 0 < w.re) (hz : Z1 w ≠ 0) : DifferentiableAt ℂ Qz w :=
  (differentiableAt_id.sub_const 1).div (differentiableAt_Z1 hw) hz

/-- **A thin strip around `[β₀, B]` on which `Z₁ ≠ 0`.** -/
lemma exists_strip {β0 B : ℝ} (hβ0 : 0 < β0) :
    ∃ r : ℝ, 0 < r ∧ ∀ w : ℂ, β0 ≤ w.re → w.re ≤ B → |w.im| < r → 0 < w.re ∧ Z1 w ≠ 0 := by
  set K : Set ℂ := (fun x : ℝ => (x : ℂ)) '' Icc β0 B with hK
  have hKc : IsCompact K := isCompact_Icc.image continuous_ofReal
  set U : Set ℂ := {w : ℂ | 0 < w.re} ∩ Z1 ⁻¹' {0}ᶜ with hU
  have hUo : IsOpen U := by
    have hc : ContinuousOn Z1 {w : ℂ | 0 < w.re} := fun w hw =>
      (differentiableAt_Z1 hw).continuousAt.continuousWithinAt
    exact hc.isOpen_inter_preimage (isOpen_lt continuous_const continuous_re) isOpen_compl_singleton
  have hKU : K ⊆ U := by
    rintro _ ⟨x, hx, rfl⟩
    have hx0 : 0 < x := lt_of_lt_of_le hβ0 hx.1
    exact ⟨by simpa using hx0, Z1_real_ne_zero hx0⟩
  obtain ⟨r, hr, hsub⟩ := hKc.exists_thickening_subset_open hUo hKU
  refine ⟨r, hr, fun w h1 h2 h3 => ?_⟩
  have hw : w ∈ thickening r K := by
    rw [mem_thickening_iff]
    refine ⟨(w.re : ℂ), ⟨w.re, ⟨h1, h2⟩, rfl⟩, ?_⟩
    rw [Complex.dist_of_re_eq (by simp)]
    simpa [Real.dist_eq] using h3
  exact hsub hw

end RamanujanTau.RankinOmegaPM
