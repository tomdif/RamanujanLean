/-
# Dyadic-block lower bound for `|L(f,σ+it)/(σ+it)|²` just right of `σ = (2k−1)/4`

For `σ = (2k−1)/4 + δ`, `0 < δ ≤ 1/16`, and `Ξ ≥ Ξ₀`:

    ∫_Ξ^{2Ξ} |L(f, σ − 2πiξ)/(σ − 2πiξ)|² dξ ≥ K₁ (2Ξ)^{−4δ},

with `K₁ > 0`, `Ξ₀` independent of `δ`. Functional equation (`fe_lower`): `|L(σ+it)|² ≫ |t|^{1−4δ}
|L(k−σ−it)|²`; then `first_moment` on the line `k − σ ∈ [k/2 + 3/16, k/2 + 1/4)`.
-/
import RamanujanTau.TauOmegaPartial.FirstMoment

set_option autoImplicit false

namespace RamanujanTau.TauOmegaPartial

open Complex MeasureTheory Set Filter Topology Asymptotics
open RamanujanTau.HeckeConvexGeneral
open scoped MatrixGroups Real Interval

variable {k : ℕ}

/-- The Fourier-side density `F_σ(ξ) = L(f, σ − 2πiξ)/(σ − 2πiξ)`. -/
noncomputable def Fs (f : CuspForm 𝒮ℒ (k : ℤ)) (σ ξ : ℝ) : ℂ :=
  fL f ((σ : ℂ) - 2 * π * ξ * I) / ((σ : ℂ) - 2 * π * ξ * I)

lemma continuous_Fs (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 1 ≤ k) {σ : ℝ} (hσ : 0 < σ) :
    Continuous (Fs f σ) := by
  unfold Fs
  refine Continuous.div ((fL_entire f hk).continuous.comp (by fun_prop)) (by fun_prop) ?_
  intro ξ h
  have := congrArg Complex.re h
  simp at this; linarith

theorem block_lower (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 12 ≤ k) {m : ℕ} (hm : 1 ≤ m)
    (hlow : ∀ n < m, coef f n = 0) (hm0 : coef f m ≠ 0) :
    ∃ K1 : ℝ, 0 < K1 ∧ ∃ Ξ0 : ℝ, 1 ≤ Ξ0 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 16 → ∀ Ξ : ℝ, Ξ0 ≤ Ξ →
      K1 * (2 * Ξ) ^ (-(4 * δ)) ≤
        ∫ ξ in Ξ..2 * Ξ, ‖Fs f (((k : ℝ) - 1) / 2 + 1 / 4 + δ) ξ‖ ^ 2 := by
  have hkR : (12 : ℝ) ≤ k := by exact_mod_cast hk
  obtain ⟨c, hc0, hfe⟩ := fe_lower f (by omega)
  obtain ⟨c3, hc3, Y0, hY0, hfm⟩ := first_moment f hk hm hlow hm0
  set B : ℝ := (k : ℝ) + 2 * π with hB
  have hB0 : 0 < B := by rw [hB]; positivity
  refine ⟨c ^ 2 * c3 / (2 * B ^ 2), by positivity, max 1 Y0, le_max_left _ _,
    fun δ hδ0 hδ1 Ξ hΞ => ?_⟩
  have hΞ1 : 1 ≤ Ξ := le_trans (le_max_left _ _) hΞ
  have hΞY : Y0 ≤ Ξ := le_trans (le_max_right _ _) hΞ
  set σ : ℝ := ((k : ℝ) - 1) / 2 + 1 / 4 + δ with hσ
  set σ' : ℝ := (k : ℝ) - σ with hσ'
  set e : ℝ := (k : ℝ) - 2 * σ with he
  set q : ℝ := -1 - 4 * δ with hq
  have hσ0 : 0 < σ := by rw [hσ]; linarith
  -- pointwise lower bound
  set g : ℝ → ℝ := fun ξ => ‖fL f ((σ' : ℂ) + ((2 * π * ξ : ℝ) : ℂ) * I)‖ ^ 2 with hg
  have hpt : ∀ ξ ∈ Icc Ξ (2 * Ξ),
      c ^ 2 / B ^ 2 * (2 * Ξ) ^ q * g ξ ≤ ‖Fs f σ ξ‖ ^ 2 := by
    intro ξ hξ
    have hξ1 : 1 ≤ ξ := le_trans hΞ1 hξ.1
    have hξ0 : 0 < ξ := by linarith
    have h1 := hfe σ (-(2 * π * ξ)) (by rw [hσ]; linarith) (by rw [hσ]; linarith)
    have ew : (k : ℂ) - ((σ : ℂ) + ((-(2 * π * ξ) : ℝ) : ℂ) * I) =
        (σ' : ℂ) + ((2 * π * ξ : ℝ) : ℂ) * I := by rw [hσ']; push_cast; ring
    have es : (σ : ℂ) + ((-(2 * π * ξ) : ℝ) : ℂ) * I = (σ : ℂ) - 2 * π * ξ * I := by
      push_cast; ring
    rw [ew, es, abs_neg, abs_of_nonneg (by positivity)] at h1
    set Lw := ‖fL f ((σ' : ℂ) + ((2 * π * ξ : ℝ) : ℂ) * I)‖ with hLw
    set s : ℂ := (σ : ℂ) - 2 * π * ξ * I with hs
    have hns : ‖s‖ ≤ B * ξ := by
      refine (Complex.norm_le_abs_re_add_abs_im s).trans ?_
      have hre : s.re = σ := by simp [hs]
      have him : s.im = -(2 * π * ξ) := by simp [hs]
      rw [hre, him, abs_neg, abs_of_pos hσ0, abs_of_nonneg (by positivity), hB]
      have : σ ≤ (k : ℝ) * ξ := by
        have : σ ≤ k := by rw [hσ]; linarith
        nlinarith
      nlinarith
    have hs0 : 0 < ‖s‖ := by
      refine norm_pos_iff.2 fun h => ?_
      have := congrArg Complex.re h; simp [hs] at this; linarith
    have he0 : 0 ≤ e := by rw [he, hσ]; linarith
    have hxe : ξ ^ e ≤ (1 + 2 * π * ξ) ^ e :=
      Real.rpow_le_rpow hξ0.le (by nlinarith [Real.pi_gt_three]) he0
    have h2 : c * ξ ^ e * Lw ≤ ‖fL f s‖ := by
      refine le_trans ?_ h1
      gcongr
    have hF : ‖Fs f σ ξ‖ = ‖fL f s‖ / ‖s‖ := by rw [Fs, norm_div]
    have h3 : c * ξ ^ e * Lw / (B * ξ) ≤ ‖Fs f σ ξ‖ := by
      rw [hF]
      calc c * ξ ^ e * Lw / (B * ξ) ≤ ‖fL f s‖ / (B * ξ) := by gcongr
        _ ≤ ‖fL f s‖ / ‖s‖ := div_le_div_of_nonneg_left (norm_nonneg _) hs0 hns
    have h4 : (c * ξ ^ e * Lw / (B * ξ)) ^ 2 ≤ ‖Fs f σ ξ‖ ^ 2 :=
      pow_le_pow_left₀ (by positivity) h3 2
    have hpow : (ξ ^ e) ^ 2 / ξ ^ 2 = ξ ^ q := by
      rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hξ0.le,
        ← Real.rpow_sub hξ0]
      congr 1; rw [hq, he, hσ]; push_cast; ring
    have hq0 : q ≤ 0 := by rw [hq]; linarith
    have hmono : (2 * Ξ) ^ q ≤ ξ ^ q := Real.rpow_le_rpow_of_nonpos hξ0 hξ.2 hq0
    have e5 : (c * ξ ^ e * Lw / (B * ξ)) ^ 2 = c ^ 2 / B ^ 2 * ((ξ ^ e) ^ 2 / ξ ^ 2) * Lw ^ 2 := by
      field_simp
    rw [e5, hpow] at h4
    have : c ^ 2 / B ^ 2 * (2 * Ξ) ^ q * Lw ^ 2 ≤ c ^ 2 / B ^ 2 * ξ ^ q * Lw ^ 2 := by gcongr
    simp only [hg]
    rw [← hLw]
    linarith
  -- integrate
  have hcontF := continuous_Fs f (by omega) hσ0
  have hgc : Continuous g := by
    simp only [hg]
    exact (((fL_entire f (by omega)).continuous.comp (by fun_prop)).norm.pow 2)
  have hint : c ^ 2 / B ^ 2 * (2 * Ξ) ^ q * ∫ ξ in Ξ..2 * Ξ, g ξ ≤
      ∫ ξ in Ξ..2 * Ξ, ‖Fs f σ ξ‖ ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on (by linarith)
      ((continuous_const.mul hgc).intervalIntegrable _ _)
      ((hcontF.norm.pow 2).intervalIntegrable _ _) hpt
  -- the first moment, after `y = 2πξ`
  have hsub : ∫ ξ in Ξ..2 * Ξ, g ξ =
      (2 * π)⁻¹ * ∫ y in (2 * π) * Ξ..(2 * π) * (2 * Ξ),
        ‖fL f ((σ' : ℂ) + (y : ℂ) * I)‖ ^ 2 := by
    have := intervalIntegral.integral_comp_mul_left (a := Ξ) (b := 2 * Ξ)
      (fun y : ℝ => ‖fL f ((σ' : ℂ) + (y : ℂ) * I)‖ ^ 2) (show (2 * π : ℝ) ≠ 0 by positivity)
    simp only [hg]
    rw [this, smul_eq_mul]
  have hYb : Y0 ≤ 2 * π * Ξ := by nlinarith [Real.pi_gt_three]
  have hfm' := hfm σ' (by rw [hσ', hσ]; linarith) (by rw [hσ', hσ]; linarith) (2 * π * Ξ) hYb
  have e2 : (2 * π) * (2 * Ξ) = 2 * (2 * π * Ξ) := by ring
  rw [e2] at hsub
  have hg_ge : c3 * Ξ ≤ ∫ ξ in Ξ..2 * Ξ, g ξ := by
    rw [hsub]
    have hpi : 0 < 2 * π := by positivity
    calc c3 * Ξ = (2 * π)⁻¹ * (c3 * (2 * π * Ξ)) := by field_simp
      _ ≤ _ := by gcongr
  have hΞ0 : 0 < 2 * Ξ := by linarith
  have hqsplit : (2 * Ξ) ^ q * Ξ = (2 * Ξ) ^ (-(4 * δ)) / 2 := by
    rw [hq, show (-1 - 4 * δ : ℝ) = -(4 * δ) + (-1) by ring, Real.rpow_add hΞ0,
      Real.rpow_neg_one]
    field_simp
  have hcoef : 0 ≤ c ^ 2 / B ^ 2 * (2 * Ξ) ^ q := by positivity
  calc c ^ 2 * c3 / (2 * B ^ 2) * (2 * Ξ) ^ (-(4 * δ))
      = c ^ 2 / B ^ 2 * c3 * ((2 * Ξ) ^ (-(4 * δ)) / 2) := by field_simp
    _ = c ^ 2 / B ^ 2 * (2 * Ξ) ^ q * (c3 * Ξ) := by rw [← hqsplit]; ring
    _ ≤ c ^ 2 / B ^ 2 * (2 * Ξ) ^ q * ∫ ξ in Ξ..2 * Ξ, g ξ := by gcongr
    _ ≤ _ := hint

end RamanujanTau.TauOmegaPartial
