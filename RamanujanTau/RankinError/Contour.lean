/-
# Shifting a vertical line of integration

`integral_line_eq`: if `g` is holomorphic on the closed strip `a ≤ Re s ≤ b` and
`‖g s‖ ≤ C / (1 + |Im s|)²` there, then `∫ g(b + iy) dy = ∫ g(a + iy) dy`.
(Cauchy on rectangles `[a,b] × [-T,T]`, `T → ∞`.)
-/
import RamanujanTau.RankinError.RieszKernel

set_option autoImplicit false

namespace RamanujanTau.RankinError

open Complex Real MeasureTheory Set Filter Topology

lemma integrable_line_of_strip {g : ℂ → ℂ} {a b : ℝ}
    (hg : ContinuousOn g {s : ℂ | a ≤ s.re ∧ s.re ≤ b}) {C : ℝ}
    (hB : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖g s‖ ≤ C / (1 + |s.im|) ^ 2) {σ : ℝ}
    (h1 : a ≤ σ) (h2 : σ ≤ b) : Integrable fun y : ℝ => g (σ + y * I) := by
  have hc : Continuous fun y : ℝ => g (σ + y * I) :=
    hg.comp_continuous (by fun_prop) (fun y => by simp [h1, h2])
  refine integrable_of_le_div_sq hc (C := C) (fun y => ?_)
  simpa using hB (σ + y * I) (by simp [h1]) (by simp [h2])

theorem integral_line_eq {g : ℂ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hg : DifferentiableOn ℂ g {s : ℂ | a ≤ s.re ∧ s.re ≤ b}) {C : ℝ}
    (hB : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖g s‖ ≤ C / (1 + |s.im|) ^ 2) :
    ∫ y : ℝ, g (b + y * I) = ∫ y : ℝ, g (a + y * I) := by
  have hia := integrable_line_of_strip hg.continuousOn hB le_rfl hab
  have hib := integrable_line_of_strip hg.continuousOn hB hab le_rfl
  -- vertical integrals over `[-T, T]`
  set Va : ℝ → ℂ := fun T => ∫ y in (-T)..T, g (a + y * I)
  set Vb : ℝ → ℂ := fun T => ∫ y in (-T)..T, g (b + y * I)
  have tVa : Tendsto Va atTop (𝓝 (∫ y : ℝ, g (a + y * I))) :=
    intervalIntegral_tendsto_integral hia tendsto_neg_atTop_atBot tendsto_id
  have tVb : Tendsto Vb atTop (𝓝 (∫ y : ℝ, g (b + y * I))) :=
    intervalIntegral_tendsto_integral hib tendsto_neg_atTop_atBot tendsto_id
  -- horizontal integrals
  set Hh : ℝ → ℂ := fun t => ∫ x in a..b, g (x + t * I)
  have hH : ∀ t : ℝ, ‖Hh t‖ ≤ C / (1 + |t|) ^ 2 * |b - a| := by
    intro t
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    rw [uIoc_of_le hab] at hx
    simpa using hB (x + t * I) (by simp; linarith [hx.1]) (by simp; exact hx.2)
  have hdecay : Tendsto (fun t : ℝ => C / (1 + |t|) ^ 2 * |b - a|) atTop (𝓝 0) := by
    have : Tendsto (fun t : ℝ => (1 + |t|) ^ 2) atTop atTop := by
      have h1 : Tendsto (fun t : ℝ => 1 + |t|) atTop atTop :=
        tendsto_atTop_add_const_left _ _ (tendsto_abs_atTop_atTop)
      exact h1.atTop_mul_atTop₀ h1 |>.congr (fun t => by ring)
    have := (this.const_div_atTop C).mul_const |b - a|
    simpa using this
  have tH : ∀ σ : ℝ → ℝ, Tendsto σ atTop atTop ∨ Tendsto σ atTop atBot →
      Tendsto (fun T => Hh (σ T)) atTop (𝓝 0) := by
    intro σ hσ
    have hd' : Tendsto (fun T => C / (1 + |σ T|) ^ 2 * |b - a|) atTop (𝓝 0) := by
      rcases hσ with hσ | hσ
      · exact hdecay.comp hσ
      · have : Tendsto (fun T => -σ T) atTop atTop := tendsto_neg_atBot_atTop.comp hσ
        have := hdecay.comp this
        simpa [Function.comp_def, abs_neg] using this
    exact squeeze_zero_norm (fun T => hH (σ T)) hd'
  have tHtop := tH (fun T => T) (Or.inl tendsto_id)
  have tHbot := tH (fun T => -T) (Or.inr tendsto_neg_atTop_atBot)
  -- Cauchy's theorem on each rectangle
  have hrect : ∀ T : ℝ, 0 ≤ T → Hh (-T) - Hh T + I • Vb T - I • Va T = 0 := by
    intro T hT
    have hsub : Set.uIcc a b ×ℂ Set.uIcc (-T) T ⊆ {s : ℂ | a ≤ s.re ∧ s.re ≤ b} := by
      intro s hs
      rw [mem_reProdIm] at hs
      have := hs.1
      rw [uIcc_of_le hab] at this
      exact ⟨this.1, this.2⟩
    have := Complex.integral_boundary_rect_eq_zero_of_differentiableOn g ⟨a, -T⟩ ⟨b, T⟩
      (hg.mono hsub)
    simpa [Hh, Va, Vb] using this
  have hlim : Tendsto (fun T => I • (Vb T - Va T)) atTop (𝓝 0) := by
    have : Tendsto (fun T => Hh T - Hh (-T)) atTop (𝓝 0) := by
      simpa using tHtop.sub tHbot
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with T hT
    have := hrect T hT
    simp only [smul_eq_mul] at this ⊢
    linear_combination -this
  have hlim2 : Tendsto (fun T => I • (Vb T - Va T)) atTop
      (𝓝 (I • ((∫ y : ℝ, g (b + y * I)) - ∫ y : ℝ, g (a + y * I)))) :=
    (tVb.sub tVa).const_smul I
  have := tendsto_nhds_unique hlim2 hlim
  rw [smul_eq_mul, mul_eq_zero] at this
  rcases this with h | h
  · exact absurd h I_ne_zero
  · exact sub_eq_zero.1 h

end RamanujanTau.RankinError
