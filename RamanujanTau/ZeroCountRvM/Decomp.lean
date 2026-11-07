/-
# Splitting `Λ'/Λ = −log 2π + ψ + L'/L` and identifying the zero count

* `phi_eq`: on `Re s > 0` with `L(Δ,s) ≠ 0`, `φ(s) = −log 2π + ψ(s) + L'/L(s)`.
* `gamma_cauchy`: Cauchy for `ψ` on `[6,σ₁] × [0,T]` moves the Gamma contribution to `Re s = 6`:
  `Re ∫₀ᵀ ψ(σ₁+iy) dy − Im ∫₆^{σ₁} ψ(x+iT) dx = ∫₀ᵀ Re ψ(6+iy) dy`.
* `sum_order_eq_zeroCount`: the zeros of `Λ` inside the rectangle, with multiplicity, are exactly
  `N(T) = zeroCount T` when `T` is not an ordinate.
-/
import RamanujanTau.ZeroCountRvM.Symmetry
import RamanujanTau.ZeroCountRvM.DigammaAsymp
import RamanujanTau.ZeroCount.Main

set_option autoImplicit false

namespace RamanujanTau.ZeroCountRvM

open Complex Set Filter Topology Metric intervalIntegral MeasureTheory
open RamanujanTau.HeckeL RamanujanTau.HeckeZeros RamanujanTau.ZeroCount
open scoped ComplexConjugate Real Interval

lemma ne_neg_nat_of_re_pos {s : ℂ} (hs : 0 < s.re) : ∀ n : ℕ, s ≠ -n := by
  intro n h
  have := congrArg Complex.re h
  simp at this
  linarith [Nat.cast_nonneg (α := ℝ) n]

lemma analyticAt_Gamma_of_re_pos {s : ℂ} (hs : 0 < s.re) : AnalyticAt ℂ Gamma s := by
  have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hd : DifferentiableOn ℂ Gamma {w : ℂ | 0 < w.re} := fun w hw =>
    (differentiableAt_Gamma w (ne_neg_nat_of_re_pos hw)).differentiableWithinAt
  exact hd.analyticAt (hopen.mem_nhds hs)

lemma differentiableAt_digamma {s : ℂ} (hs : 0 < s.re) : DifferentiableAt ℂ digamma s := by
  have han := analyticAt_Gamma_of_re_pos hs
  show DifferentiableAt ℂ (fun w => deriv Gamma w / Gamma w) s
  exact han.deriv.differentiableAt.div han.differentiableAt (Gamma_ne_zero_of_re_pos hs)

lemma lambda_factor_eq {s : ℂ} (hs : 0 < s.re) :
    heckeLambda =ᶠ[𝓝 s] fun w => ((2 * π : ℂ) ^ (-w) * Gamma w) * tauL w := by
  have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [hopen.mem_nhds hs] with w hw
  exact heckeLambda_eq_tauL (ne_neg_nat_of_re_pos hw)

lemma hasDerivAt_two_pi_cpow_neg (s : ℂ) :
    HasDerivAt (fun w : ℂ => (2 * π : ℂ) ^ (-w)) ((2 * π : ℂ) ^ (-s) * log (2 * π) * (-1)) s :=
  (hasDerivAt_id s).neg.const_cpow (Or.inl two_pi_ne_zero)

/-- **`φ = −log 2π + ψ + L'/L`.** -/
theorem phi_eq {s : ℂ} (hs : 0 < s.re) (hL : tauL s ≠ 0) :
    phi s = -(Real.log (2 * π) : ℂ) + digamma s + deriv tauL s / tauL s := by
  have heq := lambda_factor_eq hs
  have hc : (2 * π : ℂ) ^ (-s) ≠ 0 := two_pi_cpow_ne_zero _
  have hG : Gamma s ≠ 0 := Gamma_ne_zero_of_re_pos hs
  have hdc : DifferentiableAt ℂ (fun w : ℂ => (2 * π : ℂ) ^ (-w)) s :=
    (hasDerivAt_two_pi_cpow_neg s).differentiableAt
  have hdG : DifferentiableAt ℂ Gamma s := (analyticAt_Gamma_of_re_pos hs).differentiableAt
  unfold phi
  rw [logDeriv_apply, heq.deriv_eq, heq.eq_of_nhds, ← logDeriv_apply,
    logDeriv_mul (f := fun w : ℂ => (2 * π : ℂ) ^ (-w) * Gamma w) (g := tauL) s
      (mul_ne_zero hc hG) hL (hdc.mul hdG) (tauLSeries_entire s),
    logDeriv_mul (f := fun w : ℂ => (2 * π : ℂ) ^ (-w)) (g := Gamma) s hc hG hdc hdG, ← digamma_def, logDeriv_apply,
    (hasDerivAt_two_pi_cpow_neg s).deriv, logDeriv_apply]
  have hlog : log (2 * π : ℂ) = (Real.log (2 * π) : ℂ) := by
    rw [Complex.ofReal_log (by positivity)]; push_cast; rfl
  rw [hlog]
  field_simp

lemma deriv_Gamma_conj {s : ℂ} (hs : 0 < s.re) : deriv Gamma (conj s) = conj (deriv Gamma s) := by
  have h := ((analyticAt_Gamma_of_re_pos hs).differentiableAt.hasDerivAt).conj_conj
  have h2 : (conj ∘ Gamma ∘ conj) = Gamma := by
    funext w; simp [Function.comp, Complex.Gamma_conj]
  rw [h2] at h; exact h.deriv

lemma digamma_conj {s : ℂ} (hs : 0 < s.re) : digamma (conj s) = conj (digamma s) := by
  rw [digamma_def, logDeriv_apply, logDeriv_apply, deriv_Gamma_conj hs, Complex.Gamma_conj,
    map_div₀]

lemma continuous_digamma_vert {σ : ℝ} (hσ : 0 < σ) : Continuous fun y : ℝ => digamma (σ + y * I) := by
  rw [continuous_iff_continuousAt]
  intro y
  exact ContinuousAt.comp (g := digamma) (continuousAt_digamma (by simpa using hσ))
    (by fun_prop : ContinuousAt (fun y : ℝ => (σ : ℂ) + y * I) y)

lemma continuousOn_digamma_horiz {a b T : ℝ} (ha : 0 < a) :
    ContinuousOn (fun x : ℝ => digamma (x + T * I)) (Icc a b) := by
  intro x hx
  apply ContinuousAt.continuousWithinAt
  exact ContinuousAt.comp (g := digamma) (continuousAt_digamma (by simp; linarith [hx.1]))
    (by fun_prop : ContinuousAt (fun x : ℝ => (x : ℂ) + T * I) x)

/-- **Cauchy for `ψ`**: the Gamma contribution lives on `Re s = 6`. -/
theorem gamma_cauchy {σ₁ T : ℝ} (hσ : 6 ≤ σ₁) :
    (∫ y in (0 : ℝ)..T, digamma (σ₁ + y * I)).re - (∫ x in (6 : ℝ)..σ₁, digamma (x + T * I)).im =
      ∫ y in (0 : ℝ)..T, (digamma (6 + y * I)).re := by
  have hC : rectInt digamma 6 σ₁ 0 T = 0 := by
    apply rectInt_eq_zero
    intro z hz
    rw [mem_reProdIm, uIcc_of_le hσ] at hz
    exact (differentiableAt_digamma (by linarith [hz.1.1])).differentiableWithinAt
  unfold rectInt at hC
  simp only [ofReal_zero, zero_mul, add_zero, smul_eq_mul] at hC
  have hbot : (∫ x in (6 : ℝ)..σ₁, digamma (x : ℂ)).im = 0 := by
    have h1 : ∫ x in (6 : ℝ)..σ₁, digamma (x : ℂ) = conj (∫ x in (6 : ℝ)..σ₁, digamma (x : ℂ)) := by
      rw [← intervalIntegral_conj]
      apply intervalIntegral.integral_congr_ae
      filter_upwards [] with x hx
      rw [uIoc_of_le hσ] at hx
      rw [← digamma_conj (by simp; linarith [hx.1]), conj_ofReal]
    exact (Complex.conj_eq_iff_im.mp h1.symm)
  have hIm := congrArg Complex.im hC
  simp only [sub_im, add_im, mul_im, I_re, I_im, zero_mul, one_mul, zero_sub, zero_im,
    sub_zero, zero_add] at hIm
  have hre6 : (∫ y in (0 : ℝ)..T, digamma (6 + y * I)).re = ∫ y in (0 : ℝ)..T, (digamma (6 + y * I)).re := by
    have := Complex.reCLM.intervalIntegral_comp_comm
      ((continuous_digamma_vert (σ := 6) (by norm_num)).intervalIntegrable (μ := volume) 0 T)
    simp only [Complex.reCLM_apply, Complex.ofReal_ofNat] at this
    exact this.symm
  rw [← hre6]
  have h6 : ((6 : ℝ) : ℂ) = 6 := by norm_num
  rw [h6] at hIm
  linarith

/-- Orders of `Λ` and of `L(Δ,·)` agree on `Re s > 0`. -/
lemma order_lambda_eq_mult {u : ℂ} (hu : 0 < u.re) : analyticOrderNatAt heckeLambda u = mult u := by
  have heq := lambda_factor_eq hu
  have hhan : AnalyticAt ℂ (fun w : ℂ => (2 * π : ℂ) ^ (-w) * Gamma w) u := by
    have h1 : AnalyticAt ℂ (fun w : ℂ => (2 * π : ℂ) ^ (-w)) u := by
      have : Differentiable ℂ (fun w : ℂ => (2 * π : ℂ) ^ (-w)) :=
        fun w => (hasDerivAt_two_pi_cpow_neg w).differentiableAt
      exact this.analyticAt u
    exact h1.mul (analyticAt_Gamma_of_re_pos hu)
  have h0 : analyticOrderAt (fun w : ℂ => (2 * π : ℂ) ^ (-w) * Gamma w) u = 0 :=
    analyticOrderAt_eq_zero.mpr (Or.inr (mul_ne_zero (two_pi_cpow_ne_zero _)
      (Gamma_ne_zero_of_re_pos hu)))
  have hmul := analyticOrderAt_mul hhan (tauLSeries_entire.analyticAt u)
  rw [h0, zero_add] at hmul
  unfold mult analyticOrderNatAt
  rw [analyticOrderAt_congr heq]
  exact congrArg ENat.toNat hmul

lemma lambda_zero_iff {u : ℂ} (hu : 0 < u.re) : heckeLambda u = 0 ↔ tauL u = 0 := by
  rw [heckeLambda_eq_tauL (ne_neg_nat_of_re_pos hu)]
  simp [Gamma_ne_zero_of_re_pos hu]

/-- **The rectangle count is `N(T)`** for non-ordinates `T`. -/
theorem sum_order_eq_zeroCount {σ₁ T : ℝ} (hσ : 7 ≤ σ₁) (hT0 : 0 < T)
    (hnon : ∀ u : ℂ, tauL u = 0 → 11 / 2 < u.re → u.re < 13 / 2 → u.im ≠ T)
    (S : Finset ℂ)
    (hS : ∀ u, u ∈ S ↔ (heckeLambda u = 0 ∧ 12 - σ₁ < u.re ∧ u.re < σ₁ ∧ 0 < u.im ∧ u.im < T)) :
    ∑ u ∈ S, analyticOrderNatAt heckeLambda u = zeroCount T := by
  have hSeq : S = (zeroSet_finite 0 T).toFinset := by
    ext u
    rw [hS, Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨h0, h1, h2, h3, h4⟩
      have hre : 11 / 2 ≤ u.re := by
        by_contra h; push Not at h; exact heckeLambda_ne_zero_of_lt h h0
      have hpos : 0 < u.re := by linarith
      rw [zeroSet_eq_of_nonneg le_rfl]
      exact ⟨(lambda_zero_iff hpos).mp h0, h3, h4.le⟩
    · intro hu
      obtain ⟨h0, h1, h2, h3, h4⟩ := hu
      have hpos : 0 < u.re := by linarith
      refine ⟨(lambda_zero_iff hpos).mpr h0, by linarith, by linarith, h3,
        lt_of_le_of_ne h4 (hnon u h0 h1 h2)⟩
  unfold zeroCount zeroCountAB
  rw [← hSeq]
  apply Finset.sum_congr rfl
  intro u hu
  have h := (hS u).mp hu
  have hre : 11 / 2 ≤ u.re := by
    by_contra h'; push Not at h'; exact heckeLambda_ne_zero_of_lt h' h.1
  exact order_lambda_eq_mult (by linarith)

end RamanujanTau.ZeroCountRvM
