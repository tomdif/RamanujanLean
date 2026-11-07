/-
# The Riemann–von Mangoldt formula for `L(f,s)`, `f` any nonzero level-one cusp form

Let `n₀` be the first index with `a_f(n₀) ≠ 0` (`n₀ = 1` for eigenforms).  Then

  `N_f(T) = (T/π) log(T/(2π e n₀)) + O(log T)`         (`riemann_von_mangoldt_gen`).

The extra `−(T/π) log n₀` is genuine: `L(f,s) = a_f(n₀) n₀^{−s} G(s)` with `G → 1` as
`Re s → ∞`, so `arg L(f, σ₁+iT)` rotates like `−T log n₀`, on both vertical sides of the
rectangle (the left one by the functional equation).

Proof (`rvm_nonordinate_D`): `pi_count_eq_gen` (argument principle + symmetry `ρ ↦ k − ρ`),
`φ = −log(2π n₀) + ψ + G'/G` on `Re s > 0` (`phi_eq_gen`), Cauchy for `ψ` on `[k/2, σ₁] × [−T, T]`
(`gamma_cauchy_gen`), `∫₀ᵀ Re ψ(k/2+iy) dy = T log T − T + O(log T)` (`integral_re_digamma_nat`;
`k` is even), the vertical `G'/G` part `≤ π` (`Re G ≥ 3/4`), the horizontal ones `O(log T)`
(`backlund_gen` at heights `±T`).  A general `T` is moved to a non-ordinate in `(T, T+1)`.
-/
import RamanujanTau.GeneralZeros.Symmetry
import RamanujanTau.GeneralZeros.Backlund
import RamanujanTau.GeneralZeros.GammaPart

set_option autoImplicit false

namespace RamanujanTau.GeneralZeros

open Complex Set Filter Topology Metric intervalIntegral MeasureTheory ModularForm
open RamanujanTau.HeckeConvexGeneral RamanujanTau.ZeroCountRvM
open scoped ComplexConjugate Real Interval MatrixGroups

variable {k : ℕ}

/-! ### `φ = −log(2π n₀) + ψ + G'/G` -/

lemma Gn_ne_zero_of_Lam (f : CuspForm 𝒮ℒ (k : ℤ)) {n₀ : ℕ} (hn₀ : 1 ≤ n₀)
    (ha : coef f n₀ ≠ 0) {s : ℂ} (hs : 0 < s.re) (hΛ : heckeLambda f s ≠ 0) :
    Gn f n₀ s ≠ 0 := by
  intro h
  apply hΛ
  rw [heckeLambda_eq_fL f (NormData.ne_neg_nat_of_re_pos hs), fL_eq_of_Gn f hn₀ ha, h]
  simp

lemma logDeriv_cpow_div (n₀ : ℕ) (hn₀ : 1 ≤ n₀) (a : ℂ) (ha : a ≠ 0) (s : ℂ) :
    logDeriv (fun w : ℂ => (n₀ : ℂ) ^ w / a) s = (Real.log n₀ : ℂ) := by
  have hn : (n₀ : ℂ) ≠ 0 := by exact_mod_cast (show n₀ ≠ 0 by omega)
  have hd : HasDerivAt (fun w : ℂ => (n₀ : ℂ) ^ w / a) ((n₀ : ℂ) ^ s * log n₀ * 1 / a) s :=
    ((hasDerivAt_id s).const_cpow (Or.inl hn)).div_const a
  have hc : (n₀ : ℂ) ^ s ≠ 0 := by
    have := norm_natCast_cpow_pos_of_pos (n := n₀) (by omega) s
    exact norm_pos_iff.mp this
  rw [logDeriv_apply, hd.deriv]
  have hl : ((Real.log n₀ : ℝ) : ℂ) = log (n₀ : ℂ) := by
    rw [Complex.ofReal_log (Nat.cast_nonneg n₀)]; push_cast; rfl
  rw [hl]
  field_simp

/-- **`φ = −log(2π n₀) + ψ + G'/G`** on `Re s > 0`, away from the zeros. -/
theorem phi_eq_gen (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 1 ≤ k) {n₀ : ℕ} (hn₀ : 1 ≤ n₀)
    (ha : coef f n₀ ≠ 0) {s : ℂ} (hs : 0 < s.re) (hΛ : heckeLambda f s ≠ 0) :
    logDeriv (heckeLambda f) s = -((Real.log (2 * π) + Real.log n₀ : ℝ) : ℂ) + digamma s +
      deriv (Gn f n₀) s / Gn f n₀ s := by
  have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have heq : heckeLambda f =ᶠ[𝓝 s] fun w => ((2 * π : ℂ) ^ (-w) * Gamma w) * fL f w := by
    filter_upwards [hopen.mem_nhds hs] with w hw
    exact heckeLambda_eq_fL f (NormData.ne_neg_nat_of_re_pos hw)
  have hc : (2 * π : ℂ) ^ (-s) ≠ 0 := by rw [cpow_neg]; exact inv_ne_zero (two_pi_cpow_ne_zero _)
  have hG : Gamma s ≠ 0 := Gamma_ne_zero_of_re_pos hs
  have hL : fL f s ≠ 0 := by
    intro h; apply hΛ; rw [heq.eq_of_nhds, h, mul_zero]
  have hdc : DifferentiableAt ℂ (fun w : ℂ => (2 * π : ℂ) ^ (-w)) s :=
    (hasDerivAt_two_pi_cpow_neg s).differentiableAt
  have hdG : DifferentiableAt ℂ Gamma s := (analyticAt_Gamma_of_re_pos hs).differentiableAt
  have hdL : DifferentiableAt ℂ (fL f) s := fL_entire f hk s
  have hn : (n₀ : ℂ) ≠ 0 := by exact_mod_cast (show n₀ ≠ 0 by omega)
  have hP : (n₀ : ℂ) ^ s / coef f n₀ ≠ 0 := by
    have := norm_natCast_cpow_pos_of_pos (n := n₀) (by omega) s
    exact div_ne_zero (norm_pos_iff.mp this) ha
  have hdP : DifferentiableAt ℂ (fun w : ℂ => (n₀ : ℂ) ^ w / coef f n₀) s :=
    (((hasDerivAt_id s).const_cpow (Or.inl hn)).div_const _).differentiableAt
  -- `logDeriv G = log n₀ + logDeriv L`
  have hGn : logDeriv (Gn f n₀) s = (Real.log n₀ : ℂ) + logDeriv (fL f) s := by
    have : Gn f n₀ = fun w => ((n₀ : ℂ) ^ w / coef f n₀) * fL f w := rfl
    rw [this, logDeriv_mul (f := fun w : ℂ => (n₀ : ℂ) ^ w / coef f n₀) (g := fL f) s hP hL hdP hdL,
      logDeriv_cpow_div n₀ hn₀ _ ha]
  have h1 : logDeriv (heckeLambda f) s =
      logDeriv (fun w : ℂ => (2 * π : ℂ) ^ (-w) * Gamma w) s + logDeriv (fL f) s := by
    rw [logDeriv_apply, heq.deriv_eq, heq.eq_of_nhds, ← logDeriv_apply,
      logDeriv_mul (f := fun w : ℂ => (2 * π : ℂ) ^ (-w) * Gamma w) (g := fL f) s
        (mul_ne_zero hc hG) hL (hdc.mul hdG) hdL]
  have h2 : logDeriv (fun w : ℂ => (2 * π : ℂ) ^ (-w) * Gamma w) s =
      -(Real.log (2 * π) : ℂ) + digamma s := by
    rw [logDeriv_mul (f := fun w : ℂ => (2 * π : ℂ) ^ (-w)) (g := Gamma) s hc hG hdc hdG,
      ← digamma_def, logDeriv_apply, (hasDerivAt_two_pi_cpow_neg s).deriv]
    have hlog : log (2 * π : ℂ) = (Real.log (2 * π) : ℂ) := by
      rw [Complex.ofReal_log (by positivity)]; push_cast; rfl
    rw [hlog]
    field_simp
  rw [h1, h2, ← logDeriv_apply (Gn f n₀), hGn]
  push_cast
  ring

/-! ### The edge decompositions -/

lemma continuous_vert_logDeriv {G : ℂ → ℂ} (hG : Differentiable ℂ G) {σ : ℝ}
    (hne : ∀ y : ℝ, G (σ + y * I) ≠ 0) :
    Continuous fun y : ℝ => deriv G (σ + y * I) / G (σ + y * I) := by
  exact ((continuous_deriv_of_entire hG).comp (by fun_prop)).div
    (hG.continuous.comp (by fun_prop)) hne

lemma continuousOn_horiz_logDeriv {G : ℂ → ℂ} (hG : Differentiable ℂ G) {a b t : ℝ}
    (hne : ∀ x ∈ Icc a b, G (x + t * I) ≠ 0) :
    ContinuousOn (fun x : ℝ => deriv G (x + t * I) / G (x + t * I)) (Icc a b) :=
  (((continuous_deriv_of_entire hG).comp (by fun_prop)).continuousOn).div
    ((hG.continuous.comp (by fun_prop)).continuousOn) hne

/-- Vertical edge: `Re V = −2T c + Re ∫ψ + Re ∫ G'/G`. -/
lemma vert_decomp (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 1 ≤ k) (D : NormData f) (T : ℝ) :
    (∫ y in (-T)..T, logDeriv (heckeLambda f) (D.σ₁ + y * I)).re =
      -(2 * T) * (Real.log (2 * π) + Real.log D.n₀) +
      (∫ y in (-T)..T, digamma (D.σ₁ + y * I)).re +
      (∫ y in (-T)..T, deriv (Gn f D.n₀) (D.σ₁ + y * I) / Gn f D.n₀ (D.σ₁ + y * I)).re := by
  set c : ℂ := ((Real.log (2 * π) + Real.log D.n₀ : ℝ) : ℂ)
  have hσ0 : 0 < D.σ₁ := D.σ₁_pos
  have hGd := Gn_entire f hk D.hn₀
  have hne : ∀ y : ℝ, Gn f D.n₀ (D.σ₁ + y * I) ≠ 0 := fun y => D.Gn_ne_zero (by simp)
  have hψ := continuous_digamma_vert (σ := D.σ₁) hσ0
  have hℓ := continuous_vert_logDeriv hGd hne
  have h0 : ∫ y in (-T)..T, logDeriv (heckeLambda f) (D.σ₁ + y * I) =
      ∫ y in (-T)..T, ((-c + digamma (D.σ₁ + y * I)) +
        deriv (Gn f D.n₀) (D.σ₁ + y * I) / Gn f D.n₀ (D.σ₁ + y * I)) := by
    apply integral_congr; intro y _
    simp only []
    exact phi_eq_gen f hk D.hn₀ D.ha₀ (by simp; exact hσ0) (D.Lam_ne_zero_right (by simp))
  rw [h0, intervalIntegral.integral_add (f := fun y : ℝ => -c + digamma (D.σ₁ + y * I))
      (g := fun y : ℝ => deriv (Gn f D.n₀) (D.σ₁ + y * I) / Gn f D.n₀ (D.σ₁ + y * I))
      ((continuous_const.add hψ).intervalIntegrable _ _) (hℓ.intervalIntegrable _ _),
    intervalIntegral.integral_add (f := fun _ : ℝ => -c) (g := fun y : ℝ => digamma (D.σ₁ + y * I))
      (continuous_const.intervalIntegrable _ _) (hψ.intervalIntegrable _ _),
    intervalIntegral.integral_const]
  simp only [add_re, smul_re, neg_re, c, ofReal_re, smul_eq_mul]
  ring

/-- Horizontal edge: `Im H(t) = Im ∫ψ + Im ∫ G'/G`. -/
lemma horiz_decomp (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 1 ≤ k) (D : NormData f) {t : ℝ}
    (hne : ∀ x ∈ Icc ((k : ℝ) / 2) D.σ₁, heckeLambda f (x + t * I) ≠ 0) :
    (∫ x in ((k : ℝ) / 2)..D.σ₁, logDeriv (heckeLambda f) (x + t * I)).im =
      (∫ x in ((k : ℝ) / 2)..D.σ₁, digamma (x + t * I)).im +
      (∫ x in ((k : ℝ) / 2)..D.σ₁, deriv (Gn f D.n₀) (x + t * I) / Gn f D.n₀ (x + t * I)).im := by
  set c : ℂ := ((Real.log (2 * π) + Real.log D.n₀ : ℝ) : ℂ)
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkR : (0 : ℝ) < (k : ℝ) / 2 := by linarith
  have hle : (k : ℝ) / 2 ≤ D.σ₁ := by linarith [D.hσ₁]
  have hGd := Gn_entire f hk D.hn₀
  have hGne : ∀ x ∈ Icc ((k : ℝ) / 2) D.σ₁, Gn f D.n₀ (x + t * I) ≠ 0 := fun x hx =>
    Gn_ne_zero_of_Lam f D.hn₀ D.ha₀ (by simp; linarith [hx.1]) (hne x hx)
  have hψ := continuousOn_digamma_horiz (a := (k : ℝ) / 2) (b := D.σ₁) (T := t) hkR
  have hℓ := continuousOn_horiz_logDeriv hGd hGne
  have hiψ : IntervalIntegrable (fun x : ℝ => digamma (x + t * I)) volume ((k : ℝ) / 2) D.σ₁ :=
    (hψ.mono (by rw [uIcc_of_le hle])).intervalIntegrable
  have hiℓ : IntervalIntegrable (fun x : ℝ => deriv (Gn f D.n₀) (x + t * I) / Gn f D.n₀ (x + t * I))
      volume ((k : ℝ) / 2) D.σ₁ := (hℓ.mono (by rw [uIcc_of_le hle])).intervalIntegrable
  have h0 : ∫ x in ((k : ℝ) / 2)..D.σ₁, logDeriv (heckeLambda f) (x + t * I) =
      ∫ x in ((k : ℝ) / 2)..D.σ₁, ((-c + digamma (x + t * I)) +
        deriv (Gn f D.n₀) (x + t * I) / Gn f D.n₀ (x + t * I)) := by
    apply integral_congr; intro x hx
    rw [uIcc_of_le hle] at hx
    simp only []
    exact phi_eq_gen f hk D.hn₀ D.ha₀ (by simp; linarith [hx.1]) (hne x hx)
  rw [h0, intervalIntegral.integral_add (f := fun x : ℝ => -c + digamma (x + t * I))
      (g := fun x : ℝ => deriv (Gn f D.n₀) (x + t * I) / Gn f D.n₀ (x + t * I))
      ((continuous_const.intervalIntegrable _ _).add hiψ) hiℓ,
    intervalIntegral.integral_add (f := fun _ : ℝ => -c) (g := fun x : ℝ => digamma (x + t * I))
      (continuous_const.intervalIntegrable _ _) hiψ,
    intervalIntegral.integral_const]
  simp only [add_im, smul_im, neg_im, c, ofReal_im, smul_eq_mul, neg_zero, mul_zero, zero_add]

/-! ### Riemann–von Mangoldt at a non-ordinate -/

/-- Polynomial growth of `G` on a bounded vertical strip. -/
lemma Gn_growth (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 12 ≤ k) (D : NormData f) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s : ℂ, ((k : ℝ) - 1) / 2 ≤ s.re → s.re ≤ 2 * D.σ₁ →
      ‖Gn f D.n₀ s‖ ≤ B * (1 + ‖s‖) ^ 2 := by
  obtain ⟨B, hB0, hB⟩ := fL_growth f hk
  have ha : 0 < ‖coef f D.n₀‖ := norm_pos_iff.mpr D.ha₀
  have hn : (1 : ℝ) ≤ D.n₀ := by exact_mod_cast D.hn₀
  refine ⟨(D.n₀ : ℝ) ^ (2 * D.σ₁) / ‖coef f D.n₀‖ * B, by positivity, fun s h1 h2 => ?_⟩
  rw [norm_Gn f D.hn₀]
  have hp : (D.n₀ : ℝ) ^ s.re ≤ (D.n₀ : ℝ) ^ (2 * D.σ₁) := Real.rpow_le_rpow_of_exponent_le hn h2
  have hL := hB s h1
  have : (D.n₀ : ℝ) ^ s.re / ‖coef f D.n₀‖ ≤ (D.n₀ : ℝ) ^ (2 * D.σ₁) / ‖coef f D.n₀‖ :=
    div_le_div_of_nonneg_right hp ha.le
  calc (D.n₀ : ℝ) ^ s.re / ‖coef f D.n₀‖ * ‖fL f s‖
      ≤ (D.n₀ : ℝ) ^ (2 * D.σ₁) / ‖coef f D.n₀‖ * (B * (1 + ‖s‖) ^ 2) := by gcongr
    _ = _ := by ring

theorem rvm_nonordinate_D (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : f ≠ 0) (D : NormData f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T → (∀ u : ℂ, heckeLambda f u = 0 → u.im ≠ T) →
      |π * (zeroCount f T : ℝ) - (T * Real.log T - T - T * Real.log (2 * π * D.n₀))| ≤
        C * Real.log (T + 5) := by
  have hk := weight_ge f hf
  have hk1 : 1 ≤ k := by omega
  obtain ⟨m, hm⟩ := weight_even f hf
  have hm6 : 6 ≤ m := by omega
  have hκ : (k : ℝ) / 2 = (m : ℝ) := by rw [hm]; push_cast; ring
  have hkR : (12 : ℝ) ≤ k := by exact_mod_cast hk
  set σ₁ := D.σ₁ with hσ₁def
  have hσ₁ : ((k : ℝ) + 1) / 2 + 1 ≤ σ₁ := D.hσ₁
  have hGd := Gn_entire f hk1 D.hn₀
  obtain ⟨B, hB0, hB⟩ := Gn_growth f hk D
  obtain ⟨CB, hCB0, hCB⟩ := backlund_gen hGd (a := (k : ℝ) / 2) (σ₁ := σ₁) (B := B)
    (by linarith) (by linarith) hB0
    (fun s h1 h2 => hB s (by linarith) (by linarith))
    (fun y => by have := D.Gn_re_ge (s := (σ₁ : ℂ) + y * I) (by simp [hσ₁def]); linarith)
  set R : ℝ := (realCount f : ℝ) with hR
  have hR0 : 0 ≤ R := Nat.cast_nonneg _
  refine ⟨70 + 2 * m + π + CB + π * R, by positivity, fun T hT1 hnon => ?_⟩
  have hT0 : 0 < T := by linarith
  have hcount := pi_count_eq_gen f hf D hT0 hnon
  -- non-vanishing on the horizontal segments
  have hnon' : ∀ u : ℂ, heckeLambda f u = 0 → u.im ≠ -T := by
    intro u h0 h
    apply hnon ((k : ℂ) - u) (Lam_reflect_zero f hk1 h0)
    simp [h]
  have hne1 : ∀ x ∈ Icc ((k : ℝ) / 2) σ₁, heckeLambda f (x + T * I) ≠ 0 :=
    fun x _ h => hnon _ h (by simp)
  have hne2 : ∀ x ∈ Icc ((k : ℝ) / 2) σ₁, heckeLambda f (x + ((-T : ℝ) : ℂ) * I) ≠ 0 :=
    fun x _ h => hnon' _ h (by simp)
  have hGne : ∀ t : ℝ, (∀ x ∈ Icc ((k : ℝ) / 2) σ₁, heckeLambda f (x + t * I) ≠ 0) →
      ∀ x ∈ Icc ((k : ℝ) / 2) σ₁, Gn f D.n₀ (x + t * I) ≠ 0 := fun t ht x hx =>
    Gn_ne_zero_of_Lam f D.hn₀ D.ha₀ (by simp; linarith [hx.1]) (ht x hx)
  have hV := vert_decomp f hk1 D T
  have hH1 := horiz_decomp f hk1 D hne1
  have hH2 := horiz_decomp f hk1 D hne2
  have hB1 := hCB T (hGne T hne1)
  have hB2 := hCB (-T) (hGne (-T) hne2)
  rw [abs_neg, abs_of_pos hT0] at hB2
  rw [abs_of_pos hT0] at hB1
  have hvert := abs_re_integral_logDeriv_vert hGd (σ₁ := σ₁) (y₀ := -T) (y₁ := T) (by linarith)
    (fun y => by have := D.Gn_re_ge (s := (σ₁ : ℂ) + y * I) (by simp [hσ₁def]); linarith)
  have hcauchy := gamma_cauchy_gen (a := (k : ℝ) / 2) (σ₁ := σ₁) (y₀ := -T) (y₁ := T)
    (by linarith) (by linarith)
  have hsymm := integral_re_digamma_symm (a := (k : ℝ) / 2) (by linarith) T
  have hstir := integral_re_digamma_nat hm6 hT1
  have hκc : ((((k : ℝ) / 2 : ℝ)) : ℂ) = (m : ℂ) := by rw [hκ]; push_cast; rfl
  rw [hκc] at hsymm hcauchy
  -- rewrite `pi_count_eq_gen` in terms of the pieces
  have e2 : (∫ x in ((k : ℝ) / 2)..σ₁, logDeriv (heckeLambda f) (x + (-T) * I)) =
      ∫ x in ((k : ℝ) / 2)..σ₁, logDeriv (heckeLambda f) (x + ((-T : ℝ) : ℂ) * I) := by
    push_cast; rfl
  rw [← hσ₁def] at hV hH1 hH2
  rw [e2, hV, hH1, hH2] at hcount
  have e3 : (∫ x in ((k : ℝ) / 2)..σ₁, digamma (x + ((-T : ℝ) : ℂ) * I)) =
      ∫ x in ((k : ℝ) / 2)..σ₁, digamma (x + (-T : ℝ) * I) := rfl
  set Iψ := ∫ y in (0 : ℝ)..T, (digamma ((m : ℂ) + y * I)).re
  set Eℓ := (∫ y in (-T)..T, deriv (Gn f D.n₀) (σ₁ + y * I) / Gn f D.n₀ (σ₁ + y * I)).re
  set E1 := (∫ x in ((k : ℝ) / 2)..σ₁, deriv (Gn f D.n₀) (x + T * I) / Gn f D.n₀ (x + T * I)).im
  set E2 := (∫ x in ((k : ℝ) / 2)..σ₁,
    deriv (Gn f D.n₀) (x + ((-T : ℝ) : ℂ) * I) / Gn f D.n₀ (x + ((-T : ℝ) : ℂ) * I)).im
  have hkey : π * (2 * (zeroCount f T : ℝ) + R) =
      -(2 * T) * (Real.log (2 * π) + Real.log D.n₀) + 2 * Iψ + Eℓ - E1 + E2 := by
    rw [hcount]; linarith
  have hn1 : (1 : ℝ) ≤ D.n₀ := by exact_mod_cast D.hn₀
  have hlog2πn : Real.log (2 * π * D.n₀) = Real.log (2 * π) + Real.log D.n₀ := by
    rw [Real.log_mul (by positivity) (by linarith)]
  rw [hlog2πn]
  have hlog1 : 1 ≤ Real.log (T + 5) := by
    have h : Real.exp 1 ≤ T + 5 := by linarith [Real.exp_one_lt_d9]
    have := Real.log_le_log (Real.exp_pos 1) h
    rwa [Real.log_exp] at this
  have hlog25 : Real.log (T + 2) ≤ Real.log (T + 5) := Real.log_le_log (by linarith) (by linarith)
  have hE := abs_le.mp hvert
  have hE1 := abs_le.mp hB1
  have hE2 := abs_le.mp hB2
  have hS := abs_le.mp hstir
  have hpi := Real.pi_pos
  have hCBl : CB * Real.log (T + 2) ≤ CB * Real.log (T + 5) :=
    mul_le_mul_of_nonneg_left hlog25 hCB0
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  set L := Real.log (T + 5)
  have hb1 : 30 + 2 * ((m : ℝ) - 6) ≤ 30 * L + 2 * ((m : ℝ) * L) := by
    have := mul_le_mul_of_nonneg_left hlog1 (by positivity : (0 : ℝ) ≤ 30 + 2 * m)
    nlinarith
  have hb2 : π ≤ π * L := by
    have := mul_le_mul_of_nonneg_left hlog1 hpi.le
    linarith
  have hb3 : π * R ≤ π * R * L := by
    have := mul_le_mul_of_nonneg_left hlog1 (by positivity : (0 : ℝ) ≤ π * R)
    linarith
  clear_value Iψ Eℓ E1 E2
  clear hcount hV hH1 hH2 hcauchy hsymm hB hCB hGne hne1 hne2 hnon hnon' e2 e3 hvert hB1 hB2 hstir
  set A := Iψ - (T * Real.log T - T)
  have key : π * (zeroCount f T : ℝ) - (T * Real.log T - T - T * (Real.log (2 * π) +
      Real.log D.n₀)) = A + (Eℓ - E1 + E2) / 2 - π * R / 2 := by
    simp only [A]; linear_combination hkey / 2
  have hC : (70 + 2 * m + π + CB + π * R) * L =
      70 * L + 2 * ((m : ℝ) * L) + π * L + CB * L + π * R * L := by ring
  have hπR : 0 ≤ π * R := by positivity
  rw [key, hC, abs_le]
  constructor <;> linarith

/-- **Riemann–von Mangoldt at a non-ordinate**, with `n₀` the first nonzero index. -/
theorem rvm_nonordinate_gen (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : f ≠ 0) {n₀ : ℕ}
    (ha₀ : coef f n₀ ≠ 0) (hmin : ∀ n < n₀, coef f n = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T → (∀ u : ℂ, heckeLambda f u = 0 → u.im ≠ T) →
      |π * (zeroCount f T : ℝ) - (T * Real.log T - T - T * Real.log (2 * π * n₀))| ≤
        C * Real.log (T + 5) := by
  have hk1 : 1 ≤ k := by have := weight_ge f hf; omega
  obtain ⟨D, hD⟩ := exists_normData f hk1 ha₀ hmin
  have := rvm_nonordinate_D f hf D
  rw [hD] at this
  exact this

end RamanujanTau.GeneralZeros
