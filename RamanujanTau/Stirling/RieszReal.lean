/-
# Contour shift and Riesz means with a real growth exponent

Real-exponent versions of `RankinError.integral_line_eq` and
`RankinError.rieszAsymp_of_continuation`. The originals take `‖F‖ ≤ B(1+|t|)^K`, `K : ℕ`, and
return Riesz order `K+1`. Only integrability is needed: here `‖F‖ ≤ B(1+|t|)^r` with real
`r < k` gives `RieszAsymp a c₀ k (1 − σ₁)`, because `‖P_k F‖ ≪ (1+|t|)^{r−k−1}` and
`k + 1 − r > 1`.
-/
import RamanujanTau.RankinError.PerronShift

set_option autoImplicit false

namespace RamanujanTau.Stirling

open Complex Real MeasureTheory Set Filter Topology
open RamanujanTau.RankinError

lemma integrable_line_of_strip_rpow {p : ℝ} (hp : 1 < p) {g : ℂ → ℂ} {a b : ℝ}
    (hg : ContinuousOn g {s : ℂ | a ≤ s.re ∧ s.re ≤ b}) {C : ℝ}
    (hB : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖g s‖ ≤ C * (1 + |s.im|) ^ (-p)) {σ : ℝ}
    (h1 : a ≤ σ) (h2 : σ ≤ b) : Integrable fun y : ℝ => g (σ + y * I) := by
  have hc : Continuous fun y : ℝ => g (σ + y * I) :=
    hg.comp_continuous (by fun_prop) (fun y => by simp [h1, h2])
  have hi : Integrable (fun y : ℝ => C * (1 + ‖y‖) ^ (-p)) :=
    (integrable_one_add_norm (by simpa using hp)).const_mul C
  refine hi.mono' hc.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  simpa [Real.norm_eq_abs] using hB (σ + y * I) (by simp [h1]) (by simp [h2])

theorem integral_line_eq_rpow {p : ℝ} (hp : 1 < p) {g : ℂ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hg : DifferentiableOn ℂ g {s : ℂ | a ≤ s.re ∧ s.re ≤ b}) {C : ℝ}
    (hB : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖g s‖ ≤ C * (1 + |s.im|) ^ (-p)) :
    ∫ y : ℝ, g (b + y * I) = ∫ y : ℝ, g (a + y * I) := by
  have hia := integrable_line_of_strip_rpow hp hg.continuousOn hB le_rfl hab
  have hib := integrable_line_of_strip_rpow hp hg.continuousOn hB hab le_rfl
  -- vertical integrals over `[-T, T]`
  set Va : ℝ → ℂ := fun T => ∫ y in (-T)..T, g (a + y * I)
  set Vb : ℝ → ℂ := fun T => ∫ y in (-T)..T, g (b + y * I)
  have tVa : Tendsto Va atTop (𝓝 (∫ y : ℝ, g (a + y * I))) :=
    intervalIntegral_tendsto_integral hia tendsto_neg_atTop_atBot tendsto_id
  have tVb : Tendsto Vb atTop (𝓝 (∫ y : ℝ, g (b + y * I))) :=
    intervalIntegral_tendsto_integral hib tendsto_neg_atTop_atBot tendsto_id
  -- horizontal integrals
  set Hh : ℝ → ℂ := fun t => ∫ x in a..b, g (x + t * I)
  have hH : ∀ t : ℝ, ‖Hh t‖ ≤ C * (1 + |t|) ^ (-p) * |b - a| := by
    intro t
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    rw [uIoc_of_le hab] at hx
    simpa using hB (x + t * I) (by simp; linarith [hx.1]) (by simp; exact hx.2)
  have hdecay : Tendsto (fun t : ℝ => C * (1 + |t|) ^ (-p) * |b - a|) atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => 1 + |t|) atTop atTop :=
      tendsto_atTop_add_const_left _ _ (tendsto_abs_atTop_atTop)
    have := ((tendsto_rpow_neg_atTop (by linarith : 0 < p)).comp h1).const_mul C |>.mul_const |b - a|
    simpa [Function.comp_def] using this
  have tH : ∀ σ : ℝ → ℝ, Tendsto σ atTop atTop ∨ Tendsto σ atTop atBot →
      Tendsto (fun T => Hh (σ T)) atTop (𝓝 0) := by
    intro σ hσ
    have hd' : Tendsto (fun T => C * (1 + |σ T|) ^ (-p) * |b - a|) atTop (𝓝 0) := by
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


theorem rieszAsymp_of_continuation_rpow (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (ha0 : a 0 = 0) (k : ℕ)
    (hk : 1 ≤ k) {r : ℝ} (hr : r < k)
    {c σ₀ σ₁ c₀ B : ℝ} (hc : 1 < c) (h01 : σ₀ < σ₁) (hσ₁ : 0 < σ₁) (hσ₁c : σ₁ ≤ c)
    (hσ₁1 : σ₁ ≤ 1) (hsum : Summable fun n : ℕ => a n * (n : ℝ) ^ (-c))
    (F : ℂ → ℂ) (hF : DifferentiableOn ℂ F {s : ℂ | σ₀ < s.re})
    (hD : ∀ s : ℂ, s.re = c → LSeries (fun n => (a n : ℂ)) s = F s + c₀ / (s - 1))
    (hFB : ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ c → ‖F s‖ ≤ B * (1 + |s.im|) ^ r) :
    RieszAsymp a c₀ k (1 - σ₁) := by
  set p : ℝ := k + 1 - r with hpdef
  have hp : 1 < p := by rw [hpdef]; linarith
  have hc0 : 0 < c := by linarith
  set m : ℝ := min σ₁ 1 with hm
  set M : ℝ := k.factorial * (2 / m) ^ (k + 1) * |B| with hM
  have hM0 : 0 ≤ M := by positivity
  -- bound for `Pk * F` on the strip
  have hPF : ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ c → ‖Pk k s * F s‖ ≤ M * (1 + |s.im|) ^ (-p) := by
    intro s h1 h2
    have hP := norm_Pk_le k hσ₁ h1
    have hFs := hFB s h1 h2
    have ht : (0:ℝ) < 1 + |s.im| := by positivity
    rw [norm_mul]
    have hFs' : ‖F s‖ ≤ |B| * (1 + |s.im|) ^ r :=
      hFs.trans (mul_le_mul_of_nonneg_right (le_abs_self B) (by positivity))
    have hsplit : (1 + |s.im|) ^ r / (1 + |s.im|) ^ (k + 1) = (1 + |s.im|) ^ (-p) := by
      rw [← Real.rpow_natCast, ← Real.rpow_sub ht, hpdef]; push_cast; ring_nf
    calc ‖Pk k s‖ * ‖F s‖ ≤ (k.factorial * (2 / m) ^ (k + 1) / (1 + |s.im|) ^ (k + 1)) *
          (|B| * (1 + |s.im|) ^ r) := mul_le_mul hP hFs' (norm_nonneg _) (by positivity)
      _ = M * ((1 + |s.im|) ^ r / (1 + |s.im|) ^ (k + 1)) := by
          rw [hM]; field_simp
      _ = M * (1 + |s.im|) ^ (-p) := by rw [hsplit]
  -- the error integral
  have hI : Integrable fun y : ℝ => M * (1 + |y|) ^ (-p) := by
    have := (integrable_one_add_norm (E := ℝ) (μ := volume) (r := p) (by simpa using hp)).const_mul M
    simpa [Real.norm_eq_abs] using this
  set I₀ : ℝ := ∫ y : ℝ, M * (1 + |y|) ^ (-p) with hI₀
  refine ⟨(I₀ / (2 * π) + |c₀|), fun x hx => ?_⟩
  rcases lt_or_ge x 1 with hx1 | hx1
  · -- `x < 1`
    rw [W_eq_zero_of_lt_one a k hx1, zero_sub, abs_neg]
    have hI0 : 0 ≤ I₀ := integral_nonneg fun y => by positivity
    have hxe : x ^ (k + 1) ≤ x ^ ((k : ℝ) + 1 - (1 - σ₁)) := by
      rw [← Real.rpow_natCast]
      apply Real.rpow_le_rpow_of_exponent_ge hx hx1.le
      push_cast; linarith
    have h1 : |c₀ * x ^ (k + 1) / (k + 1)| ≤ |c₀| * x ^ (k + 1) := by
      rw [abs_div, abs_mul, abs_of_pos (by positivity : (0:ℝ) < x ^ (k + 1)),
        abs_of_pos (by positivity : (0:ℝ) < k + 1)]
      apply div_le_self (by positivity)
      have : (0:ℝ) ≤ k := Nat.cast_nonneg k; linarith
    calc _ ≤ |c₀| * x ^ (k + 1) := h1
      _ ≤ |c₀| * x ^ ((k : ℝ) + 1 - (1 - σ₁)) := mul_le_mul_of_nonneg_left hxe (abs_nonneg _)
      _ ≤ (I₀ / (2 * π) + |c₀|) * x ^ ((k : ℝ) + 1 - (1 - σ₁)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have : 0 ≤ I₀ / (2 * π) := by positivity
          linarith
  · -- `x ≥ 1`
    have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
    have hsumc : Summable fun n : ℕ => a n * (n : ℝ) ^ (-c) := hsum
    have hP := perron_riesz a ha ha0 hk hc hx hsumc
    -- integrability of the two pieces on the line `c`
    have hcont_line : ∀ σ : ℝ, σ₁ ≤ σ → σ ≤ c →
        Continuous fun y : ℝ => (x : ℂ) ^ ln σ y * (Pk k (ln σ y) * F (ln σ y)) := by
      intro σ h1 h2
      have hσ0 : 0 < σ := by linarith
      refine (Continuous.const_cpow (by fun_prop) (Or.inl hx0)).mul
        ((continuous_Pk_line k hσ0).mul ?_)
      exact hF.continuousOn.comp_continuous (by fun_prop) (fun y => by simp [ln]; linarith)
    have hbound_line : ∀ σ : ℝ, σ₁ ≤ σ → σ ≤ c → ∀ y : ℝ,
        ‖(x : ℂ) ^ ln σ y * (Pk k (ln σ y) * F (ln σ y))‖ ≤ x ^ σ * (M * (1 + |y|) ^ (-p)) := by
      intro σ h1 h2 y
      rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hx]
      have := hPF (ln σ y) (by simp [ln, h1]) (by simp [ln, h2])
      simp only [ln, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
        sub_self, add_zero, add_im, mul_im, zero_add] at this ⊢
      exact mul_le_mul_of_nonneg_left this (by positivity)
    have hint_line : ∀ σ : ℝ, σ₁ ≤ σ → σ ≤ c →
        Integrable fun y : ℝ => (x : ℂ) ^ ln σ y * (Pk k (ln σ y) * F (ln σ y)) := by
      intro σ h1 h2
      exact (hI.const_mul (x ^ σ)).mono' (hcont_line σ h1 h2).aestronglyMeasurable
        (Eventually.of_forall (hbound_line σ h1 h2))
    have hint_main : Integrable fun y : ℝ =>
        (x : ℂ) ^ ln c y * (Pk k (ln c y) * (c₀ / (ln c y - 1))) := by
      have hP1 := integrable_Pk_line hk hc0
      have hmeas : AEStronglyMeasurable (fun y : ℝ =>
          (x : ℂ) ^ ln c y * (Pk k (ln c y) * (c₀ / (ln c y - 1)))) := by
        refine Continuous.aestronglyMeasurable ?_
        refine (Continuous.const_cpow (by fun_prop) (Or.inl hx0)).mul
          ((continuous_Pk_line k hc0).mul (continuous_const.div (by fun_prop) ?_))
        intro y h; have := congrArg re h; simp [ln] at this; linarith
      refine (hP1.norm.const_mul (x ^ c * (|c₀| / (c - 1)))).mono' hmeas
        (Eventually.of_forall fun y => ?_)
      rw [norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos hx, norm_div, Complex.norm_real,
        Real.norm_eq_abs]
      have hre : (ln c y).re = c := by simp [ln]
      rw [hre]
      have hge : c - 1 ≤ ‖ln c y - 1‖ := by
        have := Complex.abs_re_le_norm (ln c y - 1)
        simp [ln] at this
        rw [abs_of_pos (by linarith)] at this; exact this
      have : |c₀| / ‖ln c y - 1‖ ≤ |c₀| / (c - 1) :=
        div_le_div_of_nonneg_left (abs_nonneg _) (by linarith) hge
      have h0 : 0 ≤ ‖Pk k (ln c y)‖ := norm_nonneg _
      calc x ^ c * (‖Pk k (ln c y)‖ * (|c₀| / ‖ln c y - 1‖))
          ≤ x ^ c * (‖Pk k (ln c y)‖ * (|c₀| / (c - 1))) := by gcongr
        _ = x ^ c * (|c₀| / (c - 1)) * ‖Pk k (ln c y)‖ := by ring
    -- split the Perron integral
    have hsplit : ∫ y : ℝ, (x : ℂ) ^ ln c y * Pk k (ln c y) *
        LSeries (fun n => (a n : ℂ)) (ln c y) =
        (∫ y : ℝ, (x : ℂ) ^ ln c y * (Pk k (ln c y) * F (ln c y))) +
        ∫ y : ℝ, (x : ℂ) ^ ln c y * (Pk k (ln c y) * (c₀ / (ln c y - 1))) := by
      rw [← integral_add (hint_line c hσ₁c le_rfl) hint_main]
      congr 1; funext y
      rw [hD (ln c y) (by simp [ln])]; ring
    -- the main term
    have hmain : ∫ y : ℝ, (x : ℂ) ^ ln c y * (Pk k (ln c y) * (c₀ / (ln c y - 1))) =
        (c₀ * x / (k + 1) : ℂ) * (2 * π * phi (k + 1) (1 / x)) := by
      have hinv := mellinInv_Pk (k := k + 1) (by omega) (σ := c - 1) (by linarith)
        (u := 1 / x) (by positivity)
      unfold mellinInv at hinv
      rw [Complex.real_smul] at hinv
      have h2π : (2 * π : ℂ) ≠ 0 := by
        have := Real.pi_pos; exact_mod_cast (by positivity : (2 * π : ℝ) ≠ 0)
      have e : ∀ y : ℝ, (x : ℂ) ^ ln c y * (Pk k (ln c y) * (c₀ / (ln c y - 1))) =
          (c₀ * x / (k + 1) : ℂ) * ((((1 / x : ℝ) : ℂ) ^ (-((c - 1 : ℝ) + y * I))) •
            Pk (k + 1) ((c - 1 : ℝ) + y * I)) := by
        intro y
        have hre : 1 < (ln c y).re := by simp [ln]; linarith
        have hdiv := Pk_div_sub_one k hre
        rw [cpow_div_neg zero_le_one hx, smul_eq_mul]
        have hl : ((c - 1 : ℝ) : ℂ) + y * I = ln c y - 1 := by simp [ln]; ring
        rw [hl, ofReal_one, one_cpow, one_mul]
        have hxs : (x : ℂ) ^ ln c y = x * (x : ℂ) ^ (ln c y - 1) := by
          rw [cpow_sub _ _ hx0, cpow_one]; field_simp
        have hk1 : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
        have hs1 : ln c y - 1 ≠ 0 := by
          intro h; have := congrArg re h; simp [ln] at this; linarith
        have hdiv' : Pk (k + 1) (ln c y - 1) = ((k : ℂ) + 1) * (Pk k (ln c y) / (ln c y - 1)) := by
          rw [hdiv]; field_simp
        rw [hxs, hdiv']
        field_simp
      have hJ : ∫ y : ℝ, (((1 / x : ℝ) : ℂ) ^ (-((c - 1 : ℝ) + y * I))) •
          Pk (k + 1) ((c - 1 : ℝ) + y * I) = (2 * π : ℂ) * (phi (k + 1) (1 / x) : ℂ) := by
        rw [← hinv, ← mul_assoc]
        rw [show (2 * π : ℂ) * ((1 / (2 * π) : ℝ) : ℂ) = 1 by push_cast; field_simp, one_mul]
      simp_rw [e]
      rw [integral_const_mul, hJ]
    -- the contour shift for the error term
    have hshift : ∫ y : ℝ, (x : ℂ) ^ ln c y * (Pk k (ln c y) * F (ln c y)) =
        ∫ y : ℝ, (x : ℂ) ^ ln σ₁ y * (Pk k (ln σ₁ y) * F (ln σ₁ y)) := by
      have hdiff : DifferentiableOn ℂ (fun s : ℂ => (x : ℂ) ^ s * (Pk k s * F s))
          {s : ℂ | σ₁ ≤ s.re ∧ s.re ≤ c} := by
        intro s hs
        have h0 : 0 < s.re := by linarith [hs.1]
        refine DifferentiableWithinAt.mul ?_ (DifferentiableWithinAt.mul ?_ ?_)
        · exact (DifferentiableAt.const_cpow differentiableAt_id (Or.inl hx0)).differentiableWithinAt
        · exact ((differentiableOn_Pk k) s h0).mono (fun t ht => by simp at ht ⊢; linarith [ht.1])
        · exact (hF s (by simp; linarith [hs.1])).mono (fun t ht => by simp at ht ⊢; linarith [ht.1])
      have hB' : ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ c →
          ‖(x : ℂ) ^ s * (Pk k s * F s)‖ ≤ (x ^ c * M) * (1 + |s.im|) ^ (-p) := by
        intro s h1 h2
        rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hx, mul_assoc]
        exact mul_le_mul (Real.rpow_le_rpow_of_exponent_le hx1 h2) (hPF s h1 h2)
          (norm_nonneg _) (by positivity)
      exact integral_line_eq_rpow hp hσ₁c hdiff hB'
    have herr : ‖∫ y : ℝ, (x : ℂ) ^ ln σ₁ y * (Pk k (ln σ₁ y) * F (ln σ₁ y))‖ ≤ x ^ σ₁ * I₀ := by
      calc _ ≤ ∫ y : ℝ, x ^ σ₁ * (M * (1 + |y|) ^ (-p)) :=
            norm_integral_le_of_norm_le (hI.const_mul _)
              (Eventually.of_forall (hbound_line σ₁ le_rfl hσ₁c))
        _ = x ^ σ₁ * I₀ := by rw [integral_const_mul]
    -- assemble
    rw [hsplit, hmain, hshift] at hP
    set E : ℂ := ∫ y : ℝ, (x : ℂ) ^ ln σ₁ y * (Pk k (ln σ₁ y) * F (ln σ₁ y)) with hE
    set R : ℝ := ∑' n : ℕ, a n * phi k (n / x) with hR
    have hRc : (∑' n : ℕ, (a n : ℂ) * phi k (n / x)) = (R : ℂ) := by
      rw [hR, ofReal_tsum]; push_cast; rfl
    rw [hRc] at hP
    have hphi : phi (k + 1) (1 / x) = (1 - 1 / x) ^ (k + 1) :=
      phi_of_le ((div_le_one hx).2 hx1)
    -- `R - c₀ x (1-1/x)^{k+1}/(k+1) = E / (2π)`
    have hRe : |R - c₀ * x * (1 - 1 / x) ^ (k + 1) / (k + 1)| ≤ x ^ σ₁ * I₀ / (2 * π) := by
      have h2π : (2 * π : ℂ) ≠ 0 := by
        have := Real.pi_pos; exact_mod_cast (by positivity : (2 * π : ℝ) ≠ 0)
      have hEq : ((R - c₀ * x * (1 - 1 / x) ^ (k + 1) / (k + 1) : ℝ) : ℂ) = E / (2 * π) := by
        rw [hphi] at hP
        rw [eq_div_iff h2π]
        push_cast
        push_cast at hP
        linear_combination hP
      have : |R - c₀ * x * (1 - 1 / x) ^ (k + 1) / (k + 1)| = ‖E‖ / (2 * π) := by
        rw [← Real.norm_eq_abs, ← Complex.norm_real, hEq, norm_div]
        congr 1
        rw [show (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (by positivity)]
      rw [this]
      exact div_le_div_of_nonneg_right herr (by positivity)
    -- from `R` to `W`
    rw [W_eq_tsum a ha0 hk hx, ← hR]
    have h1x : 0 ≤ 1 - 1 / x := by rw [sub_nonneg]; exact (div_le_one hx).2 hx1
    have hbern : 1 - (1 - 1 / x) ^ (k + 1) ≤ (k + 1) * (1 / x) := by
      have := (pow_succ_sub_bounds k h1x (h := 1 / x) (by positivity)).2
      rw [sub_add_cancel, one_pow, one_pow, mul_one] at this
      linarith
    have hpow_le : (1 - 1 / x) ^ (k + 1) ≤ 1 := pow_le_one₀ h1x (by
      have : 0 < 1 / x := by positivity
      linarith)
    have hxk : x ^ k * x ^ σ₁ = x ^ ((k : ℝ) + 1 - (1 - σ₁)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hx]; congr 1; ring
    have hxk2 : x ^ k ≤ x ^ ((k : ℝ) + 1 - (1 - σ₁)) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    have hk1 : (0:ℝ) < k + 1 := by positivity
    -- the main-term discrepancy
    have hdisc : |c₀ * x * (1 - 1 / x) ^ (k + 1) / (k + 1) - c₀ * x / (k + 1)| ≤ |c₀| := by
      have : c₀ * x * (1 - 1 / x) ^ (k + 1) / (k + 1) - c₀ * x / (k + 1) =
          -(c₀ * x * (1 - (1 - 1 / x) ^ (k + 1)) / (k + 1)) := by ring
      rw [this, abs_neg, abs_div, abs_mul, abs_mul, abs_of_pos hx, abs_of_pos hk1,
        abs_of_nonneg (show (0:ℝ) ≤ 1 - (1 - 1 / x) ^ (k + 1) by linarith)]
      rw [div_le_iff₀ hk1]
      have : x * (1 - (1 - 1 / x) ^ (k + 1)) ≤ k + 1 := by
        have := mul_le_mul_of_nonneg_left hbern hx.le
        rw [show x * ((k + 1) * (1 / x)) = k + 1 by field_simp] at this
        exact this
      calc |c₀| * x * (1 - (1 - 1 / x) ^ (k + 1)) = |c₀| * (x * (1 - (1 - 1 / x) ^ (k + 1))) := by
            ring
        _ ≤ |c₀| * (k + 1) := mul_le_mul_of_nonneg_left this (abs_nonneg _)
    have hfin : |R - c₀ * x / (k + 1)| ≤ x ^ σ₁ * I₀ / (2 * π) + |c₀| := by
      have := abs_add_le (R - c₀ * x * (1 - 1 / x) ^ (k + 1) / (k + 1))
        (c₀ * x * (1 - 1 / x) ^ (k + 1) / (k + 1) - c₀ * x / (k + 1))
      rw [show R - c₀ * x * (1 - 1 / x) ^ (k + 1) / (k + 1) +
        (c₀ * x * (1 - 1 / x) ^ (k + 1) / (k + 1) - c₀ * x / (k + 1)) =
        R - c₀ * x / (k + 1) by ring] at this
      linarith
    have heq : x ^ k * R - c₀ * x ^ (k + 1) / (k + 1) = x ^ k * (R - c₀ * x / (k + 1)) := by
      ring
    rw [heq, abs_mul, abs_of_pos (by positivity)]
    have hxσ : 1 ≤ x ^ σ₁ := Real.one_le_rpow hx1 hσ₁.le
    calc x ^ k * |R - c₀ * x / (k + 1)| ≤ x ^ k * (x ^ σ₁ * I₀ / (2 * π) + |c₀|) :=
          mul_le_mul_of_nonneg_left hfin (by positivity)
      _ = (I₀ / (2 * π)) * (x ^ k * x ^ σ₁) + |c₀| * x ^ k := by ring
      _ ≤ (I₀ / (2 * π)) * (x ^ k * x ^ σ₁) + |c₀| * (x ^ k * x ^ σ₁) := by
          have : x ^ k ≤ x ^ k * x ^ σ₁ := le_mul_of_one_le_right (by positivity) hxσ
          have hI0 : 0 ≤ I₀ := integral_nonneg fun y => by positivity
          nlinarith [abs_nonneg c₀]
      _ = (I₀ / (2 * π) + |c₀|) * x ^ ((k : ℝ) + 1 - (1 - σ₁)) := by rw [← hxk]; ring

end RamanujanTau.Stirling

#print axioms RamanujanTau.Stirling.integral_line_eq_rpow
#print axioms RamanujanTau.Stirling.rieszAsymp_of_continuation_rpow
