/-
# Short intervals contain zeros: gaps `≪ t^{1/2+ε}`

For `0 < ε < 1/2` there are `K, T₀` such that every interval `[t₀ − K t₀^{1/2+ε}, t₀ + K t₀^{1/2+ε}]`
with `t₀ ≥ T₀` contains a zero of `Z(t) = Λ(Δ, 6+it)`.

Suppose not, put `h = K t₀^{1/2+ε}`, `α = π/2 − 1/t₀`, `w(t) = e^{αt} tri_h(t − t₀)`.  Then `Z` has one
sign on the support of `w`, so `|∫ Z w| = ∫ |Z| w`.

* upper bound (`Window`): `|∫ Z w| ≤ 2π M h / cos⁶α ≤ 2π M h (π t₀/2)⁶`;
* lower bound: on `|t − t₀| ≤ h/2`, `w ≥ e^{πt/2} e^{−2} h/2` and Stirling gives
  `|Z(t)| e^{πt/2} ≥ c t^{11/2} |L(Δ,6+it)|`; then `∫ |L| ≥ |∫ L| ≥ h/2 − K₁ (1+2t₀)^{1/2+ε}`
  (`Contour`).

Comparing: `h/2 ≤ K₁(3t₀)^{1/2+ε} + C t₀^{1/2}`, false for `K` large.
-/
import RamanujanTau.HardyCount.Window
import RamanujanTau.HardyCount.Contour

set_option autoImplicit false

namespace RamanujanTau.HardyCount

open Complex MeasureTheory Set Filter
open RamanujanTau.HeckeL RamanujanTau.HardyZeros
open scoped Real

/-- A continuous function without zeros on `[a,b]` has one sign there. -/
lemma const_sign {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ} (h0 : ∀ t ∈ Icc a b, f t ≠ 0) :
    (∀ t ∈ Icc a b, 0 < f t) ∨ (∀ t ∈ Icc a b, f t < 0) := by
  by_contra hc
  push Not at hc
  obtain ⟨⟨x, hx, hfx⟩, ⟨y, hy, hfy⟩⟩ := hc
  have hivt := intermediate_value_uIcc (a := x) (b := y) hf.continuousOn
  have h0mem : (0 : ℝ) ∈ uIcc (f x) (f y) := by
    rw [mem_uIcc]; left; exact ⟨hfx, hfy⟩
  obtain ⟨z, hz, hfz⟩ := hivt h0mem
  exact h0 z (uIcc_subset_Icc hx hy hz) hfz

/-- `|∫ f w| = ∫ |f| w` when `w ≥ 0` vanishes off `[a,b]` and `f` has one sign on `[a,b]`. -/
lemma abs_integral_eq_of_sign {f w : ℝ → ℝ} {a b : ℝ} (hw0 : ∀ t, 0 ≤ w t)
    (hw : ∀ t ∉ Icc a b, w t = 0)
    (hs : (∀ t ∈ Icc a b, 0 < f t) ∨ (∀ t ∈ Icc a b, f t < 0)) :
    |∫ t, f t * w t| = ∫ t, |f t| * w t := by
  have hnn : 0 ≤ ∫ t, |f t| * w t := integral_nonneg fun t => mul_nonneg (abs_nonneg _) (hw0 t)
  rcases hs with hs | hs
  · have : ∀ t, f t * w t = |f t| * w t := by
      intro t
      by_cases ht : t ∈ Icc a b
      · rw [abs_of_pos (hs t ht)]
      · rw [hw t ht]; simp
    rw [integral_congr_ae (Eventually.of_forall this), abs_of_nonneg hnn]
  · have : ∀ t, f t * w t = -(|f t| * w t) := by
      intro t
      by_cases ht : t ∈ Icc a b
      · rw [abs_of_neg (hs t ht)]; ring
      · rw [hw t ht]; simp
    rw [integral_congr_ae (Eventually.of_forall this), integral_neg, abs_neg, abs_of_nonneg hnn]

/-- The Stirling constant `c_Z = (√π/3) e^{−10} (2π)^{−6}`. -/
noncomputable def cZ : ℝ := Real.sqrt π / 3 * Real.exp (-10) * (2 * π) ^ (-6 : ℝ)

lemma cZ_pos : 0 < cZ := by unfold cZ; positivity

/-- **Stirling lower bound for `Z`**: `c_Z t^{11/2} |L(Δ,6+it)| ≤ |Z(t)| e^{πt/2}` for `t ≥ 0`. -/
lemma Zr_lower {t : ℝ} (ht : 0 ≤ t) :
    cZ * t ^ (11 / 2 : ℝ) * ‖tauL (6 + t * I)‖ ≤ |Zr t| * Real.exp (π * t / 2) := by
  have hs : ∀ n : ℕ, (6 + t * I : ℂ) ≠ -n :=
    RamanujanTau.HeckeZeros.ne_neg_nat_of_re_pos (by simp)
  have hZ : |Zr t| = ‖(2 * π : ℂ) ^ (-(6 + t * I))‖ * ‖Complex.Gamma (6 + t * I)‖ *
      ‖tauL (6 + t * I)‖ := by
    rw [← norm_Zc_eq, Zc, heckeLambda_eq_tauL hs, norm_mul, norm_mul]
  have h2π : ‖(2 * π : ℂ) ^ (-(6 + t * I))‖ = (2 * π) ^ (-6 : ℝ) := by
    have e : (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) := by push_cast; rfl
    rw [e, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    congr 1; simp
  have hΓ := RamanujanTau.Stirling.stirling_le_norm_Gamma (σ := 6) (by norm_num) t
  have e6 : ((6 : ℝ) : ℂ) = 6 := by push_cast; rfl
  rw [e6] at hΓ
  have hT : t ^ (11 / 2 : ℝ) ≤ ‖(3 / 2 : ℂ) + t * I‖ ^ ((6 : ℝ) - 1 / 2) := by
    have h1 : t ≤ ‖(3 / 2 : ℂ) + t * I‖ := by
      have := Complex.abs_im_le_norm ((3 / 2 : ℂ) + t * I)
      simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im] at this
      have e : (3 / 2 : ℂ).im = 0 := by norm_num
      rw [e] at this
      simp at this
      exact (le_abs_self t).trans this
    rw [show (6 : ℝ) - 1 / 2 = 11 / 2 by norm_num]
    exact Real.rpow_le_rpow ht h1 (by norm_num)
  have hE : Real.exp (-(π * |t|) / 2) * Real.exp (π * t / 2) = 1 := by
    rw [abs_of_nonneg ht, ← Real.exp_add]; ring_nf; simp
  rw [hZ, h2π]
  have hL0 := norm_nonneg (tauL (6 + t * I))
  have hp0 : 0 ≤ (2 * π) ^ (-6 : ℝ) := by positivity
  calc cZ * t ^ (11 / 2 : ℝ) * ‖tauL (6 + t * I)‖
      = (2 * π) ^ (-6 : ℝ) * (Real.sqrt π / 3 * Real.exp (-10) * t ^ (11 / 2 : ℝ) *
          (Real.exp (-(π * |t|) / 2) * Real.exp (π * t / 2))) * ‖tauL (6 + t * I)‖ := by
        rw [hE, cZ]; ring
    _ ≤ (2 * π) ^ (-6 : ℝ) * (Real.sqrt π / 3 * Real.exp (-10) *
          ‖(3 / 2 : ℂ) + t * I‖ ^ ((6 : ℝ) - 1 / 2) *
          (Real.exp (-(π * |t|) / 2) * Real.exp (π * t / 2))) * ‖tauL (6 + t * I)‖ := by
        gcongr
    _ = (2 * π) ^ (-6 : ℝ) * ((Real.sqrt π / 3 * Real.exp (-10) *
          ‖(3 / 2 : ℂ) + t * I‖ ^ ((6 : ℝ) - 1 / 2) * Real.exp (-(π * |t|) / 2)) *
          Real.exp (π * t / 2)) * ‖tauL (6 + t * I)‖ := by ring
    _ ≤ (2 * π) ^ (-6 : ℝ) * (‖Complex.Gamma (6 + t * I)‖ * Real.exp (π * t / 2)) *
          ‖tauL (6 + t * I)‖ := by gcongr
    _ = _ := by ring

lemma rhs_identity (M h t₀ Q R c p : ℝ) (hc : c ≠ 0) (hp : p ≠ 0) (h6 : t₀ ^ 6 = Q * R) :
    2 * π * M * h * (π * t₀ / 2) ^ 6 =
      h / 2 * Real.exp (-2) * c * (Q / p) * (π ^ 7 * M / 16 * p * Real.exp 2 / c * R) := by
  have hE : Real.exp (-2) * Real.exp 2 = 1 := by rw [← Real.exp_add]; simp
  have e1 : h / 2 * Real.exp (-2) * c * (Q / p) * (π ^ 7 * M / 16 * p * Real.exp 2 / c * R) =
      h / 2 * (Real.exp (-2) * Real.exp 2) * Q * (π ^ 7 * M / 16) * R := by
    field_simp
  rw [e1, hE, div_pow, mul_pow, h6]
  ring

set_option maxHeartbeats 1000000 in
/-- **Zeros in short intervals.** -/
theorem Zr_zero_near {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1 / 2) :
    ∃ K T₀ : ℝ, 0 < K ∧ 1 ≤ T₀ ∧ ∀ t₀ : ℝ, T₀ ≤ t₀ →
      ∃ t ∈ Icc (t₀ - K * t₀ ^ (1 / 2 + ε)) (t₀ + K * t₀ ^ (1 / 2 + ε)), Zr t = 0 := by
  set θ : ℝ := 1 / 2 + ε with hθ
  have hθ1 : θ < 1 := by rw [hθ]; linarith
  have hθ0 : 1 / 2 < θ := by rw [hθ]; linarith
  obtain ⟨M, hM0, hM⟩ := abs_integral_Zr_exp_tri_le
  obtain ⟨K₁, hK₁0, hK₁⟩ := norm_integral_tauL_ge hε0 hε1.le
  set C₃ : ℝ := π ^ 7 * M / 16 * (2 : ℝ) ^ (11 / 2 : ℝ) * Real.exp 2 / cZ with hC₃
  have hC₃0 : 0 ≤ C₃ := by have := cZ_pos; rw [hC₃]; positivity
  set K : ℝ := 2 * (3 * K₁ + C₃) + 1 with hK
  have hKpos : 0 < K := by rw [hK]; positivity
  set T₀ : ℝ := max 1 (K ^ (1 / (1 - θ))) with hT₀
  refine ⟨K, T₀, hKpos, le_max_left _ _, fun t₀ ht₀ => ?_⟩
  have ht₀1 : 1 ≤ t₀ := (le_max_left _ _).trans ht₀
  have ht₀pos : 0 < t₀ := by linarith
  set h : ℝ := K * t₀ ^ θ with hh
  have hpθ : 0 < t₀ ^ θ := Real.rpow_pos_of_pos ht₀pos θ
  have hhpos : 0 < h := by rw [hh]; exact mul_pos hKpos hpθ
  -- `h ≤ t₀`
  have hht : h ≤ t₀ := by
    have h1 : K ≤ t₀ ^ (1 - θ) := by
      have hK' : K = (K ^ (1 / (1 - θ))) ^ (1 - θ) := by
        rw [← Real.rpow_mul hKpos.le, one_div, inv_mul_cancel₀ (by linarith), Real.rpow_one]
      rw [hK']
      exact Real.rpow_le_rpow (by positivity) ((le_max_right _ _).trans ht₀) (by linarith)
    have h2 : t₀ ^ (1 - θ) * t₀ ^ θ = t₀ := by
      rw [← Real.rpow_add ht₀pos]; simp
    rw [hh]
    calc K * t₀ ^ θ ≤ t₀ ^ (1 - θ) * t₀ ^ θ := by gcongr
      _ = t₀ := h2
  by_contra hno
  push Not at hno
  have hsign := const_sign continuous_Zr hno
  -- the weight
  set α : ℝ := π / 2 - 1 / t₀ with hα
  have hinv : 1 / t₀ ≤ 1 := by rw [div_le_one ht₀pos]; exact ht₀1
  have hinvpos : 0 < 1 / t₀ := by positivity
  have hα0 : 0 ≤ α := by rw [hα]; linarith [Real.pi_gt_three]
  have hαπ : α < π / 2 := by rw [hα]; linarith
  set w : ℝ → ℝ := fun t => Real.exp (α * t) * tri h (t - t₀) with hw
  have hw0 : ∀ t, 0 ≤ w t := fun t => mul_nonneg (Real.exp_pos _).le (tri_nonneg _ _)
  have hwsupp : ∀ t ∉ Icc (t₀ - h) (t₀ + h), w t = 0 := by
    intro t ht
    have : h ≤ |t - t₀| := by
      by_contra hc
      push Not at hc
      exact ht ⟨by linarith [(abs_lt.mp hc).1], by linarith [(abs_lt.mp hc).2]⟩
    simp [hw, tri_of_le_abs this]
  have hEq := abs_integral_eq_of_sign hw0 hwsupp hsign
  have hup := hM α hα0 hαπ h hhpos.le t₀
  have hI : (∫ t, Zr t * w t) = ∫ t, Zr t * Real.exp (α * t) * tri h (t - t₀) := by
    simp only [hw, mul_assoc]
  rw [hI] at hEq
  rw [hEq] at hup
  -- `cos α ≥ 2/(π t₀)`
  have hcos : 2 / π * (1 / t₀) ≤ Real.cos α := by
    rw [hα, Real.cos_pi_div_two_sub]
    exact Real.mul_le_sin hinvpos.le (by linarith [Real.pi_gt_three])
  have hcpos : 0 < 2 / π * (1 / t₀) := by positivity
  have hup2 : ∫ t, |Zr t| * w t ≤ 2 * π * M * h * (π * t₀ / 2) ^ 6 := by
    refine hup.trans ?_
    have hc6 : (2 / π * (1 / t₀)) ^ 6 ≤ Real.cos α ^ 6 := pow_le_pow_left₀ hcpos.le hcos 6
    rw [div_le_iff₀ (pow_pos (hcpos.trans_le hcos) 6)]
    have e : (π * t₀ / 2) ^ 6 * (2 / π * (1 / t₀)) ^ 6 = 1 := by
      rw [← mul_pow]; field_simp
    calc 2 * π * M * h = 2 * π * M * h * ((π * t₀ / 2) ^ 6 * (2 / π * (1 / t₀)) ^ 6) := by
          rw [e, mul_one]
      _ ≤ 2 * π * M * h * ((π * t₀ / 2) ^ 6 * Real.cos α ^ 6) := by gcongr
      _ = _ := by ring
  -- lower bound
  set a' : ℝ := t₀ - h / 2 with ha'
  set b' : ℝ := t₀ + h / 2 with hb'
  have hab' : a' ≤ b' := by rw [ha', hb']; linarith
  have ha'0 : t₀ / 2 ≤ a' := by rw [ha']; linarith
  have hb'2 : b' ≤ 2 * t₀ := by rw [hb']; linarith
  set P : ℝ := (t₀ / 2) ^ (11 / 2 : ℝ) with hP
  have hP0 : 0 < P := Real.rpow_pos_of_pos (by linarith) _
  have hcontL : Continuous fun t : ℝ => ‖tauL (6 + t * I)‖ :=
    (tauLSeries_entire.continuous.comp (by fun_prop)).norm
  have hcontW : Continuous fun t => |Zr t| * w t := by
    simp only [hw]
    exact continuous_Zr.abs.mul ((by fun_prop : Continuous fun t => Real.exp (α * t)).mul
      ((continuous_tri h).comp (by fun_prop)))
  have hintW : Integrable fun t => |Zr t| * w t := by
    refine ((Zr_integrable hα0 hαπ).norm.mul_const h).mono' hcontW.aestronglyMeasurable
      (Eventually.of_forall fun t => ?_)
    simp only [hw, Real.norm_eq_abs, abs_mul, abs_abs, abs_of_pos (Real.exp_pos _),
      abs_of_nonneg (tri_nonneg _ _)]
    rw [mul_assoc]
    gcongr
    exact tri_le _ _ hhpos.le
  have hpt : ∀ t ∈ uIcc a' b', h / 2 * Real.exp (-2) * cZ * P * ‖tauL (6 + t * I)‖ ≤
      |Zr t| * w t := by
    intro t ht
    rw [uIcc_of_le hab'] at ht
    have ht0 : t₀ / 2 ≤ t := ha'0.trans ht.1
    have htpos : 0 ≤ t := by linarith
    have htri : h / 2 ≤ tri h (t - t₀) := by
      have habs : |t - t₀| ≤ h / 2 := by
        rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
      rw [tri_of_abs_le (by linarith)]; linarith
    have hexp : Real.exp (π * t / 2) * Real.exp (-2) ≤ Real.exp (α * t) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have : t / t₀ ≤ 2 := by rw [div_le_iff₀ ht₀pos]; linarith [ht.2]
      have e : α * t = π * t / 2 - t / t₀ := by rw [hα]; field_simp
      rw [e]; linarith
    have hPt : P ≤ t ^ (11 / 2 : ℝ) := Real.rpow_le_rpow (by linarith) ht0 (by norm_num)
    have hlow := Zr_lower htpos
    have hL0 := norm_nonneg (tauL (6 + t * I))
    have hcz := cZ_pos
    have hZ0 := abs_nonneg (Zr t)
    calc h / 2 * Real.exp (-2) * cZ * P * ‖tauL (6 + t * I)‖
        ≤ h / 2 * Real.exp (-2) * (cZ * t ^ (11 / 2 : ℝ) * ‖tauL (6 + t * I)‖) := by
          have : cZ * P * ‖tauL (6 + t * I)‖ ≤ cZ * t ^ (11 / 2 : ℝ) * ‖tauL (6 + t * I)‖ := by
            gcongr
          calc h / 2 * Real.exp (-2) * cZ * P * ‖tauL (6 + t * I)‖
              = h / 2 * Real.exp (-2) * (cZ * P * ‖tauL (6 + t * I)‖) := by ring
            _ ≤ _ := by gcongr
      _ ≤ h / 2 * Real.exp (-2) * (|Zr t| * Real.exp (π * t / 2)) := by gcongr
      _ = |Zr t| * ((Real.exp (π * t / 2) * Real.exp (-2)) * (h / 2)) := by ring
      _ ≤ |Zr t| * (Real.exp (α * t) * tri h (t - t₀)) := by
          gcongr
  have hlow1 : (∫ t in a'..b', h / 2 * Real.exp (-2) * cZ * P * ‖tauL (6 + t * I)‖) ≤
      ∫ t, |Zr t| * w t := by
    calc (∫ t in a'..b', h / 2 * Real.exp (-2) * cZ * P * ‖tauL (6 + t * I)‖)
        ≤ ∫ t in a'..b', |Zr t| * w t :=
          intervalIntegral.integral_mono_on hab'
            ((hcontL.const_mul _).intervalIntegrable _ _) (hcontW.intervalIntegrable _ _)
            fun t ht => hpt t (by rw [uIcc_of_le hab']; exact ht)
      _ = ∫ t in Ioc a' b', |Zr t| * w t := intervalIntegral.integral_of_le hab'
      _ ≤ ∫ t, |Zr t| * w t := setIntegral_le_integral hintW
          (Eventually.of_forall fun t => mul_nonneg (abs_nonneg _) (hw0 t))
  have hLint : ‖∫ t in a'..b', tauL (6 + t * I)‖ ≤ ∫ t in a'..b', ‖tauL (6 + t * I)‖ :=
    intervalIntegral.norm_integral_le_integral_norm hab'
  have hK1 := hK₁ a' b' (by linarith) hab'
  have hba : b' - a' = h := by rw [ha', hb']; ring
  rw [hba] at hK1
  rw [intervalIntegral.integral_const_mul] at hlow1
  -- combine
  have hcomb : h / 2 * Real.exp (-2) * cZ * P * (h / 2 - K₁ * (1 + b') ^ θ) ≤
      2 * π * M * h * (π * t₀ / 2) ^ 6 := by
    have hpos : 0 ≤ h / 2 * Real.exp (-2) * cZ * P := by have := cZ_pos; positivity
    calc h / 2 * Real.exp (-2) * cZ * P * (h / 2 - K₁ * (1 + b') ^ θ)
        ≤ h / 2 * Real.exp (-2) * cZ * P * ∫ t in a'..b', ‖tauL (6 + t * I)‖ := by
          gcongr; exact hK1.trans hLint
      _ ≤ _ := hlow1.trans hup2
  -- simplify: divide by `h/2 · e^{-2} cZ P`
  have hPdef : P = t₀ ^ (11 / 2 : ℝ) / 2 ^ (11 / 2 : ℝ) := by
    rw [hP, Real.div_rpow ht₀pos.le (by norm_num)]
  have h6 : t₀ ^ 6 = t₀ ^ (11 / 2 : ℝ) * t₀ ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add ht₀pos, ← Real.rpow_natCast]; norm_num
  have hQ : 0 < t₀ ^ (11 / 2 : ℝ) := Real.rpow_pos_of_pos ht₀pos _
  have h2p : 0 < (2 : ℝ) ^ (11 / 2 : ℝ) := by positivity
  have hkey : h / 2 - K₁ * (1 + b') ^ θ ≤ C₃ * t₀ ^ (1 / 2 : ℝ) := by
    have hcz := cZ_pos
    have hE2 : Real.exp (-2) * Real.exp 2 = 1 := by rw [← Real.exp_add]; simp
    rw [hPdef] at hcomb
    have hrhs : 2 * π * M * h * (π * t₀ / 2) ^ 6 =
        h / 2 * Real.exp (-2) * cZ * (t₀ ^ (11 / 2 : ℝ) / 2 ^ (11 / 2 : ℝ)) *
          (C₃ * t₀ ^ (1 / 2 : ℝ)) := by
      rw [hC₃]
      exact rhs_identity M h t₀ _ _ cZ _ hcz.ne' h2p.ne' h6
    rw [hrhs] at hcomb
    have hpos : 0 < h / 2 * Real.exp (-2) * cZ * (t₀ ^ (11 / 2 : ℝ) / 2 ^ (11 / 2 : ℝ)) := by
      positivity
    exact le_of_mul_le_mul_left hcomb hpos
  -- `(1 + b')^θ ≤ 3 t₀^θ` and `t₀^{1/2} ≤ t₀^θ`
  have hb3 : (1 + b') ^ θ ≤ 3 * t₀ ^ θ := by
    calc (1 + b') ^ θ ≤ (3 * t₀) ^ θ := Real.rpow_le_rpow (by linarith) (by linarith) (by linarith)
      _ = 3 ^ θ * t₀ ^ θ := Real.mul_rpow (by norm_num) ht₀pos.le
      _ ≤ 3 * t₀ ^ θ := by
          gcongr
          calc (3 : ℝ) ^ θ ≤ 3 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hθ1.le
            _ = 3 := Real.rpow_one 3
  have hhalf : t₀ ^ (1 / 2 : ℝ) ≤ t₀ ^ θ := Real.rpow_le_rpow_of_exponent_le ht₀1 hθ0.le
  have hfinal : h ≤ 2 * (3 * K₁ + C₃) * t₀ ^ θ := by
    have h1 : K₁ * (1 + b') ^ θ ≤ K₁ * (3 * t₀ ^ θ) := by gcongr
    have h2 : C₃ * t₀ ^ (1 / 2 : ℝ) ≤ C₃ * t₀ ^ θ := by gcongr
    linarith
  have : h = (2 * (3 * K₁ + C₃) + 1) * t₀ ^ θ := by rw [hh, hK]
  linarith

end RamanujanTau.HardyCount
