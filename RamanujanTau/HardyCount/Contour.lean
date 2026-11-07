/-
# Lower bound for `|∫ₐᵇ L(Δ, 6+it) dt|`

* On a line `Re s = σ₁` far to the right, `L(Δ,s) = 1 + ∑_{n≥2} τ(n) n^{−s}` with
  `∑_{n≥2} |τ(n)| n^{−σ₁} ≤ 1/2`, so `Re L(Δ, σ₁+it) ≥ 1/2` (`re_tauL_right_ge`).
* Convexity, uniformly for `σ ≥ 6`: `‖L(Δ,σ+it)‖ ≤ C (1+|t|)^{1/2+ε}` (`tauL_right_half_bound`).
* Cauchy's theorem on the rectangle `[6,σ₁] × [a,b]` then gives
  `|∫ₐᵇ L(Δ,6+it) dt| ≥ (b−a)/2 − K (1+b)^{1/2+ε}` (`norm_integral_tauL_ge`).
-/
import RamanujanTau.HeckeConvex.Main

set_option autoImplicit false

namespace RamanujanTau.HardyCount

open Complex MeasureTheory Set Filter
open RamanujanTau.HeckeL RamanujanTau.HeckeConvex
open scoped Real

/-- `Re L(Δ, σ₁ + it) ≥ 1/2` on some line `Re s = σ₁ ≥ 7`. -/
theorem re_tauL_right_ge : ∃ σ₁ : ℝ, 7 ≤ σ₁ ∧ ∀ y : ℝ, 1 / 2 ≤ (tauL (σ₁ + y * I)).re := by
  have hsum7 : LSeriesSummable tauC (7 : ℂ) := LSeriesSummable_tau_of_gt_13_2 (by norm_num)
  set S : ℝ := ∑' n, ‖LSeries.term tauC 7 n‖ with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun _ => norm_nonneg _
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < 1 / (2 * (S + 1)) by positivity)
    (show (1 / 2 : ℝ) < 1 by norm_num)
  refine ⟨7 + k, by linarith [Nat.cast_nonneg (α := ℝ) k], fun y => ?_⟩
  set s : ℂ := ((7 + k : ℝ) : ℂ) + y * I with hs
  have hsre : s.re = 7 + k := by simp [hs]
  have hsum : LSeriesSummable tauC s := LSeriesSummable_tau_of_gt_13_2 (by rw [hsre]; linarith [Nat.cast_nonneg (α := ℝ) k])
  rw [tauL_eq_LSeries_of_gt (by rw [hsre]; linarith [Nat.cast_nonneg (α := ℝ) k]), LSeries,
    hsum.tsum_eq_add_tsum_ite 1]
  have h1 : LSeries.term tauC s 1 = 1 := by
    rw [LSeries.term_def]; simp [tauC, RamanujanTau.tau_one]
  rw [h1]
  -- bound the rest
  have hpt : ∀ n : ℕ, ‖(if n = 1 then 0 else LSeries.term tauC s n)‖ ≤
      (1 / 2) ^ k * ‖LSeries.term tauC 7 n‖ := by
    intro n
    split_ifs with hn1
    · simp only [norm_zero]; positivity
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · subst hn0; simp
    have hn2 : (2 : ℝ) ≤ n := by
      have : 2 ≤ n := by omega
      exact_mod_cast this
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq, if_neg (by omega), if_neg (by omega), hsre]
    have e7 : ((7 : ℂ)).re = 7 := by norm_num
    rw [e7]
    have hnp : (0 : ℝ) < n := by linarith
    have hsplit : (n : ℝ) ^ ((7 : ℝ) + k) = (n : ℝ) ^ (7 : ℝ) * (n : ℝ) ^ k := by
      rw [Real.rpow_add hnp, Real.rpow_natCast]
    rw [hsplit]
    have hnk : (2 : ℝ) ^ k ≤ (n : ℝ) ^ k := pow_le_pow_left₀ (by norm_num) hn2 k
    have h7 : 0 < (n : ℝ) ^ (7 : ℝ) := Real.rpow_pos_of_pos hnp _
    have hk2 : (1 / 2 : ℝ) ^ k = 1 / 2 ^ k := by rw [div_pow, one_pow]
    rw [hk2]
    have h2k : (0 : ℝ) < 2 ^ k := by positivity
    rw [div_le_iff₀ (by positivity)]
    calc ‖tauC n‖ = ‖tauC n‖ / (n : ℝ) ^ (7 : ℝ) * (n : ℝ) ^ (7 : ℝ) := by field_simp
      _ ≤ 1 / 2 ^ k * (‖tauC n‖ / (n : ℝ) ^ (7 : ℝ)) * ((n : ℝ) ^ (7 : ℝ) * (n : ℝ) ^ k) := by
        rw [show 1 / 2 ^ k * (‖tauC n‖ / (n : ℝ) ^ (7 : ℝ)) * ((n : ℝ) ^ (7 : ℝ) * (n : ℝ) ^ k) =
          (‖tauC n‖ / (n : ℝ) ^ (7 : ℝ) * (n : ℝ) ^ (7 : ℝ)) * ((n : ℝ) ^ k / 2 ^ k) by
            field_simp]
        have : 1 ≤ (n : ℝ) ^ k / 2 ^ k := by rw [le_div_iff₀ h2k]; linarith
        have h0 : 0 ≤ ‖tauC n‖ / (n : ℝ) ^ (7 : ℝ) * (n : ℝ) ^ (7 : ℝ) := by positivity
        nlinarith
  have hsum7' : Summable fun n => (1 / 2 : ℝ) ^ k * ‖LSeries.term tauC 7 n‖ :=
    hsum7.norm.mul_left _
  have hrest : ‖∑' n : ℕ, (if n = 1 then 0 else LSeries.term tauC s n)‖ ≤ 1 / 2 := by
    have hnorm : Summable fun n : ℕ => ‖(if n = 1 then 0 else LSeries.term tauC s n)‖ :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpt hsum7'
    refine (norm_tsum_le_tsum_norm hnorm).trans ?_
    refine (Summable.tsum_le_tsum hpt hnorm hsum7').trans ?_
    rw [tsum_mul_left, ← hS]
    have : (1 / 2 : ℝ) ^ k * (S + 1) ≤ 1 / 2 := by
      have := hk.le
      rw [le_div_iff₀ (by positivity)] at this
      linarith
    nlinarith
  have hre := Complex.abs_re_le_norm (∑' n : ℕ, (if n = 1 then 0 else LSeries.term tauC s n))
  rw [Complex.add_re, Complex.one_re]
  have := neg_abs_le (∑' n : ℕ, (if n = 1 then 0 else LSeries.term tauC s n)).re
  linarith

/-- **Convexity, uniformly to the right of the critical line.** -/
theorem tauL_right_half_bound {ε : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ t : ℝ, 6 ≤ σ →
      ‖tauL ((σ : ℂ) + t * I)‖ ≤ C * (1 + |t|) ^ (1 / 2 + ε) := by
  obtain ⟨Cf, hCf0, hCf⟩ := fC_bound hε0 hε
  obtain ⟨D, hD0, hD⟩ := tauL_bounded_of_gt (σ := 13 / 2 + ε) (by linarith)
  refine ⟨2 * Real.exp 10 * Cf * 4 + D, by positivity, fun σ t hσ => ?_⟩
  have ht1 : (1 : ℝ) ≤ 1 + |t| := by linarith [abs_nonneg t]
  have hp1 : 1 ≤ (1 + |t|) ^ (1 / 2 + ε) := Real.one_le_rpow ht1 (by linarith)
  set s : ℂ := (σ : ℂ) + t * I with hsdef
  have hsre : s.re = σ := by simp [hsdef]
  have hsim : s.im = t := by simp [hsdef]
  rcases le_or_gt σ (13 / 2 + ε) with h2 | h2
  · have hL := tauL_line hε0 hε hCf (s := s) (by rw [hsre]; linarith) (by rw [hsre]; exact h2)
    rw [hsre] at hL
    set θ : ℝ := 13 / 2 + ε - σ with hθ
    have hθ0 : 0 ≤ θ := by rw [hθ]; linarith
    have hθ1 : θ ≤ 1 / 2 + ε := by rw [hθ]; linarith
    have hn1 : 1 ≤ ‖s / 2‖ := by
      have : (s / 2).re = σ / 2 := by simp [hsre]
      have h := Complex.re_le_norm (s / 2)
      linarith
    have hn : ‖s / 2‖ ≤ 4 * (1 + |t|) := by
      rw [norm_div, Complex.norm_two, div_le_iff₀ (by norm_num)]
      refine (Complex.norm_le_abs_re_add_abs_im s).trans ?_
      rw [hsre, hsim, abs_of_nonneg (by linarith : (0:ℝ) ≤ σ)]; linarith [abs_nonneg t]
    have hp : ‖s / 2‖ ^ θ ≤ 4 * (1 + |t|) ^ (1 / 2 + ε) := by
      calc ‖s / 2‖ ^ θ ≤ ‖s / 2‖ ^ (1 / 2 + ε) := Real.rpow_le_rpow_of_exponent_le hn1 hθ1
        _ ≤ (4 * (1 + |t|)) ^ (1 / 2 + ε) := Real.rpow_le_rpow (by positivity) hn (by linarith)
        _ = 4 ^ (1 / 2 + ε) * (1 + |t|) ^ (1 / 2 + ε) := Real.mul_rpow (by norm_num) (by linarith)
        _ ≤ 4 * (1 + |t|) ^ (1 / 2 + ε) := by
          gcongr
          calc (4 : ℝ) ^ (1 / 2 + ε) ≤ 4 ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
            _ = 4 := Real.rpow_one 4
    calc ‖tauL s‖ ≤ 2 * Real.exp 10 * Cf * ‖s / 2‖ ^ θ := hL
      _ ≤ 2 * Real.exp 10 * Cf * (4 * (1 + |t|) ^ (1 / 2 + ε)) := by gcongr
      _ ≤ (2 * Real.exp 10 * Cf * 4 + D) * (1 + |t|) ^ (1 / 2 + ε) := by nlinarith
  · have := hD s (by rw [hsre]; exact h2.le)
    have h1 : D ≤ D * (1 + |t|) ^ (1 / 2 + ε) := le_mul_of_one_le_right hD0 hp1
    have h3 : 0 ≤ 2 * Real.exp 10 * Cf * 4 * (1 + |t|) ^ (1 / 2 + ε) := by positivity
    calc ‖tauL s‖ ≤ D := this
      _ ≤ (2 * Real.exp 10 * Cf * 4 + D) * (1 + |t|) ^ (1 / 2 + ε) := by nlinarith

/-- **Lower bound for the integral of `L(Δ,·)` along the critical line.** -/
theorem norm_integral_tauL_ge {ε : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1 / 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ a b : ℝ, 0 ≤ a → a ≤ b →
      (b - a) / 2 - K * (1 + b) ^ (1 / 2 + ε) ≤ ‖∫ t in a..b, tauL (6 + t * I)‖ := by
  obtain ⟨σ₁, hσ₁, hre⟩ := re_tauL_right_ge
  obtain ⟨C, hC0, hC⟩ := tauL_right_half_bound hε0 hε
  refine ⟨2 * (σ₁ - 6) * C, by nlinarith, fun a b ha hab => ?_⟩
  have hrect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn tauL
    ((6 : ℂ) + a * I) ((σ₁ : ℂ) + b * I) tauLSeries_entire.differentiableOn
  have e1 : ((6 : ℂ) + a * I).re = 6 := by simp
  have e2 : ((6 : ℂ) + a * I).im = a := by simp
  have e3 : ((σ₁ : ℂ) + b * I).re = σ₁ := by simp
  have e4 : ((σ₁ : ℂ) + b * I).im = b := by simp
  rw [e1, e2, e3, e4] at hrect
  set Ha := ∫ x : ℝ in (6 : ℝ)..σ₁, tauL (x + a * I)
  set Hb := ∫ x : ℝ in (6 : ℝ)..σ₁, tauL (x + b * I)
  set X := ∫ y : ℝ in a..b, tauL (σ₁ + y * I)
  set Y := ∫ y : ℝ in a..b, tauL (((6 : ℝ) : ℂ) + y * I)
  have hY : (∫ t in a..b, tauL (6 + t * I)) = Y := by
    simp only [Y]; congr 1
  rw [hY]
  have hEq : I • Y = Ha - Hb + I • X := by linear_combination -hrect
  have hcont : Continuous fun y : ℝ => tauL (σ₁ + y * I) :=
    tauLSeries_entire.continuous.comp (by fun_prop)
  -- `‖X‖ ≥ (b−a)/2`
  have hX : (b - a) / 2 ≤ ‖X‖ := by
    have hint := hcont.intervalIntegrable (μ := volume) a b
    have hreX : X.re = ∫ y in a..b, (tauL (σ₁ + y * I)).re := (intervalIntegral.intervalIntegral_re hint).symm
    have hmono : (∫ y in a..b, (1 / 2 : ℝ)) ≤ ∫ y in a..b, (tauL (σ₁ + y * I)).re :=
      intervalIntegral.integral_mono_on hab intervalIntegrable_const
        ((Complex.continuous_re.comp hcont).intervalIntegrable a b) fun y _ => hre y
    rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
    have := Complex.re_le_norm X
    linarith
  -- horizontal sides
  have hside : ∀ c : ℝ, 0 ≤ c → c ≤ b →
      ‖∫ x : ℝ in (6 : ℝ)..σ₁, tauL (x + c * I)‖ ≤ C * (1 + b) ^ (1 / 2 + ε) * (σ₁ - 6) := by
    intro c hc0 hcb
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (6 : ℝ)) (b := σ₁)
      (f := fun x : ℝ => tauL (x + c * I)) (C := C * (1 + b) ^ (1 / 2 + ε)) (fun x hx => by
        rw [uIoc_of_le (by linarith)] at hx
        refine (hC x c hx.1.le).trans ?_
        gcongr
        rw [abs_of_nonneg hc0]; exact hcb)
    rwa [abs_of_nonneg (by linarith)] at this
  have hA := hside a ha hab
  have hB := hside b (ha.trans hab) le_rfl
  have hnorm : ‖Y‖ = ‖I • Y‖ := by rw [norm_smul, Complex.norm_I, one_mul]
  have htri : ‖I • X‖ ≤ ‖I • Y‖ + ‖Ha‖ + ‖Hb‖ := by
    have : I • X = I • Y - Ha + Hb := by rw [hEq]; ring
    rw [this]
    exact (norm_add_le _ _).trans (by linarith [norm_sub_le (I • Y) Ha])
  rw [norm_smul, Complex.norm_I, one_mul] at htri
  rw [hnorm, norm_smul, Complex.norm_I, one_mul]
  nlinarith

end RamanujanTau.HardyCount
