/-
# Window lower bound from a rectangle, for an arbitrary entire function; normalisation of `L(f,s)`

* `window_lower_gen`: for entire `g` with `|g(σ₁+iy) − 1| ≤ 1/4`, Cauchy on
  `[σ₀,σ₁] × [a,b]` gives `∫_a^b |g(σ₀+iy)| dy ≥ (b−a)/2` as soon as the horizontal sides satisfy
  `F(a), F(b) ≤ (b−a)/8`, `F(c) = ∫_{σ₀}^{σ₁} |g(x+ic)| dx`
  (`HardyCountHafner.window_lower` is the case `g = L(Δ,·)`, `σ₀ = 6`).
* `exists_normalized`: for a general cusp form `a_f(1)` may vanish, so `L(f,s)` need not tend to
  `1` as `Re s → ∞`.  With `n₀` the first index where `a_f(n₀) ≠ 0`,
  `g(s) = n₀^s a_f(n₀)^{−1} L(f,s) = 1 + ∑_{n>n₀} (a_f(n)/a_f(n₀)) (n₀/n)^s` does, uniformly in
  `Im s`: `|g(σ₁+iy) − 1| ≤ ρ` for some `σ₁`.  Since `|g(σ+it)| = n₀^σ |a_f(n₀)|^{−1} |L(f,σ+it)|`,
  this only changes constants.
-/
import RamanujanTau.HafnerGeneral.Horizontal
import RamanujanTau.RankinSelbergGeneral.Positive

set_option autoImplicit false

namespace RamanujanTau.HafnerGeneral

open Complex MeasureTheory Set Filter ModularForm
open RamanujanTau.HeckeConvexGeneral
open scoped Real MatrixGroups

/-- **Window lower bound** for an entire `g` close to `1` on `Re s = σ₁`. -/
theorem window_lower_gen {g : ℂ → ℂ} (hg : Differentiable ℂ g) {σ₀ σ₁ : ℝ} (h01 : σ₀ ≤ σ₁)
    (hρ : ∀ y : ℝ, ‖g (σ₁ + y * I) - 1‖ ≤ 1 / 4)
    {a b : ℝ} (hab : a ≤ b) (ha : Fh g σ₀ σ₁ a ≤ (b - a) / 8) (hb : Fh g σ₀ σ₁ b ≤ (b - a) / 8) :
    (b - a) / 2 ≤ ∫ t in a..b, ‖g (σ₀ + t * I)‖ := by
  have hrect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn g
    ((σ₀ : ℂ) + a * I) ((σ₁ : ℂ) + b * I) hg.differentiableOn
  have e1 : ((σ₀ : ℂ) + a * I).re = σ₀ := by simp
  have e2 : ((σ₀ : ℂ) + a * I).im = a := by simp
  have e3 : ((σ₁ : ℂ) + b * I).re = σ₁ := by simp
  have e4 : ((σ₁ : ℂ) + b * I).im = b := by simp
  rw [e1, e2, e3, e4] at hrect
  set Ha := ∫ x : ℝ in σ₀..σ₁, g (x + a * I) with hHa
  set Hb := ∫ x : ℝ in σ₀..σ₁, g (x + b * I) with hHb
  set X := ∫ y : ℝ in a..b, g (σ₁ + y * I) with hX
  set Y := ∫ y : ℝ in a..b, g (σ₀ + y * I) with hY
  have hEq : I • Y = Ha - Hb + I • X := by linear_combination -hrect
  have hHa' : ‖Ha‖ ≤ (b - a) / 8 :=
    (intervalIntegral.norm_integral_le_integral_norm h01).trans ha
  have hHb' : ‖Hb‖ ≤ (b - a) / 8 :=
    (intervalIntegral.norm_integral_le_integral_norm h01).trans hb
  have hcR : Continuous fun y : ℝ => g (σ₁ + y * I) := hg.continuous.comp (by fun_prop)
  have hXsub : X - ((b - a : ℝ) : ℂ) = ∫ y : ℝ in a..b, (g (σ₁ + y * I) - 1) := by
    rw [intervalIntegral.integral_sub (hcR.intervalIntegrable _ _) intervalIntegrable_const,
      intervalIntegral.integral_const]
    simp [hX]
  have hXb : ‖X - ((b - a : ℝ) : ℂ)‖ ≤ (b - a) / 4 := by
    rw [hXsub]
    have := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a) (b := b) (C := 1 / 4) (f := fun y : ℝ => g (σ₁ + y * I) - 1)
      (fun y _ => hρ y)
    rw [abs_of_nonneg (by linarith)] at this
    linarith
  have hXl : 3 * (b - a) / 4 ≤ ‖X‖ := by
    have h1 := norm_sub_norm_le (((b - a : ℝ) : ℂ)) X
    rw [norm_sub_rev, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)] at h1
    linarith
  have hYl : (b - a) / 2 ≤ ‖Y‖ := by
    have hn : ‖Y‖ = ‖I • Y‖ := by rw [norm_smul, Complex.norm_I, one_mul]
    rw [hn, hEq]
    have h3 : ‖I • X‖ = ‖X‖ := by rw [norm_smul, Complex.norm_I, one_mul]
    have h1 := norm_sub_norm_le (I • X) (-(Ha - Hb))
    rw [sub_neg_eq_add, norm_neg, h3, add_comm] at h1
    have h2 := norm_sub_le Ha Hb
    linarith
  refine hYl.trans ?_
  rw [hY]
  exact intervalIntegral.norm_integral_le_integral_norm hab

variable {k : ℕ}

/-- A nonzero cusp form has a nonzero coefficient. -/
lemma exists_coef_ne_zero (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : f ≠ 0) (hk : 1 ≤ k) :
    ∃ n, coef f n ≠ 0 := by
  obtain ⟨n, _, hn⟩ := RankinSelbergGeneral.exists_coeff_ne_zero f hf hk
  refine ⟨n, fun h => hn ?_⟩
  rw [coeffSq_eq, h, norm_zero]; norm_num

/-- **Normalisation**: with `n₀` the first index where `a_f(n₀) ≠ 0`, the entire function
`g(s) = n₀^s a_f(n₀)^{−1} L(f,s)` satisfies `|g(σ₁+iy) − 1| ≤ ρ` for some `σ₁ ≥ σa`. -/
theorem exists_normalized (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : f ≠ 0) (hk : 1 ≤ k) {σa : ℝ}
    (hσa : ((k : ℝ) + 1) / 2 < σa) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ n₀ : ℕ, 1 ≤ n₀ ∧ coef f n₀ ≠ 0 ∧ ∃ σ₁ : ℝ, σa ≤ σ₁ ∧ ∀ y : ℝ,
      ‖(n₀ : ℂ) ^ ((σ₁ : ℂ) + y * I) / coef f n₀ * fL f ((σ₁ : ℂ) + y * I) - 1‖ ≤ ρ := by
  classical
  have hex := exists_coef_ne_zero f hf hk
  set n₀ := Nat.find hex with hn₀
  have ha₀ : coef f n₀ ≠ 0 := Nat.find_spec hex
  have hmin : ∀ n < n₀, coef f n = 0 := fun n hn => by
    by_contra h; exact Nat.find_min hex hn h
  have hn₀1 : 1 ≤ n₀ := by
    rcases Nat.eq_zero_or_pos n₀ with h | h
    · exact absurd (h ▸ coef_zero f) ha₀
    · exact h
  set a₀ := coef f n₀ with ha₀def
  have ha₀n : 0 < ‖a₀‖ := norm_pos_iff.mpr ha₀
  have hn₀R : (1 : ℝ) ≤ n₀ := by exact_mod_cast hn₀1
  have hσa0 : 0 < σa := lt_of_le_of_lt (by positivity) hσa
  have hsum : LSeriesSummable (coef f) (σa : ℂ) := LSeriesSummable_coef f hk (by simpa using hσa)
  set S : ℝ := ∑' n, ‖LSeries.term (coef f) σa n‖ with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun _ => norm_nonneg _
  set B : ℝ := (n₀ : ℝ) ^ σa / ‖a₀‖ with hB
  have hB0 : 0 ≤ B := by positivity
  set q : ℝ := (n₀ : ℝ) / ((n₀ : ℝ) + 1) with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by rw [hq, div_lt_one (by positivity)]; linarith
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < ρ / (B * S + 1) by positivity) hq1
  refine ⟨n₀, hn₀1, ha₀, σa + K, by linarith [Nat.cast_nonneg (α := ℝ) K], fun y => ?_⟩
  set σ₁ : ℝ := σa + K with hσ₁
  set s : ℂ := (σ₁ : ℂ) + y * I with hs
  have hsre : s.re = σ₁ := by simp [hs]
  have hσ₁a : σa ≤ σ₁ := by rw [hσ₁]; linarith [Nat.cast_nonneg (α := ℝ) K]
  have hsums : LSeriesSummable (coef f) s :=
    LSeriesSummable_coef f hk (by rw [hsre]; linarith)
  have hpos : (0 : ℝ) < n₀ := by linarith
  have hcp0 : (n₀ : ℂ) ^ s ≠ 0 := by
    have := norm_natCast_cpow_pos_of_pos (n := n₀) (by omega) s
    exact norm_pos_iff.mp this
  rw [fL_eq_LSeries f hk (by rw [hsre]; linarith), LSeries, hsums.tsum_eq_add_tsum_ite n₀]
  have hterm : LSeries.term (coef f) s n₀ = a₀ / (n₀ : ℂ) ^ s := by
    rw [LSeries.term_def, if_neg (by omega)]
  rw [hterm]
  set R := ∑' n, (if n = n₀ then 0 else LSeries.term (coef f) s n) with hR
  have hsimp : (n₀ : ℂ) ^ s / a₀ * (a₀ / (n₀ : ℂ) ^ s + R) - 1 = (n₀ : ℂ) ^ s / a₀ * R := by
    field_simp; ring
  rw [hsimp, hR, ← tsum_mul_left]
  -- pointwise bound
  have hpt : ∀ n : ℕ, ‖(n₀ : ℂ) ^ s / a₀ * (if n = n₀ then 0 else LSeries.term (coef f) s n)‖ ≤
      q ^ K * B * ‖LSeries.term (coef f) σa n‖ := by
    intro n
    have hrhs : 0 ≤ q ^ K * B * ‖LSeries.term (coef f) σa n‖ := by positivity
    split_ifs with hn
    · simpa using hrhs
    rcases lt_or_gt_of_ne hn with hlt | hgt
    · have : LSeries.term (coef f) s n = 0 := by
        rw [LSeries.term_def]; split_ifs <;> simp [hmin n hlt]
      rw [this, mul_zero, norm_zero]; exact hrhs
    · have hn0 : n ≠ 0 := by omega
      have hnR : (n₀ : ℝ) + 1 ≤ n := by exact_mod_cast hgt
      have hnpos : (0 : ℝ) < n := by linarith
      rw [norm_mul, norm_div, norm_natCast_cpow_of_pos (by omega), LSeries.norm_term_eq,
        LSeries.norm_term_eq, if_neg hn0, if_neg hn0, hsre]
      have e7 : ((σa : ℂ)).re = σa := by simp
      rw [e7]
      set c := ‖coef f n‖ with hc
      have hc0 : 0 ≤ c := norm_nonneg _
      have h1 : (n₀ : ℝ) ^ σ₁ = (n₀ : ℝ) ^ σa * (n₀ : ℝ) ^ K := by
        rw [hσ₁, Real.rpow_add hpos, Real.rpow_natCast]
      have h2 : (n : ℝ) ^ σ₁ = (n : ℝ) ^ σa * (n : ℝ) ^ K := by
        rw [hσ₁, Real.rpow_add hnpos, Real.rpow_natCast]
      have hqn : ((n₀ : ℝ) / n) ^ K ≤ q ^ K := by
        apply pow_le_pow_left₀ (by positivity)
        rw [hq]; exact div_le_div_of_nonneg_left (by positivity) (by positivity) hnR
      have hX : 0 ≤ (n₀ : ℝ) ^ σa / ‖a₀‖ * (c / (n : ℝ) ^ σa) := by positivity
      have hnσ : 0 < (n : ℝ) ^ σa := Real.rpow_pos_of_pos hnpos _
      have hnK : 0 < (n : ℝ) ^ K := by positivity
      calc (n₀ : ℝ) ^ σ₁ / ‖a₀‖ * (c / (n : ℝ) ^ σ₁)
          = ((n₀ : ℝ) ^ σa / ‖a₀‖ * (c / (n : ℝ) ^ σa)) * ((n₀ : ℝ) / n) ^ K := by
            rw [h1, h2, div_pow]; field_simp
        _ ≤ ((n₀ : ℝ) ^ σa / ‖a₀‖ * (c / (n : ℝ) ^ σa)) * q ^ K :=
            mul_le_mul_of_nonneg_left hqn hX
        _ = q ^ K * B * (c / (n : ℝ) ^ σa) := by rw [hB]; ring
  have hsumR : Summable fun n => q ^ K * B * ‖LSeries.term (coef f) σa n‖ :=
    hsum.norm.mul_left _
  have hnorm : Summable fun n : ℕ =>
      ‖(n₀ : ℂ) ^ s / a₀ * (if n = n₀ then 0 else LSeries.term (coef f) s n)‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpt hsumR
  refine (norm_tsum_le_tsum_norm hnorm).trans ?_
  refine (Summable.tsum_le_tsum hpt hnorm hsumR).trans ?_
  rw [tsum_mul_left, ← hS]
  have h := hK.le
  rw [le_div_iff₀ (by positivity)] at h
  have : 0 ≤ q ^ K := by positivity
  nlinarith

end RamanujanTau.HafnerGeneral
