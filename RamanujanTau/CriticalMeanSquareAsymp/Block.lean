/-
# Sharp unit-block comparison along the rays `τ = ±w + iκw`

For `σ = ±1`, `κ > 0`, `N ≥ 1`:

    |∫_N^{N+1} w¹¹ |Δ(σw + iκw)|² dw − N¹¹ H(κN)| ≤ B / (κ¹² N²),

where `H(y) = ∫₀¹ |Δ(x+iy)|² dx`.  Pointwise, with `a = Δ(σw+iκw)`, `b = Δ(σw+iκN)`:
`|a|, |b| ≤ M (κN)^{-6}` and `|a − b| ≤ A κ (κN)^{-7}` (Cauchy estimate), so
`||a|² − |b|²| ≤ |a−b|(|a|+|b|) = O(κ^{-12} N^{-13})`, and `w¹¹ − N¹¹ = O(N¹⁰)`.
Summing `N = 1, …, n` gives an error `≤ 2B κ^{-12}`, uniformly in `n`.
-/
import RamanujanTau.CriticalMeanSquareLower.RayBlock
import RamanujanTau.EisensteinReal.HoroIdent

set_option autoImplicit false

namespace RamanujanTau.CriticalMeanSquareAsymp

open Complex MeasureTheory Set Filter Topology
open UpperHalfPlane hiding I
open RamanujanTau.HardyZeros RamanujanTau.HardyCountHafner
  RamanujanTau.CriticalMeanSquare RamanujanTau.CriticalMeanSquareLower
open scoped Real Interval

/-- The signed ray integrand `w¹¹ |Δ(σw + iκw)|²`. -/
noncomputable def Gsig (σ κ w : ℝ) : ℝ := w ^ 11 * ‖Dc (pt (σ * w) (κ * w))‖ ^ 2

lemma Gsig_neg_one (κ w : ℝ) : Gsig (-1) κ w = Gw κ w := by
  unfold Gsig Gw; rw [neg_one_mul]

lemma Gsig_nonneg (σ κ : ℝ) {w : ℝ} (hw : 0 ≤ w) : 0 ≤ Gsig σ κ w := by
  unfold Gsig; positivity

lemma continuousOn_Gsig (σ : ℝ) {κ : ℝ} (hκ : 0 < κ) : ContinuousOn (Gsig σ κ) (Ioi 0) := by
  have hc : Continuous fun w : ℝ => pt (σ * w) (κ * w) := by unfold pt; fun_prop
  have h1 : ContinuousOn (fun w : ℝ => Dc (pt (σ * w) (κ * w))) (Ioi 0) :=
    continuousOn_Dc.comp hc.continuousOn (fun w hw => by
      show 0 < (pt (σ * w) (κ * w)).im
      rw [pt_im]; exact mul_pos hκ hw)
  exact (continuousOn_pow 11).mul (h1.norm.pow 2)

lemma continuous_Dc_horiz_sig (σ : ℝ) {y : ℝ} (hy : 0 < y) :
    Continuous fun w : ℝ => Dc (pt (σ * w) y) :=
  continuousOn_Dc.comp_continuous (by unfold pt; fun_prop) (fun w => by
    show 0 < (pt (σ * w) y).im
    rw [pt_im]; exact hy)

/-- Period integral along either orientation. -/
lemma integral_period_sig {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (y a : ℝ) :
    ∫ w in a..a + 1, ‖Dc (pt (σ * w) y)‖ ^ 2 = Hh y := by
  rcases hσ with rfl | rfl
  · simp only [one_mul]
    have hper : Function.Periodic (fun x : ℝ => ‖Dc (pt x y)‖ ^ 2) 1 := by
      intro x
      simp only
      rw [show pt (x + 1) y = pt x y + 1 by simp [pt]; ring, Dc_add_one]
    have := hper.intervalIntegral_add_eq a 0
    rw [this, zero_add]
    rfl
  · simp only [neg_one_mul]
    exact integral_period y a

/-- Pointwise sup bounds for `Δ`. -/
lemma exists_Dc_bounds : ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℂ, 0 < z.im →
    ‖Dc z‖ ≤ M / z.im ^ 6 ∧ ‖Dc z‖ * z.im ^ 6 ≤ M * Real.exp (-(π * z.im)) := by
  obtain ⟨M, hM0, hM⟩ := exists_Delta_bound_exp
  refine ⟨M, hM0, fun z hz => ?_⟩
  rw [Dc_of_im_pos hz]
  have h := hM ⟨z, hz⟩
  have : (⟨z, hz⟩ : ℍ).im = z.im := rfl
  rw [this] at h
  have hy6 : 0 < z.im ^ 6 := by positivity
  have he : 1 ≤ Real.exp (π * z.im) := Real.one_le_exp (by positivity)
  have hE : 0 < Real.exp (π * z.im) := Real.exp_pos _
  have h0 : 0 ≤ ‖HeckeL.Δf ⟨z, hz⟩‖ * z.im ^ 6 := by positivity
  constructor
  · rw [le_div_iff₀ hy6]; nlinarith
  · rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ hE]; exact h

lemma pow11_diff_le {x : ℝ} (hx : 1 ≤ x) : (x + 1) ^ 11 - x ^ 11 ≤ 2047 * x ^ 10 := by
  have e : (x + 1) ^ 11 - x ^ 11 = 11 * x ^ 10 + 55 * x ^ 9 + 165 * x ^ 8 + 330 * x ^ 7 +
      462 * x ^ 6 + 462 * x ^ 5 + 330 * x ^ 4 + 165 * x ^ 3 + 55 * x ^ 2 + 11 * x + 1 := by ring
  have h9 : x ^ 9 ≤ x ^ 10 := pow_le_pow_right₀ hx (by norm_num)
  have h8 : x ^ 8 ≤ x ^ 10 := pow_le_pow_right₀ hx (by norm_num)
  have h7 : x ^ 7 ≤ x ^ 10 := pow_le_pow_right₀ hx (by norm_num)
  have h6 : x ^ 6 ≤ x ^ 10 := pow_le_pow_right₀ hx (by norm_num)
  have h5 : x ^ 5 ≤ x ^ 10 := pow_le_pow_right₀ hx (by norm_num)
  have h4 : x ^ 4 ≤ x ^ 10 := pow_le_pow_right₀ hx (by norm_num)
  have h3 : x ^ 3 ≤ x ^ 10 := pow_le_pow_right₀ hx (by norm_num)
  have h2 : x ^ 2 ≤ x ^ 10 := pow_le_pow_right₀ hx (by norm_num)
  have h1 : x ≤ x ^ 10 := by simpa using pow_le_pow_right₀ hx (show 1 ≤ 10 by norm_num)
  have h0 : (1 : ℝ) ≤ x ^ 10 := one_le_pow₀ hx
  rw [e]; linarith

/-- **Sharp block comparison.** -/
lemma block_sharp {M A : ℝ} (hM0 : 0 ≤ M) (hA0 : 0 ≤ A)
    (hM : ∀ z : ℂ, 0 < z.im → ‖Dc z‖ ≤ M / z.im ^ 6)
    (hA : ∀ x y₁ y₂ y₀ : ℝ, 0 < y₀ → y₀ ≤ y₁ → y₀ ≤ y₂ →
      ‖Dc (pt x y₁) - Dc (pt x y₂)‖ ≤ A * |y₁ - y₂| / y₀ ^ 7)
    {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {κ N : ℝ} (hκ : 0 < κ) (hN : 1 ≤ N) :
    |(∫ w in N..N + 1, Gsig σ κ w) - N ^ 11 * Hh (κ * N)| ≤
      (2047 * M ^ 2 + 2 * A * M) / (κ ^ 12 * N ^ 2) := by
  have hN0 : 0 < N := by linarith
  set y₀ : ℝ := κ * N with hy₀
  have hy₀0 : 0 < y₀ := mul_pos hκ hN0
  set f : ℝ → ℝ := fun w => ‖Dc (pt (σ * w) y₀)‖ ^ 2 with hf
  have hfc : Continuous f := (continuous_Dc_horiz_sig σ hy₀0).norm.pow 2
  set B : ℝ := (2047 * M ^ 2 + 2 * A * M) / (κ ^ 12 * N ^ 2) with hB
  have hpt : ∀ w ∈ Ι N (N + 1), ‖Gsig σ κ w - N ^ 11 * f w‖ ≤ B := by
    intro w hw
    rw [uIoc_of_le (by linarith)] at hw
    obtain ⟨hw1, hw2⟩ := hw
    have hw1' : N ≤ w := hw1.le
    have hw0 : 0 < w := by linarith
    set a := Dc (pt (σ * w) (κ * w))
    set b := Dc (pt (σ * w) y₀)
    have hy₀w : y₀ ≤ κ * w := by rw [hy₀]; gcongr
    have ha : ‖a‖ ≤ M / y₀ ^ 6 := by
      refine (hM _ (by rw [pt_im]; positivity)).trans ?_
      rw [pt_im]; gcongr
    have hb : ‖b‖ ≤ M / y₀ ^ 6 := by
      refine (hM _ (by rw [pt_im]; positivity)).trans ?_
      rw [pt_im]
    have hab : ‖a - b‖ ≤ A * κ / y₀ ^ 7 := by
      have h := hA (σ * w) (κ * w) y₀ y₀ hy₀0 hy₀w le_rfl
      have habs : |κ * w - y₀| ≤ κ := by
        rw [hy₀, ← mul_sub, abs_of_nonneg (by nlinarith)]
        nlinarith
      refine h.trans ?_
      rw [div_le_div_iff_of_pos_right (by positivity)]
      exact mul_le_mul_of_nonneg_left habs hA0
    have hsq : |‖a‖ ^ 2 - ‖b‖ ^ 2| ≤ A * κ / y₀ ^ 7 * (2 * (M / y₀ ^ 6)) := by
      have e : ‖a‖ ^ 2 - ‖b‖ ^ 2 = (‖a‖ - ‖b‖) * (‖a‖ + ‖b‖) := by ring
      rw [e, abs_mul, abs_of_nonneg (by positivity : 0 ≤ ‖a‖ + ‖b‖)]
      have h1 : |‖a‖ - ‖b‖| ≤ ‖a - b‖ := abs_norm_sub_norm_le a b
      have h2 : ‖a‖ + ‖b‖ ≤ 2 * (M / y₀ ^ 6) := by linarith
      exact mul_le_mul (h1.trans hab) h2 (by positivity) (by positivity)
    have hw11 : N ^ 11 ≤ w ^ 11 := pow_le_pow_left₀ hN0.le hw1' 11
    have hw11' : w ^ 11 - N ^ 11 ≤ 2047 * N ^ 10 := by
      have := pow_le_pow_left₀ hw0.le hw2 11
      have := pow11_diff_le hN
      linarith
    have ha2 : ‖a‖ ^ 2 ≤ (M / y₀ ^ 6) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) ha 2
    have e : Gsig σ κ w - N ^ 11 * f w = (w ^ 11 - N ^ 11) * ‖a‖ ^ 2 +
        N ^ 11 * (‖a‖ ^ 2 - ‖b‖ ^ 2) := by
      simp only [Gsig, hf, a, b]; ring
    rw [Real.norm_eq_abs, e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg (by linarith), abs_of_nonneg (by positivity),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ N ^ 11)]
    have t1 : (w ^ 11 - N ^ 11) * ‖a‖ ^ 2 ≤ 2047 * N ^ 10 * (M / y₀ ^ 6) ^ 2 :=
      mul_le_mul hw11' ha2 (by positivity) (by positivity)
    have t2 : N ^ 11 * |‖a‖ ^ 2 - ‖b‖ ^ 2| ≤ N ^ 11 * (A * κ / y₀ ^ 7 * (2 * (M / y₀ ^ 6))) :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    have e2 : 2047 * N ^ 10 * (M / y₀ ^ 6) ^ 2 + N ^ 11 * (A * κ / y₀ ^ 7 * (2 * (M / y₀ ^ 6)))
        = B := by
      rw [hB, hy₀]; field_simp
    linarith
  have hint2 : IntervalIntegrable (Gsig σ κ) volume N (N + 1) := by
    refine ContinuousOn.intervalIntegrable ((continuousOn_Gsig σ hκ).mono ?_)
    rw [uIcc_of_le (by linarith)]
    intro w hw; exact lt_of_lt_of_le hN0 hw.1
  have hint1 : IntervalIntegrable (fun w => N ^ 11 * f w) volume N (N + 1) :=
    (hfc.const_mul _).intervalIntegrable _ _
  have hval : ∫ w in N..N + 1, N ^ 11 * f w = N ^ 11 * Hh y₀ := by
    rw [intervalIntegral.integral_const_mul, hf, integral_period_sig hσ]
  have hbd := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  rw [intervalIntegral.integral_sub hint2 hint1, hval, Real.norm_eq_abs] at hbd
  rw [show N + 1 - N = 1 by ring, abs_one, mul_one] at hbd
  exact hbd

/-- `Aint(y) = y¹² H(y)`. -/
lemma Aint_eq {y : ℝ} (hy : 0 < y) : EisensteinReal.Horo.Aint y = y ^ 12 * Hh y := by
  unfold EisensteinReal.Horo.Aint
  rw [dif_pos hy, Hh, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr (fun x _ => ?_)
  simp only [RankinSelberg.G]
  rw [Dc_pt_eq hy x, RankinSelberg.hp_im hy x]
  ring

lemma sum_inv_sq_le (n : ℕ) :
    ∑ j ∈ Finset.range n, (1 : ℝ) / ((j : ℝ) + 1) ^ 2 ≤ 2 - 2 / ((n : ℝ) + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have key : 1 / ((n : ℝ) + 1) ^ 2 ≤ 2 / ((n : ℝ) + 1) - 2 / ((n : ℝ) + 1 + 1) := by
      rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
        (by positivity)]
      nlinarith
    push_cast
    linarith

/-- **Summed blocks** `N = 1, …, n`:
`|κ¹² ∫_1^{n+1} Gsig − ∑_{N ≤ n} Aint(κN)/N| ≤ 2B`. -/
lemma sum_sharp {M A : ℝ} (hM0 : 0 ≤ M) (hA0 : 0 ≤ A)
    (hM : ∀ z : ℂ, 0 < z.im → ‖Dc z‖ ≤ M / z.im ^ 6)
    (hA : ∀ x y₁ y₂ y₀ : ℝ, 0 < y₀ → y₀ ≤ y₁ → y₀ ≤ y₂ →
      ‖Dc (pt x y₁) - Dc (pt x y₂)‖ ≤ A * |y₁ - y₂| / y₀ ^ 7)
    {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {κ : ℝ} (hκ : 0 < κ) (n : ℕ) :
    |κ ^ 12 * (∫ w in (1 : ℝ)..(n : ℝ) + 1, Gsig σ κ w) -
      ∑ j ∈ Finset.range n, EisensteinReal.Horo.Aint (κ * ((j : ℝ) + 1)) / ((j : ℝ) + 1)| ≤
      2 * (2047 * M ^ 2 + 2 * A * M) := by
  set B := 2047 * M ^ 2 + 2 * A * M with hB
  have hB0 : 0 ≤ B := by positivity
  have hκ12 : 0 < κ ^ 12 := by positivity
  have hii : ∀ a b : ℝ, 1 ≤ a → 1 ≤ b → IntervalIntegrable (Gsig σ κ) volume a b := by
    intro a b ha hb
    refine ContinuousOn.intervalIntegrable ((continuousOn_Gsig σ hκ).mono ?_)
    intro w hw
    have : (1 : ℝ) ≤ min a b := le_min ha hb
    show 0 < w
    linarith [hw.1]
  suffices H : ∀ n : ℕ, |κ ^ 12 * (∫ w in (1 : ℝ)..(n : ℝ) + 1, Gsig σ κ w) -
      ∑ j ∈ Finset.range n, EisensteinReal.Horo.Aint (κ * ((j : ℝ) + 1)) / ((j : ℝ) + 1)| ≤
      B * ∑ j ∈ Finset.range n, (1 : ℝ) / ((j : ℝ) + 1) ^ 2 by
    refine (H n).trans ?_
    have h1 := sum_inv_sq_le n
    have h2 : 0 ≤ 2 / ((n : ℝ) + 1) := by positivity
    nlinarith
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hsplit : ∫ w in (1 : ℝ)..((n + 1 : ℕ) : ℝ) + 1, Gsig σ κ w =
        (∫ w in (1 : ℝ)..(n : ℝ) + 1, Gsig σ κ w) +
          ∫ w in (n : ℝ) + 1..(n : ℝ) + 1 + 1, Gsig σ κ w := by
      push_cast
      exact (intervalIntegral.integral_add_adjacent_intervals (hii _ _ le_rfl hn1)
        (hii _ _ hn1 (by linarith))).symm
    have hblk := block_sharp hM0 hA0 hM hA hσ hκ hn1
    rw [hsplit, Finset.sum_range_succ, Finset.sum_range_succ]
    have hy : 0 < κ * ((n : ℝ) + 1) := by positivity
    have hA : EisensteinReal.Horo.Aint (κ * ((n : ℝ) + 1)) / ((n : ℝ) + 1) =
        κ ^ 12 * (((n : ℝ) + 1) ^ 11 * Hh (κ * ((n : ℝ) + 1))) := by
      rw [Aint_eq hy]; field_simp
    rw [hA]
    have hblk' : |κ ^ 12 * (∫ w in (n : ℝ) + 1..(n : ℝ) + 1 + 1, Gsig σ κ w) -
        κ ^ 12 * (((n : ℝ) + 1) ^ 11 * Hh (κ * ((n : ℝ) + 1)))| ≤
          B * (1 / ((n : ℝ) + 1) ^ 2) := by
      rw [← mul_sub, abs_mul, abs_of_pos hκ12]
      calc κ ^ 12 * |_| ≤ κ ^ 12 * (B / (κ ^ 12 * ((n : ℝ) + 1) ^ 2)) :=
            mul_le_mul_of_nonneg_left hblk hκ12.le
        _ = B * (1 / ((n : ℝ) + 1) ^ 2) := by field_simp
    set I1 := ∫ w in (1 : ℝ)..(n : ℝ) + 1, Gsig σ κ w
    set I2 := ∫ w in (n : ℝ) + 1..(n : ℝ) + 1 + 1, Gsig σ κ w
    set S1 := ∑ j ∈ Finset.range n, EisensteinReal.Horo.Aint (κ * ((j : ℝ) + 1)) / ((j : ℝ) + 1)
    set T2 := κ ^ 12 * (((n : ℝ) + 1) ^ 11 * Hh (κ * ((n : ℝ) + 1)))
    have e : κ ^ 12 * (I1 + I2) - (S1 + T2) = (κ ^ 12 * I1 - S1) + (κ ^ 12 * I2 - T2) := by ring
    rw [e, mul_add]
    exact (abs_add_le _ _).trans (add_le_add ih hblk')

end RamanujanTau.CriticalMeanSquareAsymp
