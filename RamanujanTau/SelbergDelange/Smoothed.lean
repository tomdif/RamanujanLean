/-
# The smoothed Rankin–Selberg PNT with de la Vallée-Poussin error term

**Theorem** (`smoothed_boundK`, unconditional).  There are `a > 0` and `K` such that for `x ≥ 3`

  `‖Σ_n vR(n)(1 − n/x)₊ − x(1 − 1/x)²/2‖ ≤ K x exp(−a√log x)`.

Proof: `perron_shiftK` + `contour_boundK` with `T = exp(√log x) − 2` (copied from
`TauPNTError.smoothed_bound`).
-/
import RamanujanTau.SelbergDelange.Perron

set_option autoImplicit false

namespace RamanujanTau.SelbergDelange

open Complex MeasureTheory Set Filter Topology
open RamanujanTau.EdgeNonvanishing RamanujanTau.TauPNTUncond RamanujanTau.RankinError
open RamanujanTau.TauPNTError (sq_mul_exp_le one_le_log_three)

set_option maxHeartbeats 2000000 in
/-- **Smoothed Rankin–Selberg PNT with error term** (unconditional). -/
theorem smoothed_boundK : ∃ a : ℝ, 0 < a ∧ a ≤ 1 / 64 ∧ ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 3 ≤ x →
    ‖∑' n : ℕ, (vR n : ℂ) * (phi 1 (n / x) : ℂ) - ((x * (1 - 1 / x) ^ 2 / 2 : ℝ) : ℂ)‖ ≤
      K * x * Real.exp (-a * Real.sqrt (Real.log x)) := by
  obtain ⟨c, hc, hc400, C₀, hC₀, hreg'⟩ := regK_exists
  have hc32 : c ≤ 1 / 32 := by linarith
  set I₂ : ℝ := ∫ y : ℝ, 1 / (1 + |y|) ^ 2 with hI₂
  set I₅ : ℝ := ∫ y : ℝ, (1 + |y|) ^ (-(5 / 4 : ℝ)) with hI₅
  have hI₂0 : 0 ≤ I₂ := integral_nonneg fun y => by positivity
  have hI₅0 : 0 ≤ I₅ := integral_nonneg fun y => by positivity
  set K₀ : ℝ := 16 * C₀ * I₂ + 128 * C₀ + 1024 * C₀ * I₅ with hK₀
  have hK₀0 : 0 ≤ K₀ := by positivity
  have hπ : 0 < 2 * Real.pi := by positivity
  refine ⟨c / 2, by positivity, by linarith, K₀ * (4 / c) ^ 2 / (2 * Real.pi), by positivity,
    fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hlogx : 1 ≤ Real.log x :=
    one_le_log_three.trans (Real.log_le_log (by norm_num) hx)
  set ℓ : ℝ := Real.sqrt (Real.log x) with hℓ
  have hℓsq : ℓ ^ 2 = Real.log x := Real.sq_sqrt (by linarith)
  have hℓ1 : 1 ≤ ℓ := by
    rw [hℓ, show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hlogx
  have hℓ0 : 0 < ℓ := by linarith
  have hexpℓ : 2 < Real.exp ℓ := by
    have h1 := Real.exp_le_exp.mpr hℓ1
    have h2 := Real.exp_one_gt_d9
    linarith
  set T : ℝ := Real.exp ℓ - 2 with hT
  have hT0 : 0 < T := by linarith
  have hTℓ : Real.log (T + 2) = ℓ := by rw [hT, sub_add_cancel, Real.log_exp]
  have hcb := contour_boundK hreg' hc hc32 hC₀ (x := x) (by linarith) hT0
  rw [hTℓ] at hcb
  set E : ℝ := Real.exp (-c * ℓ) with hE
  have hE0 : 0 < E := Real.exp_pos _
  -- (i)
  have h1 : x ^ (1 - c / ℓ) = x * E := by
    rw [Real.rpow_def_of_pos hx0, hE, ← hℓsq]
    have : Real.exp (ℓ ^ 2 * (1 - c / ℓ)) = Real.exp (ℓ ^ 2) * Real.exp (-c * ℓ) := by
      rw [← Real.exp_add]; congr 1; field_simp; ring
    rw [this, hℓsq, Real.exp_log hx0]
  -- (ii)
  have h1T : Real.exp ℓ / 2 ≤ 1 + T := by rw [hT]; linarith
  have h2 : 1 / (1 + T) ^ 2 ≤ 4 * E := by
    have hpos : 0 < Real.exp ℓ / 2 := by positivity
    have hsq : (Real.exp ℓ / 2) ^ 2 ≤ (1 + T) ^ 2 := pow_le_pow_left₀ hpos.le h1T 2
    have e : 1 / (Real.exp ℓ / 2) ^ 2 = 4 * Real.exp (-2 * ℓ) := by
      rw [div_pow, ← Real.exp_nat_mul, one_div_div, show (-2 : ℝ) * ℓ = -(2 * ℓ) by ring,
        Real.exp_neg]
      push_cast; field_simp; norm_num
    have h3 : Real.exp (-2 * ℓ) ≤ E := by
      rw [hE]; apply Real.exp_le_exp.mpr; nlinarith
    calc 1 / (1 + T) ^ 2 ≤ 1 / (Real.exp ℓ / 2) ^ 2 :=
          one_div_le_one_div_of_le (by positivity) hsq
      _ = 4 * Real.exp (-2 * ℓ) := e
      _ ≤ 4 * E := by linarith
  -- (iii)
  have h3 : (1 + T) ^ (-(1 / 4 : ℝ)) ≤ 2 * E := by
    have hpos : 0 < Real.exp ℓ / 2 := by positivity
    have h4 := Real.rpow_le_rpow_of_nonpos hpos h1T (by norm_num : -(1 / 4 : ℝ) ≤ 0)
    refine h4.trans ?_
    rw [Real.rpow_def_of_pos hpos, Real.log_div (Real.exp_pos _).ne' (by norm_num),
      Real.log_exp, hE]
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have : Real.exp ((ℓ - Real.log 2) * -(1 / 4)) ≤ Real.exp (-c * ℓ + Real.log 2) := by
      apply Real.exp_le_exp.mpr; nlinarith
    rw [Real.exp_add, Real.exp_log (by norm_num)] at this
    linarith
  -- assemble
  have hper := perron_shiftK hreg' hc.le hC₀ (x := x) (by linarith)
  have hkey : (2 * Real.pi : ℂ) * (∑' n : ℕ, (vR n : ℂ) * (phi 1 (n / x) : ℂ) -
      ((x * (1 - 1 / x) ^ 2 / 2 : ℝ) : ℂ)) = ∫ y : ℝ, gK x (1 + y * I) := by
    rw [mul_sub, hper]; push_cast; ring
  have hnorm : ‖(2 * Real.pi : ℂ) * (∑' n : ℕ, (vR n : ℂ) * (phi 1 (n / x) : ℂ) -
      ((x * (1 - 1 / x) ^ 2 / 2 : ℝ) : ℂ))‖ =
      2 * Real.pi * ‖∑' n : ℕ, (vR n : ℂ) * (phi 1 (n / x) : ℂ) -
      ((x * (1 - 1 / x) ^ 2 / 2 : ℝ) : ℂ)‖ := by
    rw [norm_mul]; congr 1
    rw [show (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hπ]
  rw [hkey] at hnorm
  have hℓ2 : 1 ≤ ℓ ^ 2 := by nlinarith
  have hbound : ‖∫ y : ℝ, gK x (1 + y * I)‖ ≤ K₀ * (x * (ℓ ^ 2 * E)) := by
    refine hcb.trans ?_
    rw [h1]
    have hA : 2 * (x * (16 * C₀ * ℓ ^ 2 / (1 + T) ^ 2)) ≤ 128 * C₀ * (x * (ℓ ^ 2 * E)) := by
      have : 16 * C₀ * ℓ ^ 2 / (1 + T) ^ 2 = 16 * C₀ * ℓ ^ 2 * (1 / (1 + T) ^ 2) := by ring
      rw [this]
      have : 0 ≤ 16 * C₀ * ℓ ^ 2 := by positivity
      have h5 : 16 * C₀ * ℓ ^ 2 * (1 / (1 + T) ^ 2) ≤ 16 * C₀ * ℓ ^ 2 * (4 * E) :=
        mul_le_mul_of_nonneg_left h2 this
      nlinarith
    have hB : x * (512 * C₀) * (1 + T) ^ (-(1 / 4 : ℝ)) * I₅ ≤
        1024 * C₀ * I₅ * (x * (ℓ ^ 2 * E)) := by
      have : 0 ≤ x * (512 * C₀) := by positivity
      have h6 : x * (512 * C₀) * (1 + T) ^ (-(1 / 4 : ℝ)) ≤ x * (512 * C₀) * (2 * E) :=
        mul_le_mul_of_nonneg_left h3 this
      have h7 : x * (512 * C₀) * (2 * E) ≤ x * (512 * C₀) * (2 * (ℓ ^ 2 * E)) := by
        gcongr; nlinarith
      have h8 := mul_le_mul_of_nonneg_right (h6.trans h7) hI₅0
      nlinarith
    have hC : x * E * (16 * C₀ * ℓ ^ 2) * I₂ = 16 * C₀ * I₂ * (x * (ℓ ^ 2 * E)) := by ring
    rw [hC, hK₀]
    nlinarith
  have hfin : ℓ ^ 2 * E ≤ (4 / c) ^ 2 * Real.exp (-(c / 2) * ℓ) := sq_mul_exp_le hc hℓ0.le
  rw [hnorm] at hbound
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hπ]
  have : K₀ * (x * (ℓ ^ 2 * E)) ≤ K₀ * (x * ((4 / c) ^ 2 * Real.exp (-(c / 2) * ℓ))) := by
    gcongr
  nlinarith

end RamanujanTau.SelbergDelange
