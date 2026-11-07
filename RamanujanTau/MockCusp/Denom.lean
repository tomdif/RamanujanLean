/-
# A lower bound for `|1 − e^v|` away from `2πiℤ`

`norm_one_sub_exp_ge`: if `|v − 2πik| ≥ r` for every integer `k`, then `‖1 − e^v‖ ≥ min(1, r)/3`.
-/
import Mathlib

set_option autoImplicit false

namespace MockCusp
open Complex
open scoped Real

lemma sq_norm_one_sub_exp (v : ℂ) :
    ‖1 - cexp v‖ ^ 2 = (1 - Real.exp v.re) ^ 2 + 4 * Real.exp v.re * Real.sin (v.im / 2) ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [sub_re, one_re, exp_re, sub_im, one_im, exp_im, zero_sub]
  have h1 : Real.cos v.im = 1 - 2 * Real.sin (v.im / 2) ^ 2 := by
    have e := Real.cos_two_mul (v.im / 2)
    rw [show 2 * (v.im / 2) = v.im by ring] at e
    have := Real.sin_sq_add_cos_sq (v.im / 2)
    linarith
  have h2 := Real.sin_sq_add_cos_sq v.im
  linear_combination (-2 * Real.exp v.re) * h1 + Real.exp v.re ^ 2 * h2

/-- Jordan: `|sin(t/2)| ≥ |t|/π` for `|t| ≤ π`. -/
lemma sin_half_sq_ge {t : ℝ} (ht : |t| ≤ π) : (t / π) ^ 2 ≤ Real.sin (t / 2) ^ 2 := by
  have hpi := Real.pi_pos
  have key : ∀ u : ℝ, 0 ≤ u → u ≤ π → u / π ≤ Real.sin (u / 2) := by
    intro u hu hu'
    have := Real.mul_le_sin (x := u / 2) (by linarith) (by linarith)
    calc u / π = 2 / π * (u / 2) := by field_simp
      _ ≤ _ := this
  rcases le_total 0 t with h | h
  · have hk := key t h (by rw [abs_of_nonneg h] at ht; exact ht)
    have : 0 ≤ t / π := div_nonneg h hpi.le
    nlinarith
  · have hk := key (-t) (by linarith) (by rw [abs_of_nonpos h] at ht; exact ht)
    rw [show -t / 2 = -(t / 2) by ring, Real.sin_neg] at hk
    have : 0 ≤ -t / π := div_nonneg (by linarith) hpi.le
    have e : (t / π) ^ 2 = (-t / π) ^ 2 := by ring
    rw [e]
    nlinarith

/-- the basic case `|Im v| ≤ π`. -/
lemma norm_one_sub_exp_ge_of_im {v : ℂ} (hv : |v.im| ≤ π) : min 1 ‖v‖ / 3 ≤ ‖1 - cexp v‖ := by
  have hpi := Real.pi_pos
  have hpi4 : π ^ 2 < 10 := by nlinarith [Real.pi_lt_d2]
  set s := v.re
  set t := v.im
  have hsq := sq_norm_one_sub_exp v
  have hJ := sin_half_sq_ge hv
  have ht2 : t ^ 2 / 10 ≤ Real.sin (t / 2) ^ 2 := by
    have : (t / π) ^ 2 = t ^ 2 / π ^ 2 := by ring
    rw [this] at hJ
    calc t ^ 2 / 10 ≤ t ^ 2 / π ^ 2 := by
          apply div_le_div_of_nonneg_left (sq_nonneg t) (by positivity) hpi4.le
      _ ≤ _ := hJ
  have hv2 : ‖v‖ ^ 2 = s ^ 2 + t ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  -- lower bound for the squared norm
  have hmain : (min 1 ‖v‖) ^ 2 / 9 ≤ ‖1 - cexp v‖ ^ 2 := by
    have hm1 : (min 1 ‖v‖) ^ 2 ≤ 1 := by
      have := min_le_left 1 ‖v‖
      have h0 : 0 ≤ min 1 ‖v‖ := le_min zero_le_one (norm_nonneg _)
      nlinarith
    have hm2 : (min 1 ‖v‖) ^ 2 ≤ s ^ 2 + t ^ 2 := by
      have := min_le_right 1 ‖v‖
      have h0 : 0 ≤ min 1 ‖v‖ := le_min zero_le_one (norm_nonneg _)
      rw [← hv2]; nlinarith
    rw [hsq]
    rcases le_total 0 s with hs | hs
    · -- `s ≥ 0`
      have he : s ≤ Real.exp s - 1 := by linarith [Real.add_one_le_exp s]
      have he1 : 1 ≤ Real.exp s := Real.one_le_exp hs
      have : s ^ 2 ≤ (1 - Real.exp s) ^ 2 := by nlinarith
      nlinarith [sq_nonneg (Real.sin (t / 2))]
    · rcases le_total (-1) s with hs1 | hs1
      · -- `−1 ≤ s ≤ 0`
        have he : Real.exp s ≤ 1 + s / 2 := by
          -- `e^s ≤ 1 + s + s²/2 ≤ 1 + s/2` for `−1 ≤ s ≤ 0`
          have h := Real.exp_bound' (x := -s) (by linarith) (by linarith) (n := 2) (by norm_num)
          have hpos : 0 < Real.exp (-s) := Real.exp_pos _
          have hinv : Real.exp s = (Real.exp (-s))⁻¹ := by rw [Real.exp_neg, inv_inv]
          -- use the simpler `e^{-s} ≥ 1 − s`
          have hge : 1 - s ≤ Real.exp (-s) := by linarith [Real.add_one_le_exp (-s)]
          have hge2 : 1 - s + s ^ 2 / 2 ≤ Real.exp (-s) := by
            have := Real.quadratic_le_exp_of_nonneg (x := -s) (by linarith)
            nlinarith
          rw [hinv]
          have hd : 0 < 1 - s + s ^ 2 / 2 := by nlinarith
          rw [inv_le_comm₀ hpos (by linarith)]
          calc (1 + s / 2)⁻¹ ≤ 1 - s + s ^ 2 / 2 := by
                rw [inv_le_comm₀ (by linarith) hd]
                rw [inv_eq_one_div, div_le_iff₀ hd]
                nlinarith
            _ ≤ _ := hge2
        have hl : Real.exp (-1) ≤ Real.exp s := Real.exp_le_exp.mpr hs1
        have he1 : (1 : ℝ) / 3 ≤ Real.exp (-1) := by
          rw [Real.exp_neg, one_div]
          exact inv_anti₀ (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
        have ha : s ^ 2 / 4 ≤ (1 - Real.exp s) ^ 2 := by nlinarith
        have hb : 4 * (1 / 3) * (t ^ 2 / 10) ≤ 4 * Real.exp s * Real.sin (t / 2) ^ 2 := by
          have : 0 ≤ t ^ 2 / 10 := by positivity
          have h13 : (1 : ℝ) / 3 ≤ Real.exp s := he1.trans hl
          calc 4 * (1 / 3) * (t ^ 2 / 10) ≤ 4 * Real.exp s * (t ^ 2 / 10) := by gcongr
            _ ≤ _ := by gcongr
        nlinarith
      · -- `s ≤ −1`
        have hl : Real.exp s ≤ Real.exp (-1) := Real.exp_le_exp.mpr hs1
        have he1 : Real.exp (-1) ≤ 1 / 2 := by
          rw [Real.exp_neg, ← one_div]
          rw [div_le_div_iff₀ (Real.exp_pos 1) (by norm_num)]
          linarith [Real.exp_one_gt_d9]
        have : (1 : ℝ) / 4 ≤ (1 - Real.exp s) ^ 2 := by nlinarith [Real.exp_pos s]
        nlinarith [Real.exp_pos s, sq_nonneg (Real.sin (t / 2))]
  have h0 : 0 ≤ min 1 ‖v‖ / 3 := by positivity
  have : (min 1 ‖v‖ / 3) ^ 2 ≤ ‖1 - cexp v‖ ^ 2 := by
    rw [div_pow]; norm_num; linarith
  exact (pow_le_pow_iff_left₀ h0 (norm_nonneg _) (by norm_num)).mp this

/-- **`|1 − e^v| ≥ min(1, r)/3`** when `v` is at distance `≥ r` from `2πiℤ`. -/
theorem norm_one_sub_exp_ge {v : ℂ} {r : ℝ} (hr : ∀ k : ℤ, r ≤ ‖v - 2 * π * I * k‖) :
    min 1 r / 3 ≤ ‖1 - cexp v‖ := by
  have hpi := Real.pi_pos
  set k : ℤ := round (v.im / (2 * π))
  set v' := v - 2 * π * I * k
  have hk : |v.im / (2 * π) - k| ≤ 1 / 2 := abs_sub_round _
  have him : v'.im = v.im - 2 * π * k := by simp [v']
  have hv' : |v'.im| ≤ π := by
    rw [him]
    have : v.im - 2 * π * k = 2 * π * (v.im / (2 * π) - k) := by field_simp
    rw [this, abs_mul, abs_of_pos (by positivity)]
    nlinarith
  have hexp : cexp v' = cexp v := by
    rw [show v' = v + ((-k : ℤ) : ℂ) * (2 * π * I) by simp [v']; ring, Complex.exp_add,
      Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have h1 := norm_one_sub_exp_ge_of_im hv'
  rw [hexp] at h1
  refine le_trans ?_ h1
  gcongr
  exact hr k

end MockCusp
