/-
# Tauberian step 3: choice of parameters

`Rmean_bound`: `|R(x)| ≤ C h x^{12 − 1/8000}` for `x ≥ max(1,h)`, with `L = x^{1−1/4000}`.
-/
import RamanujanTau.SCSProof.Tauber2

set_option autoImplicit false

namespace RamanujanTau.SCSProof

open MeasureTheory Complex Filter
open RamanujanTau.RankinError
open scoped Real

lemma I2_nonneg : 0 ≤ I2 := integral_nonneg fun y => by positivity
lemma I32_nonneg : 0 ≤ I32 := integral_nonneg fun y => by positivity

set_option maxHeartbeats 2000000 in
theorem Rmean_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℕ, 1 ≤ h → ∀ x : ℝ, 1 ≤ x → (h : ℝ) ≤ x →
    |Rmean h x (x * x ^ (-(1 / 4000 : ℝ)))| ≤ C * h * x ^ (12 - 1 / 8000 : ℝ) := by
  obtain ⟨K, hK0, hK⟩ := pointwise_G
  obtain ⟨C₀, hC₀, hT⟩ := abs_laplace_le
  refine ⟨4 * Real.exp 1 * (I2 * K * 5 ^ 32 + 2 * I32 * C₀), by
    have := I2_nonneg; have := I32_nonneg; positivity, fun h hh x hx hhx => ?_⟩
  have hx0 : 0 < x := by linarith
  set s := x ^ (1 / 8000 : ℝ) with hs
  have hs0 : 0 < s := Real.rpow_pos_of_pos hx0 _
  have hs1 : 1 ≤ s := Real.one_le_rpow hx (by norm_num)
  have hxs : x = s ^ 8000 := by
    rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
  have hσ : x ^ (-(1 / 4000 : ℝ)) = 1 / s ^ 2 := by
    rw [hxs, ← Real.rpow_natCast, ← Real.rpow_mul hs0.le]
    rw [show ((8000 : ℕ) : ℝ) * -(1 / 4000) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hs0.le,
      Real.rpow_natCast, one_div]
  have hσ0 : 0 < x ^ (-(1 / 4000 : ℝ)) := Real.rpow_pos_of_pos hx0 _
  have hσ1 : x ^ (-(1 / 4000 : ℝ)) ≤ 1 := by rw [hσ]; rw [div_le_one (by positivity)]; nlinarith [one_le_pow₀ hs1 (n := 2)]
  have hY : (1 : ℝ) ≤ s ^ 10 := one_le_pow₀ hs1
  have hR := Rmean_le K C₀ hK0 hC₀ hK hT h hh hx hhx hσ0 hσ1 hY
  have hh0 : (1 : ℝ) ≤ h := by exact_mod_cast hh
  -- simplify the right-hand side
  have e1 : x ^ (477 / 40 : ℝ) = s ^ 95400 := by
    rw [hxs, ← Real.rpow_natCast s 8000, ← Real.rpow_mul hs0.le,
      show ((8000 : ℕ) : ℝ) * (477 / 40) = ((95400 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have e2 : (s ^ 10) ^ (-(1 / 2 : ℝ)) = 1 / s ^ 5 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs0.le,
      show ((10 : ℕ) : ℝ) * -(1 / 2) = -((5 : ℕ) : ℝ) by norm_num, Real.rpow_neg hs0.le,
      Real.rpow_natCast, one_div]
  have e3 : x ^ (12 - 1 / 8000 : ℝ) = s ^ 95999 := by
    rw [hxs, ← Real.rpow_natCast s 8000, ← Real.rpow_mul hs0.le,
      show ((8000 : ℕ) : ℝ) * (12 - 1 / 8000) = ((95999 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [e1, e2, hσ] at hR
  rw [e3, hσ]
  have hθ : 2 * s ^ 10 / (1 / s ^ 2) + 3 ≤ 5 * s ^ 12 := by
    have : 2 * s ^ 10 / (1 / s ^ 2) = 2 * s ^ 12 := by field_simp
    rw [this]; nlinarith [one_le_pow₀ hs1 (n := 12)]
  have hθ32 : (2 * s ^ 10 / (1 / s ^ 2) + 3) ^ 32 ≤ 5 ^ 32 * s ^ 384 := by
    calc (2 * s ^ 10 / (1 / s ^ 2) + 3) ^ 32 ≤ (5 * s ^ 12) ^ 32 := by
          gcongr
      _ = 5 ^ 32 * s ^ 384 := by ring
  have hx12 : x ^ 12 = s ^ 96000 := by rw [hxs]; ring
  rw [hx12] at hR
  have hI2 := I2_nonneg; have hI32 := I32_nonneg
  have hbig : Real.exp 1 * (2 / (1 / s ^ 2)) ^ 2 * (I2 * (K * h * (2 * s ^ 10 / (1 / s ^ 2) + 3) ^ 32 *
      s ^ 95400) + I32 * (1 / s ^ 5) * (2 * C₀ * s ^ 96000)) ≤
      4 * Real.exp 1 * (I2 * K * 5 ^ 32 + 2 * I32 * C₀) * h * s ^ 95999 := by
    have e4 : (2 / (1 / s ^ 2)) ^ 2 = 4 * s ^ 4 := by field_simp; ring
    rw [e4]
    have k1 : I2 * (K * h * (2 * s ^ 10 / (1 / s ^ 2) + 3) ^ 32 * s ^ 95400) ≤
        I2 * K * 5 ^ 32 * h * s ^ 95784 := by
      calc I2 * (K * h * (2 * s ^ 10 / (1 / s ^ 2) + 3) ^ 32 * s ^ 95400)
          ≤ I2 * (K * h * (5 ^ 32 * s ^ 384) * s ^ 95400) := by gcongr
        _ = I2 * K * 5 ^ 32 * h * s ^ 95784 := by ring
    have k2 : I32 * (1 / s ^ 5) * (2 * C₀ * s ^ 96000) = 2 * I32 * C₀ * s ^ 95995 := by
      field_simp
    have hp1 : s ^ 95784 ≤ s ^ 95995 := pow_le_pow_right₀ hs1 (by norm_num)
    have hp2 : s ^ 95995 ≤ h * s ^ 95995 := by
      have : 0 ≤ s ^ 95995 := by positivity
      nlinarith
    have hA : 0 ≤ I2 * K * 5 ^ 32 * h := by positivity
    have hB : 0 ≤ 2 * I32 * C₀ := by positivity
    calc Real.exp 1 * (4 * s ^ 4) * (I2 * (K * h * (2 * s ^ 10 / (1 / s ^ 2) + 3) ^ 32 * s ^ 95400) +
          I32 * (1 / s ^ 5) * (2 * C₀ * s ^ 96000))
        ≤ Real.exp 1 * (4 * s ^ 4) * (I2 * K * 5 ^ 32 * h * s ^ 95995 + 2 * I32 * C₀ * (h * s ^ 95995)) := by
          rw [k2]
          refine mul_le_mul_of_nonneg_left (add_le_add (k1.trans ?_) ?_) (by positivity)
          · have := mul_le_mul_of_nonneg_left hp1 hA
            linarith
          · exact mul_le_mul_of_nonneg_left hp2 hB
      _ = 4 * Real.exp 1 * (I2 * K * 5 ^ 32 + 2 * I32 * C₀) * h * s ^ 95999 := by ring
  have h2π : 1 ≤ 2 * π := by linarith [Real.pi_gt_three]
  have hRn : 0 ≤ |Rmean h x (x * (1 / s ^ 2))| := abs_nonneg _
  have := hR.trans hbig
  nlinarith

end RamanujanTau.SCSProof
