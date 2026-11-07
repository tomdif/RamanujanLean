import RamanujanTau.HardyRamanujan.Main
import RamanujanTau.CardySaddle
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Entropy of ordinary partitions

Logarithmic consequences of the proved Hardy–Ramanujan asymptotic for
`p n = Fintype.card (Nat.Partition n)`, and its normalization against the Cardy
saddle algebra. No identification with black-hole microstates is asserted.
-/

set_option autoImplicit false

namespace HardyRamanujan

open Filter
open scoped Real Topology

lemma partition_count_pos (n : ℕ) : 0 < (p n : ℝ) := by
  exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (Nat.Partition n))

/-- The full additive error in the logarithmic Hardy–Ramanujan formula tends to zero. -/
theorem entropy_remainder_tendsto_zero :
    Tendsto (fun n : ℕ => Real.log (p n : ℝ) - π * √(2 * n / 3) +
      Real.log (4 * √3 * n)) atTop (𝓝 0) := by
  have h := hardy_ramanujan.log (by norm_num)
  simp only [Real.log_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Real.log_div (mul_pos (partition_count_pos n) (by positivity)).ne'
    (Real.exp_ne_zero _), Real.log_mul (partition_count_pos n).ne' (by positivity),
    Real.log_exp]
  ring

/-- `log p(n) = π√(2n/3) - log n - log(4√3) + o(1)`. -/
theorem entropy_log_correction :
    Tendsto (fun n : ℕ => Real.log (p n : ℝ) - π * √(2 * n / 3) + Real.log n)
      atTop (𝓝 (-Real.log (4 * √3))) := by
  have h := entropy_remainder_tendsto_zero.sub_const (Real.log (4 * √3))
  simp only [zero_sub] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Real.log_mul (by positivity) hn0.ne']
  ring

/-- The leading entropy growth for the actual number of ordinary partitions. -/
theorem entropy_sqrt_limit :
    Tendsto (fun n : ℕ => Real.log (p n : ℝ) / √n)
      atTop (𝓝 (π * √(2 / 3 : ℝ))) := by
  have hinv : Tendsto (fun n : ℕ => (√(n : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ) / √n) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ← Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_atTop (r := (1 / 2 : ℝ)) (by norm_num)).tendsto_div_nhds_zero.comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  have hsmall := entropy_log_correction.mul hinv
  simp only [mul_zero] at hsmall
  have h := (hsmall.sub hlog).add_const (π * √(2 / 3 : ℝ))
  simp only [sub_zero, zero_add] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : √(2 * (n : ℝ) / 3) = √(2 / 3 : ℝ) * √n := by
    rw [show 2 * (n : ℝ) / 3 = (2 / 3) * n by ring, Real.sqrt_mul (by norm_num)]
  rw [hs]
  have hs0 : √(n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hn0).ne'
  field_simp
  ring

/-- Match unifiedtheory's `C = 1/12` normalization with the partition exponent. -/
theorem partition_cardy_leading (n : ℕ) :
    Cardy.leadingEntropy (1 / 12) n = π * √(2 * n / 3) := by
  unfold Cardy.leadingEntropy
  have hs : √(2 * (n : ℝ) / 3) = 2 * √(2 * (1 / 12) * n) := by
    rw [show 2 * (n : ℝ) / 3 = 2 ^ 2 * (2 * (1 / 12) * n) by ring,
      Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  rw [hs]
  ring

/-- The partition saddle `π/√(6n)` attains the minimum over positive inverse temperatures. -/
theorem partition_saddle_minimum {n : ℕ} (hn : 1 ≤ n) :
    Cardy.saddleExponent (1 / 12) n (tn n) = Cardy.leadingEntropy (1 / 12) n ∧
      ∀ β : ℝ, 0 < β →
        Cardy.saddleExponent (1 / 12) n (tn n) ≤ Cardy.saddleExponent (1 / 12) n β := by
  have heq : Cardy.saddleExponent (1 / 12) n (tn n) =
      Cardy.leadingEntropy (1 / 12) n := by
    apply Cardy.saddle_eq_leading_of_balance _ _ _ (by norm_num) (by positivity) (tn_pos hn)
    calc
      2 * π ^ 2 * (1 / 12) / tn n = π ^ 2 / (6 * tn n) := by ring
      _ = An n := An_eq hn
      _ = tn n * n := by unfold An; ring
  refine ⟨heq, ?_⟩
  intro β hβ
  rw [heq]
  exact Cardy.leading_le_saddle _ _ _ (by norm_num) (by positivity) hβ

/-- The actual partition entropy has the Cardy leading term and an explicit logarithmic correction. -/
theorem entropy_cardy_log_correction :
    Tendsto (fun n : ℕ => Real.log (p n : ℝ) - Cardy.leadingEntropy (1 / 12) n +
      Real.log n) atTop (𝓝 (-Real.log (4 * √3))) := by
  simpa only [partition_cardy_leading] using entropy_log_correction

end HardyRamanujan
