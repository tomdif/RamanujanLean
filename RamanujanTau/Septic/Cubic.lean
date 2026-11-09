/-
# The cubic `r(ξ) = ξ³ − 6ξ² + 5ξ − 1` and its roots `1/(2cos(kπ/7))²` (Rebák §4)

`−(2y)⁶ r(1/(2y)²) = U₆(y) = 64y⁶ − 80y⁴ + 24y² − 1`, and `U₆(cos θ) sin θ = sin 7θ` (Mathlib's Chebyshev `U`),
so `r(1/(4cos²(kπ/7))) = 0` for `k = 1, 2, 3`. We also record the elementary order facts
`1/(4cos²(3π/7)) > 1 > 1/(4cos²(2π/7)) > 1/(4cos²(π/7))`.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option autoImplicit false

namespace RamanujanTau.Septic

open Real Polynomial

/-- Ramanujan's cubic at `p = 1`, `R = 7`. -/
def rcub (ξ : ℝ) : ℝ := ξ ^ 3 - 6 * ξ ^ 2 + 5 * ξ - 1

lemma U6_eq : Chebyshev.U ℝ 6 = 64 * X ^ 6 - 80 * X ^ 4 + 24 * X ^ 2 - 1 := by
  have h3 := Chebyshev.U_add_two ℝ 1
  have h4 := Chebyshev.U_add_two ℝ 2
  have h5 := Chebyshev.U_add_two ℝ 3
  have h6 := Chebyshev.U_add_two ℝ 4
  norm_num at h3 h4 h5 h6
  rw [h6, h5, h4, h3, Chebyshev.U_two]
  ring

lemma U6_cos (k : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ 6) :
    64 * cos (k * π / 7) ^ 6 - 80 * cos (k * π / 7) ^ 4 + 24 * cos (k * π / 7) ^ 2 - 1 = 0 := by
  have h := Chebyshev.U_real_cos (k * π / 7) 6
  rw [U6_eq] at h
  simp only [eval_sub, eval_add, eval_mul, eval_pow, eval_X, eval_ofNat, eval_one] at h
  have hs : sin ((((6 : ℤ) : ℝ) + 1) * ((k : ℝ) * π / 7)) = 0 := by
    rw [show (((6 : ℤ) : ℝ) + 1) * ((k : ℝ) * π / 7) = ((k : ℤ) : ℝ) * π by push_cast; ring]
    exact sin_int_mul_pi k
  have hpos : 0 < sin (k * π / 7) := by
    apply sin_pos_of_pos_of_lt_pi
    · have : (1 : ℝ) ≤ k := by exact_mod_cast hk1
      have := pi_pos; positivity
    · have : (k : ℝ) ≤ 6 := by exact_mod_cast hk
      have := pi_pos; nlinarith
  rw [hs] at h
  have := (mul_eq_zero.mp h).resolve_right hpos.ne'
  linarith

/-- `r(1/(4y²)) = 0` whenever `U₆(y) = 0`. -/
lemma rcub_root (y : ℝ) (hy : y ≠ 0)
    (h : 64 * y ^ 6 - 80 * y ^ 4 + 24 * y ^ 2 - 1 = 0) : rcub (1 / (4 * y ^ 2)) = 0 := by
  unfold rcub
  have hy2 : y ^ 2 ≠ 0 := pow_ne_zero 2 hy
  field_simp
  linear_combination (-1 : ℝ) * h

lemma cos_k_pos (k : ℕ) (hk : k ≤ 3) : 0 < cos (k * π / 7) := by
  apply cos_pos_of_mem_Ioo
  have : (k : ℝ) ≤ 3 := by exact_mod_cast hk
  have := pi_pos
  constructor <;> nlinarith [Nat.cast_nonneg (α := ℝ) k]

/-- the three roots -/
noncomputable def rootA : ℝ := 1 / (4 * cos (3 * π / 7) ^ 2)
noncomputable def rootB : ℝ := 1 / (4 * cos (2 * π / 7) ^ 2)
noncomputable def rootC : ℝ := 1 / (4 * cos (1 * π / 7) ^ 2)

lemma c1_pos : 0 < cos (1 * π / 7) := by exact_mod_cast cos_k_pos 1 (by norm_num)
lemma c2_pos : 0 < cos (2 * π / 7) := by exact_mod_cast cos_k_pos 2 (by norm_num)
lemma c3_pos : 0 < cos (3 * π / 7) := by exact_mod_cast cos_k_pos 3 (by norm_num)

lemma rootA_root : rcub rootA = 0 :=
  rcub_root _ c3_pos.ne' (by exact_mod_cast U6_cos 3 (by norm_num) (by norm_num))
lemma rootB_root : rcub rootB = 0 :=
  rcub_root _ c2_pos.ne' (by exact_mod_cast U6_cos 2 (by norm_num) (by norm_num))
lemma rootC_root : rcub rootC = 0 :=
  rcub_root _ c1_pos.ne' (by exact_mod_cast U6_cos 1 (by norm_num) (by norm_num))

lemma c3_lt_half : cos (3 * π / 7) < 1 / 2 := by
  rw [← cos_pi_div_three]
  apply cos_lt_cos_of_nonneg_of_le_pi (by positivity) (by nlinarith [pi_pos])
  nlinarith [pi_pos]

lemma c2_gt_half : 1 / 2 < cos (2 * π / 7) := by
  rw [← cos_pi_div_three]
  apply cos_lt_cos_of_nonneg_of_le_pi (by positivity) (by nlinarith [pi_pos])
  nlinarith [pi_pos]

lemma c1_gt_c2 : cos (2 * π / 7) < cos (1 * π / 7) := by
  apply cos_lt_cos_of_nonneg_of_le_pi (by positivity) (by nlinarith [pi_pos])
  nlinarith [pi_pos]

lemma rootA_gt_one : 1 < rootA := by
  unfold rootA
  have h0 := c3_pos; have h1 := c3_lt_half
  rw [lt_div_iff₀ (by positivity)]; nlinarith

lemma rootB_lt_one : rootB < 1 := by
  unfold rootB
  have h0 := c2_pos; have h1 := c2_gt_half
  rw [div_lt_iff₀ (by positivity)]; nlinarith

lemma rootC_lt_rootB : rootC < rootB := by
  unfold rootB rootC
  have h0 := c2_pos; have h1 := c1_gt_c2
  apply one_div_lt_one_div_of_lt (by positivity)
  nlinarith

end RamanujanTau.Septic
