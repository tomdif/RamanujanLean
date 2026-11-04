import RamanujanTau.HalfHecke.Gauss
import RamanujanTau.AtkinSporadic.HalfHecke

/-!
# The sign of the quadratic Gauss sum for `Q = 11` and `Q = 37`

`gQ 11 = i√11` and `gQ 37 = √37`. From `gQ² = (−1/Q)Q` the sum is `±` these values; the sign is
fixed by `Im gQ 11 = Σ (b/11) sin(2πb/11) > 0` and `Re gQ 37 = Σ (b/37) cos(2πb/37) > 0`, which
follow by pairing quadratic residues with larger non-residues and monotonicity of `sin`, `cos`.
-/

set_option autoImplicit false
open Complex Finset
open scoped Real
namespace RamanujanTau.HalfHecke

noncomputable section

variable (Q : ℕ) [hQ : Fact Q.Prime]
omit hQ in
lemma term_eq (x : ℤ) (b : ℕ) : ((x : ℂ)) * cexp (2 * π * I * b / Q) = ((x * Real.cos (2*π*b/Q) : ℝ) : ℂ) + ((x * Real.sin (2*π*b/Q) : ℝ) : ℂ) * I := by
  have : (2 * π * I * b / Q : ℂ) = ((2*π*b/Q : ℝ) : ℂ) * I := by push_cast; ring
  rw [this, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]; push_cast; ring
lemma gQ_re : (gQ Q).re = ∑ b ∈ range Q, (legendreSym Q b : ℝ) * Real.cos (2*π*b/Q) := by
  rw [gQ_eq_range, Complex.re_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [term_eq]; simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im]; ring
lemma gQ_im : (gQ Q).im = ∑ b ∈ range Q, (legendreSym Q b : ℝ) * Real.sin (2*π*b/Q) := by
  rw [gQ_eq_range, Complex.im_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [term_eq]; simp only [Complex.add_im, Complex.ofReal_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_im]; ring
instance fact11 : Fact (Nat.Prime 11) := ⟨by norm_num⟩
instance fact37 : Fact (Nat.Prime 37) := ⟨by norm_num⟩
theorem gQ_im_pos_11 : 0 < (gQ 11).im := by
  rw [gQ_im]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, zero_add]
  have l0 : legendreSym 11 0 = 0 := by rw [AtkinSporadic.legendreSym_val 11 (by norm_num)]; decide
  have l1 : legendreSym 11 1 = 1 := by rw [AtkinSporadic.legendreSym_val 11 (by norm_num)]; decide
  have l2 : legendreSym 11 2 = -1 := by rw [AtkinSporadic.legendreSym_val 11 (by norm_num)]; decide
  have l3 : legendreSym 11 3 = 1 := by rw [AtkinSporadic.legendreSym_val 11 (by norm_num)]; decide
  have l4 : legendreSym 11 4 = 1 := by rw [AtkinSporadic.legendreSym_val 11 (by norm_num)]; decide
  have l5 : legendreSym 11 5 = 1 := by rw [AtkinSporadic.legendreSym_val 11 (by norm_num)]; decide
  have l6 : legendreSym 11 6 = -1 := by rw [AtkinSporadic.legendreSym_val 11 (by norm_num)]; decide
  have l7 : legendreSym 11 7 = -1 := by rw [AtkinSporadic.legendreSym_val 11 (by norm_num)]; decide
  have l8 : legendreSym 11 8 = -1 := by rw [AtkinSporadic.legendreSym_val 11 (by norm_num)]; decide
  have l9 : legendreSym 11 9 = 1 := by rw [AtkinSporadic.legendreSym_val 11 (by norm_num)]; decide
  have l10 : legendreSym 11 10 = -1 := by rw [AtkinSporadic.legendreSym_val 11 (by norm_num)]; decide
  simp only [l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10]
  push_cast
  have e6 : Real.sin (2 * π * 6 / 11) = - Real.sin (2 * π * 5 / 11) := by rw [← Real.sin_two_pi_sub]; congr 1; ring
  have e7 : Real.sin (2 * π * 7 / 11) = - Real.sin (2 * π * 4 / 11) := by rw [← Real.sin_two_pi_sub]; congr 1; ring
  have e8 : Real.sin (2 * π * 8 / 11) = - Real.sin (2 * π * 3 / 11) := by rw [← Real.sin_two_pi_sub]; congr 1; ring
  have e9 : Real.sin (2 * π * 9 / 11) = - Real.sin (2 * π * 2 / 11) := by rw [← Real.sin_two_pi_sub]; congr 1; ring
  have e10 : Real.sin (2 * π * 10 / 11) = - Real.sin (2 * π * 1 / 11) := by rw [← Real.sin_two_pi_sub]; congr 1; ring
  rw [e6, e7, e8, e9, e10]
  have hpi := Real.pi_pos
  have p1 : 0 < Real.sin (2 * π * 1 / 11) := Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith)
  have p4 : 0 < Real.sin (2 * π * 4 / 11) := Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith)
  have p5 : 0 < Real.sin (2 * π * 5 / 11) := Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith)
  have p3 : Real.sin (2 * π * 2 / 11) < Real.sin (2 * π * 3 / 11) := by
    rw [show 2 * π * 3 / 11 = π - 5 * π / 11 by ring, Real.sin_pi_sub]
    exact Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) (by linarith) (by linarith)
  linarith
theorem gQ_re_pos_37 : 0 < (gQ 37).re := by
  rw [gQ_re]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, zero_add]
  have l0 : legendreSym 37 0 = 0 := by rw [AtkinSporadic.legendreSym_val 37 (by norm_num)]; decide
  have l1 : legendreSym 37 1 = 1 := by rw [AtkinSporadic.legendreSym_val 37 (by norm_num)]; decide
  have l2 : legendreSym 37 2 = -1 := by rw [AtkinSporadic.legendreSym_val 37 (by norm_num)]; decide
  have l3 : legendreSym 37 3 = 1 := by rw [AtkinSporadic.legendreSym_val 37 (by norm_num)]; decide
  have l4 : legendreSym 37 4 = 1 := by rw [AtkinSporadic.legendreSym_val 37 (by norm_num)]; decide
  have l5 : legendreSym 37 5 = -1 := by rw [AtkinSporadic.legendreSym_val 37 (by norm_num)]; decide
  have l6 : legendreSym 37 6 = -1 := by rw [AtkinSporadic.legendreSym_val 37 (by norm_num)]; decide
  have l7 : legendreSym 37 7 = 1 := by rw [AtkinSporadic.legendreSym_val 37 (by norm_num)]; decide
  have l8 : legendreSym 37 8 = -1 := by rw [AtkinSporadic.legendreSym_val 37 (by norm_num)]; decide
  have l9 : legendreSym 37 9 = 1 := by rw [AtkinSporadic.legendreSym_val 37 (by norm_num)]; decide
  have l10 : legendreSym 37 10 = 1 := by rw [AtkinSporadic.legendreSym_val 37 (by norm_num)]; decide
  have l11 : legendreSym 37 11 = 1 := by rw [AtkinSporadic.legendreSym_val 37 (by norm_num)]; decide
  have l12 : legendreSym 37 12 = 1 := by rw [AtkinSporadic.legendreSym_val 37 (by norm_num)]; decide
  have l13 : legendreSym 37 13 = -1 := by rw [AtkinSporadic.legendreSym_val 37 (by norm_num)]; decide
  have l14 : legendreSym 37 14 = -1 := by rw [AtkinSporadic.legendreSym_val 37 (by norm_num)]; decide
  have l15 : legendreSym 37 15 = -1 := by rw [AtkinSporadic.legendreSym_val 37 (by norm_num)]; decide
  have l16 : legendreSym 37 16 = 1 := by rw [AtkinSporadic.legendreSym_val 37 (by norm_num)]; decide
  have l17 : legendreSym 37 17 = -1 := by rw [AtkinSporadic.legendreSym_val 37 (by norm_num)]; decide
  have l18 : legendreSym 37 18 = -1 := by rw [AtkinSporadic.legendreSym_val 37 (by norm_num)]; decide
  have l19 : legendreSym 37 19 = -1 := by rw [AtkinSporadic.legendreSym_val 37 (by norm_num)]; decide
  have l20 : legendreSym 37 20 = -1 := by rw [AtkinSporadic.legendreSym_val 37 (by norm_num)]; decide
  have l21 : legendreSym 37 21 = 1 := by rw [AtkinSporadic.legendreSym_val 37 (by norm_num)]; decide
  have l22 : legendreSym 37 22 = -1 := by rw [AtkinSporadic.legendreSym_val 37 (by norm_num)]; decide
  have l23 : legendreSym 37 23 = -1 := by rw [AtkinSporadic.legendreSym_val 37 (by norm_num)]; decide
  have l24 : legendreSym 37 24 = -1 := by rw [AtkinSporadic.legendreSym_val 37 (by norm_num)]; decide
  have l25 : legendreSym 37 25 = 1 := by rw [AtkinSporadic.legendreSym_val 37 (by norm_num)]; decide
  have l26 : legendreSym 37 26 = 1 := by rw [AtkinSporadic.legendreSym_val 37 (by norm_num)]; decide
  have l27 : legendreSym 37 27 = 1 := by rw [AtkinSporadic.legendreSym_val 37 (by norm_num)]; decide
  have l28 : legendreSym 37 28 = 1 := by rw [AtkinSporadic.legendreSym_val 37 (by norm_num)]; decide
  have l29 : legendreSym 37 29 = -1 := by rw [AtkinSporadic.legendreSym_val 37 (by norm_num)]; decide
  have l30 : legendreSym 37 30 = 1 := by rw [AtkinSporadic.legendreSym_val 37 (by norm_num)]; decide
  have l31 : legendreSym 37 31 = -1 := by rw [AtkinSporadic.legendreSym_val 37 (by norm_num)]; decide
  have l32 : legendreSym 37 32 = -1 := by rw [AtkinSporadic.legendreSym_val 37 (by norm_num)]; decide
  have l33 : legendreSym 37 33 = 1 := by rw [AtkinSporadic.legendreSym_val 37 (by norm_num)]; decide
  have l34 : legendreSym 37 34 = 1 := by rw [AtkinSporadic.legendreSym_val 37 (by norm_num)]; decide
  have l35 : legendreSym 37 35 = -1 := by rw [AtkinSporadic.legendreSym_val 37 (by norm_num)]; decide
  have l36 : legendreSym 37 36 = 1 := by rw [AtkinSporadic.legendreSym_val 37 (by norm_num)]; decide
  simp only [l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15, l16, l17, l18, l19, l20, l21, l22, l23, l24, l25, l26, l27, l28, l29, l30, l31, l32, l33, l34, l35, l36]
  push_cast
  have e19 : Real.cos (2 * π * 19 / 37) = Real.cos (2 * π * 18 / 37) := by rw [← Real.cos_two_pi_sub]; congr 1; ring
  have e20 : Real.cos (2 * π * 20 / 37) = Real.cos (2 * π * 17 / 37) := by rw [← Real.cos_two_pi_sub]; congr 1; ring
  have e21 : Real.cos (2 * π * 21 / 37) = Real.cos (2 * π * 16 / 37) := by rw [← Real.cos_two_pi_sub]; congr 1; ring
  have e22 : Real.cos (2 * π * 22 / 37) = Real.cos (2 * π * 15 / 37) := by rw [← Real.cos_two_pi_sub]; congr 1; ring
  have e23 : Real.cos (2 * π * 23 / 37) = Real.cos (2 * π * 14 / 37) := by rw [← Real.cos_two_pi_sub]; congr 1; ring
  have e24 : Real.cos (2 * π * 24 / 37) = Real.cos (2 * π * 13 / 37) := by rw [← Real.cos_two_pi_sub]; congr 1; ring
  have e25 : Real.cos (2 * π * 25 / 37) = Real.cos (2 * π * 12 / 37) := by rw [← Real.cos_two_pi_sub]; congr 1; ring
  have e26 : Real.cos (2 * π * 26 / 37) = Real.cos (2 * π * 11 / 37) := by rw [← Real.cos_two_pi_sub]; congr 1; ring
  have e27 : Real.cos (2 * π * 27 / 37) = Real.cos (2 * π * 10 / 37) := by rw [← Real.cos_two_pi_sub]; congr 1; ring
  have e28 : Real.cos (2 * π * 28 / 37) = Real.cos (2 * π * 9 / 37) := by rw [← Real.cos_two_pi_sub]; congr 1; ring
  have e29 : Real.cos (2 * π * 29 / 37) = Real.cos (2 * π * 8 / 37) := by rw [← Real.cos_two_pi_sub]; congr 1; ring
  have e30 : Real.cos (2 * π * 30 / 37) = Real.cos (2 * π * 7 / 37) := by rw [← Real.cos_two_pi_sub]; congr 1; ring
  have e31 : Real.cos (2 * π * 31 / 37) = Real.cos (2 * π * 6 / 37) := by rw [← Real.cos_two_pi_sub]; congr 1; ring
  have e32 : Real.cos (2 * π * 32 / 37) = Real.cos (2 * π * 5 / 37) := by rw [← Real.cos_two_pi_sub]; congr 1; ring
  have e33 : Real.cos (2 * π * 33 / 37) = Real.cos (2 * π * 4 / 37) := by rw [← Real.cos_two_pi_sub]; congr 1; ring
  have e34 : Real.cos (2 * π * 34 / 37) = Real.cos (2 * π * 3 / 37) := by rw [← Real.cos_two_pi_sub]; congr 1; ring
  have e35 : Real.cos (2 * π * 35 / 37) = Real.cos (2 * π * 2 / 37) := by rw [← Real.cos_two_pi_sub]; congr 1; ring
  have e36 : Real.cos (2 * π * 36 / 37) = Real.cos (2 * π * 1 / 37) := by rw [← Real.cos_two_pi_sub]; congr 1; ring
  rw [e19, e20, e21, e22, e23, e24, e25, e26, e27, e28, e29, e30, e31, e32, e33, e34, e35, e36]
  have hpi := Real.pi_pos
  have c1 : Real.cos (2 * π * 2 / 37) < Real.cos (2 * π * 1 / 37) := Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity) (by linarith) (by linarith)
  have c3 : Real.cos (2 * π * 5 / 37) < Real.cos (2 * π * 3 / 37) := Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity) (by linarith) (by linarith)
  have c4 : Real.cos (2 * π * 6 / 37) < Real.cos (2 * π * 4 / 37) := Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity) (by linarith) (by linarith)
  have c7 : Real.cos (2 * π * 8 / 37) < Real.cos (2 * π * 7 / 37) := Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity) (by linarith) (by linarith)
  have c9 : Real.cos (2 * π * 13 / 37) < Real.cos (2 * π * 9 / 37) := Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity) (by linarith) (by linarith)
  have c10 : Real.cos (2 * π * 14 / 37) < Real.cos (2 * π * 10 / 37) := Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity) (by linarith) (by linarith)
  have c11 : Real.cos (2 * π * 15 / 37) < Real.cos (2 * π * 11 / 37) := Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity) (by linarith) (by linarith)
  have c12 : Real.cos (2 * π * 17 / 37) < Real.cos (2 * π * 12 / 37) := Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity) (by linarith) (by linarith)
  have c16 : Real.cos (2 * π * 18 / 37) < Real.cos (2 * π * 16 / 37) := Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity) (by linarith) (by linarith)
  linarith

/-- **Gauss: `gQ 11 = i√11`.** -/
theorem gQ_11 : gQ 11 = I * ((Real.sqrt 11 : ℝ) : ℂ) := by
  have hsq := gQ_sq 11 (by norm_num)
  have hm : chiQ 11 (-1) = -1 := by
    rw [chiQ_apply, show quadraticChar (ZMod 11) (-1) = -1 by decide]; norm_num
  rw [hm] at hsq
  have hs : ((Real.sqrt 11 : ℝ) : ℂ) ^ 2 = 11 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have h2 : gQ 11 ^ 2 = (I * ((Real.sqrt 11 : ℝ) : ℂ)) ^ 2 := by
    rw [hsq, mul_pow, hs, I_sq]; push_cast; ring
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h2 with h | h
  · exact h
  · exfalso
    have him := gQ_im_pos_11
    rw [h] at him
    simp at him
    have := Real.sqrt_nonneg 11
    linarith

/-- **Gauss: `gQ 37 = √37`.** -/
theorem gQ_37 : gQ 37 = ((Real.sqrt 37 : ℝ) : ℂ) := by
  have hsq := gQ_sq 37 (by norm_num)
  have hm : chiQ 37 (-1) = 1 := by
    rw [chiQ_apply, show quadraticChar (ZMod 37) (-1) = 1 by decide]; norm_num
  rw [hm] at hsq
  have hs : ((Real.sqrt 37 : ℝ) : ℂ) ^ 2 = 37 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have h2 : gQ 37 ^ 2 = ((Real.sqrt 37 : ℝ) : ℂ) ^ 2 := by
    rw [hsq, hs]; push_cast; ring
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h2 with h | h
  · exact h
  · exfalso
    have hre := gQ_re_pos_37
    rw [h] at hre
    simp at hre
    have := Real.sqrt_nonneg 37
    linarith

end

end RamanujanTau.HalfHecke
