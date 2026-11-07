/-
# The real-direction shift for the general dual kernel `J_j`

`G_j(s) = y^{s+j} Q_j(s)` is the integrand of `J_j(y) = J_j^{(1/2)}(y)`. From
`KernelPhase.Qk_add_one` (valid for every `j`), `‖G_j(w+1)‖ ‖P_j(w)‖ = 16π⁴ y ‖G_j(w)‖`,
with `P_j(w) = (−w)(m−w)(w+j+1)(w+m)`. Here: the modulus recursion for general `j`, the
upper bound `‖P_j(w)‖ ≤ (‖w+c‖²+c²)(‖w‖²+m²)` (`c = (j+1)/2`), and the right/left
multi-step shifts. This generalises `KernelPhase/Shift.lean` (which is `j = 1`).
-/
import RamanujanTau.KernelPhase.Shift

set_option autoImplicit false

namespace RamanujanTau.RankinExact

open Complex Real Finset
open RamanujanTau.RankinErrorGeneral RamanujanTau.RankinLandau RamanujanTau.KernelPhase

/-- The integrand of `J_j(y)`: `G_j(s) = y^{s+j} Q_j(s)`. -/
noncomputable def Gj (m j : ℕ) (y : ℝ) (s : ℂ) : ℂ := (y : ℂ) ^ (s + (j : ℂ)) * Qk m j s

variable (m j : ℕ)

lemma Jc_eq_Gj (y : ℝ) :
    Jc m j (1 / 2) y = ((1 / (2 * π) : ℝ) : ℂ) * ∫ t : ℝ, Gj m j y (((1 / 2 : ℝ) : ℂ) + t * I) :=
  rfl

lemma norm_Gj {y : ℝ} (hy : 0 < y) (s : ℂ) :
    ‖Gj m j y s‖ = y ^ (s.re + j) * ‖Qk m j s‖ := by
  unfold Gj
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy]
  simp

/-- The modulus recursion `‖G_j(w+1)‖ ‖P_j(w)‖ = 16π⁴ y ‖G_j(w)‖`. -/
lemma norm_Gj_add_one {y : ℝ} (hy : 0 < y) {w : ℂ} (h0 : w ≠ 0) (hm : w ≠ m) :
    ‖Gj m j y (w + 1)‖ * ‖Pk m j w‖ = 16 * π ^ 4 * y * ‖Gj m j y w‖ := by
  have h := congrArg norm (Qk_add_one m j h0 hm)
  rw [norm_mul, norm_mul] at h
  have h16 : ‖(16 : ℂ) * (π : ℂ) ^ 4‖ = 16 * π ^ 4 := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    norm_num
  rw [h16] at h
  rw [norm_Gj m j hy, norm_Gj m j hy, mul_assoc, h,
    show (w + 1).re + j = (w.re + j) + 1 by simp; ring, Real.rpow_add hy, Real.rpow_one]
  ring

lemma norm_Pk_le_gen (w : ℂ) :
    ‖Pk m j w‖ ≤ (‖w + ((j : ℂ) + 1) / 2‖ ^ 2 + (((j : ℝ) + 1) / 2) ^ 2) *
      (‖w‖ ^ 2 + (m : ℝ) ^ 2) := by
  have e : Pk m j w = -(((w + ((j : ℂ) + 1) / 2) ^ 2 - (((j : ℂ) + 1) / 2) ^ 2) *
      ((m : ℂ) ^ 2 - w ^ 2)) := by unfold Pk; ring
  rw [e, norm_neg, norm_mul]
  have hc : ‖(((j : ℂ) + 1) / 2) ^ 2‖ = (((j : ℝ) + 1) / 2) ^ 2 := by
    rw [norm_pow, show ((j : ℂ) + 1) / 2 = (((j : ℝ) + 1) / 2 : ℝ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have a1 : ‖(w + ((j : ℂ) + 1) / 2) ^ 2 - (((j : ℂ) + 1) / 2) ^ 2‖ ≤
      ‖w + ((j : ℂ) + 1) / 2‖ ^ 2 + (((j : ℝ) + 1) / 2) ^ 2 := by
    refine (norm_sub_le _ _).trans ?_; rw [norm_pow, hc]
  have a2 : ‖(m : ℂ) ^ 2 - w ^ 2‖ ≤ ‖w‖ ^ 2 + (m : ℝ) ^ 2 := by
    refine (norm_sub_le _ _).trans ?_; rw [norm_pow, norm_pow, Complex.norm_natCast]; linarith
  exact mul_le_mul a1 a2 (norm_nonneg _) (by positivity)

/-- **Shift to the right**: for `Im s ≠ 0`, `‖G_j(s+k)‖ ≤ ‖G_j(s)‖ (16π⁴y/(Im s)⁴)^k`. -/
theorem norm_Gj_add_nat_le {y : ℝ} (hy : 0 < y) {s : ℂ} (hs : s.im ≠ 0) (k : ℕ) :
    ‖Gj m j y (s + k)‖ ≤ ‖Gj m j y s‖ * (16 * π ^ 4 * y / s.im ^ 4) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    set w : ℂ := s + k with hw
    have hwim : w.im = s.im := by simp [hw]
    have h0 : w ≠ 0 := fun h => hs (by rw [← hwim, h]; simp)
    have hm : w ≠ m := fun h => hs (by rw [← hwim, h]; simp)
    have hrec := norm_Gj_add_one m j hy h0 hm
    have hP := abs_im_pow_le_norm_Pk m j w
    rw [hwim] at hP
    have hi4 : 0 < s.im ^ 4 := by positivity
    have hi4' : s.im ^ 4 = |s.im| ^ 4 := by rw [← abs_pow, abs_of_pos hi4]
    have hP' : s.im ^ 4 ≤ ‖Pk m j w‖ := by rw [hi4']; exact hP
    rw [show s + ((k + 1 : ℕ) : ℂ) = w + 1 by rw [hw]; push_cast; ring]
    have key : ‖Gj m j y (w + 1)‖ ≤ 16 * π ^ 4 * y / s.im ^ 4 * ‖Gj m j y w‖ := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hi4]
      calc ‖Gj m j y (w + 1)‖ * s.im ^ 4 ≤ ‖Gj m j y (w + 1)‖ * ‖Pk m j w‖ := by gcongr
        _ = 16 * π ^ 4 * y * ‖Gj m j y w‖ := hrec
    calc ‖Gj m j y (w + 1)‖ ≤ 16 * π ^ 4 * y / s.im ^ 4 * ‖Gj m j y w‖ := key
      _ ≤ 16 * π ^ 4 * y / s.im ^ 4 * (‖Gj m j y s‖ * (16 * π ^ 4 * y / s.im ^ 4) ^ k) := by
          gcongr
      _ = ‖Gj m j y s‖ * (16 * π ^ 4 * y / s.im ^ 4) ^ (k + 1) := by ring

/-- **Shift to the left**: for `−1/2 ≤ Re s ≤ 1/2` and `k ≤ K`,
`‖G_j(s−k)‖ ≤ ‖G_j(s)‖ (B²/(16π⁴y))^k` with `B = (K+j+1)² + m² + (Im s)²`. -/
theorem norm_Gj_sub_nat_le (hm1 : 1 ≤ m) {y : ℝ} (hy : 0 < y) {s : ℂ}
    (h1 : -1 / 2 ≤ s.re) (h2 : s.re ≤ 1 / 2) (K : ℕ) :
    ∀ k : ℕ, k ≤ K → ‖Gj m j y (s - k)‖ ≤
      ‖Gj m j y s‖ * ((((K : ℝ) + j + 1) ^ 2 + (m : ℝ) ^ 2 + s.im ^ 2) ^ 2 /
        (16 * π ^ 4 * y)) ^ k := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have hkK : (k : ℝ) + 1 ≤ K := by exact_mod_cast hk
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hm1' : (1 : ℝ) ≤ m := by exact_mod_cast hm1
    set w : ℂ := s - ((k + 1 : ℕ) : ℂ) with hw
    have hwre : w.re = s.re - k - 1 := by simp [hw]; ring
    have hwim : w.im = s.im := by simp [hw]
    have h0 : w ≠ 0 := fun h => by
      have := congrArg Complex.re h; rw [hwre] at this; simp at this; linarith
    have hm : w ≠ m := fun h => by
      have := congrArg Complex.re h; rw [hwre] at this; simp at this; linarith
    have hrec := norm_Gj_add_one m j hy h0 hm
    have hw1 : w + 1 = s - k := by rw [hw]; push_cast; ring
    rw [hw1] at hrec
    set B : ℝ := ((K : ℝ) + j + 1) ^ 2 + (m : ℝ) ^ 2 + s.im ^ 2 with hB
    have hPB : ‖Pk m j w‖ ≤ B * B := by
      refine (norm_Pk_le_gen m j w).trans ?_
      have e1 : ‖w + ((j : ℂ) + 1) / 2‖ ^ 2 = (s.re - k - 1 + ((j : ℝ) + 1) / 2) ^ 2 + s.im ^ 2 := by
        rw [RamanujanTau.Stirling.sq_norm_eq]; simp [hwre, hwim]
      have e2 : ‖w‖ ^ 2 = (s.re - k - 1) ^ 2 + s.im ^ 2 := by
        rw [RamanujanTau.Stirling.sq_norm_eq, hwre, hwim]
      have b1 : (s.re - k - 1 + ((j : ℝ) + 1) / 2) ^ 2 + (((j : ℝ) + 1) / 2) ^ 2 ≤
          ((K : ℝ) + j + 1) ^ 2 := by
        have u1 : s.re - k - 1 + ((j : ℝ) + 1) / 2 ≤ (K : ℝ) + ((j : ℝ) + 1) / 2 := by linarith
        have u2 : -((K : ℝ) + ((j : ℝ) + 1) / 2) ≤ s.re - k - 1 + ((j : ℝ) + 1) / 2 := by
          nlinarith
        have : (s.re - k - 1 + ((j : ℝ) + 1) / 2) ^ 2 ≤ ((K : ℝ) + ((j : ℝ) + 1) / 2) ^ 2 := by
          exact sq_le_sq' u2 u1
        nlinarith [Nat.cast_nonneg (α := ℝ) K]
      have b2 : (s.re - k - 1) ^ 2 ≤ ((K : ℝ) + j + 1) ^ 2 := by nlinarith
      rw [e1, e2]
      have hm2 : (0 : ℝ) ≤ (m : ℝ) ^ 2 := sq_nonneg _
      have hs2 : (0 : ℝ) ≤ s.im ^ 2 := sq_nonneg _
      have f1 : (s.re - k - 1 + ((j : ℝ) + 1) / 2) ^ 2 + s.im ^ 2 + (((j : ℝ) + 1) / 2) ^ 2 ≤ B := by
        rw [hB]; linarith
      have f2 : (s.re - k - 1) ^ 2 + s.im ^ 2 + (m : ℝ) ^ 2 ≤ B := by rw [hB]; linarith
      exact mul_le_mul f1 f2 (by positivity) (by rw [hB]; positivity)
    have hT : 0 < 16 * π ^ 4 * y := by positivity
    have key : ‖Gj m j y w‖ ≤ ‖Gj m j y (s - k)‖ * (B ^ 2 / (16 * π ^ 4 * y)) := by
      rw [mul_div_assoc', le_div_iff₀ hT, mul_comm _ (16 * π ^ 4 * y), ← hrec]
      gcongr
      rw [sq]; exact hPB
    calc ‖Gj m j y w‖ ≤ ‖Gj m j y (s - k)‖ * (B ^ 2 / (16 * π ^ 4 * y)) := key
      _ ≤ (‖Gj m j y s‖ * (B ^ 2 / (16 * π ^ 4 * y)) ^ k) * (B ^ 2 / (16 * π ^ 4 * y)) := by
          gcongr; exact ih (by omega)
      _ = ‖Gj m j y s‖ * (B ^ 2 / (16 * π ^ 4 * y)) ^ (k + 1) := by ring

lemma differentiableAt_Gj {y : ℝ} (hy : 0 < y) {s : ℂ} (hs : s.re < 1 ∨ s.im ≠ 0) :
    DifferentiableAt ℂ (Gj m j y) s := by
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hQ : DifferentiableAt ℂ (Qk m j) s := by
    rcases hs with hs | hs
    · exact ((differentiableOn_Qk m j) s hs).differentiableAt
        (IsOpen.mem_nhds (isOpen_lt Complex.continuous_re continuous_const) hs)
    · exact differentiableAt_Qk_of_im_ne m j hs
  exact ((differentiableAt_id.add_const _).const_cpow (Or.inl hy0)).mul hQ

end RamanujanTau.RankinExact
