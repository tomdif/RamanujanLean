/-
# The sharp top-kernel bound: `‖J_{r+1}(y)‖ ≪ y^{(9+6r)/8}`

Assembly of the bent contour for general `j = r + 1` (as in `KernelPhase/Contour.lean`):
with `Y = y^{1/8}`, every piece is `≪ Y^{9+6r}`, so

    ‖J_j(y)‖ ≤ C y^{3j/4 + 3/8}        (y ≥ 1),

the sharp (Meijer-`G`) exponent `(A−1)/(2A) + j(A−1)/A` for degree `A = 4`, with no `ε`.
-/
import RamanujanTau.RankinExact.Pieces

set_option autoImplicit false

namespace RamanujanTau.RankinExact

open Complex Real MeasureTheory Set Filter
open scoped Interval
open RamanujanTau.RankinErrorGeneral RamanujanTau.RankinLandau RamanujanTau.KernelPhase

variable {m : ℕ}

/-- **The contour bound** `‖∫ G_{r+1}(1/2+it) dt‖ ≤ C Y^{9+6r}` for `Y ≥ D` (`y = Y⁸`). -/
theorem integral_Gj_le (hm : 1 ≤ m) (r : ℕ) : ∃ C : ℝ, ∀ Y : ℝ, Dc m r ≤ Y →
    ‖∫ t : ℝ, Gj m (r + 1) (Y ^ 8) (((1 / 2 : ℝ) : ℂ) + t * I)‖ ≤ C * Y ^ (9 + 6 * r) := by
  obtain ⟨K, hSB⟩ := exists_stripBoundJ m r hm
  set I₃ : ℝ := ∫ t : ℝ, (1 + |t|) ^ (-(3 / 2) : ℝ) with hI₃
  have hI₃0 : 0 ≤ I₃ := integral_nonneg fun t => by positivity
  set E : ℝ := Real.exp (Dc m r)
  refine ⟨K * I₃ + 2 * K * (2 ^ (r + 1) * Real.exp (Dc m r / (2 * π)) +
        2 * π * ((5 + 2 * r).factorial : ℝ)) + 2 * (128 * K * E) +
    2 * K + 2 * (128 * K) + 2 * (128 * π ^ 4 * K), fun Y hY => ?_⟩
  obtain ⟨hY1, hY2, hYn, hnY, hT00, hT0U⟩ := paramsJ hm hY
  have hY0 : 0 < Y := by linarith
  have hK := hSB.1
  have hy0 : (0 : ℝ) < Y ^ 8 := by positivity
  set n : ℕ := ⌈Y⌉₊ with hn
  set T0 : ℝ := 2 * π * Y ^ 2 with hT0
  set U : ℝ := Y ^ 8 with hU
  set f : ℂ → ℂ := Gj m (r + 1) (Y ^ 8) with hf
  set F : ℝ → ℂ := fun t => f (((1 / 2 : ℝ) : ℂ) + t * I) with hF
  have hFc : Continuous F := continuous_jint m (r + 1) (σ := 1 / 2) (by norm_num) (y := Y ^ 8) hy0
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have htail := piece_tailJ hm hSB hY
  have hsplit : ∫ t in -U..U, F t =
      (∫ t in -U..-T0, F t) + (∫ t in -T0..T0, F t) + ∫ t in T0..U, F t := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hFc.intervalIntegrable _ _)
      (hFc.intervalIntegrable _ _), intervalIntegral.integral_add_adjacent_intervals
      (hFc.intervalIntegrable _ _) (hFc.intervalIntegrable _ _)]
  have H1 : DifferentiableOn ℂ f ([[(1 / 2 - n : ℝ), (1 / 2 : ℝ)]] ×ℂ [[-T0, T0]]) := by
    intro s hs
    rw [mem_reProdIm, uIcc_of_le (show (1 / 2 - n : ℝ) ≤ 1 / 2 by linarith)] at hs
    exact (differentiableAt_Gj m (r + 1) hy0 (Or.inl (by linarith [hs.1.2]))).differentiableWithinAt
  have H2 : DifferentiableOn ℂ f ([[(1 / 2 : ℝ), (1 / 2 + n : ℝ)]] ×ℂ [[T0, U]]) := by
    intro s hs
    rw [mem_reProdIm, uIcc_of_le hT0U] at hs
    exact (differentiableAt_Gj m (r + 1) hy0 (Or.inr (by linarith [hs.2.1]))).differentiableWithinAt
  have H3 : DifferentiableOn ℂ f ([[(1 / 2 : ℝ), (1 / 2 + n : ℝ)]] ×ℂ [[-U, -T0]]) := by
    intro s hs
    rw [mem_reProdIm, uIcc_of_le (show -U ≤ -T0 by linarith)] at hs
    exact (differentiableAt_Gj m (r + 1) hy0 (Or.inr (by linarith [hs.2.2]))).differentiableWithinAt
  have R1 := rect_diff f (1 / 2 - n : ℝ) (1 / 2 : ℝ) (-T0) T0 H1
  have R2 := rect_diff f (1 / 2 : ℝ) (1 / 2 + n : ℝ) T0 U H2
  have R3 := rect_diff f (1 / 2 : ℝ) (1 / 2 + n : ℝ) (-U) (-T0) H3
  have P1 := piece_leftJ hm hSB hY
  have P2 := piece_right_topJ hm hSB hY
  have P3 := piece_right_botJ hm hSB hY
  have P4 := piece_h_leftJ hm hSB hY (t := -T0) (by rw [abs_neg, abs_of_pos hT00])
  have P5 := piece_h_leftJ hm hSB hY (t := T0) (abs_of_pos hT00)
  have P6 := piece_h_rightJ hm hSB hY (t := T0) (abs_of_pos hT00)
  have P7 := piece_h_rightJ hm hSB hY (t := -T0) (by rw [abs_neg, abs_of_pos hT00])
  have P8 := piece_h_topJ hm hSB hY (t := U) (abs_of_pos hy0)
  have P9 := piece_h_topJ hm hSB hY (t := -U) (by rw [abs_neg, abs_of_pos hy0])
  set S := ∫ t : ℝ, F t
  set A := ∫ t in -U..-T0, F t
  set B := ∫ t in -T0..T0, F t
  set Cc := ∫ t in T0..U, F t
  set VL := ∫ t in -T0..T0, f (((1 / 2 - n : ℝ) : ℂ) + t * I)
  set VT := ∫ t in T0..U, f (((1 / 2 + n : ℝ) : ℂ) + t * I)
  set VB := ∫ t in -U..-T0, f (((1 / 2 + n : ℝ) : ℂ) + t * I)
  have e1 := norm_sub_norm_le S (∫ t in -U..U, F t)
  have e2 : ‖∫ t in -U..U, F t‖ ≤ ‖A‖ + ‖B‖ + ‖Cc‖ := by
    rw [hsplit]; exact norm_add₃_le
  have e3 := norm_sub_norm_le B VL
  have e4 := norm_sub_norm_le Cc VT
  have e5 := norm_sub_norm_le A VB
  rw [norm_sub_rev] at e4 e5
  have hY89 : K * Y ^ 8 * I₃ ≤ K * I₃ * Y ^ (9 + 6 * r) := by
    have : Y ^ 8 ≤ Y ^ (9 + 6 * r) := pow_le_pow_right₀ hY1 (by omega)
    calc K * Y ^ 8 * I₃ = K * I₃ * Y ^ 8 := by ring
      _ ≤ K * I₃ * Y ^ (9 + 6 * r) := by gcongr
  push_cast at R1 R2 R3 P1 P2 P3 P4 P5 P6 P7 P8 P9
  simp only [hf] at R1 R2 R3
  linarith

/-- **The sharp kernel bound for every `j = r + 1 ≥ 1`**:
`‖J_{r+1}(y)‖ ≤ C y^{(9+6r)/8}` for `y ≥ 1`. -/
theorem kernel_sharp (hm : 1 ≤ m) (r : ℕ) :
    ∃ C : ℝ, ∀ y : ℝ, 1 ≤ y → ‖Jc m (r + 1) (1 / 2) y‖ ≤ C * y ^ (((9 + 6 * r : ℕ) : ℝ) / 8) := by
  obtain ⟨C, hC⟩ := integral_Gj_le hm r
  obtain ⟨K₀, hK₀, hK₀b⟩ := norm_Jc_le m (r + 1) hm (σ := 1 / 2) (by norm_num)
    (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) r])
  set Y₀ : ℝ := Dc m r with hY₀
  have hY₀1 : 1 ≤ Y₀ := by have := Dc_ge m r; linarith
  refine ⟨1 / (2 * π) * |C| + K₀ * Y₀ ^ (3 + 2 * r), fun y hy => ?_⟩
  have hy0 : 0 < y := by linarith
  set Y : ℝ := y ^ ((1 : ℝ) / 8) with hYdef
  have hY0 : 0 < Y := Real.rpow_pos_of_pos hy0 _
  have hY1 : 1 ≤ Y := Real.one_le_rpow hy (by norm_num)
  have hyY : Y ^ 8 = y := by
    rw [hYdef, ← Real.rpow_mul_natCast hy0.le]; norm_num
  have hy98 : y ^ (((9 + 6 * r : ℕ) : ℝ) / 8) = Y ^ (9 + 6 * r) := by
    rw [← hyY, rpow8 hY0.le, show 8 * (((9 + 6 * r : ℕ) : ℝ) / 8) = ((9 + 6 * r : ℕ) : ℝ) by ring,
      Real.rpow_natCast]
  rw [hy98]
  have hpi := Real.pi_pos
  have hY9 : 0 ≤ Y ^ (9 + 6 * r) := by positivity
  rcases le_or_gt Y₀ Y with hbig | hsmall
  · have h := hC Y hbig
    rw [hyY] at h
    rw [Jc_eq_Gj, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * π))]
    calc 1 / (2 * π) * ‖∫ t : ℝ, Gj m (r + 1) y (((1 / 2 : ℝ) : ℂ) + t * I)‖ ≤
        1 / (2 * π) * (|C| * Y ^ (9 + 6 * r)) := by
          gcongr; exact h.trans (by gcongr; exact le_abs_self C)
      _ ≤ (1 / (2 * π) * |C| + K₀ * Y₀ ^ (3 + 2 * r)) * Y ^ (9 + 6 * r) := by
          have : 0 ≤ K₀ * Y₀ ^ (3 + 2 * r) * Y ^ (9 + 6 * r) := by positivity
          nlinarith
  · have h := hK₀b y hy0
    have e : y ^ ((1 / 2 : ℝ) + ((r + 1 : ℕ) : ℝ)) = Y ^ (12 + 8 * r) := by
      rw [← hyY, rpow8 hY0.le, show 8 * ((1 / 2 : ℝ) + ((r + 1 : ℕ) : ℝ)) =
        ((12 + 8 * r : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    rw [e] at h
    have h12 : Y ^ (12 + 8 * r) ≤ Y₀ ^ (3 + 2 * r) * Y ^ (9 + 6 * r) := by
      have : Y ^ (3 + 2 * r) ≤ Y₀ ^ (3 + 2 * r) := pow_le_pow_left₀ hY0.le hsmall.le _
      calc Y ^ (12 + 8 * r) = Y ^ (3 + 2 * r) * Y ^ (9 + 6 * r) := by rw [← pow_add]; ring_nf
        _ ≤ Y₀ ^ (3 + 2 * r) * Y ^ (9 + 6 * r) := by gcongr
    have : 0 ≤ 1 / (2 * π) * |C| * Y ^ (9 + 6 * r) := by positivity
    calc ‖Jc m (r + 1) (1 / 2) y‖ ≤ K₀ * Y ^ (12 + 8 * r) := h
      _ ≤ K₀ * (Y₀ ^ (3 + 2 * r) * Y ^ (9 + 6 * r)) := by gcongr
      _ ≤ (1 / (2 * π) * |C| + K₀ * Y₀ ^ (3 + 2 * r)) * Y ^ (9 + 6 * r) := by nlinarith

end RamanujanTau.RankinExact
