/-
# `KernelOneBound m`, unconditionally: `‖J_1(y)‖ ≪ y^{9/8}`

Assembly of the bent contour. With `Y = y^{1/8}`, `τ = 2πY²`, `n = ⌈Y⌉₊`, `U = Y⁸`:

    ∫_{Re s = 1/2} = (tail |t| ≥ U) + ∫_{−U}^{−τ} + ∫_{−τ}^{τ} + ∫_{τ}^{U},

and Cauchy on the rectangles `[1/2−n, 1/2]×[−τ, τ]`, `[1/2, 1/2+n]×[τ, U]`,
`[1/2, 1/2+n]×[−U, −τ]` (`rect_diff`) moves the three finite pieces onto
`Re s = 1/2 − n`, `Re s = 1/2 + n` plus six horizontal segments. Every piece is `≪ Y⁹`
(`Pieces`), so `‖J_1(y)‖ ≪ y^{9/8}` — the sharp exponent, with no `η` loss.
-/
import RamanujanTau.KernelPhase.Pieces
import RamanujanTau.RankinLandau.Final

set_option autoImplicit false

namespace RamanujanTau.KernelPhase

open Complex Real MeasureTheory Set Filter
open scoped Interval
open RamanujanTau.RankinErrorGeneral RamanujanTau.RankinLandau

variable {m : ℕ}

/-- **The contour bound** `‖∫ G(1/2+it) dt‖ ≤ C Y⁹` for `Y ≥ 9 + m²` (`y = Y⁸`). -/
theorem integral_G_le (hm : 1 ≤ m) : ∃ C : ℝ, ∀ Y : ℝ, 9 + (m : ℝ) ^ 2 ≤ Y →
    ‖∫ t : ℝ, G m (Y ^ 8) (((1 / 2 : ℝ) : ℂ) + t * I)‖ ≤ C * Y ^ 9 := by
  obtain ⟨K, hSB⟩ := exists_stripBound m hm
  set I₃ : ℝ := ∫ t : ℝ, (1 + |t|) ^ (-(3 / 2) : ℝ) with hI₃
  have hI₃0 : 0 ≤ I₃ := integral_nonneg fun t => by positivity
  set E : ℝ := Real.exp (9 + (m : ℝ) ^ 2)
  refine ⟨K * I₃ + K * (Real.exp ((9 + (m : ℝ) ^ 2) / (2 * π)) + 480 * π) + 2 * (128 * K * E) +
    2 * K + 2 * (128 * K) + 2 * (128 * π ^ 4 * K), fun Y hY => ?_⟩
  obtain ⟨hY1, hY2, hYn, hnY, hT00, hT0U⟩ := params hm hY
  have hY0 : 0 < Y := by linarith
  have hK := hSB.1
  have hy0 : (0 : ℝ) < Y ^ 8 := by positivity
  set n : ℕ := ⌈Y⌉₊ with hn
  set T0 : ℝ := 2 * π * Y ^ 2 with hT0
  set U : ℝ := Y ^ 8 with hU
  set f : ℂ → ℂ := G m (Y ^ 8) with hf
  set F : ℝ → ℂ := fun t => f (((1 / 2 : ℝ) : ℂ) + t * I) with hF
  have hFc : Continuous F := continuous_jint m 1 (σ := 1 / 2) (by norm_num) (y := Y ^ 8) hy0
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  -- the tail
  have htail := piece_tail hm hSB hY
  -- splitting `[-U, U]`
  have hsplit : ∫ t in -U..U, F t =
      (∫ t in -U..-T0, F t) + (∫ t in -T0..T0, F t) + ∫ t in T0..U, F t := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hFc.intervalIntegrable _ _)
      (hFc.intervalIntegrable _ _), intervalIntegral.integral_add_adjacent_intervals
      (hFc.intervalIntegrable _ _) (hFc.intervalIntegrable _ _)]
  -- the three rectangles
  have H1 : DifferentiableOn ℂ f ([[(1 / 2 - n : ℝ), (1 / 2 : ℝ)]] ×ℂ [[-T0, T0]]) := by
    intro s hs
    rw [mem_reProdIm, uIcc_of_le (show (1 / 2 - n : ℝ) ≤ 1 / 2 by linarith)] at hs
    exact (differentiableAt_G m hy0 (Or.inl (by linarith [hs.1.2]))).differentiableWithinAt
  have H2 : DifferentiableOn ℂ f ([[(1 / 2 : ℝ), (1 / 2 + n : ℝ)]] ×ℂ [[T0, U]]) := by
    intro s hs
    rw [mem_reProdIm, uIcc_of_le hT0U] at hs
    exact (differentiableAt_G m hy0 (Or.inr (by linarith [hs.2.1]))).differentiableWithinAt
  have H3 : DifferentiableOn ℂ f ([[(1 / 2 : ℝ), (1 / 2 + n : ℝ)]] ×ℂ [[-U, -T0]]) := by
    intro s hs
    rw [mem_reProdIm, uIcc_of_le (show -U ≤ -T0 by linarith)] at hs
    exact (differentiableAt_G m hy0 (Or.inr (by linarith [hs.2.2]))).differentiableWithinAt
  have R1 := rect_diff f (1 / 2 - n : ℝ) (1 / 2 : ℝ) (-T0) T0 H1
  have R2 := rect_diff f (1 / 2 : ℝ) (1 / 2 + n : ℝ) T0 U H2
  have R3 := rect_diff f (1 / 2 : ℝ) (1 / 2 + n : ℝ) (-U) (-T0) H3
  -- the pieces
  have P1 := piece_left hm hSB hY
  have P2 := piece_right_top hm hSB hY
  have P3 := piece_right_bot hm hSB hY
  have P4 := piece_h_left hm hSB hY (t := -T0) (by rw [abs_neg, abs_of_pos hT00])
  have P5 := piece_h_left hm hSB hY (t := T0) (abs_of_pos hT00)
  have P6 := piece_h_right hm hSB hY (t := T0) (abs_of_pos hT00)
  have P7 := piece_h_right hm hSB hY (t := -T0) (by rw [abs_neg, abs_of_pos hT00])
  have P8 := piece_h_top hm hSB hY (t := U) (abs_of_pos hy0)
  have P9 := piece_h_top hm hSB hY (t := -U) (by rw [abs_neg, abs_of_pos hy0])
  -- names
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
  have hY89 : K * Y ^ 8 * I₃ ≤ K * I₃ * Y ^ 9 := by
    have : Y ^ 8 ≤ Y ^ 9 := pow_le_pow_right₀ hY1 (by norm_num)
    calc K * Y ^ 8 * I₃ = K * I₃ * Y ^ 8 := by ring
      _ ≤ K * I₃ * Y ^ 9 := by gcongr
  push_cast at R1 R2 R3 P1 P2 P3 P4 P5 P6 P7 P8 P9
  simp only [hf] at R1 R2 R3
  linarith

/-- **The sharp kernel bound** `‖J_1(y)‖ ≤ C y^{9/8}` for `y ≥ 1`. -/
theorem kernelOne_sharp (hm : 1 ≤ m) :
    ∃ C : ℝ, ∀ y : ℝ, 1 ≤ y → ‖Jc m 1 (1 / 2) y‖ ≤ C * y ^ ((9 : ℝ) / 8) := by
  obtain ⟨C, hC⟩ := integral_G_le hm
  obtain ⟨K₀, hK₀, hK₀b⟩ := norm_Jc_le m 1 hm (σ := 1 / 2) (by norm_num) (by norm_num)
  set Y₀ : ℝ := 9 + (m : ℝ) ^ 2 with hY₀
  have hY₀1 : 1 ≤ Y₀ := by rw [hY₀]; nlinarith [sq_nonneg (m : ℝ)]
  refine ⟨1 / (2 * π) * |C| + K₀ * Y₀ ^ 3, fun y hy => ?_⟩
  have hy0 : 0 < y := by linarith
  set Y : ℝ := y ^ ((1 : ℝ) / 8) with hYdef
  have hY0 : 0 < Y := Real.rpow_pos_of_pos hy0 _
  have hY1 : 1 ≤ Y := Real.one_le_rpow hy (by norm_num)
  have hyY : Y ^ 8 = y := by
    rw [hYdef, ← Real.rpow_mul_natCast hy0.le]; norm_num
  have hy98 : y ^ ((9 : ℝ) / 8) = Y ^ 9 := by
    rw [hYdef, ← Real.rpow_mul_natCast hy0.le]; norm_num
  rw [hy98]
  have hpi := Real.pi_pos
  have hY9 : 0 ≤ Y ^ 9 := by positivity
  rcases le_or_gt Y₀ Y with hbig | hsmall
  · have h := hC Y hbig
    rw [hyY] at h
    rw [Jc_eq_G, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * π))]
    calc 1 / (2 * π) * ‖∫ t : ℝ, G m y (((1 / 2 : ℝ) : ℂ) + t * I)‖ ≤
        1 / (2 * π) * (|C| * Y ^ 9) := by
          gcongr; exact h.trans (by gcongr; exact le_abs_self C)
      _ ≤ (1 / (2 * π) * |C| + K₀ * Y₀ ^ 3) * Y ^ 9 := by
          have : 0 ≤ K₀ * Y₀ ^ 3 * Y ^ 9 := by positivity
          nlinarith
  · have h := hK₀b y hy0
    have e : y ^ ((1 / 2 : ℝ) + ((1 : ℕ) : ℝ)) = Y ^ 12 := by
      rw [← hyY, rpow8 hY0.le]; norm_num
    rw [e] at h
    have h12 : Y ^ 12 ≤ Y₀ ^ 3 * Y ^ 9 := by
      have : Y ^ 3 ≤ Y₀ ^ 3 := pow_le_pow_left₀ hY0.le hsmall.le 3
      calc Y ^ 12 = Y ^ 3 * Y ^ 9 := by ring
        _ ≤ Y₀ ^ 3 * Y ^ 9 := by gcongr
    have : 0 ≤ 1 / (2 * π) * |C| * Y ^ 9 := by positivity
    calc ‖Jc m 1 (1 / 2) y‖ ≤ K₀ * Y ^ 12 := h
      _ ≤ K₀ * (Y₀ ^ 3 * Y ^ 9) := by gcongr
      _ ≤ (1 / (2 * π) * |C| + K₀ * Y₀ ^ 3) * Y ^ 9 := by nlinarith

/-- **`KernelOneBound m` holds for every `m ≥ 1`** (unconditionally). -/
theorem kernelOneBound (hm : 1 ≤ m) : KernelOneBound m := by
  intro η hη
  obtain ⟨C, hC⟩ := kernelOne_sharp hm
  refine ⟨|C|, fun y hy => ?_⟩
  refine (hC y hy).trans ?_
  have h1 : y ^ ((9 : ℝ) / 8) ≤ y ^ ((9 : ℝ) / 8 + η) :=
    Real.rpow_le_rpow_of_exponent_le hy (by linarith)
  have h0 : 0 ≤ y ^ ((9 : ℝ) / 8) := by positivity
  calc C * y ^ ((9 : ℝ) / 8) ≤ |C| * y ^ ((9 : ℝ) / 8) := by gcongr; exact le_abs_self C
    _ ≤ |C| * y ^ ((9 : ℝ) / 8 + η) := by gcongr

end RamanujanTau.KernelPhase
