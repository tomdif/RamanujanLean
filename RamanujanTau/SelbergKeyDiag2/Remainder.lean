/-
# M3 step 4 (end): the shifted-contour remainder is `O((α/(T(u)T(u')))^{1/6})`

`norm_Rsh_le`: `|R(u,u',v,α)| ≤ K (α/(T(u)T(u')))^{1/6}` uniformly in `u, u', v ∈ ℝ`, `α > 0`
(Stirling on `Re z = −1/6`, `HeckeAFE.norm_Gamma_ratio_line`, as in `SelbergKey2.W2sh_line_bound`;
the extra factor `1/(2z − iv)` has modulus `≤ 3` there).  Level 1.
-/
import RamanujanTau.SelbergKeyDiag2.Mellin2

set_option autoImplicit false

namespace RamanujanTau.SelbergKeyDiag2

open Complex MeasureTheory Set Filter Topology RamanujanTau.HeckeAFE RamanujanTau.SelbergKey
  RamanujanTau.SelbergKey2
open scoped Real

theorem norm_Rsh_le : ∃ K : ℝ, 0 ≤ K ∧ ∀ u u' v α : ℝ, 0 < α →
    ‖Rsh u u' v α‖ ≤ K * (α / (Tq u * Tq u')) ^ (1 / 6 : ℝ) := by
  set x : ℝ := -1 / 6 with hxdef
  obtain ⟨C, hC0, hC⟩ := norm_Gamma_ratio_line (x := x) (by norm_num [hxdef])
  have hp0 : 0 ≤ 2 * (11 / 2 + x) := by norm_num [hxdef]
  set E : ℝ := Real.exp ((2 * (11 / 2 + x) + π) ^ 2 / 2)
  set J : ℝ := ∫ y : ℝ, Real.exp (-(1 / 2) * y ^ 2)
  have hJ : 0 ≤ J := integral_nonneg fun _ => (Real.exp_pos _).le
  set K : ℝ := (2 * π)⁻¹ * (C * C * Real.exp (x ^ 2) * 18 * E * J)
  refine ⟨K, by positivity, fun u u' v α hα => ?_⟩
  set G : ℝ := ‖Gamma (6 + u * I)‖ * ‖Gamma (6 + u' * I)‖
  have hG : 0 < G := mul_pos (norm_pos_iff.2 (HafnerProportion.Gamma_line_ne_zero u))
    (norm_pos_iff.2 (HafnerProportion.Gamma_line_ne_zero u'))
  set B : ℝ := C * C * (Tq u * Tq u') ^ x * G * α ^ (-x) * Real.exp (x ^ 2) * 18 * E
  have hB : ∀ y : ℝ, ‖fM (6 + u * I) (6 - u' * I) α v ((x : ℂ) + y * I)‖ ≤
      B * Real.exp (-(1 / 2) * y ^ 2) := by
    intro y
    unfold fM
    rw [div_eq_mul_inv, div_eq_mul_inv, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul,
      norm_ofReal_cpow hα, norm_cexp_sq]
    have hr : (-((x : ℂ) + y * I)).re = -x := by simp
    rw [hr]
    have hi : ‖((x : ℂ) + y * I)⁻¹‖ ≤ 6 := by
      rw [norm_inv]
      have := norm_line_ge (c := x) y
      rw [show |x| = 1 / 6 by norm_num [hxdef]] at this
      rw [inv_le_comm₀ (lt_of_lt_of_le (by norm_num) this) (by norm_num)]
      linarith
    have hi2 : ‖(2 * ((x : ℂ) + y * I) - v * I)⁻¹‖ ≤ 3 := by
      rw [norm_inv]
      have := Complex.abs_re_le_norm (2 * ((x : ℂ) + y * I) - v * I)
      have hre : (2 * ((x : ℂ) + y * I) - v * I).re = -1 / 3 := by simp [hxdef]; norm_num
      rw [hre, show |(-1 / 3 : ℝ)| = 1 / 3 by norm_num] at this
      rw [inv_le_comm₀ (lt_of_lt_of_le (by norm_num) this) (by norm_num)]
      linarith
    have he : Real.exp (x ^ 2 - y ^ 2) = Real.exp (x ^ 2) * Real.exp (-1 * y ^ 2) := by
      rw [← Real.exp_add]; ring_nf
    rw [he]
    have h1 := hC u y
    have h2 : ‖Gamma ((6 - u' * I) + ((x : ℂ) + y * I))‖ ≤
        C * Tq u' ^ x * ((1 + |y|) ^ (11 / 2 + x) * Real.exp (π * |y| / 2)) *
          ‖Gamma (6 + u' * I)‖ := by
      have := hC (-u') y
      rw [Tq_neg, show (6 + ((-u' : ℝ) : ℂ) * I) = 6 - u' * I by push_cast; ring,
        norm_Gamma_six_sub] at this
      exact this
    have hpe := poly_exp_bound2 hp0 y
    have hTx : 0 ≤ Tq u ^ x := (Real.rpow_pos_of_pos (Tq_pos u) _).le
    have hTx' : 0 ≤ Tq u' ^ x := (Real.rpow_pos_of_pos (Tq_pos u') _).le
    have hαx : 0 ≤ α ^ (-x) := (Real.rpow_pos_of_pos hα _).le
    have hsq : ((1 + |y|) ^ (11 / 2 + x) * Real.exp (π * |y| / 2)) *
        ((1 + |y|) ^ (11 / 2 + x) * Real.exp (π * |y| / 2)) =
        (1 + |y|) ^ (2 * (11 / 2 + x)) * Real.exp (π * |y|) := by
      have ea : Real.exp (π * |y|) = Real.exp (π * |y| / 2) * Real.exp (π * |y| / 2) := by
        rw [← Real.exp_add]; ring_nf
      have eb : (1 + |y|) ^ (2 * (11 / 2 + x)) = (1 + |y|) ^ (11 / 2 + x) * (1 + |y|) ^ (11 / 2 + x) := by
        rw [← Real.rpow_add (by positivity)]; ring_nf
      rw [ea, eb]; ring
    have hTT : (Tq u * Tq u') ^ x = Tq u ^ x * Tq u' ^ x :=
      Real.mul_rpow (Tq_pos u).le (Tq_pos u').le
    calc ‖Gamma (6 + ↑u * I + (↑x + ↑y * I))‖ * ‖Gamma (6 - ↑u' * I + (↑x + ↑y * I))‖ * α ^ (-x) *
          (Real.exp (x ^ 2) * Real.exp (-1 * y ^ 2)) * ‖((x : ℂ) + y * I)⁻¹‖ *
          ‖(2 * ((x : ℂ) + y * I) - v * I)⁻¹‖
        ≤ (C * Tq u ^ x * ((1 + |y|) ^ (11 / 2 + x) * Real.exp (π * |y| / 2)) *
            ‖Gamma (6 + u * I)‖) *
          (C * Tq u' ^ x * ((1 + |y|) ^ (11 / 2 + x) * Real.exp (π * |y| / 2)) *
            ‖Gamma (6 + u' * I)‖) * α ^ (-x) *
          (Real.exp (x ^ 2) * Real.exp (-1 * y ^ 2)) * 6 * 3 := by
          gcongr
      _ = C * C * (Tq u * Tq u') ^ x * G * α ^ (-x) * Real.exp (x ^ 2) * 18 *
          ((1 + |y|) ^ (2 * (11 / 2 + x)) * Real.exp (π * |y|) * Real.exp (-1 * y ^ 2)) := by
          rw [hTT, ← hsq]; simp only [G]; ring
      _ ≤ C * C * (Tq u * Tq u') ^ x * G * α ^ (-x) * Real.exp (x ^ 2) * 18 *
          (E * Real.exp (-(1 / 2) * y ^ 2)) := by
          have : 0 ≤ C * C * (Tq u * Tq u') ^ x * G * α ^ (-x) * Real.exp (x ^ 2) * 18 := by
            have := Real.rpow_nonneg (mul_nonneg (Tq_pos u).le (Tq_pos u').le) x
            positivity
          exact mul_le_mul_of_nonneg_left hpe this
      _ = _ := by ring
  have hint := (integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1 / 2)).const_mul B
  have hI := norm_integral_le_of_norm_le hint (Eventually.of_forall hB)
  rw [integral_const_mul] at hI
  unfold Rsh vline
  rw [norm_div, norm_mul, normGG]
  have h2pi : ‖(2 * π : ℂ)⁻¹‖ = (2 * π)⁻¹ := by
    rw [norm_inv, show (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
  rw [h2pi, div_le_iff₀ hG]
  have hdiv : (α / (Tq u * Tq u')) ^ (1 / 6 : ℝ) = (Tq u * Tq u') ^ x * α ^ (-x) := by
    rw [Real.div_rpow hα.le (mul_nonneg (Tq_pos u).le (Tq_pos u').le), hxdef,
      show -(-1 / 6 : ℝ) = 1 / 6 by norm_num, show (-1 / 6 : ℝ) = -(1 / 6) by norm_num,
      Real.rpow_neg (mul_nonneg (Tq_pos u).le (Tq_pos u').le), div_eq_mul_inv, mul_comm]
  rw [hdiv]
  calc (2 * π)⁻¹ * ‖∫ y : ℝ, fM (6 + u * I) (6 - u' * I) α v (((-1 / 6 : ℝ) : ℂ) + y * I)‖
      ≤ (2 * π)⁻¹ * (B * J) := by gcongr
    _ = _ := by simp only [B, K, G]; ring

end RamanujanTau.SelbergKeyDiag2
