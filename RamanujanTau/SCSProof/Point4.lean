/-
# Pointwise bound for `G_h` in the variables `σ + iv`

`pointwise_G`: `‖G_h(σ+iv)‖ ≤ K h (|2v/σ| + 3)³² σ^{−12+3/40}` for `h ≥ 1`, `0 < σ ≤ 1`, `hσ ≤ 1`.
-/
import RamanujanTau.SCSProof.Point3

set_option autoImplicit false

namespace RamanujanTau.SCSProof

open Complex
open scoped Real ComplexConjugate

theorem pointwise_G : ∃ K : ℝ, 0 ≤ K ∧ ∀ h : ℕ, 1 ≤ h → ∀ σ v : ℝ, 0 < σ → σ ≤ 1 →
    (h : ℝ) * σ ≤ 1 →
      ‖Gh h ((σ : ℂ) + v * I)‖ ≤ K * h * (|2 * v / σ| + 3) ^ 32 * σ ^ (-(477 / 40 : ℝ)) := by
  obtain ⟨K, hK0, hK⟩ := pointwise_par
  refine ⟨K * (4 * π) ^ (477 / 40 : ℝ), by positivity, fun h hh σ v hσ hσ1 hhσ => ?_⟩
  set Y := σ / (4 * π) with hYdef
  have hY : 0 < Y := by positivity
  have hY1 : Y ≤ 1 := by
    rw [hYdef, div_le_one (by positivity)]; nlinarith [Real.pi_gt_three]
  set t := Y ^ (1 / 40 : ℝ) with ht
  have ht0 : 0 < t := Real.rpow_pos_of_pos hY _
  have ht1 : t ≤ 1 := Real.rpow_le_one hY.le hY1 (by norm_num)
  let P : Par := ⟨h, Y, t ^ 4 / 2, 2 * v / σ, hY, hY1, by positivity, by
    have : t ^ 4 ≤ 1 := pow_le_one₀ ht0.le ht1
    linarith⟩
  have hPh : P.h * (4 * π * P.Y) ≤ 1 := by
    show (h : ℝ) * (4 * π * (σ / (4 * π))) ≤ 1
    rw [show 4 * π * (σ / (4 * π)) = σ by field_simp]; exact hhσ
  have hb := hK P hh rfl hPh
  have hW : 2 * π * P.Y * (1 + I * conj ((zeta0 P : UpperHalfPlane) : ℂ)) = (σ : ℂ) + v * I := by
    rw [W0_eq]
    show (((4 * π * (σ / (4 * π)) : ℝ)) : ℂ) + ((2 * π * (σ / (4 * π)) * (2 * v / σ) : ℝ) : ℂ) * I = _
    congr 2
    · congr 1; field_simp
    · congr 1; field_simp; ring
  rw [hW] at hb
  refine hb.trans (le_of_eq ?_)
  show K * h * (|2 * v / σ| + 3) ^ 32 * t ^ 3 * (1 / Y ^ 12) = _
  have e1 : t ^ 3 * (1 / Y ^ 12) = Y ^ (-(477 / 40 : ℝ)) := by
    have h1 : t ^ 3 = Y ^ (3 / 40 : ℝ) := by
      rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hY.le]; norm_num
    have h2 : (1 / Y ^ 12 : ℝ) = Y ^ (-(12 : ℝ)) := by
      rw [Real.rpow_neg hY.le, one_div]; norm_cast
    rw [h1, h2, ← Real.rpow_add hY]
    norm_num
  have e2 : Y ^ (-(477 / 40 : ℝ)) = (4 * π) ^ (477 / 40 : ℝ) * σ ^ (-(477 / 40 : ℝ)) := by
    rw [hYdef, Real.div_rpow hσ.le (by positivity), Real.rpow_neg (by positivity : (0:ℝ) ≤ 4 * π),
      div_eq_mul_inv, inv_inv]
    ring
  rw [mul_assoc (K * h * _), e1, e2]
  ring

end RamanujanTau.SCSProof
