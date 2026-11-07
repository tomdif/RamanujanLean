/-
# M3 steps 3+4 combined: the base sum with both residues

For `0 < |v| ≤ 1`, `α > 0`, `p = iv/2`, `r = α/(T(u)T(u+v))` (`base_full`):

    Σ_n (λ(n)²/n) n^{iv} W̃_{u,u+v}(αn²)
      = c₀ G(p) α^{−p} e^{−v²/4}/(iv) + (−c₀/(iv) + γ_Δ − iv ε(v)) + O(r^{1/20} + r^{1/6}).

The first term is the pole of `R(s)` (`z = iv/2`), the bracket is the Laurent polynomial of
`R(1−iv)` plus the remainder `−iv ε(v)`.  Level 1.
-/
import RamanujanTau.SelbergKeyDiag2.Base3
import RamanujanTau.SelbergKeyDiag2.Remainder

set_option autoImplicit false

namespace RamanujanTau.SelbergKeyDiag2

open Complex MeasureTheory Set Filter Topology RamanujanTau.HeckeAFE RamanujanTau.SelbergKey
  RamanujanTau.SelbergKey2
open RamanujanTau.GoodSecondTerm (c0 gammaD)
open scoped Real

/-- The main term `c₀ G(p) α^{−p} e^{−v²/4}/(iv) + (−c₀/(iv) + γ_Δ − iv ε(v))`. -/
noncomputable def baseMain (u v α : ℝ) : ℂ :=
  (c0 : ℂ) * (Gsh u (u + v) (((v / 2 : ℝ) : ℂ) * I) * (α : ℂ) ^ (-(((v / 2 : ℝ) : ℂ) * I)) *
      Real.exp (-(v / 2) ^ 2)) / ((v : ℂ) * I) +
    (-(c0 : ℂ) / ((v : ℂ) * I) + gammaD - (v : ℂ) * I * epsv v)

theorem base_full : ∃ K : ℝ, 0 ≤ K ∧ ∀ u v α : ℝ, 0 < α → v ≠ 0 → |v| ≤ 1 →
    ‖(∑' n : ℕ, cA n * ft u v α n) - baseMain u v α‖ ≤
      K * ((α / TT u v) ^ (1 / 20 : ℝ) + (α / TT u v) ^ (1 / 6 : ℝ)) := by
  obtain ⟨K₁, hK₁0, hK₁⟩ := base_eval
  obtain ⟨K₂, hK₂0, hK₂⟩ := norm_Rsh_le
  obtain ⟨CW, hCW0, hCW⟩ := Wsh_sub_one (c := 1 / 20) (by norm_num) (by norm_num)
  refine ⟨K₁ + |gammaD| * CW + |c0| * K₂, by positivity, fun u v α hα hv0 hv => ?_⟩
  have hM := mellin_Wsh u (u + v) hv0 hα
  have hJ : Jv u v α = (Gsh u (u + v) (((v / 2 : ℝ) : ℂ) * I) * (α : ℂ) ^ (-(((v / 2 : ℝ) : ℂ) * I)) *
      Real.exp (-(v / 2) ^ 2) - 1) / ((v : ℂ) * I) + Rsh u (u + v) v α := hM
  have hvI : (v : ℂ) * I ≠ 0 := mul_ne_zero (by exact_mod_cast hv0) I_ne_zero
  have e : (∑' n : ℕ, cA n * ft u v α n) - baseMain u v α =
      ((∑' n : ℕ, cA n * ft u v α n) -
        ((gammaD : ℂ) * Wsh u (u + v) α + (c0 : ℂ) * Jv u v α - (v : ℂ) * I * epsv v)) +
      (gammaD : ℂ) * (Wsh u (u + v) α - 1) + (c0 : ℂ) * Rsh u (u + v) v α := by
    rw [hJ]; unfold baseMain; field_simp; ring
  rw [e]
  set r := α / TT u v
  have hr0 : 0 ≤ r := (div_pos hα (TT_pos u v)).le
  have h1 := hK₁ u v α hα hv
  have h2 : ‖(gammaD : ℂ) * (Wsh u (u + v) α - 1)‖ ≤ |gammaD| * (CW * r ^ (1 / 20 : ℝ)) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hCW u (u + v) α hα) (abs_nonneg _)
  have h3 : ‖(c0 : ℂ) * Rsh u (u + v) v α‖ ≤ |c0| * (K₂ * r ^ (1 / 6 : ℝ)) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hK₂ u (u + v) v α hα) (abs_nonneg _)
  have ha := Real.rpow_nonneg hr0 (1 / 20 : ℝ)
  have hb := Real.rpow_nonneg hr0 (1 / 6 : ℝ)
  calc ‖_ + (gammaD : ℂ) * (Wsh u (u + v) α - 1) + (c0 : ℂ) * Rsh u (u + v) v α‖
      ≤ K₁ * r ^ (1 / 20 : ℝ) + |gammaD| * (CW * r ^ (1 / 20 : ℝ)) + |c0| * (K₂ * r ^ (1 / 6 : ℝ)) :=
        (norm_add₃_le).trans (add_le_add_three h1 h2 h3)
    _ ≤ _ := by nlinarith [mul_nonneg hK₁0 hb, mul_nonneg (mul_nonneg (abs_nonneg gammaD) hCW0) hb,
          mul_nonneg (mul_nonneg (abs_nonneg c0) hK₂0) ha]

end RamanujanTau.SelbergKeyDiag2
