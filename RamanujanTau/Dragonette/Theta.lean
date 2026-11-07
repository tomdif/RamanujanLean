/-
# The theta function `Σ_{n∈ℤ} e^{−n²z}` and its transformation

`Jt z = jacobiTheta (i z/π) = Σ_{n∈ℤ} e^{−n² z}` for `Re z > 0`. Jacobi's transformation (Mathlib
`jacobiTheta_S_smul`) reads `Jt(π²/z) = (z/π)^{1/2} Jt(z)`.
-/
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import RamanujanTau.MockTheta3Radial

set_option autoImplicit false

namespace Dragonette
open Complex
open scoped Real

/-- `Jt z = Σ_{n∈ℤ} e^{−n² z}`. -/
noncomputable def Jt (z : ℂ) : ℂ := jacobiTheta (I * z / π)

lemma im_Iz {z : ℂ} : (I * z / π).im = z.re / π := by
  rw [show I * z / π = I * (z / (π : ℝ)) by push_cast; ring, mul_im, I_re, I_im, zero_mul, one_mul, zero_add,
    div_ofReal_re]

lemma im_Iz_pos {z : ℂ} (hz : 0 < z.re) : 0 < (I * z / π).im := by
  rw [im_Iz]; exact div_pos hz Real.pi_pos

lemma re_ne {z : ℂ} (hz : 0 < z.re) : z ≠ 0 := fun h => by rw [h] at hz; simp at hz

lemma re_pi_sq_div_pos {z : ℂ} (hz : 0 < z.re) : 0 < ((π : ℂ) ^ 2 / z).re := by
  have hz0 := re_ne hz
  rw [show (π : ℂ) ^ 2 / z = ((π ^ 2 : ℝ) : ℂ) * z⁻¹ by push_cast; ring, re_ofReal_mul, inv_re]
  exact mul_pos (by positivity) (div_pos hz (Complex.normSq_pos.mpr hz0))

/-- **Jacobi's transformation**: `Jt(π²/z) = (z/π)^{1/2} Jt(z)`. -/
theorem Jt_transform {z : ℂ} (hz : 0 < z.re) : Jt (π ^ 2 / z) = (z / π) ^ (1 / 2 : ℂ) * Jt z := by
  have hz0 := re_ne hz
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h := jacobiTheta_S_smul ⟨I * z / π, im_Iz_pos hz⟩
  rw [UpperHalfPlane.modular_S_smul] at h
  unfold Jt
  have e1 : (-(I * z / π))⁻¹ = I * (π ^ 2 / z) / π := by
    field_simp; rw [I_sq]
  have e2 : -I * (I * z / π) = z / π := by ring_nf; rw [I_sq]; ring
  rw [← e1, h, e2]

/-- the series. -/
lemma Jt_eq_tsum {z : ℂ} (hz : 0 < z.re) :
    Jt z = 1 + 2 * ∑' n : ℕ, cexp (-z) ^ ((n + 1) ^ 2) := by
  unfold Jt
  rw [jacobiTheta_eq_tsum_nat (im_Iz_pos hz)]
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  congr 2
  · congr 1; funext n
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    field_simp
    ring_nf
    rw [I_sq]; ring

/-- `‖Jt z − 1‖ ≤ 2e^{−Re z}/(1 − e^{−Re z})`. -/
lemma norm_Jt_sub_one {z : ℂ} (hz : 0 < z.re) :
    ‖Jt z - 1‖ ≤ 2 / (1 - Real.exp (-z.re)) * Real.exp (-z.re) := by
  have h := norm_jacobiTheta_sub_one_le (im_Iz_pos hz)
  rw [im_Iz, show -π * (z.re / π) = -z.re by field_simp] at h
  exact h

lemma exp_neg_div_le {x : ℝ} (hx : 0 < x) : Real.exp (-x) / (1 - Real.exp (-x)) ≤ 1 / x := by
  have h1 : Real.exp (-x) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have h0 := Real.exp_pos (-x)
  rw [div_le_div_iff₀ (by linarith) hx]
  have := Real.add_one_le_exp x
  have e : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
  nlinarith

/-- crude bound `‖Jt z‖ ≤ 1 + 2/Re z`. -/
lemma norm_Jt_le {z : ℂ} (hz : 0 < z.re) : ‖Jt z‖ ≤ 1 + 2 / z.re := by
  have h := norm_Jt_sub_one hz
  have h2 := exp_neg_div_le hz
  have : ‖Jt z‖ ≤ ‖Jt z - 1‖ + 1 := by
    have := norm_add_le (Jt z - 1) 1; simpa using this
  have e : 2 / (1 - Real.exp (-z.re)) * Real.exp (-z.re) = 2 * (Real.exp (-z.re) / (1 - Real.exp (-z.re))) := by
    ring
  rw [e] at h
  have : 2 * (Real.exp (-z.re) / (1 - Real.exp (-z.re))) ≤ 2 / z.re := by
    rw [show 2 / z.re = 2 * (1 / z.re) by ring]; gcongr
  linarith

/-- `‖Jt z − 1‖ ≤ 4e^{−Re z}` once `Re z ≥ 1`. -/
lemma norm_Jt_sub_one_le {z : ℂ} (hz : 1 ≤ z.re) : ‖Jt z - 1‖ ≤ 4 * Real.exp (-z.re) := by
  have h := norm_Jt_sub_one (by linarith : 0 < z.re)
  have he : Real.exp (-z.re) ≤ 1 / 2 := by
    calc Real.exp (-z.re) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
      _ ≤ 1 / 2 := by
        rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
        linarith [Real.add_one_le_exp (1 : ℝ)]
  refine h.trans ?_
  have h0 := Real.exp_pos (-z.re)
  have : 2 / (1 - Real.exp (-z.re)) ≤ 4 := by rw [div_le_iff₀ (by linarith)]; linarith
  nlinarith

/-- the link with `θA` of `MockTheta3Radial`: `2θA(−e^{−z}) − 1 = Jt z`. -/
lemma two_θA_sub_one {z : ℂ} (hz : 0 < z.re) :
    2 * MockTheta3.Radial.θA (-cexp (-z)) - 1 = Jt z := by
  set s := cexp (-z) with hs
  have hs1 : ‖s‖ < 1 := by
    rw [hs, norm_exp, neg_re, Real.exp_lt_one_iff]; linarith
  rw [MockTheta3.Radial.θA_eq, Jt_eq_tsum hz]
  have e : ∀ n : ℕ, (-1 : ℂ) ^ n * (-s) ^ (n ^ 2) = s ^ (n ^ 2) := by
    intro n
    rw [neg_pow s, ← mul_assoc, ← pow_add, Even.neg_one_pow (by
      rw [show n + n ^ 2 = n * (n + 1) by ring]; exact Nat.even_mul_succ_self n), one_mul]
  simp only [e]
  have hsum : Summable fun n : ℕ => s ^ (n ^ 2) := by
    refine Summable.of_norm_bounded (g := fun n : ℕ => ‖s‖ ^ n)
      (summable_geometric_of_lt_one (norm_nonneg _) hs1) fun n => ?_
    rw [norm_pow]
    exact pow_le_pow_of_le_one (norm_nonneg _) hs1.le (Nat.le_self_pow two_ne_zero n)
  rw [hsum.tsum_eq_zero_add]
  simp
  ring

end Dragonette
