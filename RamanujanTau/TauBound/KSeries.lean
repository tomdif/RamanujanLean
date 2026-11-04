/-
# `K(1,1;1) = ∑_j (-4π²)^{6+j}/(j!(11+j)!)` (`= 2πJ₁₁(4π) ≈ 1.8305`)

Expand `e(-1/w) = ∑_j (-2πi/w)^j/j!`, integrate termwise (dominated convergence on `ℝ`), and use
the Lipschitz integral `integral_lipInt`.
-/
import RamanujanTau.TauBound.Lipschitz

set_option autoImplicit false

namespace RamanujanTau.TauBound

open Complex MeasureTheory
open scoped Real Nat

/-- The real terms `t_j = (-4π²)^{6+j}/(j!(11+j)!)`. -/
noncomputable def tTerm (j : ℕ) : ℝ := (-4 * π ^ 2) ^ (6 + j) / ((j ! : ℝ) * ((11 + j) ! : ℝ))

theorem hasSum_kInt_one :
    HasSum (fun j => ((tTerm j : ℝ) : ℂ)) (kInt 1 1 1) := by
  set a : ℂ := -2 * π * I
  set F : ℕ → ℝ → ℂ := fun j x => a ^ j / (j ! : ℂ) * lipInt (12 + j) x
  have hpt : ∀ x : ℝ, HasSum (fun j => F j x) (kIntegrand 1 1 1 x) := by
    intro x
    set w : ℂ := (x : ℂ) + I
    have hw : w ≠ 0 := by
      intro h; have := congrArg Complex.im h; simp [w] at this
    have hexp := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℂ) (a / w)
    rw [← Complex.exp_eq_exp_ℂ] at hexp
    have hk : kIntegrand 1 1 1 x = (1 / w ^ 12 * ee (-w)) * Complex.exp (a / w) := by
      simp only [kIntegrand, ee, a, w]
      push_cast
      simp only [one_mul, one_pow]
      simp only [mul_assoc, ← Complex.exp_add, zpow_neg, zpow_natCast, one_div]
      congr 2; field_simp; ring
    rw [hk]
    have := hexp.mul_left (1 / w ^ 12 * ee (-w))
    refine this.congr_fun (fun j => ?_)
    simp only [F, lipInt]
    rw [show ((x : ℂ) + I) = w from rfl, div_pow, pow_add]
    field_simp
  set B : ℕ → ℝ → ℝ := fun j x => (2 * π) ^ j / (j ! : ℝ) * (Real.exp (2 * π) * (x ^ 2 + 1) ^ (-6 : ℝ))
  have hFb : ∀ j x, ‖F j x‖ ≤ B j x := by
    intro j x
    simp only [F, B, lipInt, norm_mul, norm_div, norm_one, norm_pow, Complex.norm_natCast, norm_ee_neg_w1]
    have ha : ‖a‖ = 2 * π := by
      simp only [a, norm_mul, norm_neg, Complex.norm_ofNat, Complex.norm_real, Complex.norm_I,
        mul_one, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    rw [ha]
    have h := norm_inv_pow_w1_le (12 + j) (by omega) x
    rw [norm_div, norm_one, norm_pow] at h
    have : (0 : ℝ) ≤ (2 * π) ^ j / (j ! : ℝ) := by positivity
    calc (2 * π) ^ j / (j ! : ℝ) * (1 / ‖(x : ℂ) + I‖ ^ (12 + j) * Real.exp (2 * π))
        ≤ (2 * π) ^ j / (j ! : ℝ) * ((x ^ 2 + 1) ^ (-6 : ℝ) * Real.exp (2 * π)) := by gcongr
      _ = _ := by ring
  have hBs : ∀ x, Summable (fun j => B j x) := fun x =>
    (Real.summable_pow_div_factorial (2 * π)).mul_right _
  have hBint : Integrable (fun x => ∑' j, B j x) := by
    have : (fun x => ∑' j, B j x) = fun x =>
        (∑' j : ℕ, (2 * π) ^ j / (j ! : ℝ)) * (Real.exp (2 * π) * (x ^ 2 + 1) ^ (-6 : ℝ)) := by
      funext x; simp only [B]; rw [tsum_mul_right]
    rw [this]
    have := (integrable_bracket (r := 0) (by norm_num) (y := 1) one_pos)
    simp only [zero_sub, one_pow] at this
    exact (this.const_mul _).const_mul _
  have hDCT := MeasureTheory.hasSum_integral_of_dominated_convergence (μ := volume) B
    (fun j => ((continuous_const.mul (continuous_lipInt (12 + j))).aestronglyMeasurable))
    (fun j => Filter.Eventually.of_forall (hFb j)) (Filter.Eventually.of_forall hBs) hBint
    (Filter.Eventually.of_forall hpt)
  simp only [Pi.mul_apply] at hDCT
  rw [kInt_eq]
  refine hDCT.congr_fun (fun j => ?_)
  symm
  rw [integral_const_mul, show 12 + j = (11 + j) + 1 by omega, integral_lipInt (11 + j) (by omega)]
  have hp : (-2 * π * I : ℂ) ^ j * (-2 * π * I) ^ (11 + j + 1) = (-4 * (π : ℂ) ^ 2) ^ (6 + j) := by
    rw [← pow_add, show j + (11 + j + 1) = 2 * (6 + j) by omega, pow_mul]
    congr 1
    ring_nf; rw [Complex.I_sq]; ring
  simp only [tTerm, a]
  push_cast
  rw [div_mul_div_comm, hp]

end RamanujanTau.TauBound
