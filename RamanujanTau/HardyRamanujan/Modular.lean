/-
# The modular transformation of `F = 1/(q;q)_∞`

For `Re z > 0`: `F(e^{−z}) = √(z/2π) · e^{π²/(6z) − z/24} · F(e^{−4π²/z})`, from Mathlib's
`η(−1/τ) = (√i)⁻¹ √τ η(τ)` at `τ = iz/(2π)`.
-/
import RamanujanTau.HardyRamanujan.GenFun

set_option autoImplicit false

namespace HardyRamanujan
open Complex Metric Realize
open scoped Real

/-- `√(z/2π)` (principal branch). -/
noncomputable def sq (z : ℂ) : ℂ := cexp (log (z / (2 * π)) / 2)

lemma norm_cexp_neg_lt_one {w : ℂ} (hw : 0 < w.re) : cexp (-w) ∈ ball (0 : ℂ) 1 := by
  rw [mem_ball_zero_iff, norm_exp, neg_re, Real.exp_lt_one_iff]; linarith

lemma re_inv_pos {z : ℂ} (hz : 0 < z.re) : 0 < (4 * π ^ 2 / z).re := by
  have hz0 : z ≠ 0 := fun h => by rw [h] at hz; simp at hz
  rw [div_re]
  have h1 : (0 : ℝ) < Complex.normSq z := Complex.normSq_pos.mpr hz0
  have h2 : ((4 : ℂ) * π ^ 2).re = 4 * π ^ 2 := by
    norm_num [pow_two]
  have h3 : ((4 : ℂ) * π ^ 2).im = 0 := by
    norm_num [pow_two]
  rw [h2, h3, zero_mul, zero_div, add_zero]
  exact div_pos (mul_pos (by positivity) hz) h1

lemma Pq_eq (q : ℂ) : Pq q = ∏' n : ℕ, (1 - q ^ (n + 1)) := by
  rw [Pq, Pfun]; congr 1; funext n; congr 2; ring

/-- **the modular transformation**. -/
theorem F_modular {z : ℂ} (hz : 0 < z.re) :
    F (cexp (-z)) = sq z * cexp (π ^ 2 / (6 * z) - z / 24) * F (cexp (-(4 * π ^ 2 / z))) := by
  have hz0 : z ≠ 0 := fun h => by rw [h] at hz; simp at hz
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  set τ : ℂ := I * z / (2 * π) with hτ
  have hτim : 0 < τ.im := by
    rw [hτ, show I * z / (2 * π) = I * (z / (2 * (π : ℝ))) by push_cast; ring, mul_im, I_re, I_im, zero_mul,
      one_mul, zero_add]
    rw [show ((2 : ℂ) * (π : ℝ)) = ((2 * π : ℝ) : ℂ) by push_cast; ring, div_ofReal_re]
    exact div_pos hz (by positivity)
  have h := ModularForm.eta_comp_eq_csqrt_I_inv (show τ ∈ UpperHalfPlane.upperHalfPlaneSet from hτim)
  simp only [Function.comp, Pi.smul_apply, Pi.mul_apply, smul_eq_mul] at h
  simp only [ModularForm.eta, ModularForm.eta_q_eq_pow, Function.Periodic.qParam] at h
  have e1 : cexp (2 * π * I * τ) = cexp (-z) := by
    rw [hτ]; congr 1; field_simp; ring_nf; try simp only [I_sq, Complex.I_sq]; try ring_nf
  have e2 : cexp (2 * π * I * (-1 / τ)) = cexp (-(4 * π ^ 2 / z)) := by
    rw [hτ]; congr 1; field_simp; ring_nf; try simp only [I_sq, Complex.I_sq]; try ring_nf
  have e3 : cexp (2 * π * I * τ / 24) = cexp (-z / 24) := by
    rw [hτ]; congr 1; field_simp; ring_nf; try simp only [I_sq, Complex.I_sq]; try ring_nf
  have e4 : cexp (2 * π * I * (-1 / τ) / 24) = cexp (-(π ^ 2 / (6 * z))) := by
    rw [hτ]; congr 1; field_simp; ring_nf; try simp only [I_sq, Complex.I_sq]; try ring_nf
  push_cast at h
  rw [e1, e2, e3, e4, ← Pq_eq, ← Pq_eq] at h
  have hw := norm_cexp_neg_lt_one hz
  have hw' := norm_cexp_neg_lt_one (re_inv_pos hz)
  have hP := Pq_ne_zero hw
  have hP' := Pq_ne_zero hw'
  -- `√τ / √I = √(z/2π)`
  have hu : 0 < (z / (2 * π)).re := by
    rw [show ((2 : ℂ) * π) = ((2 * π : ℝ) : ℂ) by push_cast; ring, div_ofReal_re]
    exact div_pos hz (by positivity)
  have hu0 : z / (2 * π) ≠ 0 := div_ne_zero hz0 (mul_ne_zero two_ne_zero hπ)
  have hlog : log τ = log I + log (z / (2 * π)) := by
    rw [hτ, show I * z / (2 * π) = I * (z / (2 * π)) by ring]
    refine (log_mul_eq_add_log_iff I_ne_zero hu0).mpr ?_
    rw [arg_I]
    have := (abs_arg_lt_pi_div_two_iff.mpr (Or.inl hu))
    rw [abs_lt] at this
    constructor <;> linarith [Real.pi_pos]
  have hsq : Complex.sqrt τ * (Complex.sqrt I)⁻¹ = sq z := by
    have hτ0 : τ ≠ 0 := fun h0 => by rw [h0] at hτim; simp at hτim
    rw [sqrt_eq_exp hτ0, sqrt_eq_exp I_ne_zero, hlog, sq, ← Complex.exp_neg, ← Complex.exp_add]
    congr 1; ring
  rw [F, F]
  have key : Pq (cexp (-z)) = cexp (-(π ^ 2 / (6 * z))) * Pq (cexp (-(4 * π ^ 2 / z))) *
      (Complex.sqrt τ * (Complex.sqrt I)⁻¹ * cexp (-z / 24))⁻¹ := by
    have hs : Complex.sqrt τ * (Complex.sqrt I)⁻¹ * cexp (-z / 24) ≠ 0 := by
      rw [hsq, sq]; exact mul_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _)
    rw [h, show (Complex.sqrt I)⁻¹ * (Complex.sqrt τ * (cexp (-z / 24) * Pq (cexp (-z)))) =
      Pq (cexp (-z)) * (Complex.sqrt τ * (Complex.sqrt I)⁻¹ * cexp (-z / 24)) by ring, mul_assoc,
      mul_inv_cancel₀ hs, mul_one]
  rw [key, hsq]
  have hexp : cexp (π ^ 2 / (6 * z) - z / 24) = (cexp (-(π ^ 2 / (6 * z))))⁻¹ * cexp (-z / 24) := by
    rw [← Complex.exp_neg, ← Complex.exp_add]; congr 1; ring
  rw [hexp]
  have : sq z ≠ 0 := Complex.exp_ne_zero _
  field_simp

end HardyRamanujan
