/-
# The coefficient integral

For `t > 0`: `p(n) = (1/2π) ∫_{−π}^{π} F(e^{−(t+iθ)}) e^{n(t+iθ)} dθ`.
-/
import RamanujanTau.HardyRamanujan.Modular

set_option autoImplicit false

namespace HardyRamanujan
open Complex Metric Realize MeasureTheory intervalIntegral
open scoped Real

/-- `z(θ) = t + iθ`. -/
noncomputable abbrev zt (t θ : ℝ) : ℂ := t + θ * I

lemma zt_re (t θ : ℝ) : (zt t θ).re = t := by simp [zt]

lemma integral_exp_int (m : ℤ) :
    ∫ θ in (-π)..π, cexp (m * (θ * I)) = if m = 0 then 2 * π else 0 := by
  split_ifs with hm
  · subst hm; simp; ring
  · have hc : (m : ℂ) * I ≠ 0 := mul_ne_zero (by exact_mod_cast hm) I_ne_zero
    have := integral_exp_mul_complex (a := -π) (b := π) hc
    simp only [show ∀ θ : ℝ, (m : ℂ) * (θ * I) = (m * I) * θ from fun θ => by ring] at *
    rw [this]
    have h2 : cexp (m * I * π) = cexp (m * I * ((-π : ℝ) : ℂ)) := by
      rw [show (m : ℂ) * I * π = m * I * ((-π : ℝ) : ℂ) + (m : ℂ) * (2 * π * I) by push_cast; ring,
        Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    rw [h2, sub_self, zero_div]; simp

lemma summable_p_exp {t : ℝ} (ht : 0 < t) : Summable fun k : ℕ => (p k : ℝ) * Real.exp (-(k * t)) := by
  have h := hasSum_F (norm_cexp_neg_lt_one (w := (t : ℂ)) (by simpa using ht))
  have hs := h.summable.norm
  refine hs.congr fun k => ?_
  rw [norm_mul, norm_pow, norm_exp, Complex.norm_natCast, ← Real.exp_nat_mul]
  simp

/-- **the coefficient integral**. -/
theorem coeff_integral (n : ℕ) {t : ℝ} (ht : 0 < t) :
    (2 * π : ℂ) * p n = ∫ θ in (-π)..π, F (cexp (-zt t θ)) * cexp (n * zt t θ) := by
  let f : ℕ → C(ℝ, ℂ) := fun k => ⟨fun θ => (p k : ℂ) * cexp ((n - k : ℤ) * zt t θ), by fun_prop⟩
  have hb : ∀ k, ‖(f k).restrict (⟨Set.uIcc (-π) π, isCompact_uIcc⟩ : TopologicalSpace.Compacts ℝ)‖
      ≤ (p k : ℝ) * Real.exp (-(k * t)) * Real.exp (n * t) := by
    intro k
    refine (ContinuousMap.norm_le _ (by positivity)).mpr fun θ => ?_
    simp only [ContinuousMap.restrict_apply, ContinuousMap.coe_mk, f, norm_mul, Complex.norm_natCast, norm_exp]
    rw [mul_assoc, ← Real.exp_add]
    refine le_of_eq ?_
    congr 2
    simp [zt]; ring
  have hsum : Summable fun k => ‖(f k).restrict (⟨Set.uIcc (-π) π, isCompact_uIcc⟩ : TopologicalSpace.Compacts ℝ)‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb ((summable_p_exp ht).mul_right _)
  have H := hasSum_intervalIntegral_of_summable_norm hsum
  -- the integrand is the sum
  have hpt : ∀ θ : ℝ, ∑' k, f k θ = F (cexp (-zt t θ)) * cexp (n * zt t θ) := by
    intro θ
    have hq : cexp (-zt t θ) ∈ ball (0 : ℂ) 1 := norm_cexp_neg_lt_one (by simp [zt]; exact ht)
    have h := (hasSum_F hq).mul_right (cexp (n * zt t θ))
    rw [← h.tsum_eq]
    congr 1; funext k
    simp only [f, ContinuousMap.coe_mk, ← Complex.exp_nat_mul, mul_assoc, ← Complex.exp_add]
    congr 2; push_cast; ring
  simp only [hpt] at H
  rw [← H.tsum_eq]
  -- each integral
  have hk : ∀ k, ∫ θ in (-π)..π, f k θ = if k = n then (2 * π : ℂ) * p n else 0 := by
    intro k
    simp only [f, ContinuousMap.coe_mk]
    have e : ∀ θ : ℝ, (p k : ℂ) * cexp ((n - k : ℤ) * zt t θ) =
        ((p k : ℂ) * cexp ((n - k : ℤ) * (t : ℂ))) * cexp ((n - k : ℤ) * (θ * I)) := by
      intro θ; rw [mul_assoc, ← Complex.exp_add]; congr 2; simp [zt]; ring
    simp only [e, intervalIntegral.integral_const_mul, integral_exp_int]
    split_ifs with h1 h2 h2
    · subst h2; simp; ring
    · exact absurd (by omega) h2
    · exact absurd (by subst h2; simp) h1
    · simp
  simp only [hk]
  rw [tsum_ite_eq]

end HardyRamanujan
