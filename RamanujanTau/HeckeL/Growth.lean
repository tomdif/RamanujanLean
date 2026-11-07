/-
# Polynomial growth of `L(Δ,s)` on the reflected line `Re s = 4`

No Stirling formula: on the line `Re s = 4` the functional equation gives

    L(Δ, s) = (2π)^{2s−12} Γ(12−s)/Γ(s) · L(Δ, 12−s),

and `Γ(12−s) = (11−s)(10−s)(9−s)(8−s) Γ(8−s)` with `8 − s = s̄`, so `|Γ(8−s)| = |Γ(s)|`.
Hence `|L(Δ, 4+it)| ≤ C·|7−it||6−it||5−it||4−it| ≪ (1+|t|)⁴`, where `C = (2π)^{−4}∑|τ(n)|n^{−8}`.
-/
import RamanujanTau.HeckeL.Main

set_option autoImplicit false

namespace RamanujanTau.HeckeL

open Complex LSeries
open scoped Real ComplexConjugate

lemma norm_LSeries_tau_le {s : ℂ} (hs : s.re = 8) :
    ‖LSeries tauC s‖ ≤ ∑' n, ‖term tauC 8 n‖ := by
  have hsum : Summable fun n => ‖term tauC s n‖ := (LSeriesSummable_tau (by rw [hs]; norm_num)).norm
  refine (norm_tsum_le_tsum_norm hsum).trans (le_of_eq ?_)
  congr 1; funext n
  rw [norm_term_eq, norm_term_eq, hs]; simp

lemma norm_two_pi_cpow (s : ℂ) : ‖(2 * π : ℂ) ^ s‖ = (2 * π) ^ s.re := by
  have h : (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) := by push_cast; rfl
  rw [h, norm_cpow_eq_rpow_re_of_pos (by positivity)]

/-- **Growth on the reflected line**: `|L(Δ, s)| ≤ C |11−s||10−s||9−s||8−s|` for `Re s = 4`. -/
theorem tauL_bound_re_four : ∃ C : ℝ, ∀ s : ℂ, s.re = 4 →
    ‖tauL s‖ ≤ C * (‖11 - s‖ * ‖10 - s‖ * ‖9 - s‖ * ‖8 - s‖) := by
  refine ⟨(2 * π) ^ (-4 : ℝ) * ∑' n, ‖term tauC 8 n‖, fun s hs => ?_⟩
  have h12 : (12 - s).re = 8 := by simp [hs]; norm_num
  have hΛ : heckeLambda s = (2 * π : ℂ) ^ (-(12 - s)) * Gamma (12 - s) * LSeries tauC (12 - s) := by
    rw [← heckeLambda_functional_equation s, heckeLambda_eq (by rw [h12]; norm_num)]
  have hne : ∀ z : ℂ, 0 < z.re → z ≠ 0 := fun z hz h => by rw [h] at hz; simp at hz
  have hG : Gamma (12 - s) = (11 - s) * ((10 - s) * ((9 - s) * ((8 - s) * Gamma (8 - s)))) := by
    have e : ∀ a : ℂ, 0 < (a - s).re → Gamma (a + 1 - s) = (a - s) * Gamma (a - s) := by
      intro a ha
      rw [show a + 1 - s = (a - s) + 1 by ring, Gamma_add_one _ (hne _ ha)]
    have r : ∀ a : ℝ, 4 < a → 0 < ((a : ℂ) - s).re := fun a ha => by simp [hs]; linarith
    rw [show (12 : ℂ) - s = (11 : ℝ) + 1 - s by push_cast; ring, e _ (r 11 (by norm_num)),
      show ((11:ℝ):ℂ) - s = (10 : ℝ) + 1 - s by push_cast; ring, e _ (r 10 (by norm_num)),
      show ((10:ℝ):ℂ) - s = (9 : ℝ) + 1 - s by push_cast; ring, e _ (r 9 (by norm_num)),
      show ((9:ℝ):ℂ) - s = (8 : ℝ) + 1 - s by push_cast; ring, e _ (r 8 (by norm_num))]
    push_cast; ring
  have hconj : 8 - s = conj s := by
    apply Complex.ext <;> simp [hs]; norm_num
  have hGn : ‖Gamma (8 - s)‖ = ‖Gamma s‖ := by
    rw [hconj, Gamma_conj, Complex.norm_conj]
  have hGs : Gamma s ≠ 0 := Gamma_ne_zero_of_re_pos (by rw [hs]; norm_num)
  have hGs' : 0 < ‖Gamma s‖ := norm_pos_iff.mpr hGs
  rw [tauL, hΛ, hG]
  simp only [norm_mul, norm_inv, norm_two_pi_cpow, hGn]
  have hre1 : (-(12 - s)).re = -8 := by simp [hs]; norm_num
  rw [hre1, hs]
  have hL := norm_LSeries_tau_le h12
  have hpow : (2 * π) ^ (4 : ℝ) * (2 * π) ^ (-8 : ℝ) = (2 * π) ^ (-4 : ℝ) := by
    rw [← Real.rpow_add (by positivity)]; norm_num
  have hP : 0 ≤ ‖11 - s‖ * ‖10 - s‖ * ‖9 - s‖ * ‖8 - s‖ := by positivity
  calc (2 * π) ^ (4 : ℝ) * ‖Gamma s‖⁻¹ * ((2 * π) ^ (-8 : ℝ) *
        (‖11 - s‖ * (‖10 - s‖ * (‖9 - s‖ * (‖8 - s‖ * ‖Gamma s‖)))) * ‖LSeries tauC (12 - s)‖)
      = ((2 * π) ^ (4 : ℝ) * (2 * π) ^ (-8 : ℝ)) * (‖11 - s‖ * ‖10 - s‖ * ‖9 - s‖ * ‖8 - s‖) *
          ‖LSeries tauC (12 - s)‖ := by field_simp
    _ ≤ ((2 * π) ^ (4 : ℝ) * (2 * π) ^ (-8 : ℝ)) * (‖11 - s‖ * ‖10 - s‖ * ‖9 - s‖ * ‖8 - s‖) *
          ∑' n, ‖term tauC 8 n‖ := by gcongr
    _ = _ := by rw [hpow]; ring

end RamanujanTau.HeckeL
