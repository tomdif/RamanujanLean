/-
# A priori bounds for `G_h(W) = Σ τ(n)τ(n+h) e^{−nW}`

* `tau_sq_laplace`: `Σ τ(n)² e^{−nσ} ≤ C₀ σ^{−12}` (Parseval + `|Δ| ≤ C y^{−6}`);
* `abs_laplace_le`: `Σ |τ(n)τ(n+h)| e^{−nσ} ≤ (1 + e^{hσ})/2 · C₀ σ^{−12}`;
* `norm_Gh_le`: `|G_h(W)| ≤ Σ |a_n| e^{−n Re W}`;
* `norm_Gh_sub_le`: `|G_h(W) − G_h(W')| ≤ |W − W'| Σ n|a_n| e^{−nσ}` for `Re W, Re W' ≥ σ`;
* `n_laplace_le`: `Σ n|a_n|e^{−nσ} ≤ (2/σ) Σ |a_n| e^{−nσ/2}`.
-/
import RamanujanTau.SCSProof.Qform3

set_option autoImplicit false

namespace RamanujanTau.SCSProof

open MeasureTheory Set Complex
open UpperHalfPlane hiding I
open RamanujanTau.RankinSelberg
open scoped MatrixGroups Real ComplexConjugate

/-- `|a_n| = |τ(n)τ(n+h)|`. -/
noncomputable def aabs (h n : ℕ) : ℝ := |((tau n * tau (n + h) : ℤ) : ℝ)|

lemma aabs_nonneg (h n : ℕ) : 0 ≤ aabs h n := abs_nonneg _

lemma aabs_le (h n : ℕ) :
    aabs h n ≤ ((tau n : ℝ) ^ 2 + (tau (n + h) : ℝ) ^ 2) / 2 := by
  unfold aabs
  push_cast
  rw [abs_mul]
  nlinarith [sq_nonneg (|(tau n : ℝ)| - |(tau (n + h) : ℝ)|), sq_abs (tau n : ℝ),
    sq_abs (tau (n + h) : ℝ)]

/-- **Parseval bound.** -/
theorem tau_sq_laplace : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ σ : ℝ, 0 < σ →
    Summable (fun n : ℕ => (tau n : ℝ) ^ 2 * Real.exp (-n * σ)) ∧
      ∑' n : ℕ, (tau n : ℝ) ^ 2 * Real.exp (-n * σ) ≤ C₀ * σ ^ (-(12 : ℝ)) := by
  obtain ⟨C, hC⟩ := CuspFormClass.exists_bound (CuspForm.discriminant : CuspForm 𝒮ℒ 12)
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (by simpa using hC UpperHalfPlane.I)
  refine ⟨C ^ 2 * (4 * π) ^ 12, by positivity, fun σ hσ => ?_⟩
  set y := σ / (4 * π)
  have hy : 0 < y := by positivity
  have hP := hasSum_normSq_coeff (CuspForm.discriminant : CuspForm 𝒮ℒ 12) hy
  have e : ∀ n : ℕ, ‖(qExpansion 1 (CuspForm.discriminant : CuspForm 𝒮ℒ 12)).coeff n‖ ^ 2 *
      Real.exp (-2 * π * y) ^ (2 * n) = (tau n : ℝ) ^ 2 * Real.exp (-n * σ) := by
    intro n
    rw [TauBound.qExpansion_discriminant_coeff_tau, ← Real.exp_nat_mul]
    simp only [Complex.norm_intCast, sq_abs]
    congr 1; congr 1
    simp only [y]; field_simp; push_cast; ring
  simp_rw [e] at hP
  refine ⟨hP.summable, ?_⟩
  rw [hP.tsum_eq]
  have hb : ∀ x : ℝ, ‖(CuspForm.discriminant : CuspForm 𝒮ℒ 12) (hp hy x)‖ ^ 2 ≤ (C / y ^ 6) ^ 2 := by
    intro x
    have := hC (hp hy x)
    rw [hp_im] at this
    have e12 : (((12 : ℤ) : ℝ) / 2) = ((6 : ℕ) : ℝ) := by norm_num
    rw [e12, Real.rpow_natCast] at this
    gcongr
  calc ∫ x in (0 : ℝ)..1, ‖(CuspForm.discriminant : CuspForm 𝒮ℒ 12) (hp hy x)‖ ^ 2
      ≤ ∫ x in (0 : ℝ)..1, (C / y ^ 6) ^ 2 := by
        refine intervalIntegral.integral_mono_on zero_le_one ?_ intervalIntegrable_const
          (fun x _ => hb x)
        exact ((ModularFormClass.holo _).continuous.comp (continuous_hp hy)).norm.pow 2
          |>.intervalIntegrable _ _
    _ = (C / y ^ 6) ^ 2 := by simp
    _ = C ^ 2 * (4 * π) ^ 12 * σ ^ (-(12 : ℝ)) := by
        simp only [y]
        rw [Real.rpow_neg hσ.le, show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        field_simp

end RamanujanTau.SCSProof
