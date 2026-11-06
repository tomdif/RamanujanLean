/-
# A priori bounds for `G^f_h` (weight-`k` copy of the start of `SCSProof.Gbounds`)

* `coef_sq_laplace`: `Σ |a_f(n)|² e^{−nσ} ≤ C₀ σ^{−k}` (Parseval + `|f| ≤ C y^{−k/2}`);
* `aabsF_le`: `|conj a(n) a(n+h)| ≤ (|a(n)|² + |a(n+h)|²)/2`.

At `k = 12` this is `SCSProof.tau_sq_laplace` (exponent `σ^{−12}`).  After the normalization
`λ_f(n) = a_f(n)n^{−(k−1)/2}` the exponent `−k` plays exactly the role of `−12`.
-/
import RamanujanTau.SubconvexGeneral.TwoPointF

set_option autoImplicit false

namespace RamanujanTau.SubconvexGeneral

open MeasureTheory Set Complex
open UpperHalfPlane hiding I
open RamanujanTau.RankinSelberg RamanujanTau.HeckeConvexGeneral
open scoped MatrixGroups Real ComplexConjugate

variable {k : ℕ}

/-- `|a_n| = |conj a_f(n) · a_f(n+h)|`. -/
noncomputable def aabsF (f : CuspForm 𝒮ℒ (k : ℤ)) (h n : ℕ) : ℝ :=
  ‖conj (coef f n) * coef f (n + h)‖

lemma aabsF_le (f : CuspForm 𝒮ℒ (k : ℤ)) (h n : ℕ) :
    aabsF f h n ≤ (‖coef f n‖ ^ 2 + ‖coef f (n + h)‖ ^ 2) / 2 := by
  unfold aabsF
  rw [norm_mul, Complex.norm_conj]
  nlinarith [sq_nonneg (‖coef f n‖ - ‖coef f (n + h)‖)]

/-- **Parseval bound, weight `k`.** -/
theorem coef_sq_laplace (f : CuspForm 𝒮ℒ (k : ℤ)) : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ σ : ℝ, 0 < σ →
    Summable (fun n : ℕ => ‖coef f n‖ ^ 2 * Real.exp (-n * σ)) ∧
      ∑' n : ℕ, ‖coef f n‖ ^ 2 * Real.exp (-n * σ) ≤ C₀ * σ ^ (-(k : ℝ)) := by
  obtain ⟨C, hC⟩ := CuspFormClass.exists_bound f
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (by simpa using hC UpperHalfPlane.I)
  refine ⟨C ^ 2 * (4 * π) ^ k, by positivity, fun σ hσ => ?_⟩
  set y := σ / (4 * π)
  have hy : 0 < y := by positivity
  have hP := hasSum_normSq_coeff f hy
  have e : ∀ n : ℕ, ‖(qExpansion 1 f).coeff n‖ ^ 2 *
      Real.exp (-2 * π * y) ^ (2 * n) = ‖coef f n‖ ^ 2 * Real.exp (-n * σ) := by
    intro n
    rw [← Real.exp_nat_mul]
    congr 2
    simp only [y]; field_simp; push_cast; ring
  simp_rw [e] at hP
  refine ⟨hP.summable, ?_⟩
  rw [hP.tsum_eq]
  set e2 : ℝ := (k : ℝ) / 2
  have hb : ∀ x : ℝ, ‖f (hp hy x)‖ ^ 2 ≤ (C / y ^ e2) ^ 2 := by
    intro x
    have := hC (hp hy x)
    rw [hp_im] at this
    have ek : (((k : ℤ) : ℝ) / 2) = e2 := by simp [e2]
    rw [ek] at this
    gcongr
  calc ∫ x in (0 : ℝ)..1, ‖f (hp hy x)‖ ^ 2
      ≤ ∫ x in (0 : ℝ)..1, (C / y ^ e2) ^ 2 := by
        refine intervalIntegral.integral_mono_on zero_le_one ?_ intervalIntegrable_const
          (fun x _ => hb x)
        exact ((ModularFormClass.holo _).continuous.comp (continuous_hp hy)).norm.pow 2
          |>.intervalIntegrable _ _
    _ = (C / y ^ e2) ^ 2 := by simp
    _ = C ^ 2 * (4 * π) ^ k * σ ^ (-(k : ℝ)) := by
        have hyk : (y ^ e2) ^ 2 = y ^ k := by
          rw [← Real.rpow_natCast (y ^ e2), ← Real.rpow_mul hy.le, ← Real.rpow_natCast]
          congr 1; simp only [e2]; push_cast; ring
        rw [div_pow, hyk, Real.rpow_neg hσ.le, Real.rpow_natCast]
        simp only [y]
        rw [div_pow]
        field_simp

end RamanujanTau.SubconvexGeneral
