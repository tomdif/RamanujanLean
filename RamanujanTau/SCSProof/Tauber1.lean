/-
# Tauberian step 1: the exponential-Riesz kernel

For `x, L > 0`, `σ₀ = L/x`, `s(y) = σ₀ + iy`:
`2π Σ_n a_n φ₁(e^{(n−x)/L}) = ∫ e^{x s/L} P₁(s) G_h(s/L) dy`, `φ₁(u) = (1−u)₊`
(`RankinError.mellinInv_Pk`, `k = 1`).  Note `φ₁(e^{(n−x)/L}) = 1 − e^{(n−x)/L}` for `n < x`, `0` else.
-/
import RamanujanTau.SCSProof.Point4
import RamanujanTau.RankinError.RieszKernel

set_option autoImplicit false

namespace RamanujanTau.SCSProof

open MeasureTheory Complex Filter
open RamanujanTau.RankinError
open scoped Real

/-- `a_n = τ(n)τ(n+h)` as a real number. -/
noncomputable def aR (h n : ℕ) : ℝ := ((tau n * tau (n + h) : ℤ) : ℝ)

lemma abs_aR (h n : ℕ) : |aR h n| = aabs h n := rfl

lemma cpow_exp_neg (r : ℝ) (s : ℂ) : ((Real.exp r : ℝ) : ℂ) ^ (-s) = cexp (-s * r) := by
  rw [Complex.ofReal_exp, Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _),
    Complex.log_exp (by simp [Real.pi_pos]) (by simp [Real.pi_pos.le])]
  ring_nf

/-- The term function on the line. -/
noncomputable def kterm (h : ℕ) (x L : ℝ) (n : ℕ) (y : ℝ) : ℂ :=
  (aR h n : ℂ) * (((Real.exp ((n - x) / L) : ℝ) : ℂ) ^ (-((L / x : ℝ) + y * I)) *
    Pk 1 ((L / x : ℝ) + y * I))

lemma norm_kterm (h : ℕ) {x L : ℝ} (hx : 0 < x) (hL : 0 < L) (n : ℕ) (y : ℝ) :
    ‖kterm h x L n y‖ = aabs h n * Real.exp (-n * (1 / x)) * Real.exp 1 *
      ‖Pk 1 ((L / x : ℝ) + y * I)‖ := by
  unfold kterm
  rw [norm_mul, norm_mul, cpow_exp_neg, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
    abs_aR]
  have hre : (-((L / x : ℝ) + y * I) * (((n - x) / L : ℝ) : ℂ)).re = -(L / x) * ((n - x) / L) := by
    simp [Complex.mul_re]
  rw [hre]
  have : -(L / x) * ((n - x) / L) = -n * (1 / x) + 1 := by field_simp; ring
  rw [this, Real.exp_add]; ring

lemma integral_kterm (h : ℕ) {x L : ℝ} (hx : 0 < x) (hL : 0 < L) (n : ℕ) :
    ∫ y, kterm h x L n y = (aR h n : ℂ) * (2 * π * (phi 1 (Real.exp ((n - x) / L)) : ℂ)) := by
  have hinv := mellinInv_Pk (k := 1) le_rfl (σ := L / x) (by positivity)
    (u := Real.exp ((n - x) / L)) (Real.exp_pos _)
  unfold mellinInv at hinv
  rw [Complex.real_smul] at hinv
  unfold kterm
  rw [integral_const_mul]
  congr 1
  have h2π : (2 * π : ℂ) ≠ 0 := by
    have := Real.pi_pos; exact_mod_cast (by positivity : (2 * π : ℝ) ≠ 0)
  rw [← hinv]
  push_cast
  field_simp
  congr 1; funext y; simp only [smul_eq_mul]; ring_nf

lemma integrable_kterm (h : ℕ) {x L : ℝ} (hx : 0 < x) (hL : 0 < L) (n : ℕ) :
    Integrable (kterm h x L n) := by
  have hP := integrable_Pk_line (k := 1) le_rfl (σ := L / x) (by positivity)
  have hmeas : AEStronglyMeasurable (kterm h x L n) := by
    refine Continuous.aestronglyMeasurable ?_
    unfold kterm
    have hc1 := continuous_Pk_line 1 (σ := L / x) (by positivity)
    refine continuous_const.mul (Continuous.mul ?_ ?_)
    · exact Continuous.const_cpow (by fun_prop) (Or.inl (by
        exact_mod_cast (Real.exp_pos _).ne'))
    · push_cast at hc1 ⊢; exact hc1
  refine (hP.norm.const_mul (aabs h n * Real.exp (-n * (1 / x)) * Real.exp 1)).mono' hmeas
    (Eventually.of_forall fun y => ?_)
  rw [norm_kterm h hx hL]

/-- **The exponential-Riesz formula.** -/
theorem laplace_riesz (h : ℕ) {x L : ℝ} (hx : 0 < x) (hL : 0 < L)
    (hsum : Summable fun n : ℕ => aabs h n * Real.exp (-n * (1 / x))) :
    (2 * π : ℂ) * ∑' n : ℕ, (aR h n : ℂ) * (phi 1 (Real.exp ((n - x) / L)) : ℂ) =
      ∫ y : ℝ, cexp (x * ((L / x : ℝ) + y * I) / L) * Pk 1 ((L / x : ℝ) + y * I) *
        Gh h (((L / x : ℝ) + y * I) / L) := by
  have hint := integrable_kterm h hx hL
  have hsumI : Summable fun n => ∫ y, ‖kterm h x L n y‖ := by
    simp_rw [norm_kterm h hx hL, integral_const_mul]
    exact (hsum.mul_right (Real.exp 1)).mul_right _
  have key := integral_tsum_of_summable_integral_norm hint hsumI
  simp_rw [integral_kterm h hx hL] at key
  rw [← tsum_mul_left]
  have e1 : ∀ n : ℕ, (2 * π : ℂ) * ((aR h n : ℂ) * (phi 1 (Real.exp ((n - x) / L)) : ℂ)) =
      (aR h n : ℂ) * (2 * π * (phi 1 (Real.exp ((n - x) / L)) : ℂ)) := fun n => by ring
  simp_rw [e1, key]
  congr 1
  funext y
  unfold kterm Gh
  rw [← tsum_mul_left]
  have hsW : Summable fun n : ℕ => ((tau n * tau (n + h) : ℤ) : ℂ) *
      cexp (-(n : ℂ) * (((L / x : ℝ) + y * I) / L)) := by
    refine summable_Gh_term h (W := ((L / x : ℝ) + y * I) / L) (by
      simp [Complex.div_re]; positivity) ?_
    have : (((L / x : ℝ) + y * I) / L : ℂ).re = 1 / x := by
      simp [Complex.div_re]; field_simp
    rw [this]; exact hsum
  congr 1
  funext n
  rw [cpow_exp_neg]
  unfold aR
  have hL0 : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have e : -(((L / x : ℝ) : ℂ) + y * I) * (((n - x) / L : ℝ) : ℂ) =
      x * (((L / x : ℝ) : ℂ) + y * I) / L + (-(n : ℂ) * ((((L / x : ℝ) : ℂ) + y * I) / L)) := by
    push_cast; field_simp; ring
  rw [e, Complex.exp_add]
  push_cast
  ring

end RamanujanTau.SCSProof
