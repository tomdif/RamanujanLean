/-
# From moment Turán inequalities to hyperbolicity of the degree-2 Jensen polynomials

If `α(n) = C · n!/(2n)! · b(2n)` with `C > 0` and `b` the moments of a kernel with monotone
`R = −Φ'/(uΦ)` (`Chebyshev.lean`), then `α(n)α(n+2) ≤ α(n+1)²` for every `n` (**`turan_seq`**), and
`J^{2,n}_α = α(n) + 2α(n+1)X + α(n+2)X²` is hyperbolic for every `n ≥ 0` (**`jensen2_hyperbolic`**).
-/
import RamanujanTau.GORZXiEff.Chebyshev

set_option autoImplicit false

namespace GORZXiEff

open Real Set MeasureTheory Filter Topology Polynomial JensenThreshold GORZXi

/-- `f(n) = n!/(2n)!`. -/
noncomputable def fq (n : ℕ) : ℝ := (n.factorial : ℝ) / ((2 * n).factorial : ℝ)

lemma fq_pos (n : ℕ) : 0 < fq n := by unfold fq; positivity

lemma fq_succ (n : ℕ) : fq (n + 1) = fq n / (2 * (2 * n + 1)) := by
  unfold fq
  rw [show 2 * (n + 1) = (2 * n + 1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ,
    Nat.factorial_succ]
  push_cast
  have : (0 : ℝ) < (2 * n).factorial := by positivity
  field_simp
  ring

variable {Φ Φ' : ℝ → ℝ}

/-- **Turán inequalities** for `α(n) = C n!/(2n)! b(2n)`. -/
theorem turan_seq (h : KernelMom Φ Φ') (hR : MonotoneOn (ratioR Φ Φ') (Ioi 0)) {C : ℝ} (hC : 0 < C)
    {α : ℕ → ℝ} (hα : ∀ n, α n = C * fq n * mom Φ (2 * n)) (n : ℕ) :
    α n * α (n + 2) ≤ α (n + 1) ^ 2 := by
  have T := turan_mom h hR n
  rw [hα, hα, hα, fq_succ (n + 1), fq_succ n]
  rw [show 2 * (n + 2) = 2 * n + 4 by ring, show 2 * (n + 1) = 2 * n + 2 by ring]
  have hf := fq_pos n
  have h0 := (mom_pos h (2 * n)).le
  have h2 := (mom_pos h (2 * n + 4)).le
  push_cast
  set A := mom Φ (2 * n); set B := mom Φ (2 * n + 2); set D := mom Φ (2 * n + 4)
  set f := fq n
  have e : C * f * A * (C * (f / (2 * (2 * n + 1)) / (2 * (2 * (n + 1 : ℝ) + 1))) * D) =
      (C * (f / (2 * (2 * n + 1)))) ^ 2 * ((2 * n + 1) * A * D / (2 * n + 3)) := by
    field_simp; ring
  have e2 : (C * (f / (2 * (2 * n + 1))) * B) ^ 2 =
      (C * (f / (2 * (2 * n + 1)))) ^ 2 * ((2 * n + 3) * B ^ 2 / (2 * n + 3)) := by
    field_simp
  rw [e, e2]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
  exact div_le_div_of_nonneg_right T (by positivity)

/-- a real quadratic `c + bX + aX²` with `a > 0` and `b² ≥ 4ac` is hyperbolic. -/
lemma hyperbolic_quadratic {a b c : ℝ} (ha : 0 < a) (hd : 4 * a * c ≤ b ^ 2) :
    Hyperbolic (C c + C b * X + C a * X ^ 2) := by
  set s := Real.sqrt (b ^ 2 - 4 * a * c)
  have hs : s ^ 2 = b ^ 2 - 4 * a * c := Real.sq_sqrt (by linarith)
  set r₁ := (-b + s) / (2 * a)
  set r₂ := (-b - s) / (2 * a)
  have e1 : a * (r₁ + r₂) = -b := by simp only [r₁, r₂]; field_simp; ring
  have e2 : a * (r₁ * r₂) = c := by
    simp only [r₁, r₂]; field_simp; linear_combination (-1 : ℝ) * hs
  have hP : C c + C b * X + C a * X ^ 2 = C a * ((X - C r₁) * (X - C r₂)) := by
    have : C a * ((X - C r₁) * (X - C r₂)) =
        C a * X ^ 2 - C (a * (r₁ + r₂)) * X + C (a * (r₁ * r₂)) := by
      simp only [map_mul, map_add]; ring
    rw [this, e1, e2, map_neg]; ring
  have ha0 : a ≠ 0 := ha.ne'
  unfold Hyperbolic
  rw [hP, roots_C_mul _ ha0, roots_mul (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)),
    roots_X_sub_C, roots_X_sub_C, natDegree_C_mul ha0,
    natDegree_mul (X_sub_C_ne_zero _) (X_sub_C_ne_zero _), natDegree_X_sub_C, natDegree_X_sub_C]
  simp

lemma jensenSeq_two (α : ℕ → ℝ) (n : ℕ) :
    jensenSeq α 2 n = C (α n) + C (2 * α (n + 1)) * X + C (α (n + 2)) * X ^ 2 := by
  simp only [jensenSeq, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

/-- **Degree-2 Jensen polynomials are hyperbolic for every `n ≥ 0`.** -/
theorem jensen2_hyperbolic (h : KernelMom Φ Φ') (hR : MonotoneOn (ratioR Φ Φ') (Ioi 0)) {C : ℝ}
    (hC : 0 < C) {α : ℕ → ℝ} (hα : ∀ n, α n = C * fq n * mom Φ (2 * n)) (n : ℕ) :
    Hyperbolic (jensenSeq α 2 n) := by
  rw [jensenSeq_two]
  have hpos : 0 < α (n + 2) := by rw [hα]; exact mul_pos (mul_pos hC (fq_pos _)) (mom_pos h _)
  refine hyperbolic_quadratic hpos ?_
  have := turan_seq h hR hC hα n
  nlinarith

end GORZXiEff
