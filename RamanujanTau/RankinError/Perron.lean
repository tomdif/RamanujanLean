/-
# A Perron formula for Riesz means, and the contour shift

For `aₙ ≥ 0` with `∑ aₙ n^{-c} < ∞` (`c > 1`), `D(s) = ∑ aₙ n^{-s}`, `k ≥ 1`, `x > 0`:

    2π ∑ₙ aₙ φ_k(n/x) = ∫ x^{c+iy} P_k(c+iy) D(c+iy) dy          (perron_riesz)

If moreover `D(s) = F(s) + c₀/(s−1)` on `Re s = c`, with `F` holomorphic on `Re s > σ₀` and
`‖F(s)‖ ≤ B (1+|Im s|)^K` on `σ₁ ≤ Re s ≤ c` (`σ₀ < σ₁`), then with `k = K + 1`

    ∑ₙ aₙ (1 − n/x)_+^k = c₀ x (1 − 1/x)^{k+1}/(k+1) + O(x^{σ₁})      (x ≥ 1)

which is `RieszAsymp a c₀ k (1 − σ₁)` (`rieszAsymp_of_continuation`).
-/
import RamanujanTau.RankinError.Contour
import RamanujanTau.RankinError.Riesz

set_option autoImplicit false

namespace RamanujanTau.RankinError

open Complex Real MeasureTheory Set Filter Topology

/-- `((n/x : ℝ) : ℂ)^{-w} = n^{-w} x^{w}`. -/
lemma cpow_div_neg {p x : ℝ} (hp : 0 ≤ p) (hx : 0 < x) (w : ℂ) :
    ((p / x : ℝ) : ℂ) ^ (-w) = (p : ℂ) ^ (-w) * (x : ℂ) ^ w := by
  rw [div_eq_mul_inv, ofReal_mul, mul_cpow_ofReal_nonneg hp (inv_nonneg.2 hx.le), ofReal_inv,
    inv_cpow _ _ (by rw [arg_ofReal_of_nonneg hx.le]; exact Real.pi_ne_zero.symm)]
  rw [cpow_neg (x : ℂ) w, inv_inv]

lemma norm_natCast_cpow_neg {n : ℕ} (hn : n ≠ 0) (s : ℂ) :
    ‖(n : ℂ) ^ (-s)‖ = (n : ℝ) ^ (-s.re) := by
  have : (n : ℂ) = ((n : ℝ) : ℂ) := by simp
  rw [this, norm_cpow_eq_rpow_re_of_pos (by positivity)]
  simp

/-- The line `s(y) = c + iy`. -/
noncomputable abbrev ln (c y : ℝ) : ℂ := c + y * I

section Perron

variable (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (ha0 : a 0 = 0)

/-- The integrand on the line, term by term. -/
noncomputable def fterm (k : ℕ) (c x : ℝ) (n : ℕ) (y : ℝ) : ℂ :=
  (a n : ℂ) * ((n : ℂ) ^ (-ln c y) * (x : ℂ) ^ ln c y * Pk k (ln c y))

include ha0 in
lemma integral_fterm {k : ℕ} (hk : 1 ≤ k) {c x : ℝ} (hc : 0 < c) (hx : 0 < x) (n : ℕ) :
    ∫ y, fterm a k c x n y = (a n : ℂ) * (2 * π * phi k (n / x)) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp [fterm, ha0]
  · have hinv := mellinInv_Pk hk hc (u := n / x) (by positivity)
    unfold mellinInv at hinv
    rw [Complex.real_smul] at hinv
    simp_rw [cpow_div_neg (Nat.cast_nonneg n) hx, ofReal_natCast] at hinv
    unfold fterm
    rw [integral_const_mul]
    congr 1
    have h2π : (2 * π : ℂ) ≠ 0 := by
      have := Real.pi_pos; exact_mod_cast (by positivity : (2 * π : ℝ) ≠ 0)
    rw [← hinv]
    push_cast
    field_simp
    congr 1; funext y; simp only [smul_eq_mul, ln]; ring_nf

include ha ha0 in
lemma norm_fterm {k : ℕ} {c x : ℝ} (hx : 0 < x) (n : ℕ) (y : ℝ) :
    ‖fterm a k c x n y‖ = a n * (n : ℝ) ^ (-c) * x ^ c * ‖Pk k (ln c y)‖ := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp [fterm, ha0]
  · unfold fterm
    rw [norm_mul, norm_mul, norm_mul, norm_natCast_cpow_neg hn.ne', Complex.norm_real,
      norm_cpow_eq_rpow_re_of_pos hx, Real.norm_eq_abs, abs_of_nonneg (ha n)]
    have hre : (ln c y).re = c := by simp [ln]
    rw [hre]; ring

include ha ha0 in
lemma integrable_fterm {k : ℕ} (hk : 1 ≤ k) {c x : ℝ} (hc : 0 < c) (hx : 0 < x) (n : ℕ) :
    Integrable (fterm a k c x n) := by
  have hP := integrable_Pk_line hk hc
  have hmeas : AEStronglyMeasurable (fterm a k c x n) := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have : fterm a k c x 0 = fun _ => 0 := by funext y; simp [fterm, ha0]
      rw [this]; exact aestronglyMeasurable_const
    · refine Continuous.aestronglyMeasurable ?_
      unfold fterm
      have hc1 := continuous_Pk_line k hc
      have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
      have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
      refine continuous_const.mul ((Continuous.mul ?_ ?_).mul hc1)
      · exact Continuous.const_cpow (by fun_prop) (Or.inl hn0)
      · exact Continuous.const_cpow (by fun_prop) (Or.inl hx0)
  refine (hP.norm.const_mul (a n * (n : ℝ) ^ (-c) * x ^ c)).mono' hmeas
    (Eventually.of_forall fun y => ?_)
  rw [norm_fterm a ha ha0 hx]

include ha ha0 in
/-- The Perron formula for Riesz means. -/
theorem perron_riesz {k : ℕ} (hk : 1 ≤ k) {c x : ℝ} (hc : 1 < c) (hx : 0 < x)
    (hsum : Summable fun n : ℕ => a n * (n : ℝ) ^ (-c)) :
    (2 * π : ℂ) * ∑' n : ℕ, (a n : ℂ) * phi k (n / x) =
      ∫ y : ℝ, (x : ℂ) ^ ln c y * Pk k (ln c y) *
        LSeries (fun n => (a n : ℂ)) (ln c y) := by
  have hc0 : 0 < c := by linarith
  have hint := integrable_fterm a ha ha0 hk hc0 hx
  have hsumI : Summable fun n => ∫ y, ‖fterm a k c x n y‖ := by
    simp_rw [norm_fterm a ha ha0 hx, integral_const_mul]
    exact (hsum.mul_right (x ^ c)).mul_right _
  have key := integral_tsum_of_summable_integral_norm hint hsumI
  simp_rw [integral_fterm a ha0 hk hc0 hx] at key
  rw [← tsum_mul_left]
  have e1 : ∀ n : ℕ, (2 * π : ℂ) * ((a n : ℂ) * phi k (n / x)) =
      (a n : ℂ) * (2 * π * phi k (n / x)) := fun n => by ring
  simp_rw [e1, key]
  congr 1
  funext y
  unfold fterm LSeries
  rw [← tsum_mul_left]
  congr 1
  funext n
  rw [LSeries.term_def₀ (by simp [ha0])]
  ring

end Perron

end RamanujanTau.RankinError
