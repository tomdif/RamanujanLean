/-
# From Dirichlet-polynomial approximations to a mean-square limit

`mean_sq_of_approx`: let `f : ℝ → ℂ` be continuous, and suppose that for every large `T` there
is a Dirichlet polynomial `P_T = dpoly (b T) (N T)` with

* `sup_{0 ≤ t ≤ T} |f(t) − P_T(t)| ≤ ρ(T) → 0`,
* `∑_{n ≤ N(T)} |b_T(n)|² → S`,
* `H_{N(T)} ∑ n |b_T(n)|² / T → 0`.

Then `(1/T) ∫₀ᵀ |f|² → S`.  The polynomial mean square is handled by `mv_poly`; the
approximation error by the pointwise inequality `||a|² − |p|²| ≤ ρ² + ρ(1 + |p|²)` when
`|a − p| ≤ ρ`.
-/
import RamanujanTau.MeanSquare.Poly

set_option autoImplicit false

namespace RamanujanTau.MeanSquare

open Complex Finset MeasureTheory intervalIntegral Filter Topology

lemma sq_sub_sq_le {a p ρ : ℝ} (hp : 0 ≤ p) (h : |a - p| ≤ ρ) :
    |a ^ 2 - p ^ 2| ≤ ρ ^ 2 + ρ * (1 + p ^ 2) := by
  have hρ : 0 ≤ ρ := (abs_nonneg _).trans h
  have e : a ^ 2 - p ^ 2 = (a - p) * (a - p + 2 * p) := by ring
  rw [e, abs_mul]
  have h2 : |a - p + 2 * p| ≤ ρ + 2 * p := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * p)]; linarith
  calc |a - p| * |a - p + 2 * p| ≤ ρ * (ρ + 2 * p) :=
        mul_le_mul h h2 (abs_nonneg _) hρ
    _ ≤ ρ ^ 2 + ρ * (1 + p ^ 2) := by nlinarith [sq_nonneg (p - 1)]

/-- The polynomial part: `(1/T)∫₀ᵀ|P_T|² → S`. -/
lemma poly_mean_tendsto (b : ℝ → ℕ → ℂ) (N : ℝ → ℕ) {S : ℝ}
    (hdiag : Tendsto (fun T => ∑ n ∈ Icc 1 (N T), ‖b T n‖ ^ 2) atTop (𝓝 S))
    (herr : Tendsto (fun T => H (N T) * (∑ n ∈ Icc 1 (N T), (n : ℝ) * ‖b T n‖ ^ 2) / T)
      atTop (𝓝 0)) :
    Tendsto (fun T => (∫ t in (0 : ℝ)..T, ‖dpoly (b T) (N T) t‖ ^ 2) / T) atTop (𝓝 S) := by
  set A := fun T => ∑ n ∈ Icc 1 (N T), ‖b T n‖ ^ 2
  set MD := fun T => ∫ t in (0 : ℝ)..T, ‖dpoly (b T) (N T) t‖ ^ 2
  have hE : Tendsto (fun T => MD T / T - A T) atTop (𝓝 0) := by
    have h6 := herr.const_mul 6
    rw [mul_zero] at h6
    refine squeeze_zero_norm' ?_ h6
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    have hmv := mv_poly (b T) (N T) T
    rw [Real.norm_eq_abs]
    have e : MD T / T - A T = (MD T - T * A T) / T := by field_simp
    rw [e, abs_div, abs_of_pos hT, div_le_iff₀ hT]
    calc |MD T - T * A T| ≤ 6 * H (N T) * ∑ n ∈ Icc 1 (N T), (n : ℝ) * ‖b T n‖ ^ 2 := hmv
      _ = 6 * (H (N T) * (∑ n ∈ Icc 1 (N T), (n : ℝ) * ‖b T n‖ ^ 2) / T) * T := by
          field_simp
  have := hE.add hdiag
  simp only [zero_add, sub_add_cancel] at this
  exact this

/-- **Assembly lemma.** -/
theorem mean_sq_of_approx {f : ℝ → ℂ} (hf : Continuous f) {S : ℝ}
    (b : ℝ → ℕ → ℂ) (N : ℝ → ℕ) (ρ : ℝ → ℝ)
    (happrox : ∀ᶠ T in atTop, ∀ t ∈ Set.Icc 0 T, ‖f t - dpoly (b T) (N T) t‖ ≤ ρ T)
    (hρ : Tendsto ρ atTop (𝓝 0))
    (hdiag : Tendsto (fun T => ∑ n ∈ Icc 1 (N T), ‖b T n‖ ^ 2) atTop (𝓝 S))
    (herr : Tendsto (fun T => H (N T) * (∑ n ∈ Icc 1 (N T), (n : ℝ) * ‖b T n‖ ^ 2) / T)
      atTop (𝓝 0)) :
    Tendsto (fun T => (∫ t in (0 : ℝ)..T, ‖f t‖ ^ 2) / T) atTop (𝓝 S) := by
  have hP := poly_mean_tendsto b N hdiag herr
  set MD := fun T => (∫ t in (0 : ℝ)..T, ‖dpoly (b T) (N T) t‖ ^ 2) / T with hMD
  -- bound for the difference
  have hbound : Tendsto (fun T => ρ T ^ 2 + ρ T * (1 + MD T)) atTop (𝓝 0) := by
    have := (hρ.pow 2).add (hρ.mul ((tendsto_const_nhds (x := (1:ℝ))).add hP))
    simpa using this
  have hdiff : Tendsto (fun T => (∫ t in (0 : ℝ)..T, ‖f t‖ ^ 2) / T - MD T) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [happrox, eventually_gt_atTop (0 : ℝ)] with T hT hT0
    have hρ0 : 0 ≤ ρ T := (norm_nonneg _).trans (hT 0 ⟨le_rfl, hT0.le⟩)
    have hcf : Continuous fun t => ‖f t‖ ^ 2 := by fun_prop
    have hcP : Continuous fun t => ‖dpoly (b T) (N T) t‖ ^ 2 :=
      (continuous_dpoly (b T) (N T)).norm.pow 2
    have e : (∫ t in (0 : ℝ)..T, ‖f t‖ ^ 2) / T - MD T =
        (∫ t in (0 : ℝ)..T, (‖f t‖ ^ 2 - ‖dpoly (b T) (N T) t‖ ^ 2)) / T := by
      rw [hMD]; simp only
      rw [intervalIntegral.integral_sub (hcf.intervalIntegrable _ _)
        (hcP.intervalIntegrable _ _), sub_div]
    rw [e, Real.norm_eq_abs, abs_div, abs_of_pos hT0, div_le_iff₀ hT0]
    have hpt : ∀ t ∈ Set.Icc 0 T, ‖‖f t‖ ^ 2 - ‖dpoly (b T) (N T) t‖ ^ 2‖ ≤
        ρ T ^ 2 + ρ T * (1 + ‖dpoly (b T) (N T) t‖ ^ 2) := by
      intro t ht
      rw [Real.norm_eq_abs]
      refine sq_sub_sq_le (norm_nonneg _) ?_
      exact (abs_norm_sub_norm_le _ _).trans (hT t ht)
    have hI := intervalIntegral.norm_integral_le_of_norm_le hT0.le
      (Eventually.of_forall fun t ht => hpt t (Set.Ioc_subset_Icc_self ht))
      ((show Continuous fun t => ρ T ^ 2 + ρ T * (1 + ‖dpoly (b T) (N T) t‖ ^ 2) by
          fun_prop).intervalIntegrable (μ := volume) 0 T)
    rw [← Real.norm_eq_abs]
    refine hI.trans (le_of_eq ?_)
    have e2 : (fun t => ρ T ^ 2 + ρ T * (1 + ‖dpoly (b T) (N T) t‖ ^ 2)) =
        fun t => (ρ T ^ 2 + ρ T) + ρ T * ‖dpoly (b T) (N T) t‖ ^ 2 := by funext t; ring
    rw [e2, intervalIntegral.integral_add (intervalIntegrable_const (μ := volume))
      ((hcP.const_mul (ρ T)).intervalIntegrable _ _), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const]
    simp only [sub_zero, smul_eq_mul, hMD]
    field_simp
    ring
  have := hdiff.add hP
  simp only [zero_add, sub_add_cancel] at this
  exact this

end RamanujanTau.MeanSquare
