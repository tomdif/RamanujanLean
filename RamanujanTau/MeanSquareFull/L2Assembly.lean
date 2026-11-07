/-
# Mean-square assembly from an `L²` (rather than pointwise) approximation

`mean_sq_of_L2approx`: let `f : ℝ → ℂ` be continuous and suppose that for every large `T` there
are a constant `λ_T → 1` and a Dirichlet polynomial `P_T = dpoly (b T) (N T)` with

* `∫₀ᵀ |λ_T f − P_T|² ≤ B(T) T`, `B(T) → 0`,
* `∑_{n ≤ N(T)} |b_T(n)|² → S`,
* `H_{N(T)} ∑ n |b_T(n)|² / T → 0`.

Then `(1/T) ∫₀ᵀ |f|² → S`.  The comparison is pointwise:
`|‖u‖² − ‖v‖²| ≤ (1 + 1/η)‖u − v‖² + η‖v‖²` with `η = η(T) = √(B⁺(T) + 1/T) → 0`.
-/
import RamanujanTau.MeanSquare.Main

set_option autoImplicit false

namespace RamanujanTau.MeanSquareFull

open Complex Finset MeasureTheory intervalIntegral Filter Topology
open RamanujanTau.MeanSquare

lemma two_mul_le_div_add {r b η : ℝ} (hη : 0 < η) : 2 * r * b ≤ r ^ 2 / η + η * b ^ 2 := by
  rw [div_add' _ _ _ hη.ne', le_div_iff₀ hη]
  nlinarith [sq_nonneg (r - η * b)]

/-- `|‖u‖² − ‖v‖²| ≤ (1 + 1/η)‖u − v‖² + η‖v‖²`. -/
lemma norm_sq_sub_norm_sq_le (u v : ℂ) {η : ℝ} (hη : 0 < η) :
    |‖u‖ ^ 2 - ‖v‖ ^ 2| ≤ (1 + 1 / η) * ‖u - v‖ ^ 2 + η * ‖v‖ ^ 2 := by
  set a := ‖u‖
  set b := ‖v‖
  set r := ‖u - v‖
  have hab : |a - b| ≤ r := abs_norm_sub_norm_le u v
  have ha : 0 ≤ a := norm_nonneg _
  have hb : 0 ≤ b := norm_nonneg _
  have e : a ^ 2 - b ^ 2 = (a - b) * (a + b) := by ring
  have h1 : |a ^ 2 - b ^ 2| ≤ r * (r + 2 * b) := by
    rw [e, abs_mul, abs_of_nonneg (by positivity : 0 ≤ a + b)]
    have : a ≤ b + r := by have := le_abs_self (a - b); linarith
    have hr : 0 ≤ r := (abs_nonneg _).trans hab
    calc |a - b| * (a + b) ≤ r * (a + b) := by gcongr
      _ ≤ r * (r + 2 * b) := mul_le_mul_of_nonneg_left (by linarith) hr
  have h2 := two_mul_le_div_add (r := r) (b := b) hη
  have e2 : (1 + 1 / η) * r ^ 2 + η * b ^ 2 = r ^ 2 + (r ^ 2 / η + η * b ^ 2) := by ring
  rw [e2]; nlinarith

/-- **Assembly lemma, `L²` form.** -/
theorem mean_sq_of_L2approx {f : ℝ → ℂ} (hf : Continuous f) {S : ℝ}
    (lam : ℝ → ℂ) (hlam : Tendsto lam atTop (𝓝 1))
    (b : ℝ → ℕ → ℂ) (N : ℝ → ℕ) (B : ℝ → ℝ)
    (happrox : ∀ᶠ T in atTop,
      ∫ t in (0 : ℝ)..T, ‖lam T * f t - dpoly (b T) (N T) t‖ ^ 2 ≤ B T * T)
    (hB : Tendsto B atTop (𝓝 0))
    (hdiag : Tendsto (fun T => ∑ n ∈ Icc 1 (N T), ‖b T n‖ ^ 2) atTop (𝓝 S))
    (herr : Tendsto (fun T => H (N T) * (∑ n ∈ Icc 1 (N T), (n : ℝ) * ‖b T n‖ ^ 2) / T)
      atTop (𝓝 0)) :
    Tendsto (fun T => (∫ t in (0 : ℝ)..T, ‖f t‖ ^ 2) / T) atTop (𝓝 S) := by
  have hP := poly_mean_tendsto b N hdiag herr
  set MP := fun T => (∫ t in (0 : ℝ)..T, ‖dpoly (b T) (N T) t‖ ^ 2) / T with hMP
  set G := fun T => (∫ t in (0 : ℝ)..T, ‖lam T * f t‖ ^ 2) / T with hG
  set β := fun T : ℝ => max (B T) 0 + T⁻¹ with hβ
  have hβt : Tendsto β atTop (𝓝 0) := by
    have := ((hB.max (tendsto_const_nhds (x := (0:ℝ)))).add tendsto_inv_atTop_zero)
    simpa [hβ] using this
  have hsq : Tendsto (fun T => Real.sqrt (β T)) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hβt
    simpa using this
  have hbound : Tendsto (fun T => β T + Real.sqrt (β T) + Real.sqrt (β T) * MP T) atTop
      (𝓝 0) := by
    have := (hβt.add hsq).add (hsq.mul hP)
    simpa using this
  have hdiff : Tendsto (fun T => G T - MP T) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [happrox, eventually_gt_atTop (0 : ℝ)] with T hT hT0
    have hβ0 : 0 < β T := by simp only [hβ]; positivity
    set η := Real.sqrt (β T) with hη
    have hη0 : 0 < η := Real.sqrt_pos.2 hβ0
    have hηβ : β T / η = η := by rw [hη]; exact Real.div_sqrt
    have hcf : Continuous fun t => ‖lam T * f t‖ ^ 2 := by fun_prop
    have hcP : Continuous fun t => ‖dpoly (b T) (N T) t‖ ^ 2 :=
      (continuous_dpoly (b T) (N T)).norm.pow 2
    have hcE : Continuous fun t => ‖lam T * f t - dpoly (b T) (N T) t‖ ^ 2 :=
      ((continuous_const.mul hf).sub (continuous_dpoly (b T) (N T))).norm.pow 2
    have e : G T - MP T =
        (∫ t in (0 : ℝ)..T, (‖lam T * f t‖ ^ 2 - ‖dpoly (b T) (N T) t‖ ^ 2)) / T := by
      simp only [hG, hMP]
      rw [intervalIntegral.integral_sub (hcf.intervalIntegrable _ _)
        (hcP.intervalIntegrable _ _), sub_div]
    rw [e, Real.norm_eq_abs, abs_div, abs_of_pos hT0, div_le_iff₀ hT0]
    have hI := intervalIntegral.norm_integral_le_of_norm_le hT0.le
      (Eventually.of_forall fun t _ => by
        rw [Real.norm_eq_abs]
        exact norm_sq_sub_norm_sq_le (lam T * f t) (dpoly (b T) (N T) t) hη0)
      ((show Continuous fun t => (1 + 1 / η) * ‖lam T * f t - dpoly (b T) (N T) t‖ ^ 2 +
          η * ‖dpoly (b T) (N T) t‖ ^ 2 by fun_prop).intervalIntegrable (μ := volume) 0 T)
    rw [← Real.norm_eq_abs]
    refine hI.trans ?_
    rw [intervalIntegral.integral_add ((hcE.const_mul _).intervalIntegrable _ _)
      ((hcP.const_mul _).intervalIntegrable _ _), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
    have hBβ' : B T ≤ β T := by
      simp only [hβ]; linarith [le_max_left (B T) 0, inv_pos.2 hT0]
    have hEint : (∫ t in (0 : ℝ)..T, ‖lam T * f t - dpoly (b T) (N T) t‖ ^ 2) ≤ β T * T :=
      hT.trans (by gcongr)
    have hMPT : (∫ t in (0 : ℝ)..T, ‖dpoly (b T) (N T) t‖ ^ 2) = MP T * T := by
      simp only [hMP]; field_simp
    rw [hMPT]
    have h1η : 0 ≤ 1 + 1 / η := by positivity
    calc (1 + 1 / η) * (∫ t in (0 : ℝ)..T, ‖lam T * f t - dpoly (b T) (N T) t‖ ^ 2) +
          η * (MP T * T)
        ≤ (1 + 1 / η) * (β T * T) + η * (MP T * T) := by gcongr
      _ = (β T + β T / η + η * MP T) * T := by ring
      _ = (β T + η + η * MP T) * T := by rw [hηβ]
  have hGS : Tendsto G atTop (𝓝 S) := by
    have := hdiff.add hP
    simpa using this
  -- `G T = ‖λ_T‖² · M(T)`
  have hl2 : Tendsto (fun T => ‖lam T‖ ^ 2) atTop (𝓝 1) := by
    have := (hlam.norm).pow 2
    simpa using this
  have hdiv := hGS.div hl2 one_ne_zero
  rw [div_one] at hdiv
  refine hdiv.congr' ?_
  filter_upwards [hl2.eventually (lt_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num))] with T hT
  have hne : ‖lam T‖ ^ 2 ≠ 0 := by intro h; rw [h] at hT; norm_num at hT
  simp only [hG, Pi.div_apply]
  have e : (fun t => ‖lam T * f t‖ ^ 2) = fun t => ‖lam T‖ ^ 2 * ‖f t‖ ^ 2 := by
    funext t; rw [norm_mul, mul_pow]
  have hne1 : ‖lam T‖ ≠ 0 := fun h => hne (by rw [h]; ring)
  rw [e, intervalIntegral.integral_const_mul]
  field_simp

end RamanujanTau.MeanSquareFull
