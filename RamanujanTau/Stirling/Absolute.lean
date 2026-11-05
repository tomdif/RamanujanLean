/-
# Two-sided Stirling-type bounds for `|Γ(σ+it)|`

From the reflection formula, `|Γ(½+it)|² = π / cosh(πt)` (`norm_Gamma_half_sq`), hence
`|Γ(3/2+it)| = |½+it| √(π/cosh πt)`. Combined with the ratio bounds of `GammaRatio`
(non-integer shifts allowed), for every real `σ ≥ 3/2` and every real `t`, with
`T = ‖3/2 + it‖ ≍ 1 + |t|`:

    (√π/3) e⁻¹⁰ T^{σ−1/2} e^{−π|t|/2} ≤ |Γ(σ+it)| ≤ (n+1)! e¹⁰ √(2π) T^{σ−1/2} e^{−π|t|/2}

(`σ − 3/2 ≤ n + 1`). This is Stirling's `|Γ(σ+it)| ≍ |t|^{σ−1/2} e^{−π|t|/2}` with explicit
constants, uniformly for `σ` in compact subsets of `[3/2, ∞)`; smaller `σ` follow from
`Γ(s) = Γ(s+n)/∏(s+j)`.
-/
import RamanujanTau.Stirling.GammaRatio

set_option autoImplicit false

namespace RamanujanTau.Stirling

open Complex Real

/-- **`|Γ(½+it)|² = π / cosh(πt)`.** -/
theorem norm_Gamma_half_sq (t : ℝ) :
    ‖Complex.Gamma ((1 / 2 : ℂ) + t * I)‖ ^ 2 = π / Real.cosh (π * t) := by
  set s : ℂ := (1 / 2 : ℂ) + t * I with hs
  have h1 : 1 - s = starRingEnd ℂ s := by
    apply Complex.ext <;> simp [hs]; norm_num
  have hrefl := Complex.Gamma_mul_Gamma_one_sub s
  rw [h1, Complex.Gamma_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq] at hrefl
  have hsin : Complex.sin (π * s) = (Real.cosh (π * t) : ℂ) := by
    rw [show (π : ℂ) * s = ((π * t : ℝ) : ℂ) * I + π / 2 by rw [hs]; push_cast; ring,
      Complex.sin_add_pi_div_two, Complex.cos_mul_I, Complex.ofReal_cosh]
  rw [hsin] at hrefl
  have := congrArg Complex.re hrefl
  rw [Complex.ofReal_re] at this
  rw [this, ← Complex.ofReal_div, Complex.ofReal_re]

lemma cosh_bounds (x : ℝ) : Real.exp |x| / 2 ≤ Real.cosh x ∧ Real.cosh x ≤ Real.exp |x| := by
  rw [← Real.cosh_abs, Real.cosh_eq]
  have h1 : Real.exp (-|x|) ≤ Real.exp |x| := Real.exp_le_exp.2 (by linarith [abs_nonneg x])
  have h2 : 0 < Real.exp (-|x|) := Real.exp_pos _
  constructor <;> linarith

lemma sqrt_pi_div_cosh_le (t : ℝ) :
    Real.sqrt (π / Real.cosh (π * t)) ≤ Real.sqrt (2 * π) * Real.exp (-(π * |t|) / 2) := by
  have hc := (cosh_bounds (π * t)).1
  have habs : |π * t| = π * |t| := by rw [abs_mul, abs_of_pos Real.pi_pos]
  rw [habs] at hc
  have hcpos : 0 < Real.cosh (π * t) := Real.cosh_pos _
  have he : Real.exp (-(π * |t|) / 2) = Real.sqrt (Real.exp (-(π * |t|))) := by
    rw [← Real.exp_half]
  rw [he, ← Real.sqrt_mul (by positivity)]
  apply Real.sqrt_le_sqrt
  rw [div_le_iff₀ hcpos, Real.exp_neg]
  have hE : 0 < Real.exp (π * |t|) := Real.exp_pos _
  calc π = 2 * π * (Real.exp (π * |t|))⁻¹ * (Real.exp (π * |t|) / 2) := by field_simp
    _ ≤ 2 * π * (Real.exp (π * |t|))⁻¹ * Real.cosh (π * t) := by gcongr

lemma le_sqrt_pi_div_cosh (t : ℝ) :
    Real.sqrt π * Real.exp (-(π * |t|) / 2) ≤ Real.sqrt (π / Real.cosh (π * t)) := by
  have hc := (cosh_bounds (π * t)).2
  have habs : |π * t| = π * |t| := by rw [abs_mul, abs_of_pos Real.pi_pos]
  rw [habs] at hc
  have hcpos : 0 < Real.cosh (π * t) := Real.cosh_pos _
  have he : Real.exp (-(π * |t|) / 2) = Real.sqrt (Real.exp (-(π * |t|))) := by
    rw [← Real.exp_half]
  rw [he, ← Real.sqrt_mul Real.pi_pos.le]
  apply Real.sqrt_le_sqrt
  rw [le_div_iff₀ hcpos, Real.exp_neg]
  have hE : 0 < Real.exp (π * |t|) := Real.exp_pos _
  calc π * (Real.exp (π * |t|))⁻¹ * Real.cosh (π * t)
      ≤ π * (Real.exp (π * |t|))⁻¹ * Real.exp (π * |t|) := by gcongr
    _ = π := by field_simp

/-- `|Γ(3/2+it)| = |½+it| √(π/cosh πt)`. -/
lemma norm_Gamma_three_halves (t : ℝ) :
    ‖Complex.Gamma ((3 / 2 : ℂ) + t * I)‖ =
      ‖(1 / 2 : ℂ) + t * I‖ * Real.sqrt (π / Real.cosh (π * t)) := by
  have hne : (1 / 2 : ℂ) + t * I ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this
  rw [show (3 / 2 : ℂ) + t * I = ((1 / 2 : ℂ) + t * I) + 1 by ring, Complex.Gamma_add_one _ hne,
    norm_mul, ← norm_Gamma_half_sq, Real.sqrt_sq (norm_nonneg _)]

lemma norm_half_le (t : ℝ) : ‖(1 / 2 : ℂ) + t * I‖ ≤ ‖(3 / 2 : ℂ) + t * I‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), sq_norm_eq, sq_norm_eq]; simp; norm_num

lemma norm_three_halves_le (t : ℝ) : ‖(3 / 2 : ℂ) + t * I‖ ≤ 3 * ‖(1 / 2 : ℂ) + t * I‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (by positivity), mul_pow, sq_norm_eq, sq_norm_eq]; simp
  nlinarith [sq_nonneg t]

/-- **Stirling upper bound.** For `3/2 ≤ σ ≤ n + 5/2` and every real `t`, with
`T = ‖3/2+it‖`: `|Γ(σ+it)| ≤ (n+1)! e¹⁰ √(2π) T^{σ−1/2} e^{−π|t|/2}`. -/
theorem norm_Gamma_le_stirling {σ : ℝ} (hσ : 3 / 2 ≤ σ) (n : ℕ) (hn : σ - 3 / 2 ≤ n + 1)
    (t : ℝ) :
    ‖Complex.Gamma (σ + t * I)‖ ≤ ((n + 1).factorial : ℝ) * Real.exp 10 * Real.sqrt (2 * π) *
      ‖(3 / 2 : ℂ) + t * I‖ ^ (σ - 1 / 2) * Real.exp (-(π * |t|) / 2) := by
  have h := norm_Gamma_ratio_le_of_le (α := σ) (β := 3 / 2) (by norm_num) hσ n hn t
  have e32 : ((3 / 2 : ℝ) : ℂ) = (3 / 2 : ℂ) := by push_cast; ring
  rw [e32, norm_Gamma_three_halves] at h
  set T := ‖(3 / 2 : ℂ) + t * I‖ with hT
  have hT1 : 1 ≤ T := one_le_norm_of_re (by simp; norm_num)
  have hTpos : 0 < T := by linarith
  have hsplit : T ^ (σ - 1 / 2) = T ^ (σ - 3 / 2) * T := by
    rw [← Real.rpow_add_one hTpos.ne']; ring_nf
  have hc := sqrt_pi_div_cosh_le t
  have hh := norm_half_le t
  rw [← hT] at hh
  refine h.trans ?_
  rw [hsplit]
  calc ((n + 1).factorial : ℝ) * Real.exp 10 * T ^ (σ - 3 / 2) *
        (‖(1 / 2 : ℂ) + t * I‖ * Real.sqrt (π / Real.cosh (π * t)))
      ≤ ((n + 1).factorial : ℝ) * Real.exp 10 * T ^ (σ - 3 / 2) *
        (T * (Real.sqrt (2 * π) * Real.exp (-(π * |t|) / 2))) := by gcongr
    _ = _ := by ring

/-- **Stirling lower bound.** For `σ ≥ 3/2` and every real `t`, with `T = ‖3/2+it‖`:
`(√π/3) e⁻¹⁰ T^{σ−1/2} e^{−π|t|/2} ≤ |Γ(σ+it)|`. -/
theorem stirling_le_norm_Gamma {σ : ℝ} (hσ : 3 / 2 ≤ σ) (t : ℝ) :
    Real.sqrt π / 3 * Real.exp (-10) * ‖(3 / 2 : ℂ) + t * I‖ ^ (σ - 1 / 2) *
      Real.exp (-(π * |t|) / 2) ≤ ‖Complex.Gamma (σ + t * I)‖ := by
  have hz : 1 ≤ ((3 / 2 : ℂ) + t * I).re := by simp; norm_num
  have h := norm_Gamma_mul_rpow_le_add hz (θ := σ - 3 / 2) (by linarith)
  have e : (3 / 2 : ℂ) + t * I + ((σ - 3 / 2 : ℝ) : ℂ) = σ + t * I := by push_cast; ring
  rw [e, norm_Gamma_three_halves] at h
  set T := ‖(3 / 2 : ℂ) + t * I‖ with hT
  have hT1 : 1 ≤ T := one_le_norm_of_re hz
  have hTpos : 0 < T := by linarith
  have hsplit : T ^ (σ - 1 / 2) = T ^ (σ - 3 / 2) * T := by
    rw [← Real.rpow_add_one hTpos.ne']; ring_nf
  have hc := le_sqrt_pi_div_cosh t
  have hh := norm_three_halves_le t
  rw [← hT] at hh
  have hE : Real.exp (-10) * Real.exp 10 = 1 := by rw [← Real.exp_add]; simp
  have hlow : Real.sqrt π / 3 * T ^ (σ - 1 / 2) * Real.exp (-(π * |t|) / 2) ≤
      Real.exp 10 * ‖Complex.Gamma (σ + t * I)‖ := by
    refine le_trans ?_ h
    rw [hsplit]
    calc Real.sqrt π / 3 * (T ^ (σ - 3 / 2) * T) * Real.exp (-(π * |t|) / 2)
        = T / 3 * (Real.sqrt π * Real.exp (-(π * |t|) / 2)) * T ^ (σ - 3 / 2) := by ring
      _ ≤ ‖(1 / 2 : ℂ) + t * I‖ * Real.sqrt (π / Real.cosh (π * t)) * T ^ (σ - 3 / 2) := by
          gcongr; linarith
  have hpos : 0 < Real.exp (-10) := Real.exp_pos _
  calc Real.sqrt π / 3 * Real.exp (-10) * T ^ (σ - 1 / 2) * Real.exp (-(π * |t|) / 2)
      = Real.exp (-10) * (Real.sqrt π / 3 * T ^ (σ - 1 / 2) * Real.exp (-(π * |t|) / 2)) := by
        ring
    _ ≤ Real.exp (-10) * (Real.exp 10 * ‖Complex.Gamma (σ + t * I)‖) := by gcongr
    _ = _ := by rw [← mul_assoc, hE, one_mul]

end RamanujanTau.Stirling

#print axioms RamanujanTau.Stirling.norm_Gamma_half_sq
#print axioms RamanujanTau.Stirling.norm_Gamma_le_stirling
#print axioms RamanujanTau.Stirling.stirling_le_norm_Gamma
