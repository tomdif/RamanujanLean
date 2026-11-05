/-
# Hardy's theorem for `L(Δ,s)`: infinitely many zeros on the critical line `Re s = 6`

See `docs/HARDY_ZEROS.md`.

* `Zr t = Λ(6+it)` is real and even (`Zc_eq_Zr`, `Zr_neg`), continuous, and decays like
  `e^{−(π/2−ε)|t|}` (`Decay`).
* `∫ Z(t) e^{αt} dt = 2π e^{6iα} Δ(i e^{iα})` for `|α| < π/2` (`Fourier.integral_Zc_exp`:
  Mellin inversion on the real axis + identity theorem on the strip).
* `Δ(i e^{i(π/2−β)}) = O(β^N)` for every `N` (`Cusp.Dc_rot_decay`: `i e^{iα} → −1`, a cusp).
* `Abstract.hardy_abstract`: these force arbitrarily large zeros of `Z`.
-/
import RamanujanTau.HardyZeros.Cusp
import RamanujanTau.HardyZeros.Abstract

set_option autoImplicit false

namespace RamanujanTau.HardyZeros

open Complex MeasureTheory Set Filter
open RamanujanTau.HeckeL
open scoped Real

lemma norm_Zc_eq (t : ℝ) : ‖Zc t‖ = |Zr t| := by
  rw [Zc_eq_Zr, Complex.norm_real, Real.norm_eq_abs]

lemma Zr_integrable {a : ℝ} (ha0 : 0 ≤ a) (ha : a < π / 2) :
    Integrable fun t => Zr t * Real.exp (a * t) := by
  refine (integrable_heckeLambda_line ha).mono'
    ((continuous_Zr.mul (by fun_prop)).aestronglyMeasurable)
    (Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), ← norm_Zc_eq]
  have h1 : ‖Zc t‖ ≤ ‖Zc t‖ * (1 + |t|) := le_mul_of_one_le_right (norm_nonneg _)
    (by linarith [abs_nonneg t])
  have h2 : Real.exp (a * t) ≤ Real.exp (a * |t|) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_abs_self t) ha0)
  exact mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)

/-- The exponential moments of `Z` as boundary values of `Δ`. -/
lemma abs_integral_Zr_exp {α : ℝ} (hα : |α| < π / 2) :
    |∫ t, Zr t * Real.exp (α * t)| = 2 * π * ‖Dc (cexp (α * I) * I)‖ := by
  have h := integral_Zc_exp hα
  have hc : (∫ t : ℝ, Zc t * cexp (α * t)) = ((∫ t, Zr t * Real.exp (α * t) : ℝ) : ℂ) := by
    calc (∫ t : ℝ, Zc t * cexp (α * t))
        = ∫ t : ℝ, ((Zr t * Real.exp (α * t) : ℝ) : ℂ) := by
          refine integral_congr_ae (Eventually.of_forall fun t => ?_)
          simp only [Zc_eq_Zr, Complex.ofReal_mul, Complex.ofReal_exp]
      _ = _ := integral_ofReal
  rw [hc] at h
  have := congrArg norm h
  rw [Complex.norm_real, Real.norm_eq_abs] at this
  have e : (6 * ((α : ℂ) * I)).re = 0 := by simp
  rw [this, norm_mul, norm_mul, norm_mul, Complex.norm_exp, e, Real.exp_zero, one_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  norm_num

lemma Zr_decay (N : ℕ) : ∃ C β₀ : ℝ, 0 < β₀ ∧ ∀ β, 0 < β → β ≤ β₀ →
    |∫ t, Zr t * Real.exp ((π / 2 - β) * t)| ≤ C * β ^ N := by
  obtain ⟨C, β₀, hβ₀, hβ₀1, hC⟩ := Dc_rot_decay N
  refine ⟨2 * π * C, β₀, hβ₀, fun β hβ hββ₀ => ?_⟩
  have hα : |π / 2 - β| < π / 2 := by
    rw [abs_lt]; constructor <;> linarith [Real.pi_gt_three]
  rw [abs_integral_Zr_exp hα]
  have := hC β hβ hββ₀
  calc 2 * π * ‖Dc (cexp (((π / 2 - β : ℝ) : ℂ) * I) * I)‖ ≤ 2 * π * (C * β ^ N) := by
        gcongr
    _ = 2 * π * C * β ^ N := by ring

/-- **Hardy's theorem for `Z(t) = Λ(Δ, 6+it)`.** -/
theorem Zr_infinitely_many_zeros : ∀ T : ℝ, ∃ t > T, Zr t = 0 :=
  hardy_abstract Zr continuous_Zr Zr_neg (fun _ ha0 ha => Zr_integrable ha0 ha) Zr_decay

/-- **Hardy's theorem for `Λ(Δ,s)`**: the completed L-function has arbitrarily large zeros on
`Re s = 6`. -/
theorem heckeLambda_infinitely_many_critical_zeros :
    ∀ T : ℝ, ∃ t > T, heckeLambda (6 + t * I) = 0 := by
  intro T
  obtain ⟨t, ht, h0⟩ := Zr_infinitely_many_zeros T
  refine ⟨t, ht, ?_⟩
  have := Zc_eq_Zr t
  rw [h0, Complex.ofReal_zero] at this
  exact this

/-- **Hardy's theorem for the Ramanujan L-function**: `L(Δ,s)` has zeros `6 + it` with `t`
arbitrarily large. -/
theorem tauL_infinitely_many_critical_zeros : ∀ T : ℝ, ∃ t > T, tauL (6 + t * I) = 0 := by
  intro T
  obtain ⟨t, ht, h0⟩ := heckeLambda_infinitely_many_critical_zeros T
  exact ⟨t, ht, by rw [tauL, h0, mul_zero]⟩

/-- **The set of ordinates of critical zeros is infinite.** -/
theorem tauL_critical_zeros_infinite : Set.Infinite {t : ℝ | tauL (6 + t * I) = 0} := by
  refine Set.infinite_of_not_bddAbove fun ⟨T, hT⟩ => ?_
  obtain ⟨t, ht, h0⟩ := tauL_infinitely_many_critical_zeros T
  exact absurd (hT h0) (not_le.mpr ht)

/-- **Infinitely many zeros of `L(Δ,s)` on `Re s = 6`**, as a set of complex numbers. -/
theorem tauL_zeros_on_critical_line_infinite :
    Set.Infinite {s : ℂ | s.re = 6 ∧ tauL s = 0} := by
  have hinj : Set.InjOn (fun t : ℝ => (6 : ℂ) + t * I) {t : ℝ | tauL (6 + t * I) = 0} := by
    intro a _ b _ h
    have := congrArg Complex.im h
    simpa using this
  refine Set.infinite_of_injOn_mapsTo hinj (fun t ht => ?_) tauL_critical_zeros_infinite
  exact ⟨by simp, ht⟩

end RamanujanTau.HardyZeros

#print axioms RamanujanTau.HardyZeros.hardy_abstract
#print axioms RamanujanTau.HardyZeros.integral_Zc_exp
#print axioms RamanujanTau.HardyZeros.Dc_rot_decay
#print axioms RamanujanTau.HardyZeros.Zr_infinitely_many_zeros
#print axioms RamanujanTau.HardyZeros.heckeLambda_infinitely_many_critical_zeros
#print axioms RamanujanTau.HardyZeros.tauL_infinitely_many_critical_zeros
#print axioms RamanujanTau.HardyZeros.tauL_critical_zeros_infinite
#print axioms RamanujanTau.HardyZeros.tauL_zeros_on_critical_line_infinite
