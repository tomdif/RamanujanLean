import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.Basic

/-!
# Identity principles: power series in `q`, Laurent polynomials in `u`
-/

set_option autoImplicit false

noncomputable section

namespace TateFormal

open Filter Topology

/-- a power series `Σ cₙ qⁿ`, absolutely convergent on `‖q‖ ≤ ρ`, vanishing for `0 < ‖q‖ < ρ`, is zero. -/
theorem coeff_zero_of_vanish (c : ℕ → ℂ) (ρ : NNReal) (hρ : 0 < ρ)
    (hs : Summable (fun N => ‖c N‖ * (ρ : ℝ) ^ N))
    (h : ∀ q : ℂ, q ≠ 0 → ‖q‖ < ρ → ∑' N, c N * q ^ N = 0) (N : ℕ) : c N = 0 := by
  set p := FormalMultilinearSeries.ofScalars ℂ c
  have hr : (ρ : ENNReal) ≤ p.radius := by
    apply p.le_radius_of_summable_norm
    simpa [p, FormalMultilinearSeries.ofScalars_norm] using hs
  have hpos : 0 < p.radius := lt_of_lt_of_le (by exact_mod_cast hρ) hr
  have hf := p.hasFPowerSeriesOnBall hpos
  have hsum : ∀ q : ℂ, p.sum q = ∑' n, c n * q ^ n := by
    intro q
    simp only [FormalMultilinearSeries.sum, p, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
  have hev : ∀ᶠ q in 𝓝[≠] (0 : ℂ), p.sum q = 0 := by
    have hball : Metric.ball (0 : ℂ) ρ ∈ 𝓝 (0 : ℂ) := Metric.ball_mem_nhds _ (by exact_mod_cast hρ)
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hball] with q hq hq'
    rw [hsum]
    exact h q hq (by simpa using hq')
  have hz := (hf.analyticAt.frequently_zero_iff_eventually_zero).mp hev.frequently
  have := hf.hasFPowerSeriesAt.eq_zero_of_eventually hz
  have h2 := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p N (fun _ => 1)) this
  simpa [p, FormalMultilinearSeries.ofScalars_apply_eq] using h2

/-- a Laurent polynomial over `ℤ` vanishing at every `u ∈ S` (an infinite set of nonzero complex
numbers) is zero. -/
theorem laurent_eq_zero (P : LaurentPolynomial ℤ) (S : Set ℂ) (hS : S.Infinite)
    (h0 : ∀ u ∈ S, u ≠ 0)
    (h : ∀ u (hu : u ∈ S), LaurentPolynomial.eval₂ (Int.castRingHom ℂ) (Units.mk0 u (h0 u hu)) P = 0) :
    P = 0 := by
  obtain ⟨n, f, hf⟩ := P.exists_T_pow
  have hf0 : f.map (Int.castRingHom ℂ) = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply hS.mono
    intro u hu
    have := congrArg (LaurentPolynomial.eval₂ (Int.castRingHom ℂ) (Units.mk0 u (h0 u hu))) hf
    rw [LaurentPolynomial.eval₂_toLaurent, map_mul, h u hu, zero_mul] at this
    simpa [Polynomial.IsRoot, Polynomial.eval_map] using this
  have : f = 0 := Polynomial.map_injective _ (RingHom.injective_int _) (by simpa using hf0)
  rw [this, map_zero] at hf
  have hu := LaurentPolynomial.isUnit_T (R := ℤ) n
  exact (hu.mul_left_eq_zero).mp hf.symm

end TateFormal
