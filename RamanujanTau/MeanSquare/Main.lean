/-
# Carlson–Potter mean values for `L(Δ,s)` (unnormalized: critical line `Re s = 6`)

For every `σ > 37/6`,

    (1/T) ∫₀ᵀ |L(Δ, σ+it)|² dt  →  ∑_{n ≥ 1} τ(n)² n^{-2σ}     (T → ∞).

* `σ > 13/2` (absolute convergence): `mean_square_abs`;
* `37/6 < σ ≤ 13/2` (inside the convexity strip): `mean_square_strip`.

The classical theorem (Carlson 1922; Potter 1940) holds for every `σ > 6`; the range `σ > 37/6`
is what the Riesz-smoothed Perron approximation plus the convexity bound
`‖L(Δ,σ+it)‖ ≪ (1+|t|)^{13/2−σ+ε}` and the Dirichlet-polynomial mean value theorem
`∫₀ᵀ |∑ bₙ n^{-it}|² = T ∑ |bₙ|² + O(log N ∑ n |bₙ|²)` give.  See `docs/MEAN_SQUARE.md`.
-/
import RamanujanTau.MeanSquare.Strip

set_option autoImplicit false

namespace RamanujanTau.MeanSquare

open Complex Filter Topology
open RamanujanTau.HeckeL

/-- **Mean-square theorem for `L(Δ,s)`, `σ > 37/6`.** -/
theorem mean_square_tauL {σ : ℝ} (hσ : 37 / 6 < σ) :
    Tendsto (fun T : ℝ => (∫ t in (0 : ℝ)..T, ‖tauL ((σ : ℂ) + t * I)‖ ^ 2) / T) atTop
      (𝓝 (∑' n : ℕ, ((tau n : ℝ)) ^ 2 * (n : ℝ) ^ (-(2 * σ)))) := by
  rcases le_or_gt σ (13 / 2) with h | h
  · exact mean_square_strip hσ h
  · exact mean_square_abs h

/-- The limit is finite and positive: `∑ τ(n)² n^{-2σ}` converges for `σ > 6`. -/
theorem summable_mean_square_limit {σ : ℝ} (hσ : 6 < σ) :
    Summable fun n : ℕ => ((tau n : ℝ)) ^ 2 * (n : ℝ) ^ (-(2 * σ)) :=
  summable_tau_sq (by linarith)

/-- Supporting results. -/
example (b : ℕ → ℂ) (N : ℕ) (T : ℝ) :
    |(∫ t in (0 : ℝ)..T, ‖dpoly b N t‖ ^ 2) - T * ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2| ≤
      6 * H N * ∑ n ∈ Finset.Icc 1 N, (n : ℝ) * ‖b n‖ ^ 2 := mv_poly b N T

end RamanujanTau.MeanSquare

#print axioms RamanujanTau.MeanSquare.mean_square_tauL
#print axioms RamanujanTau.MeanSquare.mean_square_abs
#print axioms RamanujanTau.MeanSquare.mean_square_strip
#print axioms RamanujanTau.MeanSquare.summable_mean_square_limit
#print axioms RamanujanTau.MeanSquare.mv_poly
#print axioms RamanujanTau.MeanSquare.approx_tauL
#print axioms RamanujanTau.MeanSquare.shift_identity
#print axioms RamanujanTau.MeanSquare.perron_c
#print axioms RamanujanTau.MeanSquare.mean_sq_of_approx
