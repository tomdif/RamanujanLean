/-
# The mean square of `∑_{n≤x} τ(n)` at the critical exponent (Cramér–Tong order, up to `log`)

Headlines (evidence level (1): Lean, axiom-clean, unconditional; Deligne not used). Write
`S(x) = ∑_{1≤n≤x} τ(n)`.

* `tau_critical_mean_square_convergent`: `∫₁^∞ S(x)² x^{−2σ−1} dx < ∞` for every `σ > 23/4`;
* `tau_critical_mean_square_mellin`: `c/δ ≤ ∫₁^∞ S(x)² x^{−25/2−2δ} dx ≤ C/δ`, `0 < δ ≤ 1/16`;
* `tau_log_mean_square`: `c log X ≤ ∫₁^X S(x)² x^{−25/2} dx ≤ C log X` for `X ≥ X₀`;
* `tau_mean_square_upper`: `∫₁^X S(x)² dx ≤ C X^{25/2} log X`;
* `tau_mean_square_omega`: `∫₁^X S(x)² dx ≥ c X^{25/2}` for arbitrarily large `X`;
* `tau_mellin_uncond`: `∫₁^∞ S(x) x^{−w−1} dx = L(Δ,w)/w` (absolutely convergent) on `Re w > 23/4`.

Build: `nice -n 10 lake build RamanujanTau.Voronoi.Main`.  See `docs/VORONOI.md`.
-/
import RamanujanTau.Voronoi.Final

set_option autoImplicit false

namespace RamanujanTau.Voronoi

open Complex MeasureTheory Set Filter Topology
open RamanujanTau.HeckeL

/-- **Convergence at every `σ > 23/4`.** -/
theorem tau_critical_mean_square_convergent {σ : ℝ} (hσ : 23 / 4 < σ) :
    IntegrableOn (fun x : ℝ => (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (tau n : ℝ)) ^ 2 * x ^ (-2 * σ - 1))
      (Ioi 1) :=
  tau_mean_square_convergent hσ

/-- **Two-sided Mellin mean square.** -/
theorem tau_critical_mean_square_mellin : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 16 →
      c / δ ≤ ∫ x in Ioi (1 : ℝ),
          (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (tau n : ℝ)) ^ 2 * x ^ (-(25 / 2) - 2 * δ) ∧
      ∫ x in Ioi (1 : ℝ),
          (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (tau n : ℝ)) ^ 2 * x ^ (-(25 / 2) - 2 * δ) ≤ C / δ :=
  tau_mean_square_mellin

/-- **Logarithmic mean square**: `∫₁^X S(x)² x^{−25/2} dx ≍ log X`. -/
theorem tau_log_mean_square : ∃ c C X0 : ℝ, 0 < c ∧ 0 < C ∧ 1 ≤ X0 ∧ ∀ X : ℝ, X0 ≤ X →
    c * Real.log X ≤ ∫ x in Ioc 1 X,
        (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (tau n : ℝ)) ^ 2 * x ^ (-(25 / 2 : ℝ)) ∧
    ∫ x in Ioc 1 X, (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (tau n : ℝ)) ^ 2 * x ^ (-(25 / 2 : ℝ)) ≤
      C * Real.log X := by
  obtain ⟨c, X0, hc, hX0, hlow⟩ := log_mean_lower
  obtain ⟨C, hC, hup⟩ := log_mean_upper
  refine ⟨c, C, max X0 (Real.exp 16), hc, hC, le_trans hX0 (le_max_left _ _), fun X hX => ?_⟩
  exact ⟨hlow X (le_trans (le_max_left _ _) hX), hup X (le_trans (le_max_right _ _) hX)⟩

/-- **Upper mean square** `∫₁^X S(x)² dx ≪ X^{25/2} log X`. -/
theorem tau_mean_square_upper : ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, Real.exp 16 ≤ X →
    ∫ x in Ioc 1 X, (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (tau n : ℝ)) ^ 2 ≤
      C * X ^ (25 / 2 : ℝ) * Real.log X :=
  mean_square_upper

/-- **Ω for the mean square** `∫₁^X S(x)² dx ≠ o(X^{25/2})`. -/
theorem tau_mean_square_omega : ∃ c : ℝ, 0 < c ∧ ∀ Y : ℝ, ∃ X : ℝ, Y ≤ X ∧
    c * X ^ (25 / 2 : ℝ) ≤ ∫ x in Ioc 1 X, (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (tau n : ℝ)) ^ 2 :=
  mean_square_omega

/-- **Unconditional Mellin identity** on `Re w > 23/4`. -/
theorem tau_mellin_identity {w : ℂ} (hw : 23 / 4 < w.re) :
    MellinConvergent (fun x : ℝ => ((∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (tau n : ℝ) : ℝ) : ℂ)) (-w) ∧
      mellin (fun x : ℝ => ((∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (tau n : ℝ) : ℝ) : ℂ)) (-w) =
        tauL w / w := by
  have e : (fun x : ℝ => ((∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (tau n : ℝ) : ℝ) : ℂ)) =
      RamanujanTau.TauOmegaPartial.A Dl := funext fun x => (A_Dl_eq x).symm
  rw [e]; exact tau_mellin_uncond hw

end RamanujanTau.Voronoi

#print axioms RamanujanTau.Voronoi.tau_critical_mean_square_convergent
#print axioms RamanujanTau.Voronoi.tau_critical_mean_square_mellin
#print axioms RamanujanTau.Voronoi.tau_log_mean_square
#print axioms RamanujanTau.Voronoi.tau_mean_square_upper
#print axioms RamanujanTau.Voronoi.tau_mean_square_omega
#print axioms RamanujanTau.Voronoi.tau_mellin_identity
#print axioms RamanujanTau.Voronoi.block_bound
#print axioms RamanujanTau.Voronoi.tail_bound
#print axioms RamanujanTau.Voronoi.differentiableOn_P
#print axioms RamanujanTau.Voronoi.mellin_eq_P_strip
#print axioms RamanujanTau.Voronoi.mc_all
#print axioms RamanujanTau.Voronoi.mellin_sq
#print axioms RamanujanTau.Voronoi.Phi_upper
#print axioms RamanujanTau.Voronoi.Phi_lower
