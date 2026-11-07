/-
# The `L²`-truncated Voronoi formula for `Σ_{n≤x} τ(n)` and the Cramér–Tong limit

Evidence level (1): Lean, axiom-clean, unconditional; Deligne is not used.

* `voronoi_truncated_L2` (deliverable A): for every `0 < θ ≤ 1/4`,

      X^{−25/2} ∫_X^{2X} ( S(x) − x^{23/4}/(π√2) Σ_{n≤X^θ} τ(n) n^{−25/4} cos(4π√(nx) − π/4) )² dx → 0.

* `voronoi_truncated_L2_rate`: the same with an explicit majorant
  `C X^{25/2} (X^{−1/16} + Σ_{n>X^θ} τ(n)² n^{−25/2})` for `X ≥ 144`.
* `tau_cramer` (deliverable B): `X^{−25/2} ∫₁^X S(x)² dx → B/(50π²)`, `B = Σ τ(n)² n^{−25/2}`
  (existence of the limit; `CramerMeanSquare.tau_cramer_constant` had identified it conditionally).
* `tau_omega_pm_exact` (deliverable B): for every `c < 1/(2π√2)` and all large `X`, both
  `S(x) > c x^{23/4}` and `S(x) < −c x^{23/4}` occur in `[X, 2X]` — exact `Ω±(x^{23/4})`.

Intermediate results (all level 1): the Schläfli kernel asymptotic with phase `Ik_asymp_twelve`,
the contour identification `lineInt_eq_Ik`, the exact dual expansion `dual_W` of the Riesz means
(from the modular relation `Dq_modular` and inverse Laplace `laplace_inv`), the mean-value
theorem `mean_value`.

Build: `nice -n 10 lake build RamanujanTau.VoronoiTrunc.Main`.  See `docs/VORONOI_TRUNC.md`.
-/
import RamanujanTau.VoronoiTrunc.Omega

set_option autoImplicit false

namespace RamanujanTau.VoronoiTrunc

open Complex Real MeasureTheory Set Filter Topology

lemma Vth_eq_explicit (N : ℕ) (x : ℝ) :
    Vth N x = x ^ (23 / 4 : ℝ) / (π * √2) * ∑ n ∈ Finset.Icc 1 N,
      (tau n : ℝ) * (n : ℝ) ^ (-(25 / 4) : ℝ) * Real.cos (4 * π * √((n : ℝ) * x) - π / 4) := by
  unfold Vth bco th
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Real.sqrt_mul (Nat.cast_nonneg n)]
  ring_nf

lemma Sre_eq (x : ℝ) : Sre x = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (tau n : ℝ) := rfl

/-- **(A) The `L²`-truncated Voronoi formula.** -/
theorem voronoi_truncated_L2 {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 4) :
    Tendsto (fun X : ℝ => (∫ x in X..2 * X,
        (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (tau n : ℝ) -
          x ^ (23 / 4 : ℝ) / (π * √2) * ∑ n ∈ Finset.Icc 1 ⌊X ^ θ⌋₊,
            (tau n : ℝ) * (n : ℝ) ^ (-(25 / 4) : ℝ) * Real.cos (4 * π * √((n : ℝ) * x) - π / 4)) ^ 2) /
        X ^ (25 / 2 : ℝ)) atTop (𝓝 0) := by
  refine (voronoi_L2 hθ0 hθ).congr fun X => ?_
  congr 1
  refine intervalIntegral.integral_congr fun x _ => ?_
  show (Sre x - Vth ⌊X ^ θ⌋₊ x) ^ 2 = _
  rw [Vth_eq_explicit, Sre_eq]

/-- **(A′) With an explicit rate.** -/
theorem voronoi_truncated_L2_rate {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℝ, 144 ≤ X →
      ∫ x in X..2 * X, (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (tau n : ℝ) -
          x ^ (23 / 4 : ℝ) / (π * √2) * ∑ n ∈ Finset.Icc 1 ⌊X ^ θ⌋₊,
            (tau n : ℝ) * (n : ℝ) ^ (-(25 / 4) : ℝ) * Real.cos (4 * π * √((n : ℝ) * x) - π / 4)) ^ 2 ≤
        C * X ^ (25 / 2 : ℝ) * (X ^ (-(1 / 16) : ℝ) +
          ∑' k : ℕ, ((tau (k + (⌊X ^ θ⌋₊ + 1)) : ℝ)) ^ 2 *
            ((k + (⌊X ^ θ⌋₊ + 1) : ℕ) : ℝ) ^ (-(25 / 2) : ℝ)) := by
  obtain ⟨C, hC0, hC⟩ := voronoi_L2_bound hθ0 hθ
  refine ⟨C, hC0, fun X hX => ?_⟩
  have h := hC X hX
  rw [intervalIntegral.integral_of_le (by linarith)]
  have e1 : ∫ x in Ioc X (2 * X), (Sre x - Vth ⌊X ^ θ⌋₊ x) ^ 2 =
      ∫ x in Ioc X (2 * X), (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (tau n : ℝ) -
          x ^ (23 / 4 : ℝ) / (π * √2) * ∑ n ∈ Finset.Icc 1 ⌊X ^ θ⌋₊,
            (tau n : ℝ) * (n : ℝ) ^ (-(25 / 4) : ℝ) * Real.cos (4 * π * √((n : ℝ) * x) - π / 4)) ^ 2 := by
    congr 1; funext x; rw [Vth_eq_explicit, Sre_eq]
  have e2 : tl ⌊X ^ θ⌋₊ = ∑' k : ℕ, ((tau (k + (⌊X ^ θ⌋₊ + 1)) : ℝ)) ^ 2 *
      ((k + (⌊X ^ θ⌋₊ + 1) : ℕ) : ℝ) ^ (-(25 / 2) : ℝ) := by
    unfold tl; congr 1; funext k; rw [sq_bco]
  rw [← e1, ← e2]; exact h

/-- **(B) The Cramér–Tong theorem**: `X^{−25/2} ∫₁^X S(x)² dx → B/(50π²)`. -/
theorem tau_cramer :
    Tendsto (fun X : ℝ => (∫ x in (1 : ℝ)..X, (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (tau n : ℝ)) ^ 2) /
        X ^ (25 / 2 : ℝ)) atTop
      (𝓝 ((∑' n : ℕ, ((tau n : ℝ)) ^ 2 * (n : ℝ) ^ (-(25 / 2 : ℝ))) / (50 * π ^ 2))) := by
  have hB : Bsum = ∑' n : ℕ, ((tau n : ℝ)) ^ 2 * (n : ℝ) ^ (-(25 / 2 : ℝ)) := by
    unfold Bsum; congr 1; funext n; rw [sq_bco]
  rw [← hB]
  exact tau_cramer_core

/-- **(B′) Exact `Ω±(x^{23/4})`, in every dyadic interval**, with constant `1/(2π√2)`. -/
theorem tau_omega_pm_exact {c : ℝ} (hc : c < 1 / (2 * π * √2)) :
    ∀ᶠ X in atTop,
      (∃ x ∈ Icc X (2 * X), c * x ^ (23 / 4 : ℝ) < ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (tau n : ℝ)) ∧
      (∃ x ∈ Icc X (2 * X), ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (tau n : ℝ) < -c * x ^ (23 / 4 : ℝ)) :=
  (omega_plus hc).and (omega_minus hc)

/-- `Ω±(x^{23/4})` in the form of `TauOmegaPM.tau_partial_sum_omega_pm` (exponent `23/4`, not `< 28/5`). -/
theorem tau_partial_sum_omega_pm_exact {c : ℝ} (hc : c < 1 / (2 * π * √2)) (X : ℝ) :
    (∃ x : ℝ, X ≤ x ∧ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (tau n : ℝ) < -c * x ^ (23 / 4 : ℝ)) ∧
    (∃ x : ℝ, X ≤ x ∧ c * x ^ (23 / 4 : ℝ) < ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (tau n : ℝ)) := by
  obtain ⟨Y, hY⟩ := (tau_omega_pm_exact hc).exists_forall_of_atTop
  obtain ⟨⟨x1, hx1, h1⟩, ⟨x2, hx2, h2⟩⟩ := hY (max X Y) (le_max_right _ _)
  exact ⟨⟨x2, le_trans (le_max_left _ _) hx2.1, h2⟩, ⟨x1, le_trans (le_max_left _ _) hx1.1, h1⟩⟩

/-- The kernel asymptotic with phase, in the form used (`I₁₂(L) = J₁₂(2L)`). -/
theorem kernel_asymp (L : ℝ) (hL : 0 < L) :
    |Ik 12 L - Real.cos (2 * L - π / 4) / √(π * L)| ≤ Ck 12 / (π * L) :=
  Ik_asymp_twelve hL

end RamanujanTau.VoronoiTrunc

#print axioms RamanujanTau.VoronoiTrunc.voronoi_truncated_L2
#print axioms RamanujanTau.VoronoiTrunc.voronoi_truncated_L2_rate
#print axioms RamanujanTau.VoronoiTrunc.tau_cramer
#print axioms RamanujanTau.VoronoiTrunc.tau_omega_pm_exact
#print axioms RamanujanTau.VoronoiTrunc.tau_partial_sum_omega_pm_exact
#print axioms RamanujanTau.VoronoiTrunc.kernel_asymp
#print axioms RamanujanTau.VoronoiTrunc.lineInt_eq_Ik
#print axioms RamanujanTau.VoronoiTrunc.dual_W
#print axioms RamanujanTau.VoronoiTrunc.kB_eq_Ik
#print axioms RamanujanTau.VoronoiTrunc.Dq_modular
#print axioms RamanujanTau.VoronoiTrunc.laplace_inv
#print axioms RamanujanTau.VoronoiTrunc.mean_value
#print axioms RamanujanTau.VoronoiTrunc.DkC_WC_eq
